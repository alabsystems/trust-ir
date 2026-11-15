// Copyright 2026 Andrew Yates | SPDX-License-Identifier: Apache-2.0
use super::*;
use trust_ir_build::clean_kernel::Environment;
use trust_ir_build::clean_u32_boxed_prefix_cic::check_tagged_u32_boxed_prefix_law;
use trust_ir_build::core_execution::Limits;

fn limits() -> Limits {
    Limits {
        max_operations: 20000,
        max_locals: 4096,
        max_list_items: 4096,
        max_lookup_candidates: 1024,
        lookup_heartbeats: 1000000,
        lookup_cache_entries: 100000,
    }
}
fn refl(ty: Expr, value: Expr) -> Expr {
    Expr::apps(
        Expr::const_(
            Name::from_string("Eq.refl"),
            vec![Level::succ(Level::zero())],
        ),
        [ty, value],
    )
}
fn bound(n: u64) -> Expr {
    app(
        "ir_byte_separation_lt_of_ltb_v1",
        [nat(n), nat(4294967296), refl(c("Bool"), c("Bool.true"))],
    )
}
fn apply(proof: &Expr, x: u64, y: u64, extra: Option<u64>) -> Expr {
    let mut args = vec![
        c("Nat"),
        authored_memory(),
        nat(37),
        nat(x),
        nat(y),
        bound(x),
        bound(y),
        refl(c("Bool"), c("Bool.true")),
    ];
    if let Some(extra) = extra {
        args.push(nat(extra));
    }
    Expr::apps(proof.clone(), args)
}
fn actual(context: &Expr, words: [u64; 2], budget: u64) -> Expr {
    let initial = app(
        "ir_clean_tag32_init_v1",
        [
            c("Nat"),
            context.clone(),
            nat(71),
            list("IRScalar", words.map(|w| app("IRScalar.ptr_", [nat(w)]))),
            authored_memory(),
            nat(37),
        ],
    );
    app(
        "ir_clean_tag32_run_v1",
        [
            c("Nat"),
            context.clone(),
            nat(71),
            nat(0),
            nat(10),
            nat(0),
            nat(1),
            nat(budget),
            initial,
        ],
    )
}
fn replay(
    environment: &Environment,
    proof: &Expr,
    context: &Expr,
    words: [u64; 2],
    budget: u64,
    endpoint: Expr,
) -> bool {
    let claim = eq(
        app("IRCleanTag32RunV1", [c("Nat")]),
        actual(context, words, budget),
        endpoint,
    );
    let mut tc = TypeChecker::new(environment);
    tc.set_allow_partial(false);
    tc.set_allow_unsafe(false);
    let result = tc.check_type(proof, &claim).is_ok();
    assert!(!tc.heartbeat_spent());
    assert!(!trust_ir_build::clean_kernel::tc::declaration_budget_exhausted());
    result
}
fn save(label: &str, claim: &Expr, proof: &Expr) {
    if let Some(root) = std::env::var_os("TRUST_IR_TAGGED_PREFIX_CIC_EVIDENCE_DIR") {
        let root = std::path::PathBuf::from(root);
        std::fs::create_dir_all(&root).unwrap();
        for (kind, term) in [("claim", claim), ("proof", proof)] {
            std::fs::write(
                root.join(format!("{label}-{kind}.dag")),
                trust_ir::proof::encode_clean_expr_dag_v2(term).unwrap(),
            )
            .unwrap();
        }
    }
}

#[test]
fn initialized_universal_claims_apply_to_real_complete_context_and_all_prefixes() {
    subject(fixture(), |source| {
        let law =
            check_tagged_u32_boxed_prefix_law(source, FuncId(71), &runtime_sources(), limits())
                .unwrap();
        assert!(core::ptr::eq(law.source(), source));
        for budget in 0..4 {
            save(
                &format!("universal-prefix-{budget}"),
                law.prefix_claim(budget).unwrap(),
                law.prefix_proof(budget).unwrap(),
            );
        }
        save(
            "universal-handoff",
            law.handoff_claim(),
            law.handoff_proof(),
        );
        // The theorem itself is quantified over arbitrary host TYPE/value and
        // admitted Byte-memory, not these instantiation witnesses. Literal
        // goals below independently retain every initialized field and slot.
        for (x, y) in [(3, 5), (0, 0), (4294967295, 4294967295)] {
            let words = [2 * x + 1, 2 * y + 1];
            for budget in 0..4 {
                let proof = apply(law.prefix_proof(budget as usize).unwrap(), x, y, None);
                assert!(replay(
                    law.environment(),
                    &proof,
                    source.context(),
                    words,
                    budget,
                    authored_endpoint(words, budget, 37, budget < 3, 0, budget)
                ));
            }
            for extra in [0, 1, 5] {
                let proof = apply(law.handoff_proof(), x, y, Some(extra));
                assert!(replay(
                    law.environment(),
                    &proof,
                    source.context(),
                    words,
                    extra + 4,
                    authored_endpoint(words, extra + 4, 37, false, extra, 4)
                ));
            }
        }
        let proof = apply(law.handoff_proof(), 3, 5, Some(5));
        for bad in [
            authored_endpoint([7, 11], 9, 38, false, 5, 4),
            authored_endpoint([7, 11], 9, 37, true, 5, 4),
            authored_endpoint([7, 11], 9, 37, false, 4, 4),
            authored_endpoint([7, 11], 9, 37, false, 5, 3),
        ] {
            assert!(!replay(
                law.environment(),
                &proof,
                source.context(),
                [7, 11],
                9,
                bad
            ));
        }
    });
}

#[test]
fn construction_stop_yields_no_quantified_receipt() {
    subject(fixture(), |source| {
        let mut limited = limits();
        limited.max_operations = 0;
        assert!(
            check_tagged_u32_boxed_prefix_law(source, FuncId(71), &runtime_sources(), limited)
                .is_err()
        );
    });
}
