// Copyright 2026 Andrew Yates | SPDX-License-Identifier: Apache-2.0

//! Independent closed Add32/modulus/range replay, not source/native authority.

#![cfg(feature = "clean-tv-anchor")]

use clean_kernel::{BinderInfo, Environment, Expr, KernelTypeError, Level, Name, TypeChecker};
use std::sync::OnceLock;
use trust_ir_build::{
    core_execution::{Assembler, Limits},
    scoped_local::{LocalScope, ScopedLocal},
};

fn c(name: &str) -> Expr {
    Expr::const_str(name)
}
fn app(name: &str, args: impl IntoIterator<Item = Expr>) -> Expr {
    Expr::apps(c(name), args)
}
fn nat(value: u64) -> Expr {
    Expr::nat_lit(value)
}
fn eq(ty: Expr, left: Expr, right: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
        [ty, left, right],
    )
}
fn limit() -> Expr {
    app("ir_nat_pow2", [nat(32)])
}
fn raw(a: Expr, b: Expr) -> Expr {
    app("ir_wrap", [nat(32), app("Nat.add", [a, b])])
}
fn canonical(a: Expr, b: Expr) -> Expr {
    app("Nat.mod", [app("Nat.add", [a, b]), limit()])
}
fn value(word: Expr) -> Expr {
    app("IRStepResult.value", [app("IRScalar.int_", [word])])
}
fn evaluator(op: &str, width: u64, a: Expr, b: Expr) -> Expr {
    app(
        "ir_binop_eval",
        [
            c(op),
            app("IRTy.uint_", [nat(width)]),
            app("IRScalar.int_", [a]),
            app("IRScalar.int_", [b]),
        ],
    )
}
fn bound(a: Expr, b: Expr) -> Expr {
    app("Nat.lt", [raw(a, b), limit()])
}
fn limits(operations: usize) -> Limits {
    Limits {
        max_operations: operations,
        max_locals: 8,
        max_list_items: 1,
        max_lookup_candidates: 1,
        lookup_heartbeats: 1,
        lookup_cache_entries: 1,
    }
}
fn environment() -> &'static Environment {
    static ENV: OnceLock<Environment> = OnceLock::new();
    ENV.get_or_init(|| {
        clean_verify::eval_ir::build_canonical_arithmetic_byte_prelude_spec_v1_with_stack()
            .expect("actual checked canonical arithmetic owner")
            .into_environment()
    })
}
fn checker() -> TypeChecker<'static> {
    let mut tc = TypeChecker::new(environment());
    tc.set_allow_unsafe(false);
    tc.set_allow_partial(false);
    assert_eq!(tc.heartbeat_limit(), 2_000_000);
    tc
}
fn check(claim: &Expr, proof: &Expr, accepted: bool) {
    assert!(!claim.has_fvar_quick() && !claim.has_loose_bvars());
    assert!(!proof.has_fvar_quick() && !proof.has_loose_bvars());
    checker().check_type(claim, &Expr::prop()).unwrap();
    let claim_bytes = trust_ir::proof::encode_clean_expr_dag_v2(claim).unwrap();
    let proof_bytes = trust_ir::proof::encode_clean_expr_dag_v2(proof).unwrap();
    let decoded_claim = trust_ir::proof::decode_clean_expr_dag_v2(&claim_bytes).unwrap();
    let decoded_proof = trust_ir::proof::decode_clean_expr_dag_v2(&proof_bytes).unwrap();
    assert_eq!(claim, &decoded_claim);
    assert_eq!(proof, &decoded_proof);
    for (claim, proof) in [(claim, proof), (&decoded_claim, &decoded_proof)] {
        let tc = checker();
        let result = tc.check_type(proof, claim);
        assert!(
            !tc.heartbeat_spent(),
            "resource stop is not a semantic verdict: {result:?}"
        );
        assert!(!clean_kernel::tc::declaration_budget_exhausted());
        if accepted {
            result.unwrap();
            let audit = environment().audit_certification(claim, proof);
            assert!(audit.is_certified(), "actual rooted closure: {audit:#?}");
            for name in &audit.dependencies {
                assert!(environment().axiom_deps(name).unwrap().is_empty());
                assert!(
                    environment()
                        .foundational_axiom_deps(name)
                        .unwrap()
                        .is_empty()
                );
                assert!(environment().trust_marker_deps(name).unwrap().is_empty());
            }
        } else {
            assert!(
                matches!(result, Err(KernelTypeError::TypeMismatch { .. })),
                "{result:?}"
            );
        }
    }
}
fn close(scope: &LocalScope, parameters: &[ScopedLocal], claim: Expr, proof: Expr) -> (Expr, Expr) {
    let claim = parameters.iter().rev().fold(claim, |body, p| p.pi(body));
    let proof = parameters.iter().rev().fold(proof, |body, p| p.lam(body));
    (scope.close(&claim).unwrap(), scope.close(&proof).unwrap())
}
fn two_nat_binders(body: Expr, proof: bool) -> Expr {
    (0..2).fold(body, |body, _| {
        if proof {
            Expr::lam(BinderInfo::Default, c("Nat"), body)
        } else {
            Expr::pi(BinderInfo::Default, c("Nat"), body)
        }
    })
}

#[test]
fn universal_actual_add_uint32_and_raw_range_strictly_replay_without_input_bounds() {
    let mut scope = LocalScope::new();
    let mut assembler = Assembler::new(&mut scope, limits(100)).unwrap();
    let a = assembler.local(c("Nat")).unwrap();
    let b = assembler.local(c("Nat")).unwrap();
    let before = assembler.operations();
    let (word, equality, range) = assembler
        .byte_add_word32_mod(a.term().clone(), b.term().clone())
        .unwrap();
    assert_eq!(word, raw(a.term().clone(), b.term().clone()));
    assert_eq!(assembler.operations(), before + 10);
    assert_eq!(assembler.local_scope().allocated(), 2);
    let step = assembler
        .congruence_function(
            equality.clone(),
            c("IRStepResult"),
            Expr::lam(BinderInfo::Default, c("Nat"), value(Expr::bvar(0))),
        )
        .unwrap();
    // The goal below independently names the real evaluator, width, operator,
    // operands and prelude arithmetic, rather than reading pending metadata.
    let claims = [
        (
            eq(
                c("Nat"),
                raw(a.term().clone(), b.term().clone()),
                canonical(a.term().clone(), b.term().clone()),
            ),
            equality.term().clone(),
        ),
        (
            eq(
                c("IRStepResult"),
                evaluator("IRBinOp.add", 32, a.term().clone(), b.term().clone()),
                value(canonical(a.term().clone(), b.term().clone())),
            ),
            step.term().clone(),
        ),
        (
            bound(a.term().clone(), b.term().clone()),
            range.term().clone(),
        ),
    ];
    for (index, (claim, proof)) in claims.into_iter().enumerate() {
        let (claim, proof) = close(
            assembler.local_scope(),
            &[a.clone(), b.clone()],
            claim,
            proof,
        );
        check(&claim, &proof, true);
        if index == 0 {
            let audit = environment().audit_certification(&claim, &proof);
            for root in [
                "ir_div_go_pair_eq",
                "ir_nat_mul_canonical_agrees_v1",
                "ir_div_fuel_suffices_pos",
                "ir_div_rem_go_bound",
                "ir_nat_rem_is_residue",
                "ir_byte_mod_unique_v1",
            ] {
                assert!(
                    audit.dependencies.contains(&Name::from_string(root)),
                    "missing actual root {root}"
                );
            }
        }
        if let Some(dir) = std::env::var_os("TRUST_IR_ADD32_EVIDENCE_DIR") {
            let dir = std::path::PathBuf::from(dir);
            std::fs::create_dir_all(&dir).unwrap();
            std::fs::write(
                dir.join(format!("claim-{index}.dag-v2")),
                trust_ir::proof::encode_clean_expr_dag_v2(&claim).unwrap(),
            )
            .unwrap();
            std::fs::write(
                dir.join(format!("proof-{index}.dag-v2")),
                trust_ir::proof::encode_clean_expr_dag_v2(&proof).unwrap(),
            )
            .unwrap();
        }
    }
    // No additional total-restoring owner was installed for this derivation.
    for missing in ["ir_nat_rem_total_v1", "ir_wrap_mul_total_agrees_v1"] {
        assert!(
            environment()
                .get_const(&Name::from_string(missing))
                .is_none()
        );
    }
}

#[test]
fn independent_endpoint_mutants_refuse_width_mul_unwrapped_and_changed_operand() {
    let mut scope = LocalScope::new();
    let mut assembler = Assembler::new(&mut scope, limits(100)).unwrap();
    let a = Expr::bvar(1);
    let b = Expr::bvar(0);
    let (_, equality, _) = assembler.byte_add_word32_mod(a.clone(), b.clone()).unwrap();
    let step = assembler
        .congruence_function(
            equality,
            c("IRStepResult"),
            Expr::lam(BinderInfo::Default, c("Nat"), value(Expr::bvar(0))),
        )
        .unwrap();
    let proof = two_nat_binders(step.term().clone(), true);
    let right = value(canonical(a.clone(), b.clone()));
    for (name, left) in [
        (
            "width64",
            evaluator("IRBinOp.add", 64, a.clone(), b.clone()),
        ),
        ("Mul", evaluator("IRBinOp.mul", 32, a.clone(), b.clone())),
        ("unwrapped", value(app("Nat.add", [a.clone(), b.clone()]))),
        (
            "changed-operand",
            evaluator("IRBinOp.add", 32, app("Nat.succ", [a.clone()]), b.clone()),
        ),
    ] {
        eprintln!("semantic endpoint mutation: {name}");
        check(
            &two_nat_binders(eq(c("IRStepResult"), left, right.clone()), false),
            &proof,
            false,
        );
    }
}

#[test]
fn nested_de_bruijn_operands_are_applied_after_neutral_closure() {
    let mut scope = LocalScope::new();
    let mut assembler = Assembler::new(&mut scope, limits(100)).unwrap();
    let a = app("Nat.add", [Expr::bvar(1), Expr::bvar(0)]);
    let b = app("Nat.succ", [Expr::bvar(1)]);
    let (_, equality, range) = assembler.byte_add_word32_mod(a.clone(), b.clone()).unwrap();
    assert_eq!(assembler.local_scope().allocated(), 0);
    for (claim, proof) in [
        (
            eq(
                c("Nat"),
                raw(a.clone(), b.clone()),
                canonical(a.clone(), b.clone()),
            ),
            equality.term(),
        ),
        (bound(a, b), range.term()),
    ] {
        check(
            &two_nat_binders(claim, false),
            &two_nat_binders(proof.clone(), true),
            true,
        );
    }
}

#[test]
fn noncanonical_nat_input_keeps_the_pure_law_without_an_input_fit_premise() {
    let mut scope = LocalScope::new();
    let mut assembler = Assembler::new(&mut scope, limits(100)).unwrap();
    let a = app("Nat.succ", [nat(u32::MAX.into())]);
    let b = nat(2);
    let (_, equality, range) = assembler.byte_add_word32_mod(a.clone(), b.clone()).unwrap();
    check(
        &eq(
            c("Nat"),
            raw(a.clone(), b.clone()),
            canonical(a.clone(), b.clone()),
        ),
        equality.term(),
        true,
    );
    check(&bound(a, b), range.term(), true);
}

#[test]
fn operation_exhaustion_retains_the_same_callers_construction_ledger() {
    for cap in 1..10 {
        let mut scope = LocalScope::new();
        let mut assembler = Assembler::new(&mut scope, limits(cap)).unwrap();
        let result = assembler.byte_add_word32_mod(nat(3), nat(4));
        assert_eq!(
            result.err().unwrap(),
            "execution construction operation budget exceeded"
        );
        assert_eq!(assembler.operations(), cap);
        assert_eq!(assembler.local_scope().allocated(), 0);
    }
    let mut scope = LocalScope::new();
    let mut assembler = Assembler::new(&mut scope, limits(20)).unwrap();
    assembler.local(c("Nat")).unwrap();
    let (word, _, _) = assembler.byte_add_word32_mod(nat(3), nat(4)).unwrap();
    assert_eq!(word, raw(nat(3), nat(4)));
    assert_eq!(assembler.operations(), 11);
    assert!(assembler.byte_add_word32_mod(nat(3), nat(4)).is_err());
    assert_eq!(assembler.operations(), 20);
    assert!(assembler.byte_add_word32_mod(nat(3), nat(4)).is_err());
    assert_eq!(assembler.operations(), 20);
}

#[test]
fn mixed_add_mul_calls_spend_one_shared_ledger() {
    let mut scope = LocalScope::new();
    let mut assembler = Assembler::new(&mut scope, limits(23)).unwrap();
    let (a, _, _) = assembler.byte_add_word32_mod(nat(2), nat(3)).unwrap();
    assert_eq!(a, raw(nat(2), nat(3)));
    assert_eq!(assembler.operations(), 10);
    let (m, _, _) = assembler.byte_mul_word32_mod(nat(2), nat(3)).unwrap();
    assert_eq!(
        m,
        app("ir_wrap", [nat(32), app("ir_nat_mul", [nat(2), nat(3)])])
    );
    assert_eq!(assembler.operations(), 23);
    assert!(assembler.byte_add_word32_mod(nat(1), nat(2)).is_err());
    assert_eq!(assembler.operations(), 23);
}

#[test]
fn small_actual_evaluator_normal_forms_match_independent_reference_literals() {
    for (op, width, a, b, expected) in [
        ("IRBinOp.add", 32, 0, 7, 7),
        ("IRBinOp.add", 32, 2, 3, 5),
        ("IRBinOp.add", 32, 3, 3, 6),
        ("IRBinOp.add", 32, u64::from(u32::MAX), 1, 0),
        ("IRBinOp.add", 64, u64::from(u32::MAX), 1, 1_u64 << 32),
        ("IRBinOp.mul", 32, 2, 3, 6),
    ] {
        let literal = value(nat(expected));
        let proof = Expr::apps(
            Expr::const_(
                Name::from_string("Eq.refl"),
                vec![Level::succ(Level::zero())],
            ),
            [c("IRStepResult"), literal.clone()],
        );
        check(
            &eq(
                c("IRStepResult"),
                evaluator(op, width, nat(a), nat(b)),
                literal,
            ),
            &proof,
            true,
        );
    }
    let unwrapped = app("Nat.add", [nat(u32::MAX.into()), nat(1)]);
    let expected = nat(1_u64 << 32);
    let proof = Expr::apps(
        Expr::const_(
            Name::from_string("Eq.refl"),
            vec![Level::succ(Level::zero())],
        ),
        [c("Nat"), expected.clone()],
    );
    check(&eq(c("Nat"), unwrapped, expected), &proof, true);
}
