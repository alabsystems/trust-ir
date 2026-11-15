// Copyright 2026 Andrew Yates | SPDX-License-Identifier: Apache-2.0
#![cfg(feature = "source-value-operational")]
//! Original complete fixture, independent states and typed whole-helper goals.
use trust_ir::FuncId;
use trust_ir_build::clean_kernel::{BinderInfo, Expr, Level, Name, TypeChecker};
use trust_ir_build::clean_u32_boxed_helper_cic::check_full_tagged_u32_boxed_helper_law;
use trust_ir_build::core_execution::{Assembler, Limits, PendingEquality};
use trust_ir_build::scoped_local::LocalScope;
#[path = "clean_u32_boxed_helper_cic/boundaries.rs"]
mod boundaries;
#[path = "clean_u32_boxed_helper_cic/expected.rs"]
mod expected;
#[path = "clean_u32_boxed_prefix_cic/fixture.rs"]
mod fixture_data;
use fixture_data::{fixture, runtime_sources, subject};
fn c(n: &str) -> Expr {
    Expr::const_(
        Name::from_string(n),
        if n == "Bool.rec" {
            vec![Level::succ(Level::zero())]
        } else {
            vec![]
        },
    )
}
fn app(n: &str, a: impl IntoIterator<Item = Expr>) -> Expr {
    Expr::apps(c(n), a)
}
fn nat(n: u64) -> Expr {
    Expr::nat_lit(n)
}
fn list(t: &str, a: impl IntoIterator<Item = Expr>) -> Expr {
    a.into_iter()
        .collect::<Vec<_>>()
        .into_iter()
        .rev()
        .fold(app("IRList.nil", [c(t)]), |tail, x| {
            app("IRList.cons", [c(t), x, tail])
        })
}
fn eq(t: Expr, a: Expr, b: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
        [t, a, b],
    )
}
fn refl(t: Expr, a: Expr) -> Expr {
    Expr::apps(
        Expr::const_(
            Name::from_string("Eq.refl"),
            vec![Level::succ(Level::zero())],
        ),
        [t, a],
    )
}
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
fn actual(ctx: &Expr, x: u32, y: u32, fuel: u64) -> Expr {
    let args = list(
        "IRScalar",
        [x, y].map(|n| app("IRScalar.ptr_", [nat(2 * u64::from(n) + 1)])),
    );
    let init = app(
        "ir_clean_tag32_helper_init_v1",
        [
            c("Nat"),
            ctx.clone(),
            nat(71),
            args,
            expected::memory(),
            nat(37),
        ],
    );
    app(
        "ir_clean_tag32_helper_run_v1",
        [
            c("Nat"),
            ctx.clone(),
            nat(71),
            nat(0),
            nat(10),
            nat(4),
            nat(0),
            nat(1),
            nat(fuel),
            init,
        ],
    )
}
fn check(env: &trust_ir_build::clean_kernel::Environment, proof: &Expr, claim: &Expr) -> bool {
    let mut tc = TypeChecker::new(env);
    tc.set_allow_partial(false);
    tc.set_allow_unsafe(false);
    tc.check_type(claim, &Expr::sort(Level::zero()))
        .expect("independent complete-helper goal must be well typed");
    let result = tc.check_type(proof, claim);
    assert!(!tc.heartbeat_spent());
    assert!(!trust_ir_build::clean_kernel::tc::declaration_budget_exhausted());
    match result {
        Ok(()) => true,
        Err(trust_ir_build::clean_kernel::KernelTypeError::TypeMismatch { .. }) => false,
        Err(other) => panic!("false endpoint must refuse semantically, not {other:?}"),
    }
}
fn save(name: &str, claim: &Expr, proof: &Expr) {
    if let Some(root) = std::env::var_os("TRUST_IR_FULL_TAGGED_HELPER_EVIDENCE_DIR") {
        let root = std::path::PathBuf::from(root);
        std::fs::create_dir_all(&root).unwrap();
        for (kind, term) in [("claim", claim), ("proof", proof)] {
            std::fs::write(
                root.join(format!("{name}-{kind}.dag")),
                trust_ir::proof::encode_clean_expr_dag_v2(term).unwrap(),
            )
            .unwrap();
        }
    }
}
fn product_transport(ctx: &Expr, x: u32, y: u32, fuel: u64, proof: Expr) -> Expr {
    let mut scope = LocalScope::new();
    let mut asm = Assembler::new(&mut scope, limits()).unwrap();
    let (raw, equality, _) = asm
        .byte_mul_word32_mod(nat(x.wrapping_add(7).into()), nat(y.into()))
        .unwrap();
    let result = x.wrapping_add(7).wrapping_mul(y);
    // ir_nat_mul recurses on its second argument. Use the existing checked
    // raw->Nat.mod lemma, not billions of defeq reductions or a larger budget.
    let equality = asm
        .convert_endpoints(equality, raw.clone(), nat(result.into()))
        .unwrap();
    let state = |word| expected::with_result(x, y, fuel, 0, expected::Mutation::None, word);
    let ty = app("IRCleanTag32HelperRunV1", [c("Nat")]);
    let mapped = asm.congruence(equality, ty.clone(), state).unwrap();
    let mapped = asm
        .convert_endpoints(mapped, state(raw), state(nat(result.into())))
        .unwrap();
    let first =
        PendingEquality::candidate(ty, actual(ctx, x, y, fuel), mapped.left().clone(), proof);
    let transported = asm.compose(first, mapped).unwrap();
    let term = transported.term().clone();
    drop(asm);
    scope.close(&term).unwrap()
}
#[test]
fn full_original_helper_has_typed_quantified_trace_and_independent_complete_goals() {
    subject(fixture(), |source| {
        assert_eq!(source.source_value().module().functions.len(), 72);
        assert_eq!(source.source_value().module().func_types.len(), 73);
        let checked = check_full_tagged_u32_boxed_helper_law(
            source,
            FuncId(71),
            &runtime_sources(),
            limits(),
        )
        .unwrap();
        assert!(core::ptr::eq(checked.source(), source));
        assert_eq!(checked.instruction_count(), 11);
        for budget in 0..11 {
            save(
                &format!("prefix-{budget}"),
                checked.prefix_claim(budget).unwrap(),
                checked.prefix_proof(budget).unwrap(),
            );
        }
        save(
            "complete",
            checked.complete_claim(),
            checked.complete_proof(),
        );
        for (x, y) in [(3_u32, 5_u32), (0, 0), (u32::MAX, u32::MAX)] {
            for fuel in 0_u64..=13 {
                let count = fuel.min(11);
                let remaining = fuel - count;
                let term = if fuel < 11 {
                    checked.prefix_proof(fuel as usize).unwrap()
                } else {
                    checked.complete_proof()
                };
                let mut args = vec![
                    c("Nat"),
                    expected::memory(),
                    nat(37),
                    app("UInt32.ofNat", [nat(x.into())]),
                    app("UInt32.ofNat", [nat(y.into())]),
                    refl(c("Bool"), c("Bool.true")),
                ];
                if fuel >= 11 {
                    args.push(nat(remaining));
                }
                let proof = Expr::apps(term.clone(), args);
                let proof = if (8..=10).contains(&fuel) {
                    product_transport(source.context(), x, y, fuel, proof)
                } else {
                    proof
                };
                let goal = eq(
                    app("IRCleanTag32HelperRunV1", [c("Nat")]),
                    actual(source.context(), x, y, fuel),
                    expected::endpoint(x, y, count, remaining, expected::Mutation::None),
                );
                assert!(
                    check(checked.environment(), &proof, &goal),
                    "x{x} y{y} fuel{fuel}"
                );
                if (x, y, fuel) == (3, 5, 13) {
                    for mutation in [
                        expected::Mutation::Next,
                        expected::Mutation::RetireCallerMemory,
                        expected::Mutation::Host,
                        expected::Mutation::Tag,
                        expected::Mutation::Slot,
                        expected::Mutation::Remaining,
                    ] {
                        let wrong = eq(
                            app("IRCleanTag32HelperRunV1", [c("Nat")]),
                            actual(source.context(), x, y, fuel),
                            expected::endpoint(x, y, count, remaining, mutation),
                        );
                        assert!(
                            !check(checked.environment(), &proof, &wrong),
                            "false final world/result/fuel accepted"
                        );
                    }
                }
                if (x, y, fuel) == (3, 5, 9) {
                    let wrong = eq(
                        app("IRCleanTag32HelperRunV1", [c("Nat")]),
                        actual(source.context(), x, y, fuel),
                        expected::endpoint(x, y, count, remaining, expected::Mutation::CallerPc),
                    );
                    assert!(!check(checked.environment(), &proof, &wrong));
                }
            }
        }
        // No licensing follows from reaching or proving this model endpoint.
        assert!(matches!(
            source.source_value().module().functions[71].body_gate,
            Some(trust_ir::BodyGate::Ungated)
        ));
    });
}

#[test]
fn defined_boxer_is_really_source_checked_before_fixed_provider_refusal() {
    use trust_ir::{Block, BlockId, BodyGate, Inst, InstrNode, Ty, ValueId};
    let mut module = fixture();
    let boxer = module
        .functions
        .iter_mut()
        .find(|f| f.id == FuncId(4))
        .unwrap();
    assert!(boxer.is_declaration());
    let mut block = Block::new(BlockId(0)).with_param(ValueId(0), Ty::U32);
    block.body = vec![
        InstrNode::new(Inst::NullPtr).with_result(ValueId(1)),
        InstrNode::new(Inst::Return {
            values: vec![ValueId(1)],
        }),
    ];
    boxer.entry = block.id;
    boxer.blocks = vec![block];
    boxer.body_gate = Some(BodyGate::Ungated);
    // subject() must genuinely replay the original whole pinned admission,
    // source equation and both old scalar claims. No receipt is synthesized.
    subject(module, |source| {
        assert!(!source.source_value().module().functions[4].is_declaration());
        let result = check_full_tagged_u32_boxed_helper_law(
            source,
            FuncId(71),
            &runtime_sources(),
            limits(),
        );
        let Err(trust_ir_build::clean_u32_boxed_helper_cic::FullHelperCicError::Subject(detail)) =
            result
        else {
            panic!("defined boxer must refuse at original descriptor preparation");
        };
        assert!(detail.contains("BoxDescriptor"), "{detail}");
        println!("defined-boxer whole-source admission passed; actual factory refused: {detail}");
    });
}
