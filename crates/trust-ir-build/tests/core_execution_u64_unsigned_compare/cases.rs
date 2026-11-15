// Copyright 2026 Andrew Yates | SPDX-License-Identifier: Apache-2.0

//! Independent actual scalar comparison consumers, not fetched/native/TLA claims.
//! The explicitly installed law vocabulary belongs to the immutable Clean cut.

mod support;

use support::*;
use trust_ir::ICmpOp;
use trust_ir_build::{
    core_execution::{Assembler, PendingProof},
    scoped_local::LocalScope,
};

#[test]
fn universal_unsigned_comparisons_replay_exact_operations_root_closures_and_lossless_dags() {
    for carrier in [Carrier::Unsigned, Carrier::Signed] {
        for op in OPS {
            let mut scope = LocalScope::new();
            let mut assembler = Assembler::new(&mut scope, limits()).unwrap();
            let a = assembler.local(c("Nat")).unwrap();
            let b = assembler.local(c("Nat")).unwrap();
            let a_bound = assembler.local(bound(a.term().clone())).unwrap();
            let b_bound = assembler.local(bound(b.term().clone())).unwrap();
            let before = assembler.operations();
            let (value, evaluated) = carrier
                .derive(
                    &mut assembler,
                    op,
                    [a.term().clone(), b.term().clone()],
                    [
                        PendingProof::candidate(bound(a.term().clone()), a_bound.term().clone()),
                        PendingProof::candidate(bound(b.term().clone()), b_bound.term().clone()),
                    ],
                )
                .unwrap();
            assert_eq!(assembler.operations(), before + 1);
            assert_eq!(assembler.local_scope().allocated(), 4);
            let expected = boolean(observer(op, a.term().clone(), b.term().clone()));
            assert_eq!(value, expected);
            let claim = eq(
                c("IRStepResult"),
                carrier.operation(op, 64, a.term().clone(), b.term().clone()),
                result(expected),
            );
            let parameters = [a, b, a_bound, b_bound];
            replay(
                &scope,
                &parameters,
                evaluated.term(),
                &claim,
                Some(carrier.law(op)),
            );
        }
    }
}

#[test]
fn unsigned_comparison_full64_sign_and_tlc32_boundaries_match_independent_literals() {
    for (a, b) in [
        (0_u64, 0_u64),
        (0, u64::MAX),
        (u64::MAX, 0),
        (i64::MIN as u64, i64::MAX as u64),
        (i64::MAX as u64, i64::MIN as u64),
        (u64::MAX, u64::MAX),
        (1_u64 << 31, 1_u64 << 32),
        (1_u64 << 32, 1_u64 << 31),
    ] {
        for carrier in [Carrier::Unsigned, Carrier::Signed] {
            for op in OPS {
                let answer = literal(op, a, b);
                let mut scope = LocalScope::new();
                let mut assembler = Assembler::new(&mut scope, limits()).unwrap();
                let (_, evaluated) = carrier
                    .derive(
                        &mut assembler,
                        op,
                        [nat(a), nat(b)],
                        [bounded(a), bounded(b)],
                    )
                    .unwrap();
                // Only the separately authored unwrapped Boolean observer is
                // normalized; no closed full64 legacy wrap or division walk.
                let expected_observer = result(boolean(observer(op, nat(a), nat(b))));
                let expected_literal = result(boolean(flag(answer)));
                let converted = assembler
                    .conversion(
                        c("IRStepResult"),
                        expected_observer,
                        expected_literal.clone(),
                    )
                    .unwrap();
                let proof = assembler.compose(evaluated, converted).unwrap();
                let claim = eq(
                    c("IRStepResult"),
                    carrier.operation(op, 64, nat(a), nat(b)),
                    expected_literal,
                );
                replay(&scope, &[], proof.term(), &claim, Some(carrier.law(op)));
            }
        }
    }
}

#[test]
fn actual_small_unsigned_comparison_mutants_refuse_operands_opcode_and_desired_answer() {
    // Every baseline is true; every changed query below is independently false.
    for (op, a, b, changed_a, changed_b, changed_op) in [
        (ICmpOp::Ult, 1_u64, 2_u64, 2_u64, 0_u64, ICmpOp::Uge),
        (ICmpOp::Ule, 2, 2, 3, 1, ICmpOp::Ult),
        (ICmpOp::Ugt, 2, 1, 1, 3, ICmpOp::Ule),
        (ICmpOp::Uge, 2, 2, 1, 3, ICmpOp::Ugt),
    ] {
        assert!(literal(op, a, b));
        assert!(!literal(op, changed_a, b));
        assert!(!literal(op, a, changed_b));
        assert!(!literal(changed_op, a, b));
        for carrier in [Carrier::Unsigned, Carrier::Signed] {
            let mut scope = LocalScope::new();
            let mut assembler = Assembler::new(&mut scope, limits()).unwrap();
            let (_, evaluated) = carrier
                .derive(
                    &mut assembler,
                    op,
                    [nat(a), nat(b)],
                    [bounded(a), bounded(b)],
                )
                .unwrap();
            let converted = assembler
                .conversion(
                    c("IRStepResult"),
                    result(boolean(observer(op, nat(a), nat(b)))),
                    result(boolean(flag(true))),
                )
                .unwrap();
            let proof = assembler.compose(evaluated, converted).unwrap();
            for (operation, actual, false_answer) in [
                (
                    carrier.operation(op, 64, nat(changed_a), nat(b)),
                    false,
                    true,
                ),
                (
                    carrier.operation(op, 64, nat(a), nat(changed_b)),
                    false,
                    true,
                ),
                (
                    carrier.operation(changed_op, 64, nat(a), nat(b)),
                    false,
                    true,
                ),
                (carrier.operation(op, 64, nat(a), nat(b)), true, false),
            ] {
                let normal = result(boolean(flag(actual)));
                let independent = assembler
                    .conversion(c("IRStepResult"), operation.clone(), normal.clone())
                    .unwrap();
                replay(
                    assembler.local_scope(),
                    &[],
                    independent.term(),
                    &eq(c("IRStepResult"), operation.clone(), normal),
                    None,
                );
                refuses(
                    assembler.local_scope(),
                    &[],
                    proof.term(),
                    &eq(
                        c("IRStepResult"),
                        operation,
                        result(boolean(flag(false_answer))),
                    ),
                );
            }
        }
    }
}

#[test]
fn actual_unsigned_comparison_changed_width_refuses_after_independent_small_normal_form() {
    for carrier in [Carrier::Unsigned, Carrier::Signed] {
        let mut scope = LocalScope::new();
        let mut assembler = Assembler::new(&mut scope, limits()).unwrap();
        let (_, evaluated) = carrier
            .derive(
                &mut assembler,
                ICmpOp::Uge,
                [nat(8), nat(3)],
                [bounded(8), bounded(3)],
            )
            .unwrap();
        let converted = assembler
            .conversion(
                c("IRStepResult"),
                result(boolean(observer(ICmpOp::Uge, nat(8), nat(3)))),
                result(boolean(flag(true))),
            )
            .unwrap();
        let proof = assembler.compose(evaluated, converted).unwrap();
        // width3 wraps eight to zero; this is an actual false operation claim,
        // not a different nominal carrier with the same observable result.
        let operation = carrier.operation(ICmpOp::Uge, 3, nat(8), nat(3));
        let normal = result(boolean(flag(false)));
        let independent = assembler
            .conversion(c("IRStepResult"), operation.clone(), normal.clone())
            .unwrap();
        replay(
            assembler.local_scope(),
            &[],
            independent.term(),
            &eq(c("IRStepResult"), operation.clone(), normal),
            None,
        );
        refuses(
            assembler.local_scope(),
            &[],
            proof.term(),
            &eq(c("IRStepResult"), operation, result(boolean(flag(true)))),
        );
    }
}

#[test]
fn foreign_unsigned_comparison_carriers_and_unchecked_bounds_do_not_certify() {
    for carrier in [Carrier::Unsigned, Carrier::Signed] {
        for rhs in [false, true] {
            let mut scope = LocalScope::new();
            let mut assembler = Assembler::new(&mut scope, limits()).unwrap();
            let foreign = scalar(nat(if rhs { 3 } else { 8 }));
            let (a, b) = if rhs {
                (nat(8), foreign)
            } else {
                (foreign, nat(3))
            };
            let (_, evaluated) = carrier
                .derive(
                    &mut assembler,
                    ICmpOp::Uge,
                    [a.clone(), b.clone()],
                    [
                        PendingProof::candidate(bound(a), bounded(8).term().clone()),
                        PendingProof::candidate(bound(b), bounded(3).term().clone()),
                    ],
                )
                .unwrap();
            let claim = eq(
                c("IRStepResult"),
                carrier.operation(ICmpOp::Uge, 64, nat(8), nat(3)),
                result(boolean(flag(true))),
            );
            refuses(assembler.local_scope(), &[], evaluated.term(), &claim);
            let word = if rhs { 3 } else { 8 };
            let forged = PendingProof::candidate(bound(nat(word)), app("Nat.le_refl", [nat(word)]));
            let bounds = if rhs {
                [bounded(8), forged]
            } else {
                [forged, bounded(3)]
            };
            let (_, evaluated) = carrier
                .derive(&mut assembler, ICmpOp::Uge, [nat(8), nat(3)], bounds)
                .unwrap();
            refuses(&scope, &[], evaluated.term(), &claim);
        }
    }
}

#[test]
fn foreign_assembler_unsigned_comparison_bound_terms_are_not_proof_authority() {
    for carrier in [Carrier::Unsigned, Carrier::Signed] {
        let mut foreign_scope = LocalScope::new();
        let mut foreign_assembler = Assembler::new(&mut foreign_scope, limits()).unwrap();
        let foreign_bound = foreign_assembler.local(bound(nat(8))).unwrap();
        let mut scope = LocalScope::new();
        let mut assembler = Assembler::new(&mut scope, limits()).unwrap();
        let a = assembler.local(c("Nat")).unwrap();
        let b = assembler.local(c("Nat")).unwrap();
        let a_bound = assembler.local(bound(a.term().clone())).unwrap();
        let b_bound = assembler.local(bound(b.term().clone())).unwrap();
        // Local IDs are not cross-scope proof authority. Deliberately alias the
        // foreign Prop local onto this owner's Nat local; independent replay
        // must reject its type, even when claimed PendingProof metadata matches.
        assert_eq!(foreign_bound.id(), a.id());
        let (_, evaluated) = carrier
            .derive(
                &mut assembler,
                ICmpOp::Uge,
                [a.term().clone(), b.term().clone()],
                [
                    PendingProof::candidate(bound(a.term().clone()), foreign_bound.term().clone()),
                    PendingProof::candidate(bound(b.term().clone()), b_bound.term().clone()),
                ],
            )
            .unwrap();
        let claim = eq(
            c("IRStepResult"),
            carrier.operation(ICmpOp::Uge, 64, a.term().clone(), b.term().clone()),
            result(boolean(observer(
                ICmpOp::Uge,
                a.term().clone(),
                b.term().clone(),
            ))),
        );
        let parameters = [a, b, a_bound, b_bound];
        refuses(&scope, &parameters, evaluated.term(), &claim);
    }
}
