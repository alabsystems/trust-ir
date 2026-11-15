// Copyright 2026 Andrew Yates | SPDX-License-Identifier: Apache-2.0

//! Ordinary all-amount consumers with independent actual operation/bound goals.
//! Strict closed/rooted and lossless-DAG replay, not native/frontend admission.

#[path = "core_execution_u64_shift_in_range/support.rs"]
mod support;

use support::*;
use trust_ir_build::{
    core_execution::{Assembler, PendingProof},
    scoped_local::LocalScope,
};

#[test]
fn universal_in_range_candidates_replay_independent_actual_operations_and_output_bounds() {
    for shift in [Shift::Logical, Shift::Arithmetic] {
        let mut scope = LocalScope::new();
        let mut assembler = Assembler::new(&mut scope, limits()).unwrap();
        let word = assembler.local(c("Nat")).unwrap();
        let amount = assembler.local(c("Nat")).unwrap();
        let bounded = assembler.local(bound(word.term().clone())).unwrap();
        let in_range = assembler.local(range(amount.term().clone())).unwrap();
        let before = assembler.operations();
        let (value, evaluated, result_bound) = shift.derive(
            &mut assembler,
            word.term().clone(),
            amount.term().clone(),
            PendingProof::candidate(bound(word.term().clone()), bounded.term().clone()),
            PendingProof::candidate(range(amount.term().clone()), in_range.term().clone()),
        );
        assert_eq!(assembler.operations(), before + 1);
        assert_eq!(assembler.local_scope().allocated(), 4);
        let expected = shift.word(word.term().clone(), amount.term().clone());
        assert_eq!(value, scalar(expected.clone()));
        let evaluation_goal = eq(
            c("IRStepResult"),
            shift.operation(word.term().clone(), amount.term().clone()),
            result(scalar(expected.clone())),
        );
        let bound_goal = bound(expected);
        assert_eq!(*result_bound.proposition(), bound_goal);
        let parameters = [word, amount, bounded, in_range];
        replay(
            &scope,
            &parameters,
            evaluated.term(),
            &evaluation_goal,
            Some(shift.law()),
        );
        replay(
            &scope,
            &parameters,
            result_bound.term(),
            &bound_goal,
            Some(shift.bound_law()),
        );
    }
}

#[test]
fn in_range_candidates_cover_zero_sixty_three_and_full64_sign_boundaries() {
    // Expected literal answers are computed independently using Rust's defined
    // U64/I64 shift semantics. Only the bounded restoring RHS is normalized.
    for word in [0_u64, 8, i64::MAX as u64, i64::MIN as u64, u64::MAX] {
        for amount in [0_u64, 1, 3, 31, 63] {
            for shift in [Shift::Logical, Shift::Arithmetic] {
                let answer = match shift {
                    Shift::Logical => word >> amount,
                    Shift::Arithmetic => ((word as i64) >> amount) as u64,
                };
                let mut scope = LocalScope::new();
                let mut assembler = Assembler::new(&mut scope, limits()).unwrap();
                let (_, evaluated, result_bound) = shift.derive(
                    &mut assembler,
                    nat(word),
                    nat(amount),
                    bounded(word),
                    in_range(amount),
                );
                let converted = assembler
                    .conversion(
                        c("IRStepResult"),
                        evaluated.right().clone(),
                        result(scalar(nat(answer))),
                    )
                    .unwrap();
                let proof = assembler.compose(evaluated, converted).unwrap();
                let goal = eq(
                    c("IRStepResult"),
                    shift.operation(nat(word), nat(amount)),
                    result(scalar(nat(answer))),
                );
                replay(&scope, &[], proof.term(), &goal, Some(shift.law()));
                // Bound goal is independently reconstructed, not copied from
                // the producer, and covers both sign branches at amount zero.
                let goal = bound(shift.word(nat(word), nat(amount)));
                replay(
                    &scope,
                    &[],
                    result_bound.term(),
                    &goal,
                    Some(shift.bound_law()),
                );
            }
        }
    }
}

#[test]
fn amount_sixty_four_is_actual_shift_oob_and_false_success_candidates_refuse() {
    for shift in [Shift::Logical, Shift::Arithmetic] {
        let mut scope = LocalScope::new();
        let mut assembler = Assembler::new(&mut scope, limits()).unwrap();
        let operation = shift.operation(nat(8), nat(64));
        let fault = app(
            "IRStepResult.fault",
            [app("IROutcome.ub", [c("IRFault.shift_oob")])],
        );
        let actual = assembler
            .conversion(c("IRStepResult"), operation.clone(), fault.clone())
            .unwrap();
        replay(
            assembler.local_scope(),
            &[],
            actual.term(),
            &eq(c("IRStepResult"), operation.clone(), fault),
            None,
        );
        let false_range = PendingProof::candidate(range(nat(64)), app("Nat.le_refl", [nat(64)]));
        let (_, evaluated, result_bound) = shift.derive(
            &mut assembler,
            nat(8),
            nat(64),
            bounded(8),
            false_range.clone(),
        );
        refuses(&scope, false_range.term(), &range(nat(64)));
        refuses(
            &scope,
            evaluated.term(),
            &eq(c("IRStepResult"), operation, result(scalar(nat(1)))),
        );
        refuses(
            &scope,
            result_bound.term(),
            &bound(shift.word(nat(8), nat(64))),
        );
    }
}

#[test]
fn actual_small_operation_controls_refuse_operand_amount_opcode_and_answer_changes() {
    for shift in [Shift::Logical, Shift::Arithmetic] {
        let mut scope = LocalScope::new();
        let mut assembler = Assembler::new(&mut scope, limits()).unwrap();
        let (_, evaluated, _) =
            shift.derive(&mut assembler, nat(8), nat(3), bounded(8), in_range(3));
        let converted = assembler
            .conversion(
                c("IRStepResult"),
                evaluated.right().clone(),
                result(scalar(nat(1))),
            )
            .unwrap();
        let original = assembler.compose(evaluated, converted).unwrap();
        let shl = app(
            "ir_binop_eval",
            [
                c("IRBinOp.shl"),
                match shift {
                    Shift::Logical => app("IRTy.uint_", [nat(64)]),
                    Shift::Arithmetic => app("IRTy.int_", [nat(64)]),
                },
                scalar(nat(8)),
                scalar(nat(3)),
            ],
        );
        for (operation, actual, false_answer) in [
            (shift.operation(nat(16), nat(3)), 2, 1),
            (shift.operation(nat(8), nat(4)), 0, 1),
            (shl, 64, 1),
            (shift.operation(nat(8), nat(3)), 1, 0),
        ] {
            let normal = result(scalar(nat(actual)));
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
                original.term(),
                &eq(
                    c("IRStepResult"),
                    operation,
                    result(scalar(nat(false_answer))),
                ),
            );
        }
    }
}

#[test]
fn matching_foreign_carrier_and_forged_input_evidence_are_not_certified() {
    for shift in [Shift::Logical, Shift::Arithmetic] {
        let mut scope = LocalScope::new();
        let mut assembler = Assembler::new(&mut scope, limits()).unwrap();
        let foreign = scalar(nat(8));
        let (_, evaluated, output) = shift.derive(
            &mut assembler,
            foreign.clone(),
            nat(3),
            PendingProof::candidate(bound(foreign), bounded(8).term().clone()),
            in_range(3),
        );
        let goal = eq(
            c("IRStepResult"),
            shift.operation(nat(8), nat(3)),
            result(scalar(nat(1))),
        );
        refuses(assembler.local_scope(), evaluated.term(), &goal);
        refuses(assembler.local_scope(), output.term(), &bound(nat(1)));
        let (_, evaluated, output) = shift.derive(
            &mut assembler,
            nat(8),
            nat(3),
            PendingProof::candidate(bound(nat(8)), app("Nat.le_refl", [nat(8)])),
            in_range(3),
        );
        refuses(&scope, evaluated.term(), &goal);
        refuses(&scope, output.term(), &bound(nat(1)));
    }
}
