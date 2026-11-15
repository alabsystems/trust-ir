// Copyright 2026 Andrew Yates | SPDX-License-Identifier: Apache-2.0

//! Input-only actual Add consumers with independent operation and output goals.
//! Strict closed/rooted and lossless-DAG replay, not fetched/native/TLA admission.

#[path = "core_execution_u64_add/support.rs"]
mod support;

use support::*;
use trust_ir_build::{
    core_execution::{Assembler, PendingProof},
    scoped_local::LocalScope,
};

#[test]
fn universal_canonical_add_replays_actual_operations_and_derived_output_bounds() {
    for add in [Add::Unsigned, Add::Signed] {
        let mut scope = LocalScope::new();
        let mut assembler = Assembler::new(&mut scope, limits()).unwrap();
        let a = assembler.local(c("Nat")).unwrap();
        let b = assembler.local(c("Nat")).unwrap();
        let a_bound = assembler.local(bound(a.term().clone())).unwrap();
        let b_bound = assembler.local(bound(b.term().clone())).unwrap();
        let before = assembler.operations();
        let (value, evaluated, output) = add.derive(
            &mut assembler,
            a.term().clone(),
            b.term().clone(),
            PendingProof::candidate(bound(a.term().clone()), a_bound.term().clone()),
            PendingProof::candidate(bound(b.term().clone()), b_bound.term().clone()),
        );
        assert_eq!(assembler.operations(), before + 1);
        assert_eq!(assembler.local_scope().allocated(), 4);
        let expected = add.word(a.term().clone(), b.term().clone());
        assert_eq!(value, scalar(expected.clone()));
        let operation_goal = eq(
            c("IRStepResult"),
            add.operation(a.term().clone(), b.term().clone()),
            result(scalar(expected.clone())),
        );
        let bound_goal = bound(expected);
        assert_eq!(*output.proposition(), bound_goal);
        let parameters = [a, b, a_bound, b_bound];
        replay(
            &scope,
            &parameters,
            evaluated.term(),
            &operation_goal,
            Some(add.law()),
        );
        replay(
            &scope,
            &parameters,
            output.term(),
            &bound_goal,
            Some(add.bound_law()),
        );
    }
}

#[test]
fn canonical_add_full64_crossings_and_negative_encodings_match_independent_literals() {
    // Rust's defined U64 wrapping addition provides independent literal answers.
    // Normalize only the branch/subtraction RHS, never the legacy closed modulus.
    for (a, b) in [
        (0_u64, 0_u64),
        (1, 2),
        (i64::MAX as u64, 1),
        (i64::MIN as u64, i64::MIN as u64),
        (u64::MAX, 1),
        (u64::MAX, u64::MAX),
        (i64::MIN as u64, u64::MAX),
    ] {
        for add in [Add::Unsigned, Add::Signed] {
            let answer = a.wrapping_add(b);
            let mut scope = LocalScope::new();
            let mut assembler = Assembler::new(&mut scope, limits()).unwrap();
            let (_, evaluated, output) =
                add.derive(&mut assembler, nat(a), nat(b), bounded(a), bounded(b));
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
                add.operation(nat(a), nat(b)),
                result(scalar(nat(answer))),
            );
            replay(&scope, &[], proof.term(), &goal, Some(add.law()));
            let goal = bound(add.word(nat(a), nat(b)));
            replay(&scope, &[], output.term(), &goal, Some(add.bound_law()));
        }
    }
}

#[test]
fn actual_small_add_mutants_refuse_changed_operands_width_opcode_and_answer() {
    for add in [Add::Unsigned, Add::Signed] {
        let mut scope = LocalScope::new();
        let mut assembler = Assembler::new(&mut scope, limits()).unwrap();
        let (_, evaluated, _) =
            add.derive(&mut assembler, nat(14), nat(3), bounded(14), bounded(3));
        let converted = assembler
            .conversion(
                c("IRStepResult"),
                evaluated.right().clone(),
                result(scalar(nat(17))),
            )
            .unwrap();
        let original = assembler.compose(evaluated, converted).unwrap();
        let narrower = app(
            "ir_binop_eval",
            [c("IRBinOp.add"), add.ty(4), scalar(nat(14)), scalar(nat(3))],
        );
        let multiply = app(
            "ir_binop_eval",
            [
                c("IRBinOp.mul"),
                add.ty(64),
                scalar(nat(14)),
                scalar(nat(3)),
            ],
        );
        for (operation, actual, false_answer) in [
            (add.operation(nat(13), nat(3)), 16, 17),
            (add.operation(nat(14), nat(4)), 18, 17),
            (narrower, 1, 17),
            (multiply, 42, 17),
            (add.operation(nat(14), nat(3)), 17, 0),
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
fn matching_foreign_add_carriers_and_forged_input_evidence_are_not_certified() {
    for add in [Add::Unsigned, Add::Signed] {
        for rhs in [false, true] {
            let mut scope = LocalScope::new();
            let mut assembler = Assembler::new(&mut scope, limits()).unwrap();
            let foreign = scalar(nat(if rhs { 3 } else { 14 }));
            let (a, b) = if rhs {
                (nat(14), foreign)
            } else {
                (foreign, nat(3))
            };
            let (_, evaluated, output) = add.derive(
                &mut assembler,
                a.clone(),
                b.clone(),
                PendingProof::candidate(bound(a), bounded(14).term().clone()),
                PendingProof::candidate(bound(b), bounded(3).term().clone()),
            );
            let goal = eq(
                c("IRStepResult"),
                add.operation(nat(14), nat(3)),
                result(scalar(nat(17))),
            );
            refuses(assembler.local_scope(), evaluated.term(), &goal);
            refuses(assembler.local_scope(), output.term(), &bound(nat(17)));
            let wrong = PendingProof::candidate(
                bound(nat(if rhs { 3 } else { 14 })),
                app("Nat.le_refl", [nat(if rhs { 3 } else { 14 })]),
            );
            let (a_bound, b_bound) = if rhs {
                (bounded(14), wrong)
            } else {
                (wrong, bounded(3))
            };
            let (_, evaluated, output) =
                add.derive(&mut assembler, nat(14), nat(3), a_bound, b_bound);
            refuses(&scope, evaluated.term(), &goal);
            refuses(&scope, output.term(), &bound(nat(17)));
        }
    }
}
