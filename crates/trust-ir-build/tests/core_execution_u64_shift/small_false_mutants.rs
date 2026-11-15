// Copyright 2026 Andrew Yates | SPDX-License-Identifier: Apache-2.0

//! Genuine false queries over small actual operations, not symbolic conversions
//! whose cost could be confused with refusal. The universal positive test stays
//! in the parent. Every changed operation first has its independent literal
//! normal form replayed without expecting a shift-library root.

use super::support::{refuses, replay};
use super::{Assembler, LocalScope, Shift, app, bounded, c, eq, limits, nat, result, scalar};

pub(super) fn run() {
    for shift in [Shift::Logical, Shift::Arithmetic] {
        let mut scope = LocalScope::new();
        let (original, checks) = {
            let mut assembler = Assembler::new(&mut scope, limits()).unwrap();
            let (_, derived) = shift.derive(&mut assembler, nat(8), bounded(8));
            let restoring = assembler
                .conversion(
                    c("IRStepResult"),
                    derived.right().clone(),
                    result(scalar(nat(1))),
                )
                .unwrap();
            let original = assembler.compose(derived, restoring).unwrap();
            let shl_same_carrier = app(
                "ir_binop_eval",
                [
                    c("IRBinOp.shl"),
                    shift.ir_ty(),
                    scalar(nat(8)),
                    scalar(nat(3)),
                ],
            );
            // Both original operations on positive word8 yield1. Each changed
            // query is independently authored, with a different actual result.
            // Shl keeps the original I64/U64 carrier and yields64 in both cases;
            // swapping Lshr/AShr on this positive word would not be a false query.
            let mut checks = Vec::new();
            for (case, changed_operation, claimed_answer, actual_answer) in [
                ("changed_word16", shift.operation(nat(16), 3), 1, 2),
                ("changed_amount4", shift.operation(nat(8), 4), 1, 0),
                ("changed_opcode_shl", shl_same_carrier, 1, 64),
                ("changed_desired_answer0", shift.operation(nat(8), 3), 0, 1),
            ] {
                assert_ne!(
                    actual_answer, claimed_answer,
                    "{shift:?} {case}: genuine false query"
                );
                let actual_result = result(scalar(nat(actual_answer)));
                let independent = assembler
                    .conversion(
                        c("IRStepResult"),
                        changed_operation.clone(),
                        actual_result.clone(),
                    )
                    .unwrap();
                checks.push((
                    changed_operation,
                    claimed_answer,
                    actual_result,
                    independent,
                ));
            }
            (original, checks)
        };
        for (changed_operation, claimed_answer, actual_result, independent) in checks {
            replay(
                &scope,
                &[],
                independent.term(),
                &eq(c("IRStepResult"), changed_operation.clone(), actual_result),
                None,
            );
            // The derived original-operation proof cannot certify this false
            // claim. refuses() requires strict TypeMismatch and unspent limits.
            refuses(
                &scope,
                &[],
                original.term(),
                &eq(
                    c("IRStepResult"),
                    changed_operation,
                    result(scalar(nat(claimed_answer))),
                ),
            );
        }
    }
}
