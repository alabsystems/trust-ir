// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Derived scalar candidates for actual full64 right-shift operations.
//!
//! These adapters require the exact canonical-word proposition and derive the
//! evaluation result themselves. They install no vocabulary, check no proof,
//! and execute no fetched instruction. The complete closed claim must still be
//! independently replayed with the opt-in checked Clean shift vocabulary.
//! Operand lookup, carrier admission, result typing, machine state and native
//! evidence remain separate obligations of the consuming transfer.

use super::*;

#[cfg(test)]
#[path = "core_execution_scalar_shift_tests.rs"]
mod tests;

#[cfg(test)]
#[path = "core_execution_scalar_shift_in_range_tests.rs"]
mod in_range_tests;

fn quotient(word: Expr) -> Expr {
    app(
        "ir_dm_quot",
        [app(
            "ir_dm_go",
            [
                nat(1),
                word.clone(),
                nat(64),
                nat(8),
                app("IRDivMod.mk", [word, nat(0)]),
            ],
        )],
    )
}

fn shift_quotient(word: Expr, divisor: Expr, fuel: u64) -> Expr {
    app(
        "ir_dm_quot",
        [app(
            "ir_dm_go",
            [
                nat(1),
                word.clone(),
                nat(fuel),
                divisor,
                app("IRDivMod.mk", [word, nat(0)]),
            ],
        )],
    )
}

impl Assembler<'_> {
    /// Derive the actual U64 logical right shift and its canonical result bound.
    ///
    /// The inputs must state exactly `Nat.lt word (ir_nat_pow2 64)` and
    /// `Nat.lt amount 64`. The returned triple is the scalar, its evaluation
    /// equality, and `Nat.lt result (ir_nat_pow2 64)`, all pending candidates.
    /// No answer or output-bound proof is supplied. This charges one operation
    /// before checking shapes, creates no locals, and checks no proof. Strict
    /// closed replay with the opt-in all-amount vocabulary remains mandatory.
    pub fn byte_lshr_u64_in_range(
        &mut self,
        word: Expr,
        amount: Expr,
        bounded: PendingProof,
        in_range: PendingProof,
    ) -> Result<(Expr, PendingEquality, PendingProof)> {
        self.byte_shift_in_range(word, amount, bounded, in_range, false)
    }

    /// Derive the actual I64 arithmetic right shift and its canonical bound.
    ///
    /// Both full64 sign branches are retained using `ir_sign_bit 64 word`.
    /// The word quotient uses restoring fuel 64; the fill uses fuel 65 so that
    /// amount zero retains the full `2^64` fill. Exact input bounds, charging,
    /// pending status, and replay requirements match the U64 method. Neither
    /// carrier/fetch admission nor typed-step/native authority follows here.
    pub fn byte_ashr_i64_in_range(
        &mut self,
        word: Expr,
        amount: Expr,
        bounded: PendingProof,
        in_range: PendingProof,
    ) -> Result<(Expr, PendingEquality, PendingProof)> {
        self.byte_shift_in_range(word, amount, bounded, in_range, true)
    }

    fn byte_shift_in_range(
        &mut self,
        word: Expr,
        amount: Expr,
        bounded: PendingProof,
        in_range: PendingProof,
        arithmetic: bool,
    ) -> Result<(Expr, PendingEquality, PendingProof)> {
        self.charge()?;
        let limit = app("ir_nat_pow2", [nat(64)]);
        require_same(
            bounded.proposition(),
            &app("Nat.lt", [word.clone(), limit.clone()]),
            "shift canonical word bound",
        )?;
        require_same(
            in_range.proposition(),
            &app("Nat.lt", [amount.clone(), nat(64)]),
            "shift amount range",
        )?;
        let fits = app(
            "ir_byte_ltb_of_lt_v1",
            [word.clone(), limit.clone(), bounded.term().clone()],
        );
        let divisor = app("ir_nat_pow2", [amount.clone()]);
        let logical = shift_quotient(word.clone(), divisor.clone(), 64);
        let result = if arithmetic {
            choose(
                &constant("Nat"),
                app("ir_sign_bit", [nat(64), word.clone()]),
                app(
                    "Nat.add",
                    [
                        logical.clone(),
                        app(
                            "Nat.sub",
                            [limit.clone(), shift_quotient(limit.clone(), divisor, 65)],
                        ),
                    ],
                ),
                logical,
            )
        } else {
            logical
        };
        let value = app("IRScalar.int_", [result.clone()]);
        let (opcode, ty, law, result_law) = if arithmetic {
            (
                "IRBinOp.ashr",
                "IRTy.int_",
                "ir_byte_ashr_i64_in_range_v1",
                "ir_byte_ashr_i64_in_range_result_bound_v1",
            )
        } else {
            (
                "IRBinOp.lshr",
                "IRTy.uint_",
                "ir_byte_lshr_u64_in_range_v1",
                "ir_byte_lshr_u64_in_range_result_bound_v1",
            )
        };
        let arguments = [word.clone(), amount.clone(), fits, in_range.term().clone()];
        let equality = PendingEquality::candidate(
            constant("IRStepResult"),
            app(
                "ir_binop_eval",
                [
                    constant(opcode),
                    app(ty, [nat(64)]),
                    app("IRScalar.int_", [word]),
                    app("IRScalar.int_", [amount]),
                ],
            ),
            app("IRStepResult.value", [value.clone()]),
            app(law, arguments.clone()),
        );
        let result_bound = PendingProof::candidate(
            app("Nat.lt", [result.clone(), limit.clone()]),
            app(
                "ir_byte_separation_lt_of_ltb_v1",
                [result, limit, app(result_law, arguments)],
            ),
        );
        Ok((value, equality, result_bound))
    }

    /// Construct the existing U64 logical-right-shift evaluation at amount 3.
    ///
    /// `bounded` must state exactly `Nat.lt word (ir_nat_pow2 64)`. The returned
    /// scalar and equality are derived candidates, not checked facts. This
    /// accepts no desired answer, fetch binding, or supplied evaluation proof.
    /// Closing and strict independent replay remain mandatory; in particular
    /// the returned equality establishes no result-carrier or native authority.
    pub fn byte_lshr_u64_by_three(
        &mut self,
        word: Expr,
        bounded: PendingProof,
    ) -> Result<(Expr, PendingEquality)> {
        self.byte_shift_by_three(word, bounded, false)
    }

    /// Construct the existing I64 arithmetic-right-shift evaluation at amount 3.
    ///
    /// The full canonical range includes negative encodings. Both branches use
    /// the original `ir_sign_bit 64 word`; neither the sign nor an operation
    /// answer is supplied by the caller. The fixed fill quotient and dividend
    /// quotient use the existing restoring algorithm at fuel 64. The same
    /// pending/replay and exact-bound requirements as the logical shift apply.
    pub fn byte_ashr_i64_by_three(
        &mut self,
        word: Expr,
        bounded: PendingProof,
    ) -> Result<(Expr, PendingEquality)> {
        self.byte_shift_by_three(word, bounded, true)
    }

    fn byte_shift_by_three(
        &mut self,
        word: Expr,
        bounded: PendingProof,
        arithmetic: bool,
    ) -> Result<(Expr, PendingEquality)> {
        self.charge()?;
        let limit = app("ir_nat_pow2", [nat(64)]);
        require_same(
            bounded.proposition(),
            &app("Nat.lt", [word.clone(), limit.clone()]),
            "shift canonical word bound",
        )?;
        let fits = app(
            "ir_byte_ltb_of_lt_v1",
            [word.clone(), limit.clone(), bounded.term().clone()],
        );
        let logical = quotient(word.clone());
        let result = if arithmetic {
            choose(
                &constant("Nat"),
                app("ir_sign_bit", [nat(64), word.clone()]),
                app(
                    "Nat.add",
                    [
                        logical.clone(),
                        app("Nat.sub", [limit, quotient(app("ir_nat_pow2", [nat(64)]))]),
                    ],
                ),
                logical,
            )
        } else {
            logical
        };
        let value = app("IRScalar.int_", [result]);
        let (opcode, ty, law) = if arithmetic {
            ("IRBinOp.ashr", "IRTy.int_", "ir_byte_ashr_i64_by_three_v1")
        } else {
            ("IRBinOp.lshr", "IRTy.uint_", "ir_byte_lshr_u64_by_three_v1")
        };
        let left = app(
            "ir_binop_eval",
            [
                constant(opcode),
                app(ty, [nat(64)]),
                app("IRScalar.int_", [word.clone()]),
                app("IRScalar.int_", [nat(3)]),
            ],
        );
        let equality = PendingEquality::candidate(
            constant("IRStepResult"),
            left,
            app("IRStepResult.value", [value.clone()]),
            app(law, [word, fits]),
        );
        Ok((value, equality))
    }
}
