// Copyright 2026 Andrew Yates | SPDX-License-Identifier: Apache-2.0

//! Pending full64 Add candidates for the unchanged actual scalar evaluator.
//!
//! Only exact input canonicality is supplied. Both wrap branches, evaluation,
//! and the output bound are derived through fixed checked library laws. These
//! adapters install/check nothing and execute no fetched instruction. Closing
//! and independent strict replay remain mandatory; machine/caller, source and
//! native authority are separate. No operation answer is an input premise.

use super::*;

#[cfg(test)]
#[path = "core_execution_scalar_add_tests.rs"]
mod tests;

#[derive(Clone, Copy)]
enum AddCarrier {
    Unsigned,
    Signed,
}

impl Assembler<'_> {
    /// Derive actual U64 wrapping Add and its canonical result bound.
    ///
    /// `a_bound` and `b_bound` must state exactly `Nat.lt a (ir_nat_pow2 64)`
    /// and `Nat.lt b (ir_nat_pow2 64)`. The triple contains the scalar, its
    /// actual `ir_binop_eval.add` equality and `Nat.lt result (ir_nat_pow2 64)`.
    /// All three are pending; matched metadata is not a checked proof. One
    /// operation is charged before shape checks, with no new locals or cache.
    pub fn byte_add_u64_canonical(
        &mut self,
        a: Expr,
        b: Expr,
        a_bound: PendingProof,
        b_bound: PendingProof,
    ) -> Result<(Expr, PendingEquality, PendingProof)> {
        self.byte_add_canonical(a, b, a_bound, b_bound, AddCarrier::Unsigned)
    }

    /// Derive actual I64 wrapping Add over full64 canonical bit patterns.
    ///
    /// The nominal signed carrier is preserved; negative encodings and crossing
    /// sums use the same actual modulo arithmetic. This is not a theorem that
    /// signed mathematical addition cannot overflow, nor a TLC32 source rule.
    /// Exact input bounds, charging and pending/replay status match U64 Add.
    pub fn byte_add_i64_canonical(
        &mut self,
        a: Expr,
        b: Expr,
        a_bound: PendingProof,
        b_bound: PendingProof,
    ) -> Result<(Expr, PendingEquality, PendingProof)> {
        self.byte_add_canonical(a, b, a_bound, b_bound, AddCarrier::Signed)
    }

    fn byte_add_canonical(
        &mut self,
        a: Expr,
        b: Expr,
        a_bound: PendingProof,
        b_bound: PendingProof,
        carrier: AddCarrier,
    ) -> Result<(Expr, PendingEquality, PendingProof)> {
        self.charge()?;
        let limit = app("ir_nat_pow2", [nat(64)]);
        require_same(
            a_bound.proposition(),
            &app("Nat.lt", [a.clone(), limit.clone()]),
            "add lhs canonical word bound",
        )?;
        require_same(
            b_bound.proposition(),
            &app("Nat.lt", [b.clone(), limit.clone()]),
            "add rhs canonical word bound",
        )?;
        let a_fits = app(
            "ir_byte_ltb_of_lt_v1",
            [a.clone(), limit.clone(), a_bound.term().clone()],
        );
        let b_fits = app(
            "ir_byte_ltb_of_lt_v1",
            [b.clone(), limit.clone(), b_bound.term().clone()],
        );
        let sum = app("Nat.add", [a.clone(), b.clone()]);
        let word = choose(
            &constant("Nat"),
            app("ir_nat_ltb", [sum.clone(), limit.clone()]),
            sum.clone(),
            app("Nat.sub", [sum, limit.clone()]),
        );
        let value = app("IRScalar.int_", [word.clone()]);
        let (ty, law, bound_law) = match carrier {
            AddCarrier::Unsigned => (
                "IRTy.uint_",
                "ir_byte_add_uint_canonical_v1",
                "ir_byte_add_uint_canonical_result_bound_v1",
            ),
            AddCarrier::Signed => (
                "IRTy.int_",
                "ir_byte_add_int_canonical_v1",
                "ir_byte_add_int_canonical_result_bound_v1",
            ),
        };
        let arguments = [nat(64), a.clone(), b.clone(), a_fits, b_fits];
        let evaluated = PendingEquality::candidate(
            constant("IRStepResult"),
            app(
                "ir_binop_eval",
                [
                    constant("IRBinOp.add"),
                    app(ty, [nat(64)]),
                    app("IRScalar.int_", [a]),
                    app("IRScalar.int_", [b]),
                ],
            ),
            app("IRStepResult.value", [value.clone()]),
            app(law, arguments.clone()),
        );
        let output_bound = PendingProof::candidate(
            app("Nat.lt", [word.clone(), limit.clone()]),
            app(
                "ir_byte_separation_lt_of_ltb_v1",
                [word, limit, app(bound_law, arguments)],
            ),
        );
        Ok((value, evaluated, output_bound))
    }
}
