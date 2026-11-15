// Copyright 2026 Andrew Yates | SPDX-License-Identifier: Apache-2.0

//! Pending canonicality of the original raw full64 wrapped Add word.
//!
//! This reuses the checked canonical-arithmetic package, not another evaluator.
//! The raw `ir_wrap 64 (Nat.add a b)` remains the returned word; a separate
//! equality relates it to the existing conditional Add result. Neither an
//! overflow flag nor absence of signed/unsigned overflow is assumed or proved.
//! No fetched instruction, source, native or default-vocabulary authority is
//! supplied. The complete closed claims require independent strict replay.

use super::*;

#[cfg(test)]
#[path = "core_execution_wrapped_add_tests.rs"]
mod tests;

impl Assembler<'_> {
    /// Derive raw wrapped64 Add's conditional-result equality and Nat bound.
    ///
    /// The inputs must state exactly `Nat.lt a (ir_nat_pow2 64)` and the same
    /// bound for `b`. The returned triple is the original raw Nat word,
    /// pending `Eq Nat raw conditional_result`, and pending `Nat.lt raw
    /// (ir_nat_pow2 64)`. No result answer, output-fit premise, carrier, chosen
    /// wrap branch or overflow-flag premise is accepted.
    ///
    /// One existing operation is charged before every bound-shape check. The
    /// fixed closed Nat-to-Bool congruence allocates no scoped locals, lists,
    /// declarations or cache. Matching metadata does not validate supplied
    /// evidence: callers must carry the actual checked canonical-arithmetic
    /// owner and replay both complete claims, not merely their projections.
    pub fn byte_add_word64_canonical(
        &mut self,
        a: Expr,
        b: Expr,
        a_bound: PendingProof,
        b_bound: PendingProof,
    ) -> Result<(Expr, PendingEquality, PendingProof)> {
        self.charge()?;
        let limit = app("ir_nat_pow2", [nat(64)]);
        require_same(
            a_bound.proposition(),
            &app("Nat.lt", [a.clone(), limit.clone()]),
            "wrapped add lhs canonical word bound",
        )?;
        require_same(
            b_bound.proposition(),
            &app("Nat.lt", [b.clone(), limit.clone()]),
            "wrapped add rhs canonical word bound",
        )?;
        let arguments = [
            nat(64),
            a.clone(),
            b.clone(),
            app(
                "ir_byte_ltb_of_lt_v1",
                [a.clone(), limit.clone(), a_bound.term().clone()],
            ),
            app(
                "ir_byte_ltb_of_lt_v1",
                [b.clone(), limit.clone(), b_bound.term().clone()],
            ),
        ];
        let sum = app("Nat.add", [a, b]);
        let raw = app("ir_wrap", [nat(64), sum.clone()]);
        let conditional = choose(
            &constant("Nat"),
            app("ir_nat_ltb", [sum.clone(), limit.clone()]),
            sum.clone(),
            app("Nat.sub", [sum, limit.clone()]),
        );
        let equality_term = app("ir_byte_add_wrap_bounded_sum_v1", arguments.clone());
        let equality = PendingEquality::candidate(
            constant("Nat"),
            raw.clone(),
            conditional.clone(),
            equality_term.clone(),
        );
        // The only binder belongs to this fixed closed function. In particular
        // a/b never enter it, so no caller-owned local is captured or rebased.
        let observer = Expr::lam(
            clean_kernel::BinderInfo::Default,
            constant("Nat"),
            app("ir_nat_ltb", [Expr::bvar(0), limit.clone()]),
        );
        let raw_ltb = app("ir_nat_ltb", [raw.clone(), limit.clone()]);
        let conditional_ltb = app("ir_nat_ltb", [conditional.clone(), limit.clone()]);
        let transported = app(
            "ir_eq_cong",
            [
                constant("Nat"),
                constant("Bool"),
                observer,
                raw.clone(),
                conditional,
                equality_term,
            ],
        );
        let bounded = trans(
            &constant("Bool"),
            raw_ltb,
            conditional_ltb,
            constant("Bool.true"),
            transported,
            app("ir_byte_add_word_bound_v1", arguments),
        );
        let output_bound = PendingProof::candidate(
            app("Nat.lt", [raw.clone(), limit.clone()]),
            app(
                "ir_byte_separation_lt_of_ltb_v1",
                [raw.clone(), limit, bounded],
            ),
        );
        Ok((raw, equality, output_bound))
    }
}
