// Copyright 2026 Andrew Yates | SPDX-License-Identifier: Apache-2.0

//! Pending positive-modulus remainder bounds from the checked Clean package.
//! This is not another arithmetic evaluator or an output-answer/fit premise.
//! The original and total definitions remain distinct, and zero is excluded by
//! constructing the modulus as `Nat.succ predecessor`. Expressions and theorem
//! names are only candidates until independently closed and strictly replayed.

use super::*;

#[cfg(test)]
#[path = "core_execution_remainder_bound_tests.rs"]
mod tests;

#[derive(Clone, Copy)]
enum RemainderDefinition {
    Original,
    Total,
}

impl Assembler<'_> {
    /// Derive the original remainder's strict positive-modulus bound.
    ///
    /// For Nat expressions `dividend` and `divisor_predecessor`, the exact
    /// candidate is `Eq Bool (ir_nat_ltb (ir_nat_rem dividend (Nat.succ
    /// divisor_predecessor)) (Nat.succ divisor_predecessor)) Bool.true`.
    /// No dividend bound, remainder answer, or output-fit evidence is supplied.
    /// One existing operation is charged before construction; no locals,
    /// lists, declarations, cache or checker policy are changed. The caller
    /// must carry the actual checked opt-in package and replay the complete
    /// closed claim. Ill-typed expressions are not facts merely because the
    /// Rust metadata matches.
    pub fn remainder_positive_bound(
        &mut self,
        dividend: Expr,
        divisor_predecessor: Expr,
    ) -> Result<PendingEquality> {
        self.positive_remainder_bound(dividend, divisor_predecessor, RemainderDefinition::Original)
    }

    /// Derive the additive total restoring remainder's strict positive bound.
    ///
    /// Its exact spelling is the original helper's predicate with
    /// `ir_nat_rem_total_v1` instead of `ir_nat_rem`. The same positive-modulus
    /// construction, single charge and independent replay requirement apply.
    /// This helper does not replace the operational definition, admit a zero
    /// modulus, install the package in a default vocabulary, or prove a
    /// program/source/native refinement.
    pub fn total_remainder_positive_bound(
        &mut self,
        dividend: Expr,
        divisor_predecessor: Expr,
    ) -> Result<PendingEquality> {
        self.positive_remainder_bound(dividend, divisor_predecessor, RemainderDefinition::Total)
    }

    fn positive_remainder_bound(
        &mut self,
        dividend: Expr,
        divisor_predecessor: Expr,
        definition: RemainderDefinition,
    ) -> Result<PendingEquality> {
        self.charge()?;
        let (operation, law) = match definition {
            RemainderDefinition::Original => ("ir_nat_rem", "ir_nat_rem_positive_bound_v1"),
            RemainderDefinition::Total => {
                ("ir_nat_rem_total_v1", "ir_nat_rem_total_positive_bound_v1")
            }
        };
        let divisor = app("Nat.succ", [divisor_predecessor.clone()]);
        let remainder = app(operation, [dividend.clone(), divisor.clone()]);
        Ok(PendingEquality::candidate(
            constant("Bool"),
            app("ir_nat_ltb", [remainder, divisor]),
            constant("Bool.true"),
            app(law, [dividend, divisor_predecessor]),
        ))
    }
}
