// Copyright 2026 Andrew Yates | SPDX-License-Identifier: Apache-2.0

//! Neutral candidate assembly for the original machine-word wrapping bound.
//! This consumes the checked canonical-arithmetic vocabulary, not another
//! evaluator, an output answer or the opt-in total-restoring remainder owner.

use super::*;

/// Pending canonicality of the exact raw word, without an input-fit premise.
/// Every proposition and its term still require independent strict replay.
#[derive(Clone)]
pub struct WrappedWordBound {
    /// The original Nat expression `ir_wrap bits input`, never a host result.
    pub word: Expr,
    /// `Eq Bool (ir_nat_ltb word (ir_nat_pow2 bits)) Bool.true`.
    pub fits: PendingEquality,
    /// `Nat.lt word (ir_nat_pow2 bits)`, derived from the same Boolean bound.
    pub strict_bound: PendingProof,
}

impl Assembler<'_> {
    /// Derive the raw wrapping bound for a static machine width in `1..=64`.
    ///
    /// `word` may be any Nat expression; no canonical input, result answer,
    /// output-fit or overflow premise is supplied. Unsupported widths refuse
    /// before charging. Supported widths spend four existing operations:
    /// function congruence, endpoint conversion and two compositions. Failed
    /// work stays spent, and no scoped locals, lists, declarations or cache
    /// slots are allocated.
    ///
    /// The arithmetic body is built under a fresh neutral word binder and
    /// closed before the caller's actual expression is applied. Both returned
    /// proofs use this staging; caller-owned free/de Bruijn variables are
    /// application arguments, never captured beneath the helper binder.
    ///
    /// The caller must use the actual checked canonical-arithmetic ByteV1
    /// environment and independently replay each complete closed proposition
    /// and proof. This API does not install that vocabulary, check a candidate,
    /// execute a fetched instruction or grant source/native proof authority.
    pub fn wrapped_word_bound(&mut self, bits: u64, input: Expr) -> Result<WrappedWordBound> {
        if !(1..=64).contains(&bits) {
            return Err("wrapped word bound requires a width in 1..=64".into());
        }
        let word = Expr::bvar(0);
        let modulus = app("ir_nat_pow2", [nat(bits)]);
        // This is the positive-modulus theorem's predecessor parameter, not
        // an arithmetic answer. Replay checks succ(predecessor) against pow2.
        let predecessor = nat(if bits == 64 {
            u64::MAX
        } else {
            (1_u64 << bits) - 1
        });
        let raw = app("ir_wrap", [nat(bits), word.clone()]);
        let residue = app(
            "ir_div_rem_go",
            [modulus.clone(), word.clone(), word.clone()],
        );
        let remainder = PendingEquality::candidate(
            constant("Nat"),
            raw.clone(),
            residue.clone(),
            app("ir_nat_rem_is_residue", [word.clone(), modulus.clone()]),
        );
        let observer = Expr::lam(
            clean_kernel::BinderInfo::Default,
            constant("Nat"),
            app("ir_nat_ltb", [Expr::bvar(0), modulus.clone()]),
        );
        let observed = self.congruence_function(remainder, constant("Bool"), observer)?;
        let observed = self.convert_endpoints(
            observed,
            app("ir_nat_ltb", [raw.clone(), modulus.clone()]),
            app("ir_nat_ltb", [residue.clone(), modulus.clone()]),
        )?;
        let walk = PendingEquality::candidate(
            constant("Bool"),
            app("ir_nat_ltb", [residue.clone(), modulus.clone()]),
            app("ir_nat_ltb_walk", [residue.clone(), modulus.clone()]),
            app("ir_nat_ltb_walk_eq", [residue, modulus.clone()]),
        );
        let bounded = PendingEquality::candidate(
            constant("Bool"),
            walk.right().clone(),
            constant("Bool.true"),
            app(
                "ir_div_rem_go_bound",
                [
                    modulus.clone(),
                    word.clone(),
                    word.clone(),
                    app("ir_div_fuel_suffices_pos", [word, predecessor]),
                ],
            ),
        );
        let canonical = self.compose(observed, walk)?;
        let canonical = self.compose(canonical, bounded)?;
        let strict = app(
            "ir_byte_separation_lt_of_ltb_v1",
            [raw, modulus.clone(), canonical.term().clone()],
        );
        let close = |body| Expr::lam(clean_kernel::BinderInfo::Default, constant("Nat"), body);
        let closed_fits = close(canonical.term().clone());
        let closed_strict = close(strict);
        let raw = app("ir_wrap", [nat(bits), input.clone()]);
        Ok(WrappedWordBound {
            fits: PendingEquality::candidate(
                constant("Bool"),
                app("ir_nat_ltb", [raw.clone(), modulus.clone()]),
                constant("Bool.true"),
                Expr::app(closed_fits, input.clone()),
            ),
            strict_bound: PendingProof::candidate(
                app("Nat.lt", [raw.clone(), modulus]),
                Expr::app(closed_strict, input),
            ),
            word: raw,
        })
    }
}

#[cfg(test)]
#[path = "core_execution_wrapped_word_bound_tests.rs"]
mod tests;
