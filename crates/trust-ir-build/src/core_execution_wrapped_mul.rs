// Copyright 2026 Andrew Yates | SPDX-License-Identifier: Apache-2.0

//! Pending agreement between the original uint32 Mul word and prelude Nat.mod.
//! The existing canonical quotient/remainder laws supply the arithmetic; this
//! installs no evaluator, declaration, remainder package or proof authority.

use super::*;

impl Assembler<'_> {
    /// Assemble raw uint32 multiplication's modulus equality and strict range.
    ///
    /// The returned word is exactly `ir_wrap 32 (ir_nat_mul a b)`. Its pending
    /// equality targets `Nat.mod (Nat.mul a b) (ir_nat_pow2 32)`; its pending
    /// proof states the strict range of that same original word. Inputs may be
    /// arbitrary Nat expressions: no input-fit, result answer, quotient guess
    /// or output-bound premise is accepted.
    ///
    /// The neutral remainder proof is closed before application to caller
    /// expressions. Construction spends this caller's existing operation ledger
    /// and allocates no scoped locals, lists, declarations or lookup entries.
    /// These are pending terms, not checked receipts. Consumers must replay
    /// their complete independently reconstructed claims in the actual checked
    /// canonical-arithmetic environment. This grants no fetched-site, source,
    /// body-license or native authority.
    pub fn byte_mul_word32_mod(
        &mut self,
        a: Expr,
        b: Expr,
    ) -> Result<(Expr, PendingEquality, PendingProof)> {
        let ty = constant("Nat");
        let modulus = app("ir_nat_pow2", [nat(32)]);
        let product = app("ir_nat_mul", [a.clone(), b.clone()]);
        let original = self.wrapped_word32_mod(product.clone())?;
        let raw = original.left().clone();
        let original_modulus = original.right().clone();
        let standard = app("Nat.mul", [a.clone(), b.clone()]);
        let normalized = self.congruence_function(
            PendingEquality::candidate(
                ty.clone(),
                product.clone(),
                standard.clone(),
                app("ir_nat_mul_canonical_agrees_v1", [a, b]),
            ),
            ty.clone(),
            Expr::lam(
                clean_kernel::BinderInfo::Default,
                ty,
                app("Nat.mod", [Expr::bvar(0), modulus.clone()]),
            ),
        )?;
        let normalized = self.convert_endpoints(
            normalized,
            original_modulus,
            app("Nat.mod", [standard, modulus]),
        )?;
        let equality = self.compose(original, normalized)?;
        let bounded = self.wrapped_word_bound(32, product)?;
        Ok((raw, equality, bounded.strict_bound))
    }
}
