// Copyright 2026 Andrew Yates | SPDX-License-Identifier: Apache-2.0

//! Typed endpoint presentation is still untrusted candidate assembly.

use super::*;

impl Assembler<'_> {
    /// Present new endpoints while retaining the original claimed equality.
    ///
    /// The candidate is `let new : NewEq := (let old : OldEq := proof;
    /// old); new`. Strict kernel replay must check the original declaration,
    /// its value, and conversion of its result to the requested declaration.
    /// A true new equality cannot hide a false old metadata claim. Neither
    /// Rust metadata nor this candidate certifies either proposition.
    ///
    /// Both declaration types and the original proof remain in the caller's
    /// context: the old let is in the new let's VALUE, not its body. No lift,
    /// substitution or temporary scoped local is needed, including for
    /// contextual de Bruijn references. Only the two returned `BVar(0)` nodes
    /// refer to the respective newly introduced proof bindings.
    ///
    /// Charge one compound candidate before construction. Existing operation,
    /// local, replay and admission limits are unchanged; full strict replay,
    /// not infer-only processing, is required to check both declarations.
    pub fn ascribe_preserving_endpoints(
        &mut self,
        equality: PendingEquality,
        left: Expr,
        right: Expr,
    ) -> Result<PendingEquality> {
        self.charge()?;
        let original = Expr::let_named(
            Name::anon(),
            equality.proposition(),
            equality.term,
            Expr::bvar(0),
            false,
        );
        let term = Expr::let_named(
            Name::anon(),
            eq(&equality.ty, left.clone(), right.clone()),
            original,
            Expr::bvar(0),
            false,
        );
        Ok(PendingEquality::candidate(equality.ty, left, right, term))
    }

    /// Retain the requested equality as an explicit kernel `let` declaration.
    ///
    /// Unlike [`Self::convert_endpoints`], this wraps the original proof term
    /// in `let p : Eq ty left right := old_term; p`. The equality type is kept
    /// verbatim, and the requested endpoints remain in the declaration even
    /// under neutral binders. Independent strict replay must check that this
    /// declaration is a type and that the original term inhabits it in the
    /// caller's actual context. Neither pending metadata nor this Rust result
    /// certifies the old or new proposition.
    ///
    /// This charges one candidate before construction, allocates no scoped
    /// locals or list inputs, and neither installs declarations nor changes
    /// kernel caches, limits, or proof-admission policy. The original proof is
    /// outside the new let body's binder; only the returned `BVar(0)` refers
    /// to that proof binding.
    pub fn ascribe_endpoints(
        &mut self,
        equality: PendingEquality,
        left: Expr,
        right: Expr,
    ) -> Result<PendingEquality> {
        self.charge()?;
        let proposition = eq(&equality.ty, left.clone(), right.clone());
        let term = Expr::let_named(
            Name::anon(),
            proposition,
            equality.term,
            Expr::bvar(0),
            false,
        );
        Ok(PendingEquality::candidate(equality.ty, left, right, term))
    }
}

#[cfg(test)]
#[path = "core_execution_endpoint_ascription_tests.rs"]
mod tests;
