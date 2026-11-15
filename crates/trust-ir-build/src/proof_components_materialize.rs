// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//! Budgeted owner materialization for independently reconstructed open goals.
use super::*;

impl ProofComponents {
    /// Materialize internal named binders before ordinary kernel substitution.
    /// External handles keep their actual identities. These are normalization
    /// candidates only; no declaration or complete replay check is discarded.
    pub fn materialize_scoped_terms(
        &mut self,
        scope: &LocalScope,
        external: &[ScopedLocal],
        roots: &[Expr],
    ) -> Result<Vec<Expr>, String> {
        self.materialize_scoped_terms_observed(scope, external, roots, false)
    }
    /// Full fresh validation for internal transformations that use ordinary
    /// BVar metadata to prune their subsequent walk. No caller label is trusted.
    pub(super) fn materialize_scoped_terms_fully(
        &mut self,
        scope: &LocalScope,
        external: &[ScopedLocal],
        roots: &[Expr],
    ) -> Result<Vec<Expr>, String> {
        self.materialize_scoped_terms_observed(scope, external, roots, true)
    }
    fn materialize_scoped_terms_observed(
        &mut self,
        scope: &LocalScope,
        external: &[ScopedLocal],
        roots: &[Expr],
        fully: bool,
    ) -> Result<Vec<Expr>, String> {
        let result = self.materialize_scoped_terms_impl(scope, external, roots, fully);
        if result.is_err()
            && self
                .owner
                .as_ref()
                .is_some_and(|owner| owner.matches(&scope.memo_owner()))
        {
            self.materialized_capture_failed = true;
        }
        result
    }
    fn materialize_scoped_terms_impl(
        &mut self,
        scope: &LocalScope,
        external: &[ScopedLocal],
        roots: &[Expr],
        fully: bool,
    ) -> Result<Vec<Expr>, String> {
        if !self
            .owner
            .as_ref()
            .is_some_and(|owner| owner.matches(&scope.memo_owner()))
        {
            return Err("scoped materialization has another owner".into());
        }
        let remaining = self.context_work_remaining()?;
        if remaining == 0 {
            return Err("aggregate scoped materialization work limit".into());
        }
        if roots.len() > self.limits.operations
            || external.len() > self.limits.captures.saturating_add(self.limits.contexts)
        {
            return Err("scoped materialization input inventory limit".into());
        }
        let visible = vec![external.len(); roots.len()];
        let limits = crate::term_scope::TermScopeLimits {
            max_visits: remaining,
            max_depth: 16_384,
        };
        let (result, stats) = if fully {
            scope.close_external_forest_fully_with_limits(roots, external, &visible, limits)
        } else {
            scope.close_external_forest_with_limits(roots, external, &visible, limits)
        };
        self.analysis_visits = self
            .analysis_visits
            .checked_add(stats.visits)
            .ok_or("aggregate scoped materialization work overflow")?;
        self.context_work_remaining()?;
        let roots = match result {
            Ok(roots) => roots,
            Err(error) => {
                self.materialized_capture_failed = true;
                return Err(error.to_string());
            }
        };
        if let Err(error) = self.remember_materialized_capture_roots(external, &roots, stats.visits)
        {
            self.materialized_capture_failed = true;
            return Err(error);
        }
        Ok(roots)
    }
}

#[path = "proof_components_materialized_capture.rs"]
mod materialized_capture;

#[cfg(test)]
mod tests {
    use super::*;
    use clean_kernel::{Environment, Level};
    fn n() -> Expr {
        Expr::const_str("Nat")
    }
    fn eq(left: Expr, right: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
            [n(), left, right],
        )
    }
    fn refl(value: Expr) -> Expr {
        Expr::apps(
            Expr::const_(
                Name::from_string("Eq.refl"),
                vec![Level::succ(Level::zero())],
            ),
            [n(), value],
        )
    }
    #[test]
    fn materialized_owned_goal_survives_independent_kernel_parameter_substitution() {
        let mut scope = LocalScope::new();
        let f = scope.try_local(Expr::arrow(n(), n())).unwrap();
        let g = scope.try_local(Expr::arrow(n(), n())).unwrap();
        let input = scope.try_local(n()).unwrap();
        let original = input.lam(Expr::app(f.term().clone(), input.term().clone()));
        let actual = Expr::app(g.term().clone(), Expr::nat_lit(0));
        let deferred = original.abstract_fvar(f.id()).instantiate(g.term());
        let malformed = eq(Expr::app(deferred, Expr::nat_lit(0)), actual.clone());
        assert!(
            scope.close(&f.pi(g.pi(malformed))).is_err(),
            "ordinary kernel substitution cannot transport deferred named-binder registry pointers"
        );
        let mut parts = ProofComponents::new("materialize.goal", ProofLimits::default());
        parts
            .set_base(
                &scope,
                vec![
                    OwnedProofCapture::Parameter(f.clone()),
                    OwnedProofCapture::Parameter(g.clone()),
                ],
            )
            .unwrap();
        let mut materialized = parts
            .materialize_scoped_terms(&scope, &[f.clone(), g.clone()], &[original])
            .unwrap();
        let redirected = materialized
            .remove(0)
            .abstract_fvar(f.id())
            .instantiate(g.term());
        let proposition = eq(Expr::app(redirected, Expr::nat_lit(0)), actual.clone());
        let claim = scope.close(&f.pi(g.pi(proposition.clone()))).unwrap();
        let bundle = parts
            .close_scoped(
                &scope,
                f.lam(g.lam(refl(actual))),
                proposition,
                Default::default(),
            )
            .unwrap();
        let bytes = bundle.encode_with_claim(&claim).unwrap();
        let (decoded, transported) = ScopedProofComponentBundle::decode_with_claim(&bytes).unwrap();
        assert_eq!(claim, transported);
        let mut env = Environment::new();
        env.init_nat().unwrap();
        env.init_eq().unwrap();
        decoded.replay(&env, &claim, 2_000_000).unwrap();
    }
    #[test]
    fn scoped_materialization_keeps_owner_and_remaining_work_guards() {
        let mut scope = LocalScope::new();
        let input = scope.try_local(n()).unwrap();
        let mut foreign = LocalScope::new();
        let other = foreign.try_local(n()).unwrap();
        assert_eq!(input.id(), other.id());
        let mut parts = ProofComponents::new(
            "materialize.guards",
            ProofLimits {
                operations: 16,
                ..Default::default()
            },
        );
        parts.set_base(&scope, vec![]).unwrap();
        assert!(
            parts
                .materialize_scoped_terms(&foreign, &[], &[Expr::nat_lit(0)])
                .is_err()
        );
        assert!(
            parts
                .materialize_scoped_terms(&scope, &[other], &[input.term().clone()])
                .is_err()
        );
        assert!(
            parts
                .materialize_scoped_terms(&scope, &[input.clone(), input], &[Expr::nat_lit(0)])
                .is_err()
        );
        let mut refused = false;
        for _ in 0..32 {
            if parts
                .materialize_scoped_terms(&scope, &[], &[Expr::nat_lit(0)])
                .is_err()
            {
                refused = true;
                break;
            }
        }
        assert!(refused);
        assert!(parts.analysis_visits <= parts.limits.operations);
        let before = parts.analysis_visits;
        assert!(
            parts
                .materialize_scoped_terms(&scope, &[], &[Expr::nat_lit(0)])
                .is_err()
        );
        assert_eq!(before, parts.analysis_visits);
    }
}
