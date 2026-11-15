// Copyright 2026 Andrew Yates | SPDX-License-Identifier: Apache-2.0
//! Prepaid owned handles with explicit bounded ordinary-graph reuse.
use super::*;
use crate::scoped_local::OwnedExternalContext;

pub(crate) struct ExternalContext {
    component: Arc<()>,
    inventory: OwnedExternalContext,
}

#[cfg(test)]
#[path = "proof_components_equation_root_tests.rs"]
mod equation_root_tests;
#[cfg(test)]
#[path = "proof_components_inner_prefix_tests.rs"]
mod inner_prefix_tests;
#[cfg(test)]
#[path = "proof_components_materialization_reuse_tests.rs"]
mod reuse_tests;
impl ExternalContext {
    pub(crate) fn checkpoint(&self) -> usize {
        self.inventory.checkpoint()
    }
    pub(crate) fn restore(&mut self, checkpoint: usize) -> Result<(), String> {
        // Extension prepays both insertion and eventual suffix restoration.
        self.inventory.restore(checkpoint)
    }
}

impl ProofComponents {
    pub(super) fn external_ordinary_view<'a>(
        &self,
        scope: &LocalScope,
        context: &'a ExternalContext,
    ) -> Result<Option<crate::scoped_local::PreparedOrdinaryView<'a>>, String> {
        self.external_context_ids(scope, context)?;
        context.inventory.ordinary_view_for(scope)
    }
    pub(crate) fn charged_enable_external_materialization_reuse(
        &mut self,
        scope: &LocalScope,
        context: &mut ExternalContext,
    ) -> Result<(), String> {
        self.spend_context_work(
            context
                .inventory
                .dynamic_len()
                .checked_mul(2)
                .and_then(|n| {
                    context
                        .inventory
                        .len()
                        .checked_mul(2)
                        .and_then(|positions| n.checked_add(positions))
                })
                .and_then(|n| n.checked_add(5))
                .ok_or("prepared reuse inventory overflow")?,
        )?;
        self.external_context_ids(scope, context)?;
        scope.enable_prepared_materialization_reuse(&mut context.inventory)
    }
    pub(crate) fn poison_external_materialization(
        &self,
        scope: &LocalScope,
        context: &ExternalContext,
    ) {
        if self.external_context_ids(scope, context).is_ok() {
            context.inventory.poison_materialization();
        }
    }
    pub(crate) fn charged_external_context(
        &mut self,
        scope: &LocalScope,
        locals: &[ScopedLocal],
    ) -> Result<ExternalContext, String> {
        let setup = locals
            .len()
            .checked_mul(4)
            .and_then(|n| n.checked_add(1))
            .ok_or("external context inventory overflow")?;
        if locals.len() > self.limits.captures.saturating_add(self.limits.contexts) {
            return Err("external context inventory limit".into());
        }
        self.spend_context_work(setup)?;
        if !self
            .owner
            .as_ref()
            .is_some_and(|owner| owner.matches(&scope.memo_owner()))
        {
            return Err("external context has another component scope owner".into());
        }
        let inventory = scope.prepare_external_context(locals)?;
        let component = self
            .external_context_owner
            .get_or_insert_with(|| Arc::new(()))
            .clone();
        Ok(ExternalContext {
            component,
            inventory,
        })
    }

    fn owns_external_context(&self, context: &ExternalContext) -> bool {
        self.external_context_owner
            .as_ref()
            .is_some_and(|owner| Arc::ptr_eq(owner, &context.component))
    }

    pub(super) fn external_context_ids<'a>(
        &self,
        scope: &LocalScope,
        context: &'a ExternalContext,
    ) -> Result<&'a HashSet<FVarId>, String> {
        if !self.owns_external_context(context)
            || !self
                .owner
                .as_ref()
                .is_some_and(|owner| owner.matches(&scope.memo_owner()))
        {
            return Err("external context has another component or scope owner".into());
        }
        context.inventory.ids_for(scope)
    }

    pub(crate) fn charged_extend_external_context(
        &mut self,
        scope: &LocalScope,
        context: &mut ExternalContext,
        locals: &[ScopedLocal],
    ) -> Result<(), String> {
        let length = context
            .inventory
            .len()
            .checked_add(locals.len())
            .ok_or("external context extension overflow")?;
        if length > self.limits.captures.saturating_add(self.limits.contexts) {
            return Err("external context extension inventory limit".into());
        }
        // Four preparation units plus two for eventual pop/removal. Reuse adds
        // two for generation push/truncation and three for position-index
        // insertion/storage/eventual removal. Complete validation precedes all
        // updates; failure never changes inventory or refunds its reservation.
        self.spend_context_work(
            locals
                .len()
                .checked_mul(if context.inventory.reuses_materialization() {
                    11
                } else {
                    6
                })
                .ok_or("external context work overflow")?,
        )?;
        if !self.owns_external_context(context)
            || !self
                .owner
                .as_ref()
                .is_some_and(|owner| owner.matches(&scope.memo_owner()))
        {
            return Err("external context has another component or scope owner".into());
        }
        scope.extend_external_context(&mut context.inventory, locals)
    }

    pub(super) fn charged_materialize_external_context_fully(
        &mut self,
        scope: &LocalScope,
        context: &ExternalContext,
        roots: &[Expr],
    ) -> Result<Vec<Expr>, String> {
        let result =
            self.materialize_external_context_fully_impl(scope, context, roots, false, None);
        if result.is_err() {
            self.poison_external_materialization(scope, context);
        }
        result
    }
    pub(super) fn charged_materialize_equation_context_fully(
        &mut self,
        scope: &LocalScope,
        context: &ExternalContext,
        roots: &[Expr],
    ) -> Result<Vec<Expr>, String> {
        let result =
            self.materialize_external_context_fully_impl(scope, context, roots, true, None);
        if result.is_err() {
            self.poison_external_materialization(scope, context);
        }
        result
    }
    /// Preserve the exact prepared owner/inventory while intersecting a
    /// caller's additional work cap with the same combined component ledger.
    pub(crate) fn charged_materialize_prepared_context_with_limit(
        &mut self,
        scope: &LocalScope,
        context: &ExternalContext,
        roots: &[Expr],
        work_limit: usize,
    ) -> Result<Vec<Expr>, String> {
        let result = self.materialize_external_context_fully_impl(
            scope,
            context,
            roots,
            false,
            Some(work_limit),
        );
        if result.is_err() {
            self.poison_external_materialization(scope, context);
        }
        result
    }
    fn materialize_external_context_fully_impl(
        &mut self,
        scope: &LocalScope,
        context: &ExternalContext,
        roots: &[Expr],
        equation: bool,
        work_limit: Option<usize>,
    ) -> Result<Vec<Expr>, String> {
        if !self.owns_external_context(context)
            || !self
                .owner
                .as_ref()
                .is_some_and(|owner| owner.matches(&scope.memo_owner()))
        {
            return Err("prepared materialization has another component or scope owner".into());
        }
        if context.inventory.len() > self.limits.captures.saturating_add(self.limits.contexts)
            || roots.len() > self.limits.operations
        {
            return Err("prepared materialization inventory limit".into());
        }
        let setup = roots
            .len()
            .checked_mul(2)
            .ok_or("prepared root inventory overflow")?;
        if work_limit.is_some_and(|limit| setup > limit) {
            return Err("prepared root caller work limit".into());
        }
        self.spend_context_work(setup)?;
        let limits = crate::term_scope::TermScopeLimits {
            max_visits: self
                .context_work_remaining()?
                .min(work_limit.map_or(usize::MAX, |limit| limit - setup)),
            max_depth: 16_384,
        };
        let (result, stats) = if equation {
            scope.close_prepared_equation_forest_fully_with_limits(
                roots,
                &context.inventory,
                limits,
            )
        } else {
            scope.close_prepared_external_forest_fully_with_limits(
                roots,
                &context.inventory,
                limits,
            )
        };
        self.spend_context_work(stats.visits)?;
        result.map_err(|error| error.to_string())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use clean_kernel::{BinderInfo, Environment, Level, TypeChecker};
    fn n() -> Expr {
        Expr::const_str("Nat")
    }
    fn parts(scope: &LocalScope, operations: usize) -> ProofComponents {
        let mut parts = ProofComponents::new(
            "external.context",
            ProofLimits {
                operations,
                ..Default::default()
            },
        );
        parts.set_base(scope, vec![]).unwrap();
        parts
    }

    #[test]
    fn prepared_external_context_keeps_shadow_growth_and_prepaid_prefix_restoration() {
        let mut scope = LocalScope::new();
        let a = scope.try_local(n()).unwrap();
        let b = scope.try_local(n()).unwrap();
        let binder_id = b.id();
        let root = b.lam(Expr::nat_lit(0)); // An UNUSED deferred binder still matters.
        let mut parts = parts(&scope, 10_000);
        let mut context = parts
            .charged_external_context(&scope, &[a.clone()])
            .unwrap();
        let actual = parts
            .charged_materialize_external_context_fully(&scope, &context, &[root.clone()])
            .unwrap();
        assert_eq!(
            actual,
            vec![Expr::lam(BinderInfo::Default, n(), Expr::nat_lit(0))]
        );
        let mark = context.checkpoint();
        parts
            .charged_extend_external_context(&scope, &mut context, &[b])
            .unwrap();
        let before = parts.counts().3;
        let error = parts
            .charged_materialize_external_context_fully(&scope, &context, &[root.clone()])
            .unwrap_err();
        assert_eq!(
            error,
            crate::term_scope::TermScopeError::ShadowedLocal(binder_id).to_string()
        );
        assert!(parts.counts().3 > before);
        let paid = parts.counts().3;
        context.restore(mark).unwrap();
        assert_eq!(
            parts.counts().3,
            paid,
            "restoration was prepaid; it never refunds work"
        );
        assert!(
            context.restore(0).is_err(),
            "the initial inventory cannot be revoked"
        );
        assert_eq!(
            parts
                .charged_materialize_external_context_fully(&scope, &context, &[root])
                .unwrap(),
            actual
        );
        assert!(
            parts.counts().3 > paid,
            "restored contexts still perform a fresh complete walk"
        );
    }

    #[test]
    fn prepared_external_context_rejects_foreign_budget_missing_globals_and_atomic_bad_extensions()
    {
        let mut scope = LocalScope::new();
        let a = scope.try_local(n()).unwrap();
        let b = scope.try_local(n()).unwrap();
        let mut owner = parts(&scope, 10_000);
        let mut context = owner
            .charged_external_context(&scope, &[a.clone()])
            .unwrap();
        let mut other = parts(&scope, 10_000);
        assert!(
            other
                .charged_materialize_external_context_fully(&scope, &context, &[a.term().clone()])
                .unwrap_err()
                .contains("another component")
        );
        assert!(
            owner
                .charged_materialize_external_context_fully(&scope, &context, &[b.term().clone()])
                .is_err()
        );
        let mark = context.checkpoint();
        let before = owner.counts().3;
        assert!(
            owner
                .charged_extend_external_context(&scope, &mut context, &[b.clone(), b])
                .is_err()
        );
        assert_eq!(context.checkpoint(), mark);
        assert!(owner.counts().3 > before);
        let mut foreign = LocalScope::new();
        let x = foreign.try_local(n()).unwrap();
        assert!(
            owner
                .charged_extend_external_context(&scope, &mut context, &[x])
                .is_err()
        );
        assert_eq!(context.checkpoint(), mark);
        assert!(
            owner
                .charged_external_context(&scope, &[a.clone(), a])
                .is_err()
        );
        assert!(
            owner
                .charged_materialize_external_context_fully(&foreign, &context, &[n()])
                .is_err()
        );
    }

    #[test]
    fn prepared_external_context_repeated_typed_calls_keep_the_original_work_cap() {
        let mut scope = LocalScope::new();
        let globals = (0..32)
            .map(|_| scope.try_local(n()).unwrap())
            .collect::<Vec<_>>();
        let parameter = scope.try_local(n()).unwrap();
        let equality = Expr::apps(
            Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
            [n(), parameter.term().clone(), parameter.term().clone()],
        );
        let statement = parameter.pi(equality);
        let mut prepared = parts(&scope, 400);
        let context = prepared.charged_external_context(&scope, &globals).unwrap();
        let mut env = Environment::new();
        env.init_nat().unwrap();
        env.init_eq().unwrap();
        let proof = Expr::apps(
            Expr::const_(
                Name::from_string("Eq.refl"),
                vec![Level::succ(Level::zero())],
            ),
            [n(), Expr::nat_lit(3)],
        );
        for _ in 0..3 {
            let goal = prepared
                .charged_instantiate_in_external_context(
                    &scope,
                    &context,
                    &statement,
                    &[Expr::nat_lit(3)],
                )
                .unwrap();
            TypeChecker::new(&env).check_type(&proof, &goal).unwrap();
        }
        assert!(prepared.counts().3 <= 400);
        let mut repeated_setup = parts(&scope, 400);
        let results = (0..3)
            .map(|_| {
                repeated_setup.charged_instantiate_scoped_telescope(
                    &scope,
                    &globals,
                    &statement,
                    &[Expr::nat_lit(3)],
                )
            })
            .collect::<Vec<_>>();
        assert!(results[0].is_ok());
        assert!(
            results.iter().any(Result::is_err),
            "the same cap must expose repeated inventory work"
        );
    }

    #[test]
    fn prepared_external_context_complete_depth_and_failed_scan_work_are_preserved() {
        let scope = LocalScope::with_limits(crate::scoped_local::LocalScopeLimits {
            closing: crate::term_scope::TermScopeLimits {
                max_visits: 10_000,
                max_depth: 5,
            },
            ..Default::default()
        });
        let mut parts = parts(&scope, 10_000);
        let context = parts.charged_external_context(&scope, &[]).unwrap();
        let mut root = Expr::nat_lit(0);
        for _ in 0..5 {
            root = Expr::app(Expr::const_str("Nat.succ"), root);
        }
        let before = parts.counts().3;
        assert!(
            parts
                .charged_materialize_external_context_fully(&scope, &context, &[root])
                .unwrap_err()
                .contains("depth")
        );
        assert!(parts.counts().3 > before);
        let remaining = parts.context_work_remaining().unwrap();
        parts.spend_context_work(remaining - 4).unwrap();
        let root = Expr::app(Expr::const_str("Nat.succ"), Expr::nat_lit(0));
        assert!(
            parts
                .charged_materialize_external_context_fully(&scope, &context, &[root.clone()])
                .is_err()
        );
        assert_eq!(parts.context_work_remaining().unwrap(), 0);
        assert!(
            parts
                .charged_materialize_external_context_fully(&scope, &context, &[root])
                .is_err()
        );
        assert_eq!(parts.context_work_remaining().unwrap(), 0);
    }
}

#[cfg(test)]
mod prepared_caller_work_limit_tests {
    use super::*;
    use clean_kernel::BinderInfo;
    fn n() -> Expr {
        Expr::const_str("Nat")
    }
    #[test]
    fn prepared_caller_limit_pays_setup_and_failed_visits_without_overdrawing_either_ledger() {
        let mut scope = LocalScope::new();
        let x = scope.try_local(n()).unwrap();
        let mut root = x.term().clone();
        for _ in 0..24 {
            root = Expr::arrow(n(), root);
        }
        let (mut succeeded, mut charged_failure) = (false, false);
        for cap in 0..=160 {
            let mut parts = ProofComponents::new("prepared.caller.cutoff", Default::default());
            parts.set_base(&scope, vec![]).unwrap();
            let mut context = parts
                .charged_external_context(&scope, &[x.clone()])
                .unwrap();
            parts
                .charged_enable_external_materialization_reuse(&scope, &mut context)
                .unwrap();
            let before = parts.counts().3;
            let result = parts.charged_materialize_prepared_context_with_limit(
                &scope,
                &context,
                &[root.clone()],
                cap,
            );
            let used = parts.counts().3 - before;
            assert!(used <= cap, "cap={cap}, used={used}");
            assert_eq!(parts.counts().0, 0);
            match result {
                Ok(roots) => {
                    succeeded = true;
                    assert_eq!(roots, vec![root.clone()]);
                }
                Err(_) => charged_failure |= used > 2,
            }
        }
        assert!(succeeded && charged_failure);
        let mut parts = ProofComponents::new(
            "prepared.caller.component",
            crate::proof_assembly::ProofLimits {
                operations: 24,
                ..Default::default()
            },
        );
        parts.set_base(&scope, vec![]).unwrap();
        let context = parts.charged_external_context(&scope, &[x]).unwrap();
        let before = parts.counts().3;
        assert!(
            parts
                .charged_materialize_prepared_context_with_limit(
                    &scope,
                    &context,
                    &[root],
                    usize::MAX
                )
                .is_err()
        );
        assert!(parts.counts().3 > before && parts.counts().3 <= 24);
    }
    #[test]
    fn prepared_caller_limit_preserves_component_owner_unused_shadow_growth_and_restoration() {
        let mut scope = LocalScope::new();
        let a = scope.try_local(n()).unwrap();
        let b = scope.try_local(n()).unwrap();
        let root = b.lam(Expr::nat_lit(0));
        let mut parts = ProofComponents::new("prepared.caller.owner", Default::default());
        parts.set_base(&scope, vec![]).unwrap();
        let mut context = parts
            .charged_external_context(&scope, &[a.clone()])
            .unwrap();
        parts
            .charged_enable_external_materialization_reuse(&scope, &mut context)
            .unwrap();
        let expected = vec![Expr::lam(BinderInfo::Default, n(), Expr::nat_lit(0))];
        assert_eq!(
            parts
                .charged_materialize_prepared_context_with_limit(
                    &scope,
                    &context,
                    &[root.clone()],
                    10_000
                )
                .unwrap(),
            expected
        );
        let mut foreign = ProofComponents::new("prepared.caller.foreign", Default::default());
        foreign.set_base(&scope, vec![]).unwrap();
        assert!(
            foreign
                .charged_materialize_prepared_context_with_limit(
                    &scope,
                    &context,
                    &[root.clone()],
                    10_000
                )
                .unwrap_err()
                .contains("another component or scope owner")
        );
        let checkpoint = context.checkpoint();
        parts
            .charged_extend_external_context(&scope, &mut context, &[b.clone()])
            .unwrap();
        assert_eq!(
            parts
                .charged_materialize_prepared_context_with_limit(
                    &scope,
                    &context,
                    &[root.clone()],
                    10_000
                )
                .unwrap_err(),
            crate::term_scope::TermScopeError::ShadowedLocal(b.id()).to_string()
        );
        let paid = parts.counts().3;
        context.restore(checkpoint).unwrap();
        assert_eq!(parts.counts().3, paid);
        assert_eq!(
            parts
                .charged_materialize_prepared_context_with_limit(
                    &scope,
                    &context,
                    &[root.clone()],
                    10_000
                )
                .unwrap_err(),
            crate::term_scope::TermScopeError::VisitLimit.to_string(),
            "restoration never revokes sticky enclosing-call failure poisoning",
        );
        assert!(parts.counts().3 > paid);
        let mut fresh = parts.charged_external_context(&scope, &[a]).unwrap();
        parts
            .charged_enable_external_materialization_reuse(&scope, &mut fresh)
            .unwrap();
        assert_eq!(
            parts
                .charged_materialize_prepared_context_with_limit(&scope, &fresh, &[root], 10_000)
                .unwrap(),
            expected
        );
    }
}
