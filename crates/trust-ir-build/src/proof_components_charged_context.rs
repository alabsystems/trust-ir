// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//! Bounded producer contexts sharing the component's existing work ledger.
use super::*;

impl ProofComponents {
    pub(crate) fn context_work_totals(&self) -> (usize, usize) {
        (self.analysis_visits, self.analysis_words)
    }
    pub(crate) fn context_work_remaining(&self) -> Result<usize, String> {
        self.limits
            .operations
            .checked_sub(self.analysis_visits)
            .and_then(|left| left.checked_sub(self.analysis_words))
            .ok_or_else(|| "charged normalization aggregate work exhausted".into())
    }
    pub(crate) fn spend_context_work(&mut self, work: usize) -> Result<(), String> {
        let remaining = self.context_work_remaining()?;
        if work > remaining {
            return Err(format!(
                "charged normalization exceeded its admitted remaining work (requested={work}, remaining={remaining})"
            ));
        }
        self.analysis_visits = self
            .analysis_visits
            .checked_add(work)
            .ok_or("charged normalization work overflow")?;
        Ok(())
    }
    /// Producer-only conservative independence query. A fresh bounded walk
    /// includes every FVar occurrence; no unknown footprint becomes empty and
    /// no memo is reused across owners, scopes or subsequent attempts.
    #[cfg(test)]
    pub(crate) fn charged_independent_of(
        &mut self,
        scope: &LocalScope,
        forbidden: &[ScopedLocal],
        expression: &Expr,
    ) -> Result<(), String> {
        self.charged_independent_forest_of(scope, forbidden, &[expression])
    }

    /// One fresh syntactic reference search for roots sharing the SAME guard.
    /// Successful prior roots contained none of these forbidden IDs, so the
    /// accumulated reference union preserves each root's first refusal.
    pub(crate) fn charged_independent_forest_of(
        &mut self,
        scope: &LocalScope,
        forbidden: &[ScopedLocal],
        expressions: &[&Expr],
    ) -> Result<(), String> {
        let setup = forbidden
            .len()
            .checked_mul(3)
            .and_then(|n| {
                forbidden
                    .len()
                    .checked_add(1)
                    .and_then(|per_root| per_root.checked_mul(expressions.len()))
                    .and_then(|roots| n.checked_add(roots))
            })
            .ok_or("independence query inventory overflow")?;
        self.spend_context_work(setup)?;
        if !self
            .owner
            .as_ref()
            .is_some_and(|owner| owner.matches(&scope.memo_owner()))
            || forbidden.iter().any(|local| !scope.owns(local))
        {
            return Err("independence query has another owner".into());
        }
        let mut walker = NormalizationReferences::new(self.context_work_remaining()?);
        let scanned = expressions.iter().try_for_each(|expression| {
            // This is constructor-maintained metadata, not an uncharged walk.
            if expression.has_loose_bvars() {
                return Err("first-order data has loose bound variables".into());
            }
            walker.scan(expression)?;
            if forbidden.iter().any(|local| walker.contains(local.id())) {
                return Err("first-order data depends on final CPS callbacks".into());
            }
            Ok(())
        });
        let visits = walker.work;
        drop(walker);
        self.spend_context_work(visits)?;
        scanned
    }
    /// Close an explicit source/parameter forest under the SAME remaining
    /// component budget. Per-root visibility retains actual telescope order.
    pub(crate) fn charged_materialize_forest(
        &mut self,
        scope: &LocalScope,
        external: &[ScopedLocal],
        roots: &[Expr],
        visible: &[usize],
    ) -> Result<Vec<Expr>, String> {
        self.charged_materialize_forest_impl(scope, external, roots, visible, false, None)
    }
    /// Apply a caller's additional bounded producer ledger without increasing
    /// this component's combined budget. Failed visits remain charged.
    pub(crate) fn charged_materialize_forest_with_limit(
        &mut self,
        scope: &LocalScope,
        external: &[ScopedLocal],
        roots: &[Expr],
        visible: &[usize],
        work_limit: usize,
    ) -> Result<Vec<Expr>, String> {
        self.charged_materialize_forest_impl(
            scope,
            external,
            roots,
            visible,
            false,
            Some(work_limit),
        )
    }
    #[cfg(test)]
    pub(super) fn charged_materialize_forest_fully(
        &mut self,
        scope: &LocalScope,
        external: &[ScopedLocal],
        roots: &[Expr],
        visible: &[usize],
    ) -> Result<Vec<Expr>, String> {
        self.charged_materialize_forest_impl(scope, external, roots, visible, true, None)
    }
    fn charged_materialize_forest_impl(
        &mut self,
        scope: &LocalScope,
        external: &[ScopedLocal],
        roots: &[Expr],
        visible: &[usize],
        fully_traversed: bool,
        work_limit: Option<usize>,
    ) -> Result<Vec<Expr>, String> {
        if !self
            .owner
            .as_ref()
            .is_some_and(|owner| owner.matches(&scope.memo_owner()))
        {
            return Err("charged materialization has another owner".into());
        }
        let setup = external
            .len()
            .checked_mul(4)
            .and_then(|n| n.checked_add(roots.len().checked_mul(2)?))
            .ok_or("charged materialization inventory overflow")?;
        if external.len() > self.limits.captures.saturating_add(self.limits.contexts)
            || roots.len() > self.limits.operations
            || visible.len() != roots.len()
            || setup > self.context_work_remaining()?
            || work_limit.is_some_and(|limit| setup > limit)
        {
            return Err(format!(
                "charged materialization inventory admission limit (external={}, roots={}, visibility={}, setup={setup}, remaining={})",
                external.len(),
                roots.len(),
                visible.len(),
                self.context_work_remaining()?
            ));
        }
        self.spend_context_work(setup)?;
        let limits = crate::term_scope::TermScopeLimits {
            max_visits: self
                .context_work_remaining()?
                .min(work_limit.map_or(usize::MAX, |limit| limit - setup)),
            max_depth: 16_384,
        };
        let (result, stats) = if fully_traversed {
            scope.close_external_forest_fully_with_limits(roots, external, visible, limits)
        } else {
            scope.close_external_forest_with_limits(roots, external, visible, limits)
        };
        self.spend_context_work(stats.visits)?;
        result.map_err(|error| error.to_string())
    }
    /// Producer data only. The original declarations/values remain mandatory
    /// in complete frozen-claim replay, including unused invalid definitions.
    /// Inventory probes prepay before allocation; both failed graph scans and
    /// failed closure attempts spend their actual bounded work without refunds.
    /// Complete syntactic reference summaries stay in this component; every
    /// call authenticates its owner, original entries and visibility again.
    /// No checker or materialized context is reused between these calls.
    /// Inputs must first be materialized against the caller's explicit owned
    /// inventory; a returned context never admits a missing input global.
    pub(crate) fn charged_normalization_context_with_opaque(
        &mut self,
        scope: &LocalScope,
        globals: &[ScopedLocal],
        inputs: &[Expr],
        opaque: &[ScopedLocal],
    ) -> Result<(clean_kernel::LocalContext, Vec<ScopedLocal>), String> {
        let declarations = self
            .base
            .len()
            .checked_add(self.bindings.len())
            .ok_or("charged normalization declaration count overflow")?;
        let setup = declarations
            .checked_mul(24)
            .and_then(|n| n.checked_add(globals.len().checked_mul(4)?))
            .and_then(|n| n.checked_add(opaque.len().checked_mul(8)?))
            .and_then(|n| n.checked_add(inputs.len().checked_mul(4)?))
            .ok_or("charged normalization inventory work overflow")?;
        if globals.len() > self.limits.captures.saturating_add(self.limits.contexts)
            || inputs.len() > self.limits.operations
            || opaque.len() > declarations
            || setup > self.context_work_remaining()?
        {
            return Err("charged normalization inventory admission limit".into());
        }
        self.spend_context_work(setup)?;
        let mut entries = self.normalization_entries(scope)?;
        let mut admitted = HashSet::new();
        for global in globals {
            if !scope.owns(global) || !admitted.insert(global.id()) {
                return Err("foreign or duplicate charged input global".into());
            }
        }
        // Original captures stay explicit even when hidden behind an internal
        // definition or producer-only opacity. No dependency slice can turn a
        // missing source input into implicit normalization authority.
        if self
            .base
            .iter()
            .any(|capture| !admitted.contains(&capture.local().id()))
        {
            return Err(
                "charged normalization needs every explicitly admitted original global".into(),
            );
        }
        let indices = entries
            .iter()
            .enumerate()
            .map(|(i, (local, _))| (local.id(), i))
            .collect::<HashMap<_, _>>();
        let mut seen = HashSet::new();
        for local in opaque {
            if !scope.owns(local) || !seen.insert(local.id()) {
                return Err("foreign or duplicate charged opaque owner".into());
            }
            let index = *indices
                .get(&local.id())
                .ok_or("charged opaque definition is not retained")?;
            if entries[index].1.is_none() {
                return Err("charged opacity requires the original defining value".into());
            }
            entries[index].1 = None;
        }
        let locals = entries
            .iter()
            .map(|(local, _)| local.clone())
            .collect::<Vec<_>>();
        let mut needed = vec![false; entries.len()];
        let remaining = self.context_work_remaining()?;
        let mut walker = complete_references::References::new(
            self.normalization_references.as_deref_mut(),
            remaining,
        )?;
        let scan = (|| -> Result<(), String> {
            for input in inputs {
                walker.scan_input(input)?;
            }
            for (index, (local, value)) in entries.iter().enumerate().rev() {
                if walker.contains(local.id())? {
                    needed[index] = true;
                    walker.scan_retained(local.ty())?;
                    if let Some(value) = value {
                        walker.scan_retained(value)?;
                    }
                }
            }
            Ok(())
        })();
        let visits = walker.work();
        drop(walker);
        self.spend_context_work(visits)?;
        scan?;
        let mut forest = Vec::new();
        let mut visible = Vec::new();
        for (index, (local, value)) in entries.iter().enumerate() {
            if needed[index] {
                forest.push(local.ty().clone());
                visible.push(index);
                if let Some(value) = value {
                    forest.push(value.clone());
                    visible.push(index);
                }
            }
        }
        let (materialized, stats) = scope.close_external_forest_with_limits(
            &forest,
            &locals,
            &visible,
            crate::term_scope::TermScopeLimits {
                max_visits: self.context_work_remaining()?,
                max_depth: 16_384,
            },
        );
        self.spend_context_work(stats.visits)?;
        let mut materialized = materialized.map_err(|error| error.to_string())?.into_iter();
        let mut context = clean_kernel::LocalContext::new();
        for (index, (local, value)) in entries.into_iter().enumerate() {
            if !needed[index] {
                continue;
            }
            let ty = materialized
                .next()
                .ok_or("charged normalization lost declaration type")?;
            if value.is_some() {
                let value = materialized
                    .next()
                    .ok_or("charged normalization lost defining value")?;
                context.push_let_with_id(
                    local.id(),
                    Name::from_string("component.definition"),
                    ty,
                    value,
                );
            } else {
                context.push_with_id(
                    local.id(),
                    Name::from_string("component.parameter"),
                    ty,
                    clean_kernel::BinderInfo::Default,
                );
            }
        }
        if materialized.next().is_some() {
            return Err("charged normalization has extra roots".into());
        }
        Ok((context, locals))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use clean_kernel::{Environment, Level, TypeChecker};
    fn n() -> Expr {
        Expr::const_str("Nat")
    }
    fn eq(a: Expr, b: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
            [n(), a, b],
        )
    }
    fn refl(a: Expr) -> Expr {
        Expr::apps(
            Expr::const_(
                Name::from_string("Eq.refl"),
                vec![Level::succ(Level::zero())],
            ),
            [n(), a],
        )
    }
    fn env() -> Environment {
        let mut e = Environment::new();
        e.init_nat().unwrap();
        e.init_eq().unwrap();
        e.init_true_false().unwrap();
        e
    }
    #[test]
    fn charged_context_preserves_actual_definitions_and_producer_only_opacity_through_replay() {
        let mut scope = LocalScope::new();
        let mut p = ProofComponents::new("charged.context", ProofLimits::default());
        p.set_base(&scope, vec![]).unwrap();
        let definition = p
            .bind_scoped_owned(&mut scope, &[], n(), Expr::nat_lit(5))
            .unwrap();
        let before = p.counts().3;
        let (context, _) = p
            .charged_normalization_context_with_opaque(
                &scope,
                &[],
                &[definition.reference.clone()],
                &[],
            )
            .unwrap();
        assert_eq!(
            TypeChecker::with_context(&env(), context).whnf(&definition.reference),
            Expr::nat_lit(5)
        );
        assert!(p.counts().3 > before);
        let (opaque, _) = p
            .charged_normalization_context_with_opaque(
                &scope,
                &[],
                &[definition.reference.clone()],
                &[definition.local],
            )
            .unwrap();
        assert_eq!(
            TypeChecker::with_context(&env(), opaque).whnf(&definition.reference),
            definition.reference
        );
        let claim = eq(Expr::nat_lit(5), Expr::nat_lit(5));
        let bundle = p
            .close_scoped(
                &scope,
                refl(Expr::nat_lit(5)),
                eq(definition.reference, Expr::nat_lit(5)),
                Default::default(),
            )
            .unwrap();
        let wire = bundle.encode_with_claim(&claim).unwrap();
        let (decoded, transported) = ScopedProofComponentBundle::decode_with_claim(&wire).unwrap();
        assert_eq!(claim, transported);
        decoded.replay(&env(), &claim, 2_000_000).unwrap();
    }
    #[test]
    fn charged_context_small_inventory_budget_refuses_before_publication() {
        let mut scope = LocalScope::new();
        let x = scope.try_local(n()).unwrap();
        let mut limits = ProofLimits::default();
        limits.operations = 20;
        let mut p = ProofComponents::new("charged.inventory", limits);
        p.set_base(&scope, vec![OwnedProofCapture::Parameter(x.clone())])
            .unwrap();
        let before = p.counts();
        assert!(
            p.charged_normalization_context_with_opaque(
                &scope,
                &[x.clone()],
                &[x.term().clone()],
                &[]
            )
            .is_err()
        );
        assert_eq!(p.counts(), before);
    }
    #[test]
    fn charged_context_foreign_and_parameter_probes_remain_paid_and_refused() {
        let mut scope = LocalScope::new();
        let mut other = LocalScope::new();
        let x = scope.try_local(n()).unwrap();
        let foreign = other.try_local(n()).unwrap();
        let mut p = ProofComponents::new("charged.foreign", ProofLimits::default());
        p.set_base(&scope, vec![OwnedProofCapture::Parameter(x.clone())])
            .unwrap();
        let before = p.counts().3;
        assert!(
            p.charged_normalization_context_with_opaque(
                &scope,
                &[x.clone()],
                &[x.term().clone()],
                &[foreign]
            )
            .is_err()
        );
        let paid = p.counts().3;
        assert!(paid > before);
        assert!(
            p.charged_normalization_context_with_opaque(
                &scope,
                &[x.clone()],
                &[x.term().clone()],
                &[x.clone()]
            )
            .is_err()
        );
        assert!(p.counts().3 > paid);
    }
    #[test]
    fn charged_context_failed_graph_scan_spends_the_original_pot_without_retry_refill() {
        let mut scope = LocalScope::new();
        let mut limits = ProofLimits::default();
        limits.operations = 500;
        let mut p = ProofComponents::new("charged.graph", limits);
        p.set_base(&scope, vec![]).unwrap();
        let original = p
            .bind_scoped_owned(&mut scope, &[], n(), Expr::nat_lit(0))
            .unwrap();
        let mut input = original.reference;
        for _ in 0..512 {
            input = Expr::app(Expr::const_str("Nat.succ"), input);
        }
        assert!(
            p.charged_normalization_context_with_opaque(&scope, &[], &[input.clone()], &[])
                .is_err()
        );
        let spent = p.counts().3;
        assert_eq!(spent, 500);
        assert!(
            p.charged_normalization_context_with_opaque(&scope, &[], &[input], &[])
                .is_err()
        );
        assert_eq!(p.counts().3, spent);
    }
    #[test]
    fn charged_context_never_erases_a_cold_invalid_original_value() {
        let mut scope = LocalScope::new();
        let mut p = ProofComponents::new("charged.invalid", ProofLimits::default());
        p.set_base(&scope, vec![]).unwrap();
        let invalid = p
            .bind_scoped_owned(&mut scope, &[], n(), Expr::const_str("True.intro"))
            .unwrap();
        p.charged_normalization_context_with_opaque(
            &scope,
            &[],
            &[invalid.reference],
            &[invalid.local],
        )
        .unwrap();
        let claim = Expr::const_str("True");
        let bundle = p
            .close_scoped(
                &scope,
                Expr::const_str("True.intro"),
                claim.clone(),
                Default::default(),
            )
            .unwrap();
        let wire = bundle.encode_with_claim(&claim).unwrap();
        let (decoded, transported) = ScopedProofComponentBundle::decode_with_claim(&wire).unwrap();
        assert_eq!(claim, transported);
        let error = decoded.replay(&env(), &claim, 2_000_000).err().unwrap();
        assert!(
            error.contains("TypeMismatch") && !error.contains("BudgetExhausted"),
            "{error}"
        );
    }
    #[test]
    fn charged_context_missing_original_globals_are_not_hidden_by_owned_definitions() {
        let mut scope = LocalScope::new();
        let input = scope.try_local(n()).unwrap();
        let mut p = ProofComponents::new("charged.explicit_inputs", ProofLimits::default());
        p.set_base(&scope, vec![OwnedProofCapture::Parameter(input.clone())])
            .unwrap();
        let internal = p
            .bind_scoped_owned(&mut scope, &[], n(), input.term().clone())
            .unwrap();
        let error = p
            .charged_normalization_context_with_opaque(
                &scope,
                &[],
                &[internal.reference.clone()],
                &[internal.local.clone()],
            )
            .err()
            .unwrap();
        assert!(
            error.contains("every explicitly admitted original global"),
            "{error}"
        );
        p.charged_normalization_context_with_opaque(
            &scope,
            &[input],
            &[internal.reference],
            &[internal.local],
        )
        .unwrap();
    }
    #[test]
    fn charged_materialization_retains_parameter_visibility_and_failed_work() {
        let mut scope = LocalScope::new();
        let alpha = scope
            .try_local(Expr::sort(Level::succ(Level::zero())))
            .unwrap();
        let x = scope.try_local(alpha.term().clone()).unwrap();
        let mut p = ProofComponents::new("charged.telescope", ProofLimits::default());
        p.set_base(&scope, vec![OwnedProofCapture::Parameter(alpha.clone())])
            .unwrap();
        let external = [alpha.clone(), x.clone()];
        let before = p.counts().3;
        assert!(
            p.charged_materialize_forest(&scope, &external, &[x.ty().clone()], &[0])
                .is_err()
        );
        assert!(p.counts().3 > before);
        let actual = p
            .charged_materialize_forest(
                &scope,
                &external,
                &[alpha.ty().clone(), x.ty().clone(), x.term().clone()],
                &[0, 1, 2],
            )
            .unwrap();
        assert_eq!(actual[1], *alpha.term());
        assert_eq!(actual[2], *x.term());
    }
    #[test]
    fn charged_independence_rejects_callback_capture_foreign_owner_and_loose_data() {
        let mut scope = LocalScope::new();
        let callback = scope.try_local(n()).unwrap();
        let data = scope.try_local(n()).unwrap();
        let mut parts = ProofComponents::new("paid.independence", Default::default());
        parts.set_base(&scope, vec![]).unwrap();
        parts
            .charged_independent_of(&scope, &[callback.clone()], data.term())
            .unwrap();
        let before = parts.context_work_remaining().unwrap();
        assert!(
            parts
                .charged_independent_of(&scope, &[callback.clone()], callback.term())
                .is_err()
        );
        assert!(parts.context_work_remaining().unwrap() < before);
        let before = parts.context_work_remaining().unwrap();
        assert!(
            parts
                .charged_independent_of(&scope, &[callback.clone()], &Expr::bvar(0))
                .is_err()
        );
        assert!(parts.context_work_remaining().unwrap() < before);
        let mut foreign_scope = LocalScope::new();
        let foreign = foreign_scope.try_local(n()).unwrap();
        let before = parts.context_work_remaining().unwrap();
        assert!(
            parts
                .charged_independent_of(&scope, &[foreign], data.term())
                .is_err()
        );
        assert!(parts.context_work_remaining().unwrap() < before);
    }
    #[test]
    fn charged_independence_failed_scan_consumes_the_same_pot_without_refill() {
        let mut scope = LocalScope::new();
        let callback = scope.try_local(n()).unwrap();
        let data = scope.try_local(n()).unwrap();
        let mut parts = ProofComponents::new("paid.independence.failure", Default::default());
        parts.set_base(&scope, vec![]).unwrap();
        let remaining = parts.context_work_remaining().unwrap();
        parts.spend_context_work(remaining - 32).unwrap();
        let mut term = data.term().clone();
        for _ in 0..64 {
            term = Expr::app(term, data.term().clone());
        }
        let error = parts
            .charged_independent_of(&scope, &[callback.clone()], &term)
            .unwrap_err();
        assert!(
            error.contains("normalization dependency visit limit"),
            "{error}"
        );
        assert_eq!(parts.context_work_remaining().unwrap(), 0);
        assert!(
            parts
                .charged_independent_of(&scope, &[callback], data.term())
                .is_err()
        );
        assert_eq!(parts.context_work_remaining().unwrap(), 0);
    }

    #[test]
    fn charged_independence_forest_reuses_shared_data_with_the_same_work_cap() {
        let mut scope = LocalScope::new();
        let callback = scope.try_local(n()).unwrap();
        let data = scope.try_local(n()).unwrap();
        let mut shared = data.term().clone();
        for _ in 0..40 {
            shared = Expr::app(Expr::const_str("Nat.succ"), shared);
        }
        let parent = Expr::app(Expr::const_str("Nat.succ"), shared.clone());
        let parts = || {
            let mut parts = ProofComponents::new(
                "independence.forest",
                ProofLimits {
                    operations: 128,
                    ..Default::default()
                },
            );
            parts.set_base(&scope, vec![]).unwrap();
            parts
        };
        let mut serial = parts();
        serial
            .charged_independent_of(&scope, &[callback.clone()], &shared)
            .unwrap();
        assert!(
            serial
                .charged_independent_of(&scope, &[callback.clone()], &parent)
                .is_err()
        );
        assert_eq!(serial.context_work_remaining().unwrap(), 0);
        let mut forest = parts();
        forest
            .charged_independent_forest_of(&scope, &[callback], &[&shared, &parent])
            .unwrap();
        assert!(forest.context_work_remaining().unwrap() > 0);
    }

    #[test]
    fn charged_independence_forest_keeps_later_capture_loose_owner_and_fresh_call_guards() {
        let mut scope = LocalScope::new();
        let callback = scope.try_local(n()).unwrap();
        let data = scope.try_local(n()).unwrap();
        let mut shared = data.term().clone();
        for _ in 0..40 {
            shared = Expr::app(Expr::const_str("Nat.succ"), shared);
        }
        let mut parts = ProofComponents::new("independence.forest.guards", Default::default());
        parts.set_base(&scope, vec![]).unwrap();
        parts
            .charged_independent_forest_of(&scope, &[callback.clone()], &[&shared, &shared])
            .unwrap();
        let before = parts.counts().3;
        let error = parts
            .charged_independent_forest_of(&scope, &[callback.clone()], &[&shared, callback.term()])
            .unwrap_err();
        assert!(error.contains("final CPS callbacks"), "{error}");
        assert!(
            parts.counts().3 - before >= 88,
            "another call must scan its own shared root again"
        );
        let loose = Expr::bvar(1_000_000);
        let before = parts.counts().3;
        assert!(
            parts
                .charged_independent_forest_of(&scope, &[callback], &[&shared, &loose])
                .unwrap_err()
                .contains("loose bound")
        );
        assert!(parts.counts().3 > before);
        let mut foreign = LocalScope::new();
        let foreign_callback = foreign.try_local(n()).unwrap();
        let before = parts.counts().3;
        assert!(
            parts
                .charged_independent_forest_of(&scope, &[foreign_callback], &[&shared])
                .unwrap_err()
                .contains("another owner")
        );
        assert!(parts.counts().3 > before);
    }
}

#[cfg(test)]
mod caller_work_limit_tests {
    use super::*;
    use clean_kernel::Level;
    #[test]
    fn caller_materialization_limit_prepays_setup_and_charges_every_failed_prefix() {
        let mut scope = LocalScope::new();
        let local = scope.try_local(Expr::const_str("Nat")).unwrap();
        let mut root = local.term().clone();
        for _ in 0..24 {
            root = Expr::arrow(Expr::const_str("Nat"), root);
        }
        let mut successful = false;
        let mut charged_failure = false;
        for cap in 0..=160 {
            let mut parts = ProofComponents::new("caller.closure.cutoff", Default::default());
            parts.set_base(&scope, vec![]).unwrap();
            let result = parts.charged_materialize_forest_with_limit(
                &scope,
                &[local.clone()],
                &[root.clone()],
                &[1],
                cap,
            );
            assert!(
                parts.counts().3 <= cap,
                "cap={cap}, counts={:?}",
                parts.counts()
            );
            assert_eq!(parts.counts().0, 0);
            match result {
                Ok(actual) => {
                    successful = true;
                    assert_eq!(actual, vec![root.clone()]);
                }
                Err(_) => {
                    charged_failure |= parts.counts().3 > 6;
                }
            }
        }
        assert!(successful && charged_failure);
    }
    #[test]
    fn caller_materialization_limit_never_overrides_combined_component_budget_or_publishes_a_prefix()
     {
        let mut scope = LocalScope::new();
        let known = scope.try_local(Expr::sort(Level::zero())).unwrap();
        let unknown = scope.try_local(Expr::sort(Level::zero())).unwrap();
        let mut parts = ProofComponents::new(
            "caller.closure.component",
            crate::proof_assembly::ProofLimits {
                operations: 24,
                ..Default::default()
            },
        );
        parts.set_base(&scope, vec![]).unwrap();
        parts.spend_context_work(1).unwrap();
        let result = parts.charged_materialize_forest_with_limit(
            &scope,
            &[known.clone()],
            &[known.term().clone(), unknown.term().clone()],
            &[1, 1],
            usize::MAX,
        );
        assert!(result.is_err());
        let after = parts.counts().3;
        assert!(after > 1 && after <= 24);
        assert_eq!(parts.counts().0, 0);
        let retry = parts.charged_materialize_forest_with_limit(
            &scope,
            &[known.clone()],
            &[known.term().clone()],
            &[1],
            usize::MAX,
        );
        assert!(parts.counts().3 >= after && parts.counts().3 <= 24);
        if let Ok(roots) = retry {
            assert_eq!(roots, vec![known.term().clone()]);
        }
    }
}
