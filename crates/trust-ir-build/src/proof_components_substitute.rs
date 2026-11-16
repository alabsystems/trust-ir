// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//! Candidate-only simultaneous substitution preserving actual named binders.
use super::*;
use clean_kernel::expr::{ExprFolderOpt, ExprKind};
#[derive(Clone)]
struct Key(Expr);
impl PartialEq for Key {
    fn eq(&self, other: &Self) -> bool {
        same_graph(&self.0, &other.0)
    }
}
impl Eq for Key {}
impl std::hash::Hash for Key {
    fn hash<H: std::hash::Hasher>(&self, hash: &mut H) {
        crate::proof_assembly::normalize::hash_graph(&self.0, hash);
    }
}
struct Substitute<'a> {
    scope: &'a LocalScope,
    external: &'a HashSet<FVarId>,
    replacements: &'a HashMap<FVarId, Expr>,
    memo: HashMap<Key, Completed>,
    work: usize,
    limit: usize,
    depth: u32,
    height: u32,
    error: Option<String>,
    materialized: bool,
    ordinary: Option<crate::scoped_local::PreparedOrdinaryView<'a>>,
    reduce_applications: bool,
}
struct Completed {
    output: Expr,
    height: u32,
    replacement_head: bool,
}
struct SubstitutionStack<'a, 'b>(&'a mut Substitute<'b>);
impl ExprFolderOpt for SubstitutionStack<'_, '_> {
    fn fold_expr_opt_inner(&mut self, expression: &Expr) -> Option<Expr> {
        if self.0.reduce_applications
            && let ExprKind::App(function, argument) = expression.kind()
        {
            return self.0.fold_application(function, argument);
        }
        self.0.fold_expr_opt_inner(expression)
    }
}
impl Substitute<'_> {
    fn fold_application(
        &mut self,
        function: &std::sync::Arc<Expr>,
        argument: &std::sync::Arc<Expr>,
    ) -> Option<Expr> {
        let changed_function = self.fold_expr_arc_opt(function);
        let changed_argument = self.fold_expr_arc_opt(argument);
        if self.error.is_some() {
            return None;
        }
        let from_replacement = self
            .memo
            .get(&Key(function.as_ref().clone()))
            .is_some_and(|entry| entry.replacement_head);
        let next_function = changed_function.as_ref().unwrap_or(function);
        let next_argument = changed_argument.as_ref().unwrap_or(argument);
        if from_replacement && let ExprKind::Lam(_, _, body) = next_function.kind() {
            match super::bounded_instantiate::apply_materialized_closed_argument(
                self.scope,
                body,
                next_argument,
                &mut self.work,
                self.limit,
            ) {
                Ok(reduced) => return Some(reduced),
                Err(error) => {
                    self.error = Some(error);
                    return None;
                }
            }
        }
        (changed_function.is_some() || changed_argument.is_some())
            .then(|| Expr::app_arc(next_function.clone(), next_argument.clone()))
    }
}
impl ExprFolderOpt for Substitute<'_> {
    fn fold_expr_opt(&mut self, expression: &Expr) -> Option<Expr> {
        if self.error.is_some() {
            return None;
        }
        if self.work >= self.limit {
            self.error = Some("aggregate scoped substitution work limit".into());
            return None;
        }
        self.work += 1;
        if self.depth >= 16_384 {
            self.error = Some("scoped substitution depth limit".into());
            return None;
        }
        // This private mode consumes only the returned graph of this SAME
        // call's successful complete materialization. That walk checked every
        // deferred name, external read and complete input height before pruning.
        if self.materialized && !expression.has_fvar_quick() {
            return None;
        }
        if let Some(ordinary) = &self.ordinary
            && !expression.has_loose_bvars()
            && matches!(
                expression.kind(),
                ExprKind::App(..) | ExprKind::Lam(..) | ExprKind::Pi(..) | ExprKind::Let(..)
            )
        {
            let Some(next) = self.work.checked_add(2).filter(|work| *work <= self.limit) else {
                self.error = Some("aggregate scoped substitution work limit".into());
                return None;
            };
            self.work = next; // graph probe/pin before lookup
            if let Some(envelope) = ordinary.envelope(expression) {
                let mut absent = true;
                for source in self.replacements.keys() {
                    if self.work >= self.limit {
                        self.error = Some("aggregate scoped substitution work limit".into());
                        return None;
                    }
                    self.work += 1;
                    if envelope.may_contain(*source) {
                        absent = false;
                        break;
                    }
                }
                if absent {
                    return None;
                }
            }
        }
        if self
            .scope
            .named_binder_id(expression)
            .is_some_and(|id| self.external.contains(&id))
        {
            self.error =
                Some("substitution external handle shadows an internal named binder".into());
            return None;
        }
        let key = Key(expression.clone());
        if let Some(completed) = self.memo.get(&key) {
            if self
                .depth
                .checked_add(completed.height)
                .is_none_or(|depth| depth > 16_384)
            {
                self.error = Some("scoped substitution cached depth limit".into());
                return None;
            }
            self.height = self.height.max(completed.height);
            return (!same_graph(&completed.output, expression)).then(|| completed.output.clone());
        }
        let enclosing = std::mem::take(&mut self.height);
        self.depth += 1;
        let changed = SubstitutionStack(self).fold_expr_opt(expression);
        self.depth -= 1;
        let height = self.height + 1;
        self.height = enclosing.max(height);
        if self.error.is_some() {
            return None;
        }
        let output = changed.map(|output| self.scope.preserve_candidate_binder(expression, output));
        let replacement_head = self.reduce_applications
            && match expression.kind() {
                ExprKind::FVar(id) => self.replacements.contains_key(id),
                ExprKind::App(function, _) => self
                    .memo
                    .get(&Key(function.as_ref().clone()))
                    .is_some_and(|entry| entry.replacement_head),
                _ => false,
            };
        self.memo.insert(
            key,
            Completed {
                output: output.clone().unwrap_or_else(|| expression.clone()),
                height,
                replacement_head,
            },
        );
        output
    }
    fn fold_fvar_opt(&mut self, id: FVarId) -> Option<Expr> {
        self.replacements
            .get(&id)
            .filter(|term| !matches!(term.kind(), ExprKind::FVar(other) if *other == id))
            .cloned()
    }
}
impl ProofComponents {
    /// Substitute actual external handles simultaneously in candidate terms.
    /// Replacement terms are strictly closed relative to this owner's external
    /// inventory first; their internal BVars therefore cannot capture a root's
    /// binders. Named root binders retain their original owner metadata.
    /// This does not certify roots or drop any original declaration: complete
    /// original replay and independently frozen claim checks remain mandatory.
    pub fn substitute_scoped_terms(
        &mut self,
        scope: &LocalScope,
        external: &[ScopedLocal],
        bindings: &[(ScopedLocal, Expr)],
        roots: &[Expr],
    ) -> Result<Vec<Expr>, String> {
        self.substitute_scoped_terms_impl(scope, external, bindings, roots, false)
    }

    /// Substitute actual handles and contract lambda applications introduced
    /// at those handles' application sites. Applied arguments must be closed
    /// in ordinary BVars; other beta redexes and definitions are left alone.
    /// Inputs and outputs are completely materialized inside this same call,
    /// and every walk/contraction shares this owner's existing work ledger.
    /// This is candidate construction only: original declarations and complete
    /// frozen-claim kernel replay remain mandatory.
    pub fn substitute_scoped_applications(
        &mut self,
        scope: &LocalScope,
        external: &[ScopedLocal],
        bindings: &[(ScopedLocal, Expr)],
        roots: &[Expr],
    ) -> Result<Vec<Expr>, String> {
        self.substitute_scoped_terms_impl(scope, external, bindings, roots, true)
    }

    fn substitute_scoped_terms_impl(
        &mut self,
        scope: &LocalScope,
        external: &[ScopedLocal],
        bindings: &[(ScopedLocal, Expr)],
        roots: &[Expr],
        reduce_applications: bool,
    ) -> Result<Vec<Expr>, String> {
        if !self
            .owner
            .as_ref()
            .is_some_and(|owner| owner.matches(&scope.memo_owner()))
        {
            return Err("scoped substitution has another owner".into());
        }
        let limit = self
            .limits
            .operations
            .checked_sub(self.analysis_words)
            .ok_or("aggregate scoped substitution work limit")?;
        if self.analysis_visits >= limit {
            return Err("aggregate scoped substitution work limit".into());
        }
        if external.len() > self.limits.captures.saturating_add(self.limits.contexts)
            || bindings.len() > external.len()
            || roots.len() > self.limits.operations
        {
            return Err("scoped substitution input inventory limit".into());
        }
        let mut ids = HashSet::new();
        for local in external {
            if !scope.owns(local) || !ids.insert(local.id()) {
                return Err("foreign or duplicate substitution external handle".into());
            }
        }
        let mut sources = HashSet::new();
        for (source, _) in bindings {
            if !scope.owns(source) || !ids.contains(&source.id()) || !sources.insert(source.id()) {
                return Err("foreign, absent or duplicate substitution source".into());
            }
        }
        // External-forest closing intentionally supports ordinary ambient
        // BVars. A substitution target must instead be closed in BVars before
        // crossing root binders, so reject these explicitly at cached O(1).
        if bindings.iter().any(|(_, term)| term.has_loose_bvars()) {
            return Err("scoped substitution replacement has a loose bound variable".into());
        }
        let replacement_roots = bindings
            .iter()
            .map(|(_, term)| term.clone())
            .collect::<Vec<_>>();
        let (replacement_terms, stats) = scope.close_external_forest_fully_with_limits(
            &replacement_roots,
            external,
            &vec![external.len(); replacement_roots.len()],
            crate::term_scope::TermScopeLimits {
                max_visits: limit.saturating_sub(self.analysis_visits),
                max_depth: 16_384,
            },
        );
        self.analysis_visits = self
            .analysis_visits
            .checked_add(stats.visits)
            .ok_or("substitution materialization work overflow")?;
        if self.analysis_visits > limit {
            return Err("aggregate scoped substitution materialization work limit".into());
        }
        let replacement_terms = replacement_terms.map_err(|error| error.to_string())?;
        if replacement_terms.iter().any(Expr::has_loose_bvars) {
            return Err("materialized substitution replacement has a loose bound variable".into());
        }
        let replacements = bindings
            .iter()
            .zip(replacement_terms)
            .map(|((local, _), term)| (local.id(), term))
            .collect();
        if !reduce_applications {
            return substitute_prevalidated_scoped_terms(
                scope,
                &ids,
                &replacements,
                roots,
                &mut self.analysis_visits,
                limit,
            );
        }
        let roots = self.materialize_scoped_terms_fully(scope, external, roots)?;
        let limit = self
            .limits
            .operations
            .checked_sub(self.analysis_words)
            .ok_or("aggregate scoped substitution work limit")?;
        let output = substitute_prevalidated_scoped_terms_impl(
            scope,
            &ids,
            &replacements,
            &roots,
            &mut self.analysis_visits,
            limit,
            true,
            None,
            true,
        )?;
        // Revalidate the complete result's owner, visibility and depth after
        // substitution can have embedded an argument under body binders.
        self.materialize_scoped_terms_fully(scope, external, &output)
    }

    /// Strict named candidate substitution with a fresh substitution memo.
    #[cfg(test)]
    pub(crate) fn substitute_in_external_context(
        &mut self,
        scope: &LocalScope,
        context: &ExternalContext,
        bindings: &[(ScopedLocal, Expr)],
        roots: &[Expr],
    ) -> Result<Vec<Expr>, String> {
        let result =
            self.substitute_in_external_context_impl(scope, context, bindings, roots, false);
        if result.is_err() {
            self.poison_external_materialization(scope, context);
        }
        result
    }
    /// Fully close the actual inputs in this call, then substitute only their
    /// returned canonical graphs. No materialized flag/receipt is accepted.
    pub(crate) fn substitute_materialized_in_external_context(
        &mut self,
        scope: &LocalScope,
        context: &ExternalContext,
        bindings: &[(ScopedLocal, Expr)],
        roots: &[Expr],
    ) -> Result<Vec<Expr>, String> {
        let result =
            self.substitute_in_external_context_impl(scope, context, bindings, roots, true);
        if result.is_err() {
            self.poison_external_materialization(scope, context);
        }
        result
    }
    fn substitute_in_external_context_impl(
        &mut self,
        scope: &LocalScope,
        context: &ExternalContext,
        bindings: &[(ScopedLocal, Expr)],
        roots: &[Expr],
        materialize_roots: bool,
    ) -> Result<Vec<Expr>, String> {
        let ids = self.external_context_ids(scope, context)?;
        if bindings.len() > ids.len() || roots.len() > self.limits.operations {
            return Err("prepared substitution inventory limit".into());
        }
        self.spend_context_work(
            bindings
                .len()
                .checked_mul(4)
                .and_then(|n| n.checked_add(roots.len().checked_mul(2)?))
                .and_then(|n| n.checked_add(1))
                .ok_or("prepared substitution inventory overflow")?,
        )?;
        let mut sources = HashSet::new();
        for (source, replacement) in bindings {
            if !scope.owns(source) || !ids.contains(&source.id()) || !sources.insert(source.id()) {
                return Err("foreign, absent or duplicate substitution source".into());
            }
            if replacement.has_loose_bvars() {
                return Err("scoped substitution replacement has a loose bound variable".into());
            }
        }
        let replacement_roots = bindings
            .iter()
            .map(|(_, value)| value.clone())
            .collect::<Vec<_>>();
        let terms =
            self.charged_materialize_external_context_fully(scope, context, &replacement_roots)?;
        if terms.iter().any(Expr::has_loose_bvars) {
            return Err("materialized substitution replacement has a loose bound variable".into());
        }
        let replacements = bindings
            .iter()
            .zip(terms)
            .map(|((source, _), term)| (source.id(), term))
            .collect();
        let closed_roots;
        let roots = if materialize_roots {
            closed_roots =
                self.charged_materialize_external_context_fully(scope, context, roots)?;
            closed_roots.as_slice()
        } else {
            roots
        };
        let limit = self
            .limits
            .operations
            .checked_sub(self.analysis_words)
            .ok_or("aggregate scoped substitution work limit")?;
        let ordinary = if materialize_roots {
            self.external_ordinary_view(scope, context)?
        } else {
            None
        };
        substitute_prevalidated_scoped_terms_impl(
            scope,
            ids,
            &replacements,
            roots,
            &mut self.analysis_visits,
            limit,
            materialize_roots,
            ordinary,
            false,
        )
    }
}

/// Internal folding stage after admission/materialization. Alias construction
/// validates its complete original forest once and creates only exact same-owner
/// bare-FVar replacements itself. It must not repeatedly prepare growing public
/// substitution inventories. Every call uses a FRESH memo: adding a replacement
/// never reuses a cache entry from an earlier mapping/footprint.
pub(super) fn substitute_prevalidated_scoped_terms(
    scope: &LocalScope,
    external: &HashSet<FVarId>,
    replacements: &HashMap<FVarId, Expr>,
    roots: &[Expr],
    work: &mut usize,
    limit: usize,
) -> Result<Vec<Expr>, String> {
    substitute_prevalidated_scoped_terms_impl(
        scope,
        external,
        replacements,
        roots,
        work,
        limit,
        false,
        None,
        false,
    )
}
fn substitute_prevalidated_scoped_terms_impl(
    scope: &LocalScope,
    external: &HashSet<FVarId>,
    replacements: &HashMap<FVarId, Expr>,
    roots: &[Expr],
    work: &mut usize,
    limit: usize,
    materialized: bool,
    ordinary: Option<crate::scoped_local::PreparedOrdinaryView<'_>>,
    reduce_applications: bool,
) -> Result<Vec<Expr>, String> {
    let mut walker = Substitute {
        scope,
        external,
        replacements,
        memo: HashMap::new(),
        work: *work,
        limit,
        depth: 0,
        height: 0,
        error: None,
        materialized,
        ordinary,
        reduce_applications,
    };
    let mut output = Vec::with_capacity(roots.len());
    for root in roots {
        walker.height = 0;
        output.push(walker.fold_expr_opt(root).unwrap_or_else(|| root.clone()));
    }
    *work = walker.work;
    match walker.error {
        Some(error) => Err(error),
        None => Ok(output),
    }
}

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
    fn paired_materialized_redirection_shares_work_without_cross_root_arguments() {
        let mut scope = LocalScope::new();
        let old = scope.try_local(n()).unwrap();
        let replacement = scope.try_local(n()).unwrap();
        let mut shared = old.term().clone();
        for _ in 0..64 {
            shared = Expr::app(Expr::const_str("Nat.succ"), shared);
        }
        let roots = [
            Expr::apps(
                Expr::const_str("Nat.add"),
                [shared.clone(), Expr::nat_lit(3)],
            ),
            Expr::apps(Expr::const_str("Nat.add"), [shared, Expr::nat_lit(7)]),
        ];
        let mut expected_shared = replacement.term().clone();
        for _ in 0..64 {
            expected_shared = Expr::app(Expr::const_str("Nat.succ"), expected_shared);
        }
        let expected = [
            Expr::apps(
                Expr::const_str("Nat.add"),
                [expected_shared.clone(), Expr::nat_lit(3)],
            ),
            Expr::apps(
                Expr::const_str("Nat.add"),
                [expected_shared, Expr::nat_lit(7)],
            ),
        ];
        let run = |together: bool| {
            let mut parts = ProofComponents::new("paired.redirect.work", Default::default());
            parts.set_base(&scope, vec![]).unwrap();
            let context = parts
                .charged_external_context(&scope, &[old.clone(), replacement.clone()])
                .unwrap();
            let before = parts.counts().3;
            let bindings = [(old.clone(), replacement.term().clone())];
            let output = if together {
                parts
                    .substitute_materialized_in_external_context(
                        &scope, &context, &bindings, &roots,
                    )
                    .unwrap()
            } else {
                roots
                    .iter()
                    .map(|root| {
                        parts
                            .substitute_materialized_in_external_context(
                                &scope,
                                &context,
                                &bindings,
                                std::slice::from_ref(root),
                            )
                            .unwrap()
                            .remove(0)
                    })
                    .collect()
            };
            assert_eq!(output, expected);
            parts.counts().3 - before
        };
        assert!(
            run(true) < run(false),
            "one complete forest must avoid the repeated shared walk"
        );
    }

    #[test]
    fn paired_materialized_redirection_prepays_failure_and_poisons_complete_forest() {
        let mut scope = LocalScope::new();
        let old = scope.try_local(n()).unwrap();
        let replacement = scope.try_local(n()).unwrap();
        let mut root = old.term().clone();
        for _ in 0..16 {
            root = Expr::app(Expr::const_str("Nat.succ"), root);
        }
        let mut reached_success = false;
        let mut reached_failure = false;
        for remaining in 0..=512 {
            let mut parts = ProofComponents::new("paired.redirect.cutoff", Default::default());
            parts.set_base(&scope, vec![]).unwrap();
            let mut context = parts
                .charged_external_context(&scope, &[old.clone(), replacement.clone()])
                .unwrap();
            parts
                .charged_enable_external_materialization_reuse(&scope, &mut context)
                .unwrap();
            let available = parts.context_work_remaining().unwrap();
            parts.spend_context_work(available - remaining).unwrap();
            let before = parts.counts().3;
            let result = parts.substitute_materialized_in_external_context(
                &scope,
                &context,
                &[(old.clone(), replacement.term().clone())],
                &[root.clone(), root.clone()],
            );
            assert!(parts.counts().3 >= before && parts.counts().3 <= parts.limits.operations);
            if result.is_err() {
                reached_failure = true;
                assert!(
                    parts
                        .charged_materialize_external_context_fully(
                            &scope,
                            &context,
                            &[Expr::nat_lit(0)],
                        )
                        .is_err(),
                    "a failed paired forest must poison its prepared inventory"
                );
            } else {
                reached_success = true;
            }
        }
        assert!(reached_success && reached_failure);
    }

    #[test]
    fn prepared_substitution_refuses_foreign_budget_absent_sources_and_materialized_loose_targets()
    {
        let mut scope = LocalScope::new();
        let x = scope.try_local(n()).unwrap();
        let y = scope.try_local(n()).unwrap();
        let binder = scope.try_local(n()).unwrap();
        let mut parts = ProofComponents::new("prepared.substitution.guards", Default::default());
        parts.set_base(&scope, vec![]).unwrap();
        let context = parts
            .charged_external_context(&scope, std::slice::from_ref(&x))
            .unwrap();
        let mut other = ProofComponents::new("prepared.substitution.other", Default::default());
        other.set_base(&scope, vec![]).unwrap();
        assert!(
            other
                .substitute_in_external_context(&scope, &context, &[], &[n()])
                .unwrap_err()
                .contains("another component")
        );
        assert!(
            parts
                .substitute_in_external_context(
                    &scope,
                    &context,
                    &[(y.clone(), x.term().clone())],
                    &[y.term().clone()]
                )
                .is_err()
        );
        assert!(
            parts
                .substitute_in_external_context(
                    &scope,
                    &context,
                    &[(x.clone(), y.term().clone())],
                    &[x.term().clone()]
                )
                .is_err()
        );
        let ambient = binder.lam(Expr::bvar(0));
        assert!(
            parts
                .substitute_in_external_context(
                    &scope,
                    &context,
                    &[(x.clone(), ambient.clone())],
                    &[x.term().clone()]
                )
                .unwrap_err()
                .contains("loose bound")
        );
        // The public raw-inventory route must reject the same capture too.
        assert!(
            parts
                .substitute_scoped_terms(
                    &scope,
                    std::slice::from_ref(&x),
                    &[(x.clone(), ambient)],
                    &[x.term().clone()]
                )
                .unwrap_err()
                .contains("loose bound")
        );
    }

    #[test]
    fn candidate_substitution_memo_keeps_full_input_height_at_a_deeper_parent() {
        let scope = LocalScope::new();
        let mut parts = ProofComponents::new("substitute.depth", Default::default());
        parts.set_base(&scope, vec![]).unwrap();
        let context = parts.charged_external_context(&scope, &[]).unwrap();
        let mut shared = Expr::nat_lit(0);
        for _ in 0..16_383 {
            shared = Expr::app(Expr::const_str("Nat.succ"), shared);
        }
        let deeper = Expr::app(Expr::const_str("Nat.succ"), shared.clone());
        let before = parts.counts().3;
        let error = parts
            .substitute_in_external_context(&scope, &context, &[], &[shared, deeper])
            .unwrap_err();
        assert!(error.contains("cached depth limit"), "{error}");
        assert!(parts.counts().3 > before);
    }
    #[test]
    fn owned_substitution_keeps_capture_word_work_in_the_same_aggregate_limit() {
        let mut scope = LocalScope::new();
        let x = scope.try_local(n()).unwrap();
        let y = scope.try_local(n()).unwrap();
        let mut parts = ProofComponents::new("substitute.aggregate", ProofLimits::default());
        parts.set_base(&scope, vec![]).unwrap();
        parts
            .bind_scoped_owned(
                &mut scope,
                &[
                    OwnedProofCapture::Parameter(x.clone()),
                    OwnedProofCapture::Parameter(y.clone()),
                ],
                n(),
                Expr::apps(
                    Expr::const_str("Nat.add"),
                    [x.term().clone(), y.term().clone()],
                ),
            )
            .unwrap();
        assert!(
            parts.analysis_words > 0,
            "actual capture analysis must spend words"
        );
        let remaining = parts.context_work_remaining().unwrap();
        parts.spend_context_work(remaining - 32).unwrap();
        let mut root = Expr::nat_lit(0);
        for _ in 0..64 {
            root = Expr::app(Expr::const_str("Nat.succ"), root);
        }
        let error = parts
            .substitute_scoped_terms(&scope, &[x.clone(), y.clone()], &[], &[root])
            .unwrap_err();
        assert!(
            error.contains("aggregate scoped substitution work limit"),
            "{error}"
        );
        assert_eq!(parts.counts().3, parts.limits.operations);
        assert_eq!(parts.context_work_remaining().unwrap(), 0);
        assert!(
            parts
                .substitute_scoped_terms(&scope, &[x, y], &[], &[Expr::nat_lit(0)])
                .is_err()
        );
        assert_eq!(parts.context_work_remaining().unwrap(), 0);
    }
    #[test]
    fn simultaneous_owned_substitution_preserves_named_goal_binders_and_original_replay() {
        let mut scope = LocalScope::new();
        let f = scope.try_local(Expr::arrow(n(), n())).unwrap();
        let g = scope.try_local(Expr::arrow(n(), n())).unwrap();
        let x = scope.try_local(n()).unwrap();
        let original = x.lam(Expr::app(f.term().clone(), x.term().clone()));
        let mut parts = ProofComponents::new("substitute.binders", ProofLimits::default());
        parts
            .set_base(
                &scope,
                vec![
                    OwnedProofCapture::Parameter(f.clone()),
                    OwnedProofCapture::Parameter(g.clone()),
                ],
            )
            .unwrap();
        let redirected = parts
            .substitute_scoped_terms(
                &scope,
                &[f.clone(), g.clone()],
                &[(f.clone(), g.term().clone())],
                &[original],
            )
            .unwrap()
            .remove(0);
        let actual = Expr::app(g.term().clone(), Expr::nat_lit(0));
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
    fn prepared_owned_substitution_preserves_named_goal_binders_and_original_replay() {
        let mut scope = LocalScope::new();
        let f = scope.try_local(Expr::arrow(n(), n())).unwrap();
        let g = scope.try_local(Expr::arrow(n(), n())).unwrap();
        let x = scope.try_local(n()).unwrap();
        let original = x.lam(Expr::app(f.term().clone(), x.term().clone()));
        let mut parts = ProofComponents::new("substitute.binders", ProofLimits::default());
        parts
            .set_base(
                &scope,
                vec![
                    OwnedProofCapture::Parameter(f.clone()),
                    OwnedProofCapture::Parameter(g.clone()),
                ],
            )
            .unwrap();
        let context = parts
            .charged_external_context(&scope, &[f.clone(), g.clone()])
            .unwrap();
        let redirected = parts
            .substitute_in_external_context(
                &scope,
                &context,
                &[(f.clone(), g.term().clone())],
                &[original],
            )
            .unwrap()
            .remove(0);
        let actual = Expr::app(g.term().clone(), Expr::nat_lit(0));
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
    fn owned_substitution_is_simultaneous_and_updates_dependent_named_types() {
        let mut scope = LocalScope::new();
        let alpha = scope
            .try_local(Expr::sort(Level::succ(Level::zero())))
            .unwrap();
        let beta = scope
            .try_local(Expr::sort(Level::succ(Level::zero())))
            .unwrap();
        let x = scope.try_local(alpha.term().clone()).unwrap();
        let y = scope.try_local(beta.term().clone()).unwrap();
        let mut parts = ProofComponents::new("substitute.dependent", ProofLimits::default());
        parts
            .set_base(
                &scope,
                vec![
                    OwnedProofCapture::Parameter(alpha.clone()),
                    OwnedProofCapture::Parameter(beta.clone()),
                ],
            )
            .unwrap();
        let original = x.lam(x.term().clone());
        let candidate = parts
            .substitute_scoped_terms(
                &scope,
                &[alpha.clone(), beta.clone()],
                &[
                    (alpha.clone(), beta.term().clone()),
                    (beta.clone(), alpha.term().clone()),
                ],
                &[original, alpha.term().clone(), beta.term().clone()],
            )
            .unwrap();
        assert_eq!(candidate[1], *beta.term());
        assert_eq!(candidate[2], *alpha.term());
        let function_type = Expr::arrow(beta.term().clone(), beta.term().clone());
        let expected = y.lam(y.term().clone());
        let equality = |left: Expr, right: Expr| {
            Expr::apps(
                Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
                [function_type.clone(), left, right],
            )
        };
        let goal = equality(candidate[0].clone(), expected.clone());
        let frozen = equality(expected.clone(), expected.clone());
        let claim = scope.close(&alpha.pi(beta.pi(frozen))).unwrap();
        let root = Expr::apps(
            Expr::const_(
                Name::from_string("Eq.refl"),
                vec![Level::succ(Level::zero())],
            ),
            [function_type, expected],
        );
        let bundle = parts
            .close_scoped(&scope, alpha.lam(beta.lam(root)), goal, Default::default())
            .unwrap();
        let bytes = bundle.encode_with_claim(&claim).unwrap();
        let (decoded, transported) = ScopedProofComponentBundle::decode_with_claim(&bytes).unwrap();
        assert_eq!(claim, transported);
        let mut env = Environment::new();
        env.init_eq().unwrap();
        decoded.replay(&env, &claim, 2_000_000).unwrap();
    }

    #[test]
    fn owned_substitution_rejects_capture_foreign_sources_loose_targets_and_duplicate_inventory() {
        let mut scope = LocalScope::new();
        let f = scope.try_local(n()).unwrap();
        let x = scope.try_local(n()).unwrap();
        let mut foreign = LocalScope::new();
        let other = foreign.try_local(n()).unwrap();
        let mut parts = ProofComponents::new("substitute.refusals", ProofLimits::default());
        parts
            .set_base(&scope, vec![OwnedProofCapture::Parameter(f.clone())])
            .unwrap();
        let root = x.lam(f.term().clone());
        assert!(
            parts
                .substitute_scoped_terms(
                    &scope,
                    &[f.clone(), x.clone()],
                    &[(f.clone(), x.term().clone())],
                    &[root]
                )
                .is_err()
        );
        assert!(
            parts
                .substitute_scoped_terms(
                    &scope,
                    std::slice::from_ref(&f),
                    &[(other, f.term().clone())],
                    &[f.term().clone()]
                )
                .is_err()
        );
        assert!(
            parts
                .substitute_scoped_terms(
                    &scope,
                    std::slice::from_ref(&f),
                    &[(f.clone(), Expr::bvar(0))],
                    &[f.term().clone()]
                )
                .is_err()
        );
        assert!(
            parts
                .substitute_scoped_terms(&scope, &[f.clone(), f.clone()], &[], &[f.term().clone()])
                .is_err()
        );
        assert!(
            parts
                .substitute_scoped_terms(
                    &scope,
                    std::slice::from_ref(&f),
                    &[(f.clone(), f.term().clone()), (f.clone(), f.term().clone())],
                    &[f.term().clone()]
                )
                .is_err()
        );
    }
    #[test]
    fn owned_substitution_never_removes_cold_invalid_originals_or_refunds_work() {
        let mut scope = LocalScope::new();
        let mut parts = ProofComponents::new("substitute.originals", ProofLimits::default());
        parts.set_base(&scope, vec![]).unwrap();
        let _invalid = parts
            .bind_scoped(
                &mut scope,
                &[],
                eq(Expr::nat_lit(0), Expr::nat_lit(1)),
                refl(Expr::nat_lit(0)),
            )
            .unwrap();
        let root = parts
            .substitute_scoped_terms(&scope, &[], &[], &[Expr::const_str("True.intro")])
            .unwrap()
            .remove(0);
        let bundle = parts
            .close_scoped(&scope, root, Expr::const_str("True"), Default::default())
            .unwrap();
        let mut env = Environment::new();
        env.init_nat().unwrap();
        env.init_eq().unwrap();
        env.init_true_false().unwrap();
        let error = bundle
            .replay(&env, &Expr::const_str("True"), 2_000_000)
            .err()
            .unwrap();
        assert!(
            error.contains("TypeMismatch") && !error.contains("BudgetExhausted"),
            "{error}"
        );
        let mut parts = ProofComponents::new(
            "substitute.work",
            ProofLimits {
                operations: 16,
                ..Default::default()
            },
        );
        parts.set_base(&scope, vec![]).unwrap();
        for _ in 0..16 {
            parts
                .substitute_scoped_terms(&scope, &[], &[], &[Expr::nat_lit(0)])
                .unwrap();
        }
        let before = parts.analysis_visits;
        assert!(
            parts
                .substitute_scoped_terms(&scope, &[], &[], &[Expr::nat_lit(0)])
                .is_err()
        );
        assert_eq!(before, parts.analysis_visits);
    }
}
