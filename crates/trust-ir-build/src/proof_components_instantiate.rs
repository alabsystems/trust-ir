// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//! Reinstantiate candidate support in the same owner, retaining the complete
//! original artifact. New definitions are still untrusted until full replay.
use super::*;
use clean_kernel::expr::{ExprFolderOpt, ExprKind};

pub struct InstantiatedScopedCandidate {
    pub type_: Expr,
    pub value: Expr,
}

#[derive(Clone)]
struct RedirectKey(Expr);
impl PartialEq for RedirectKey {
    fn eq(&self, other: &Self) -> bool {
        same_graph(&self.0, &other.0)
    }
}
impl Eq for RedirectKey {}
impl std::hash::Hash for RedirectKey {
    fn hash<H: std::hash::Hasher>(&self, hash: &mut H) {
        crate::proof_assembly::normalize::hash_graph(&self.0, hash);
    }
}

struct Redirect {
    replacements: HashMap<FVarId, Expr>,
    definitions: HashSet<FVarId>,
    memo: HashMap<RedirectKey, Expr>,
    work: usize,
    limit: usize,
    depth: u32,
    error: Option<&'static str>,
}
impl Redirect {
    fn apply(&mut self, expression: &Expr) -> Result<Expr, String> {
        let output = self
            .fold_expr_opt(expression)
            .unwrap_or_else(|| expression.clone());
        self.error.map_or(Ok(output), |error| {
            Err(format!("{error}: visits={}", self.work))
        })
    }
}
impl ExprFolderOpt for Redirect {
    fn fold_expr_opt(&mut self, expression: &Expr) -> Option<Expr> {
        if self.error.is_some() {
            return None;
        }
        if self.work >= self.limit {
            self.error = Some("aggregate scoped instantiation work limit");
            return None;
        }
        self.work += 1;
        if self.depth >= 16_384 {
            self.error = Some("scoped instantiation depth limit");
            return None;
        }
        let key = RedirectKey(expression.clone());
        if let Some(output) = self.memo.get(&key) {
            return (!same_graph(output, expression)).then(|| output.clone());
        }
        self.depth += 1;
        let output = self.fold_expr_opt_inner(expression);
        self.depth -= 1;
        if self.error.is_none() {
            self.memo
                .insert(key, output.clone().unwrap_or_else(|| expression.clone()));
        }
        output
    }
    fn fold_fvar_opt(&mut self, id: FVarId) -> Option<Expr> {
        if let Some(replacement) = self.replacements.get(&id) {
            // Simultaneous substitution: do not traverse the replacement.
            return (!matches!(replacement.kind(), ExprKind::FVar(other) if *other == id))
                .then(|| replacement.clone());
        }
        self.error = Some(if self.definitions.contains(&id) {
            "instantiation missed a preceding definition"
        } else {
            "instantiation lacks an original local"
        });
        None
    }
}

impl ProofComponents {
    /// Copy the needed actual defining support under local parameter bindings.
    /// Source/target handles share this owner. Definitions cannot be replaced
    /// by caller data, and all originals remain mandatory complete replay inputs.
    pub fn instantiate_scoped_candidate<A: ScopedLocalAllocator>(
        &mut self,
        allocator: &mut A,
        original_dynamic: &[OwnedProofCapture],
        parameter_bindings: &[(ScopedLocal, ScopedLocal)],
        captures: &[OwnedProofCapture],
        type_: Expr,
        value: Expr,
    ) -> Result<InstantiatedScopedCandidate, String> {
        if self.analysis_visits >= self.limits.operations
            || self.analysis_words >= self.limits.operations
        {
            return Err("aggregate scoped instantiation work limit".into());
        }
        let scope = allocator.local_scope();
        let mut entries = self.normalization_entries(scope)?;
        let mut ids = entries
            .iter()
            .map(|(local, _)| local.id())
            .collect::<HashSet<_>>();
        for capture in original_dynamic {
            if !scope.owns(capture.local()) || !ids.insert(capture.local().id()) {
                return Err("foreign or duplicate original instantiation capture".into());
            }
            let definition = match capture {
                OwnedProofCapture::Parameter(_) => None,
                OwnedProofCapture::Definition { value, .. } => Some(value.as_ref().clone()),
            };
            entries.push((capture.local().clone(), definition));
        }
        let mut authorized = self.base_ids.clone();
        let mut capture_ids = HashSet::new();
        for capture in captures {
            if !scope.owns(capture.local()) || !capture_ids.insert(capture.local().id()) {
                return Err("foreign or duplicate target instantiation capture".into());
            }
            authorized.insert(capture.local().id());
        }
        let parameters = entries
            .iter()
            .filter(|(_, value)| value.is_none())
            .map(|(local, _)| local.id())
            .collect::<HashSet<_>>();
        let mut replacements = entries
            .iter()
            .filter(|(_, value)| value.is_none())
            .map(|(local, _)| (local.id(), local.term().clone()))
            .collect::<HashMap<_, _>>();
        let mut replaced = HashSet::new();
        for (source, target) in parameter_bindings {
            if !scope.owns(source) || !scope.owns(target) || !replaced.insert(source.id()) {
                return Err("foreign or duplicate instantiation binding".into());
            }
            if !parameters.contains(&source.id()) {
                return Err("instantiation may replace only an original parameter".into());
            }
            if !authorized.contains(&target.id()) {
                return Err("instantiation target lacks an actual preceding capture".into());
            }
            replacements.insert(source.id(), target.term().clone());
        }
        // Reachability is producer data only. Use the binder-aware empty-
        // ambient scanner before materialization, rather than repeatedly
        // closing unrelated declarations during each candidate instantiation.
        let ambient = HashSet::new();
        let mut walker = CaptureDependencies {
            scope,
            ambient: &ambient,
            work: &mut self.analysis_visits,
            word_work: &mut self.analysis_words,
            cache: &mut self.sealing_dependencies,
            retained_words: &mut self.retained_words,
            retained_sets: &mut self.retained_sets,
            limit: self.limits.operations,
            needed: Arc::new(Vec::new()),
            empty: Arc::new(Vec::new()),
            error: None,
            depth: 0,
            max_depth: 16_384,
            materialized_reuse: false,
            bound: HashSet::new(),
            pruned: false,
        };
        walker.scan(&type_)?;
        walker.scan(&value)?;
        let mut selected = Vec::new();
        let mut needed_entries = HashSet::new();
        for (index, (local, definition)) in entries.iter().enumerate().rev() {
            if walker.contains(local.id()) {
                needed_entries.insert(index);
                walker.scan(local.ty())?;
                if let Some(value) = definition {
                    walker.scan(value)?;
                }
                if definition.is_some() {
                    selected.push(index);
                }
            }
        }
        selected.reverse();
        // An unchanged actual definition remains available in this same owner
        // and prefix. Reuse it only after checking its type AND value for
        // transitive dependence on a parameter that actually changes. This is
        // preparation sharing, never removal from complete original replay.
        let mut changed = replaced
            .iter()
            .copied()
            .filter(|id| !matches!(replacements[id].kind(), ExprKind::FVar(other) if other == id))
            .collect::<Vec<_>>();
        let mut copied = Vec::new();
        for &index in &selected {
            walker.needed = walker.empty.clone();
            walker.scan(entries[index].0.ty())?;
            walker.scan(
                entries[index]
                    .1
                    .as_ref()
                    .ok_or("selected parameter as definition")?,
            )?;
            let mut affected = false;
            for id in &changed {
                if *walker.word_work >= walker.limit {
                    return Err("aggregate instantiation dependence probe limit".into());
                }
                *walker.word_work += 1;
                affected |= walker.contains(*id);
            }
            if affected {
                changed.push(entries[index].0.id());
                copied.push(index);
            } else {
                replacements.insert(entries[index].0.id(), entries[index].0.term().clone());
                needed_entries.remove(&index);
            }
        }
        drop(walker);
        let selected = copied;
        // Materialize needed types/values at their ORIGINAL prefix indices.
        // All original handles are owner-checked and all original declarations
        // remain mandatory final replay inputs, including unused false values.
        // Internal binders become BVars before any parameter redirection.
        let locals = entries
            .iter()
            .map(|(local, _)| local.clone())
            .collect::<Vec<_>>();
        let mut roots = Vec::new();
        let mut visible = Vec::new();
        let mut positions = vec![None; entries.len()];
        for (index, (local, definition)) in entries.iter().enumerate() {
            if !needed_entries.contains(&index) {
                continue;
            }
            let type_position = roots.len();
            roots.push(local.ty().clone());
            visible.push(index);
            let value_position = definition.as_ref().map(|definition| {
                let position = roots.len();
                roots.push(definition.clone());
                visible.push(index);
                position
            });
            positions[index] = Some((type_position, value_position));
        }
        let root_position = roots.len();
        roots.extend([type_, value]);
        visible.extend([locals.len(); 2]);
        let (materialized, stats) = scope.close_external_forest_with_limits(
            &roots,
            &locals,
            &visible,
            crate::term_scope::TermScopeLimits {
                max_visits: self.limits.operations.saturating_sub(self.analysis_visits),
                max_depth: 16_384,
            },
        );
        self.analysis_visits = self
            .analysis_visits
            .checked_add(stats.visits)
            .ok_or("instantiation materialization work overflow")?;
        if self.analysis_visits > self.limits.operations {
            return Err("aggregate instantiation materialization work limit".into());
        }
        let materialized = materialized.map_err(|error| error.to_string())?;
        let mut redirect = Redirect {
            replacements,
            definitions: entries
                .iter()
                .filter(|(_, definition)| definition.is_some())
                .map(|(local, _)| local.id())
                .collect(),
            memo: HashMap::new(),
            work: self.analysis_visits,
            limit: self.limits.operations,
            depth: 0,
            error: None,
        };
        for index in selected {
            let (type_position, value_position) =
                positions[index].ok_or("instantiation lost a selected declaration prefix")?;
            let rewritten_type = redirect.apply(&materialized[type_position]);
            self.analysis_visits = redirect.work;
            let rewritten_type = rewritten_type?;
            let rewritten_value = redirect.apply(
                &materialized
                    [value_position.ok_or("instantiation selected a parameter as a definition")?],
            );
            self.analysis_visits = redirect.work;
            let rewritten_value = rewritten_value?;
            let reference =
                self.bind_scoped(allocator, captures, rewritten_type, rewritten_value)?;
            redirect.work = self.analysis_visits;
            // The strict prefix walk above establishes that already processed
            // inputs cannot mention this later declaration. Exact DAG memo
            // entries therefore stay valid as the definition map grows.
            redirect
                .replacements
                .insert(entries[index].0.id(), reference);
        }
        let type_ = redirect.apply(&materialized[root_position]);
        self.analysis_visits = redirect.work;
        let type_ = type_?;
        let value = redirect.apply(&materialized[root_position + 1]);
        self.analysis_visits = redirect.work;
        Ok(InstantiatedScopedCandidate {
            type_,
            value: value?,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use clean_kernel::{Environment, Level};
    fn n() -> Expr {
        Expr::const_str("Nat")
    }
    fn env() -> Environment {
        let mut env = Environment::new();
        env.init_nat().unwrap();
        env.init_eq().unwrap();
        env.init_true_false().unwrap();
        env
    }
    fn eq(ty: Expr, left: Expr, right: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
            [ty, left, right],
        )
    }
    fn refl(ty: Expr, value: Expr) -> Expr {
        Expr::apps(
            Expr::const_(
                Name::from_string("Eq.refl"),
                vec![Level::succ(Level::zero())],
            ),
            [ty, value],
        )
    }
    fn replay(parts: ProofComponents, scope: &LocalScope, root: Expr, goal: Expr, claim: Expr) {
        let bundle = parts
            .close_scoped(scope, root, goal, Default::default())
            .unwrap();
        let wire = bundle.encode_with_claim(&claim).unwrap();
        let (decoded, transported) = ScopedProofComponentBundle::decode_with_claim(&wire).unwrap();
        assert_eq!(claim, transported);
        decoded.replay(&env(), &claim, 2_000_000).unwrap();
    }

    #[test]
    fn instantiation_rebuilds_actual_dependent_definitions_and_substitutes_simultaneously() {
        let mut scope = LocalScope::new();
        let alpha = scope
            .try_local(Expr::sort(Level::succ(Level::zero())))
            .unwrap();
        let x = scope.try_local(alpha.term().clone()).unwrap();
        let mut parts = ProofComponents::new("instantiate.dependent", ProofLimits::default());
        parts
            .set_base(
                &scope,
                vec![
                    OwnedProofCapture::Parameter(alpha.clone()),
                    OwnedProofCapture::Parameter(x.clone()),
                ],
            )
            .unwrap();
        let alias = parts
            .bind_scoped(&mut scope, &[], alpha.term().clone(), x.term().clone())
            .unwrap();
        let beta = scope
            .try_local(Expr::sort(Level::succ(Level::zero())))
            .unwrap();
        let y = scope.try_local(beta.term().clone()).unwrap();
        let captures = [
            OwnedProofCapture::Parameter(beta.clone()),
            OwnedProofCapture::Parameter(y.clone()),
        ];
        let output = parts
            .instantiate_scoped_candidate(
                &mut scope,
                &[],
                &[(alpha.clone(), beta.clone()), (x.clone(), y.clone())],
                &captures,
                alpha.term().clone(),
                alias,
            )
            .unwrap();
        let proposition = eq(beta.term().clone(), output.value.clone(), y.term().clone());
        let goal = beta.pi(y.pi(proposition));
        let frozen = eq(beta.term().clone(), y.term().clone(), y.term().clone());
        let claim = scope.close(&alpha.pi(x.pi(beta.pi(y.pi(frozen))))).unwrap();
        let root = alpha.lam(x.lam(beta.lam(y.lam(refl(beta.term().clone(), output.value)))));
        replay(parts, &scope, root, goal, claim);

        let mut scope = LocalScope::new();
        let a = scope.try_local(n()).unwrap();
        let b = scope.try_local(n()).unwrap();
        let mut parts = ProofComponents::new("instantiate.swap", ProofLimits::default());
        parts
            .set_base(
                &scope,
                vec![
                    OwnedProofCapture::Parameter(a.clone()),
                    OwnedProofCapture::Parameter(b.clone()),
                ],
            )
            .unwrap();
        let original = Expr::apps(
            Expr::const_str("Nat.add"),
            [a.term().clone(), b.term().clone()],
        );
        let output = parts
            .instantiate_scoped_candidate(
                &mut scope,
                &[],
                &[(a.clone(), b.clone()), (b.clone(), a.clone())],
                &[],
                n(),
                original,
            )
            .unwrap();
        let expected = Expr::apps(
            Expr::const_str("Nat.add"),
            [b.term().clone(), a.term().clone()],
        );
        let goal = eq(n(), output.value.clone(), expected.clone());
        let frozen = eq(n(), expected.clone(), expected);
        let claim = scope.close(&a.pi(b.pi(frozen))).unwrap();
        let root = a.lam(b.lam(refl(n(), output.value)));
        replay(parts, &scope, root, goal, claim);
    }

    #[test]
    fn instantiation_refuses_foreign_erased_ids_definition_replacement_and_bad_prefixes() {
        let mut scope = LocalScope::new();
        let input = scope.try_local(n()).unwrap();
        let mut foreign = LocalScope::new();
        let other = foreign.try_local(n()).unwrap();
        assert_eq!(input.id(), other.id());
        let mut parts = ProofComponents::new("instantiate.owner", ProofLimits::default());
        parts
            .set_base(&scope, vec![OwnedProofCapture::Parameter(input.clone())])
            .unwrap();
        assert!(
            parts
                .instantiate_scoped_candidate(
                    &mut scope,
                    &[],
                    &[(other.clone(), input.clone())],
                    &[],
                    n(),
                    input.term().clone()
                )
                .is_err()
        );
        assert!(
            parts
                .instantiate_scoped_candidate(
                    &mut scope,
                    &[],
                    &[(input.clone(), other)],
                    &[],
                    n(),
                    input.term().clone()
                )
                .is_err()
        );
        let alias = parts
            .bind_scoped(&mut scope, &[], n(), input.term().clone())
            .unwrap();
        let local = parts.bindings.last().unwrap().0.clone();
        assert!(
            parts
                .instantiate_scoped_candidate(
                    &mut scope,
                    &[],
                    &[(local, input.clone())],
                    &[],
                    n(),
                    alias
                )
                .is_err()
        );
        let absent = scope.try_local(n()).unwrap();
        assert!(
            parts
                .instantiate_scoped_candidate(
                    &mut scope,
                    &[],
                    &[(input.clone(), absent)],
                    &[],
                    n(),
                    input.term().clone()
                )
                .is_err()
        );
        let alpha = scope
            .try_local(Expr::sort(Level::succ(Level::zero())))
            .unwrap();
        let value = scope.try_local(alpha.term().clone()).unwrap();
        let reversed = [
            OwnedProofCapture::Parameter(value.clone()),
            OwnedProofCapture::Parameter(alpha),
        ];
        assert!(
            parts
                .instantiate_scoped_candidate(
                    &mut scope,
                    &reversed,
                    &[],
                    &[],
                    value.ty().clone(),
                    value.term().clone()
                )
                .is_err()
        );
    }

    #[test]
    fn instantiation_keeps_original_false_declarations_and_rejects_forged_new_worlds() {
        let mut scope = LocalScope::new();
        let mut parts = ProofComponents::new("instantiate.false", ProofLimits::default());
        parts.set_base(&scope, vec![]).unwrap();
        let _false = parts
            .bind_scoped(
                &mut scope,
                &[],
                eq(n(), Expr::nat_lit(0), Expr::nat_lit(1)),
                refl(n(), Expr::nat_lit(0)),
            )
            .unwrap();
        let output = parts
            .instantiate_scoped_candidate(
                &mut scope,
                &[],
                &[],
                &[],
                Expr::const_str("True"),
                Expr::const_str("True.intro"),
            )
            .unwrap();
        let bundle = parts
            .close_scoped(
                &scope,
                output.value,
                Expr::const_str("True"),
                Default::default(),
            )
            .unwrap();
        assert!(
            bundle
                .replay(&env(), &Expr::const_str("True"), 2_000_000)
                .is_err()
        );

        let mut scope = LocalScope::new();
        let input = scope.try_local(n()).unwrap();
        let target = scope.try_local(n()).unwrap();
        let mut parts = ProofComponents::new("instantiate.forged", ProofLimits::default());
        parts
            .set_base(
                &scope,
                vec![
                    OwnedProofCapture::Parameter(input.clone()),
                    OwnedProofCapture::Parameter(target.clone()),
                ],
            )
            .unwrap();
        let goal = eq(n(), input.term().clone(), Expr::nat_lit(0));
        let proof = refl(n(), input.term().clone());
        let output = parts
            .instantiate_scoped_candidate(
                &mut scope,
                &[],
                &[(input.clone(), target.clone())],
                &[],
                goal,
                proof,
            )
            .unwrap();
        let claim = scope
            .close(&input.pi(target.pi(output.type_.clone())))
            .unwrap();
        let bundle = parts
            .close_scoped(
                &scope,
                input.lam(target.lam(output.value)),
                output.type_,
                Default::default(),
            )
            .unwrap();
        assert!(bundle.replay(&env(), &claim, 2_000_000).is_err());
    }

    #[test]
    fn instantiation_charges_repeated_materialization_and_redirect_work_cumulatively() {
        let mut scope = LocalScope::new();
        let mut parts = ProofComponents::new(
            "instantiate.work",
            ProofLimits {
                operations: 256,
                ..Default::default()
            },
        );
        parts.set_base(&scope, vec![]).unwrap();
        let mut refused = false;
        for _ in 0..256 {
            if parts
                .instantiate_scoped_candidate(&mut scope, &[], &[], &[], n(), Expr::nat_lit(0))
                .is_err()
            {
                refused = true;
                break;
            }
        }
        assert!(
            refused,
            "instantiation must not reset the owning component budget"
        );
        assert!(parts.analysis_visits <= parts.limits.operations);
        assert!(parts.analysis_words <= parts.limits.operations);
        let before = (parts.analysis_visits, parts.analysis_words);
        assert!(
            parts
                .instantiate_scoped_candidate(&mut scope, &[], &[], &[], n(), Expr::nat_lit(0))
                .is_err()
        );
        assert_eq!(before, (parts.analysis_visits, parts.analysis_words));
    }

    #[test]
    fn instantiation_reuses_only_transitively_unchanged_actual_definitions() {
        let mut scope = LocalScope::new();
        let a = scope.try_local(n()).unwrap();
        let b = scope.try_local(n()).unwrap();
        let c = scope.try_local(n()).unwrap();
        let mut parts = ProofComponents::new("instantiate.shared", ProofLimits::default());
        parts
            .set_base(
                &scope,
                vec![
                    OwnedProofCapture::Parameter(a.clone()),
                    OwnedProofCapture::Parameter(b.clone()),
                    OwnedProofCapture::Parameter(c.clone()),
                ],
            )
            .unwrap();
        let unchanged = parts
            .bind_scoped(&mut scope, &[], n(), a.term().clone())
            .unwrap();
        let changed_value = Expr::apps(Expr::const_str("Nat.add"), [unchanged, b.term().clone()]);
        let changed = parts
            .bind_scoped(&mut scope, &[], n(), changed_value)
            .unwrap();
        let before = parts.bindings.len();
        let output = parts
            .instantiate_scoped_candidate(
                &mut scope,
                &[],
                &[(b.clone(), c.clone())],
                &[],
                n(),
                changed,
            )
            .unwrap();
        assert_eq!(
            parts.bindings.len() - before,
            1,
            "the unchanged dependency is reused; its changed user is copied"
        );
        let expected = Expr::apps(
            Expr::const_str("Nat.add"),
            [a.term().clone(), c.term().clone()],
        );
        let goal = eq(n(), output.value.clone(), expected.clone());
        let frozen = eq(n(), expected.clone(), expected);
        let claim = scope.close(&a.pi(b.pi(c.pi(frozen)))).unwrap();
        let root = a.lam(b.lam(c.lam(refl(n(), output.value))));
        replay(parts, &scope, root, goal, claim);
    }

    #[test]
    fn instantiation_keeps_cold_originals_out_of_preparation_but_not_final_replay() {
        let mut scope = LocalScope::new();
        let mut parts = ProofComponents::new(
            "instantiate.cold",
            ProofLimits {
                operations: 4096,
                ..Default::default()
            },
        );
        parts.set_base(&scope, vec![]).unwrap();
        let input = scope.try_local(n()).unwrap();
        let mut deep = input.term().clone();
        for _ in 0..300 {
            deep = Expr::app(Expr::const_str("Nat.succ"), deep);
        }
        let _invalid = parts
            .bind_scoped(
                &mut scope,
                &[],
                eq(n(), Expr::nat_lit(0), Expr::nat_lit(1)),
                input.lam(deep),
            )
            .unwrap();
        let before = parts.analysis_visits;
        let output = parts
            .instantiate_scoped_candidate(
                &mut scope,
                &[],
                &[],
                &[],
                Expr::const_str("True"),
                Expr::const_str("True.intro"),
            )
            .unwrap();
        assert!(
            parts.analysis_visits - before < 32,
            "unrelated old data must not be materialized again during preparation"
        );
        let bundle = parts
            .close_scoped(
                &scope,
                output.value,
                Expr::const_str("True"),
                Default::default(),
            )
            .unwrap();
        let error = bundle
            .replay(&env(), &Expr::const_str("True"), 2_000_000)
            .err()
            .unwrap();
        assert!(
            error.contains("TypeMismatch") && !error.contains("BudgetExhausted"),
            "original invalid cold value must still reach the checker: {error}"
        );
    }
}
