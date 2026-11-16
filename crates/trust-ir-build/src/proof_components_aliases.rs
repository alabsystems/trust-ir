// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//! Candidate aliases for actual owned lexical definitions; whole replay remains mandatory.
use super::*;

/// Untrusted identity data. An alias does not grant code/source authority;
/// consumers must replay their SAME complete original endpoint and transport.
pub struct OwnedDefinitionAlias {
    pub original: ScopedLocal,
    pub alias: ScopedLocal,
    pub reference: Expr,
}

impl ProofComponents {
    /// Retain fresh internal definitions for actual lexical definitions.
    /// Explicit original globals remain globals; no parameter can silently
    /// become a definition. All defining values remain mandatory in replay.
    pub fn alias_owned_definitions<A: ScopedLocalAllocator>(
        &mut self,
        allocator: &mut A,
        globals: &[ScopedLocal],
        definitions: &[(ScopedLocal, Expr)],
    ) -> Result<Vec<OwnedDefinitionAlias>, String> {
        if globals
            .len()
            .checked_add(
                definitions
                    .len()
                    .checked_mul(2)
                    .ok_or("alias inventory overflow")?,
            )
            .is_none_or(|count| count > self.limits.captures.saturating_add(self.limits.contexts))
            || definitions.len() > self.limits.contexts.saturating_sub(self.bindings.len())
        {
            return Err("alias input inventory limit".into());
        }
        let declaration_count = self
            .base
            .len()
            .checked_add(self.bindings.len())
            .ok_or("alias declaration count overflow")?;
        // Prepay the retained inventory and all original/global/alias handle
        // probes before allocating them. Substitution below shares one validated
        // inventory/map, so there is no uncharged quadratic preparation loop.
        let setup = declaration_count
            .checked_mul(4)
            .and_then(|v| v.checked_add(globals.len().checked_mul(16)?))
            .and_then(|v| v.checked_add(definitions.len().checked_mul(24)?))
            .ok_or("alias inventory work overflow")?;
        let used = self
            .analysis_visits
            .checked_add(self.analysis_words)
            .and_then(|v| v.checked_add(setup))
            .ok_or("alias preparation work overflow")?;
        if used >= self.limits.operations {
            return Err("alias inventory operation limit".into());
        }
        self.analysis_visits = self
            .analysis_visits
            .checked_add(setup)
            .ok_or("alias work overflow")?;
        // Charge before allocating/scanning inventories, including failed
        // requests. This never refunds preparation for a retry.
        let entries = self.normalization_entries(allocator.local_scope())?;
        let retained = entries
            .iter()
            .map(|(local, _)| local.id())
            .collect::<HashSet<_>>();
        let mut ids = HashSet::new();
        for global in globals {
            if !allocator.local_scope().owns(global)
                || !retained.contains(&global.id())
                || !ids.insert(global.id())
            {
                return Err("foreign, duplicate or unretained alias global".into());
            }
        }
        let mut allowed = globals.to_vec();
        let mut roots = Vec::new();
        let mut visible = Vec::new();
        for (index, (original, value)) in definitions.iter().enumerate() {
            if !allocator.local_scope().owns(original)
                || retained.contains(&original.id())
                || !ids.insert(original.id())
            {
                return Err(
                    "alias source is foreign, duplicated or an existing parameter/declaration"
                        .into(),
                );
            }
            roots.extend([original.ty().clone(), value.clone()]);
            visible.extend([globals.len() + index; 2]);
            allowed.push(original.clone());
        }
        let (materialized, stats) = allocator.local_scope().close_external_forest_with_limits(
            &roots,
            &allowed,
            &visible,
            crate::term_scope::TermScopeLimits {
                max_visits: self.limits.operations.saturating_sub(used),
                max_depth: 16_384,
            },
        );
        self.analysis_visits = self
            .analysis_visits
            .checked_add(stats.visits)
            .ok_or("alias materialization overflow")?;
        // Failed preparation spends work too; there is no retry/publication
        // refund. No aliases exist before the complete original forest closes.
        let materialized = materialized.map_err(|error| error.to_string())?;
        if self
            .analysis_visits
            .checked_add(self.analysis_words)
            .is_none_or(|work| work >= self.limits.operations)
        {
            return Err("alias aggregate materialization limit".into());
        }
        if materialized.len()
            != definitions
                .len()
                .checked_mul(2)
                .ok_or("alias forest size overflow")?
        {
            return Err("alias original forest lost roots".into());
        }
        let mut substitutions = HashMap::new();
        let mut result = Vec::new();
        for ((original, _), fields) in definitions.iter().zip(materialized.as_chunks::<2>().0) {
            let mut rewritten = super::substitute::substitute_prevalidated_scoped_terms(
                allocator.local_scope(),
                &ids,
                &substitutions,
                fields,
                &mut self.analysis_visits,
                self.limits.operations.saturating_sub(self.analysis_words),
            )?;
            if self
                .analysis_visits
                .checked_add(self.analysis_words)
                .is_none_or(|work| work >= self.limits.operations)
            {
                return Err("alias aggregate substitution limit".into());
            }
            if rewritten.len() != 2 {
                return Err("alias forest lost a defining value".into());
            }
            let value = rewritten.pop().unwrap();
            let type_ = rewritten.pop().unwrap();
            let reference = self.bind_scoped(allocator, &[], type_, value)?;
            if self
                .analysis_visits
                .checked_add(self.analysis_words)
                .is_none_or(|work| work > self.limits.operations)
            {
                return Err("alias aggregate binding limit".into());
            }
            let (alias, _) = self
                .bindings
                .last()
                .ok_or("alias definition was not retained")?;
            if !allocator.local_scope().owns(alias) || !same_graph(alias.term(), &reference) {
                return Err("alias reference is not its exact retained owned local".into());
            }
            let alias = alias.clone();
            // Only this exact newly retained same-owner bare FVar can enter
            // the private map. No arbitrary replacement or witness is admitted.
            substitutions.insert(original.id(), reference.clone());
            result.push(OwnedDefinitionAlias {
                original: original.clone(),
                alias,
                reference,
            });
        }
        Ok(result)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use clean_kernel::{Environment, Level};
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
    fn parts(scope: &LocalScope, globals: Vec<ScopedLocal>) -> ProofComponents {
        let mut p = ProofComponents::new("aliases.lexical", ProofLimits::default());
        p.set_base(
            scope,
            globals
                .into_iter()
                .map(OwnedProofCapture::Parameter)
                .collect(),
        )
        .unwrap();
        p
    }
    #[test]
    fn owned_definition_aliases_preserve_original_lexical_endpoint_and_replay() {
        let mut scope = LocalScope::new();
        let input = scope.try_local(n()).unwrap();
        let first = scope.try_local(n()).unwrap();
        let second = scope.try_local(n()).unwrap();
        let definitions = vec![
            (first.clone(), input.term().clone()),
            (second.clone(), first.term().clone()),
        ];
        let original = first.let_(
            input.term().clone(),
            second.let_(first.term().clone(), second.term().clone()),
        );
        let mut p = parts(&scope, vec![input.clone()]);
        let aliases = p
            .alias_owned_definitions(&mut scope, std::slice::from_ref(&input), &definitions)
            .unwrap();
        assert_ne!(aliases[0].alias.id(), first.id());
        assert_ne!(aliases[1].alias.id(), second.id());
        let claim = scope
            .close(&input.pi(eq(original.clone(), input.term().clone())))
            .unwrap();
        let proposition = eq(original, aliases[1].reference.clone());
        // SAME original lexical program is retained on the left. Refl is only
        // a candidate; strict whole-carrier replay checks the actual transport.
        let root = input.lam(refl(input.term().clone()));
        let bundle = p
            .close_scoped(&scope, root, proposition, Default::default())
            .unwrap();
        let wire = bundle.encode_with_claim(&claim).unwrap();
        let (decoded, transported) = ScopedProofComponentBundle::decode_with_claim(&wire).unwrap();
        assert_eq!(claim, transported);
        let mut env = Environment::new();
        env.init_nat().unwrap();
        env.init_eq().unwrap();
        decoded.replay(&env, &claim, 2_000_000).unwrap();
    }
    #[test]
    fn owned_definition_aliases_refuse_foreign_duplicate_and_parameter_sources() {
        let mut scope = LocalScope::new();
        let mut other = LocalScope::new();
        let input = scope.try_local(n()).unwrap();
        let local = scope.try_local(n()).unwrap();
        let foreign = other.try_local(n()).unwrap();
        for definitions in [
            vec![(foreign, Expr::nat_lit(0))],
            vec![
                (local.clone(), Expr::nat_lit(0)),
                (local.clone(), Expr::nat_lit(0)),
            ],
            vec![(input.clone(), Expr::nat_lit(0))],
        ] {
            let mut p = parts(&scope, vec![input.clone()]);
            assert!(
                p.alias_owned_definitions(&mut scope, std::slice::from_ref(&input), &definitions)
                    .is_err()
            );
            assert_eq!(p.counts().0, 0);
        }
        let mut p = parts(&scope, vec![input.clone()]);
        assert!(
            p.alias_owned_definitions(&mut scope, &[local], &[])
                .is_err()
        );
    }
    #[test]
    fn owned_definition_aliases_refuse_self_and_forward_definition_dependencies() {
        let mut scope = LocalScope::new();
        let a = scope.try_local(n()).unwrap();
        let b = scope.try_local(n()).unwrap();
        for definitions in [
            vec![(a.clone(), a.term().clone())],
            vec![(a.clone(), b.term().clone()), (b.clone(), Expr::nat_lit(0))],
        ] {
            let mut p = parts(&scope, vec![]);
            assert!(
                p.alias_owned_definitions(&mut scope, &[], &definitions)
                    .is_err()
            );
            assert_eq!(p.counts().0, 0);
        }
    }
    #[test]
    fn owned_definition_aliases_replay_cold_invalid_original_even_when_alias_unused() {
        let mut scope = LocalScope::new();
        let bad = scope.try_local(n()).unwrap();
        let original = bad.let_(Expr::const_str("True.intro"), Expr::nat_lit(0));
        let claim = scope.close(&eq(original, Expr::nat_lit(0))).unwrap();
        let mut p = parts(&scope, vec![]);
        p.alias_owned_definitions(&mut scope, &[], &[(bad, Expr::const_str("True.intro"))])
            .unwrap();
        let bundle = p
            .close_scoped(
                &scope,
                refl(Expr::nat_lit(0)),
                eq(Expr::nat_lit(0), Expr::nat_lit(0)),
                Default::default(),
            )
            .unwrap();
        let bytes = bundle.encode_with_claim(&claim).unwrap();
        let (decoded, transported) = ScopedProofComponentBundle::decode_with_claim(&bytes).unwrap();
        assert_eq!(claim, transported);
        let mut env = Environment::new();
        env.init_nat().unwrap();
        env.init_eq().unwrap();
        env.init_true_false().unwrap();
        let error = decoded.replay(&env, &claim, 2_000_000).err().unwrap();
        assert!(
            error.contains("TypeMismatch") && !error.contains("BudgetExhausted"),
            "{error}"
        );
    }
    #[test]
    fn owned_definition_aliases_charge_failed_scans_before_publication() {
        let mut scope = LocalScope::new();
        let mut other = LocalScope::new();
        let foreign = other.try_local(n()).unwrap();
        // Each definition now prepays 24 inventory units. Permit two paid
        // failed scans here; the original 24-unit boundary is retained below.
        let limits = ProofLimits {
            operations: 80,
            ..Default::default()
        };
        let mut p = ProofComponents::new("aliases.budget", limits);
        p.set_base(&scope, vec![]).unwrap();
        let before = p.counts().3;
        assert!(
            p.alias_owned_definitions(&mut scope, &[], &[(foreign.clone(), Expr::nat_lit(0))])
                .is_err()
        );
        let first = p.counts().3;
        assert!(first > before);
        assert_eq!(p.counts().0, 0);
        assert!(
            p.alias_owned_definitions(&mut scope, &[], &[(foreign, Expr::nat_lit(0))])
                .is_err()
        );
        assert!(p.counts().3 > first);
        assert_eq!(p.counts().0, 0);
    }
    #[test]
    fn owned_definition_aliases_rewrite_dependent_types_in_original_order() {
        let mut scope = LocalScope::new();
        let alpha = scope
            .try_local(Expr::sort(Level::succ(Level::zero())))
            .unwrap();
        let value = scope.try_local(alpha.term().clone()).unwrap();
        let original = alpha.let_(n(), value.let_(Expr::nat_lit(0), value.term().clone()));
        let claim = scope
            .close(&eq(original.clone(), Expr::nat_lit(0)))
            .unwrap();
        let mut p = parts(&scope, vec![]);
        let aliases = p
            .alias_owned_definitions(&mut scope, &[], &[(alpha, n()), (value, Expr::nat_lit(0))])
            .unwrap();
        assert!(same_graph(aliases[1].alias.ty(), &aliases[0].reference));
        let proposition = eq(original, aliases[1].reference.clone());
        let bundle = p
            .close_scoped(
                &scope,
                refl(Expr::nat_lit(0)),
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
    fn owned_definition_aliases_original_small_budget_refuses_before_allocating_aliases() {
        let mut scope = LocalScope::new();
        let local = scope.try_local(n()).unwrap();
        let limits = ProofLimits {
            operations: 24,
            ..Default::default()
        };
        let mut p = ProofComponents::new("aliases.prepaid_boundary", limits);
        p.set_base(&scope, vec![]).unwrap();
        let allocated = scope.allocated();
        let error = p
            .alias_owned_definitions(&mut scope, &[], &[(local, Expr::nat_lit(0))])
            .err()
            .unwrap();
        assert!(error.contains("alias inventory operation limit"), "{error}");
        assert_eq!(p.counts().0, 0);
        assert_eq!(scope.allocated(), allocated);
    }
}
