// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//! Candidate-only same-owner support restriction. Complete original replay
//! remains mandatory; a sealed term is never a premise or provider fact.
use super::*;

pub struct SealedScopedDefinition {
    pub type_: Expr,
    pub value: Expr,
    /// Original same-owner parameters, in their actual declaration order.
    pub arguments: Vec<ScopedLocal>,
}

#[cfg(test)]
mod tests {
    use super::*;
    use clean_kernel::{Environment, Level, TypeChecker};

    fn nat() -> Expr {
        Expr::const_str("Nat")
    }
    fn env() -> Environment {
        let mut env = Environment::new();
        env.init_nat().unwrap();
        env.init_eq().unwrap();
        env.init_true_false().unwrap();
        env
    }
    fn eq(left: Expr, right: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
            [nat(), left, right],
        )
    }
    fn refl(value: Expr) -> Expr {
        Expr::apps(
            Expr::const_(
                Name::from_string("Eq.refl"),
                vec![Level::succ(Level::zero())],
            ),
            [nat(), value],
        )
    }

    #[test]
    fn sealing_transitive_definition_closes_without_an_unused_answer_parameter() {
        let env = env();
        let mut scope = LocalScope::new();
        let answer = scope
            .try_local(Expr::sort(Level::succ(Level::zero())))
            .unwrap();
        let input = scope.try_local(nat()).unwrap();
        let mut parts = ProofComponents::new("seal.independent", ProofLimits::default());
        parts
            .set_base(
                &scope,
                vec![
                    OwnedProofCapture::Parameter(answer.clone()),
                    OwnedProofCapture::Parameter(input.clone()),
                ],
            )
            .unwrap();
        let alias = parts
            .bind_scoped(&mut scope, &[], nat(), input.term().clone())
            .unwrap();
        let before = parts.counts();
        let sealed = parts
            .seal_scoped_definition(&scope, &[], &[answer.clone()], nat(), alias.clone())
            .unwrap();
        assert_eq!(
            sealed
                .arguments
                .iter()
                .map(ScopedLocal::id)
                .collect::<Vec<_>>(),
            vec![input.id()]
        );
        assert_eq!(
            (parts.counts().0, parts.counts().1, parts.counts().2),
            (before.0, before.1, before.2)
        );
        TypeChecker::new(&env)
            .check_type(&sealed.value, &sealed.type_)
            .unwrap();
        let instantiated = Expr::app(sealed.value, input.term().clone());
        let proposition = eq(alias.clone(), instantiated.clone());
        let frozen = eq(input.term().clone(), instantiated);
        let claim = scope.close(&answer.pi(input.pi(frozen))).unwrap();
        let bundle = parts
            .close_scoped(
                &scope,
                answer.lam(input.lam(refl(alias))),
                proposition,
                Default::default(),
            )
            .unwrap();
        let bytes = bundle.encode_with_claim(&claim).unwrap();
        let (decoded, transported) = ScopedProofComponentBundle::decode_with_claim(&bytes).unwrap();
        assert_eq!(claim, transported);
        decoded.replay(&env, &claim, 2_000_000).unwrap();
    }

    #[test]
    fn sealing_preserves_dependent_parameter_order_and_refuses_forbidden_types() {
        let env = env();
        let mut scope = LocalScope::new();
        let alpha = scope
            .try_local(Expr::sort(Level::succ(Level::zero())))
            .unwrap();
        let value = scope.try_local(alpha.term().clone()).unwrap();
        let mut parts = ProofComponents::new("seal.telescope", ProofLimits::default());
        parts.set_base(&scope, vec![]).unwrap();
        let captures = [
            OwnedProofCapture::Parameter(alpha.clone()),
            OwnedProofCapture::Parameter(value.clone()),
        ];
        let sealed = parts
            .seal_scoped_definition(
                &scope,
                &captures,
                &[],
                alpha.term().clone(),
                value.term().clone(),
            )
            .unwrap();
        TypeChecker::new(&env)
            .check_type(&sealed.value, &sealed.type_)
            .unwrap();
        assert_eq!(
            sealed
                .arguments
                .iter()
                .map(ScopedLocal::id)
                .collect::<Vec<_>>(),
            vec![alpha.id(), value.id()]
        );
        assert!(
            parts
                .seal_scoped_definition(
                    &scope,
                    &captures,
                    &[alpha.clone()],
                    alpha.term().clone(),
                    value.term().clone()
                )
                .is_err()
        );
        let reversed = [captures[1].clone(), captures[0].clone()];
        assert!(
            parts
                .seal_scoped_definition(
                    &scope,
                    &reversed,
                    &[],
                    alpha.term().clone(),
                    value.term().clone()
                )
                .is_err()
        );
    }

    #[test]
    fn sealing_does_not_reuse_ambient_omissions_from_the_ordinary_capture_cache() {
        let mut scope = LocalScope::new();
        let alpha = scope
            .try_local(Expr::sort(Level::succ(Level::zero())))
            .unwrap();
        let value = scope.try_local(alpha.term().clone()).unwrap();
        let mut parts = ProofComponents::new("seal.cache", ProofLimits::default());
        parts
            .set_base(
                &scope,
                vec![
                    OwnedProofCapture::Parameter(alpha.clone()),
                    OwnedProofCapture::Parameter(value.clone()),
                ],
            )
            .unwrap();
        let alias = parts
            .bind_scoped(&mut scope, &[], alpha.term().clone(), value.term().clone())
            .unwrap();
        let error = parts
            .seal_scoped_definition(&scope, &[], &[alpha.clone()], alpha.term().clone(), alias)
            .err()
            .unwrap();
        assert!(error.contains("forbidden local"), "{error}");
    }

    #[test]
    fn sealing_keeps_all_original_declarations_in_mandatory_replay() {
        let env = env();
        let mut scope = LocalScope::new();
        let mut parts = ProofComponents::new("seal.false", ProofLimits::default());
        parts.set_base(&scope, vec![]).unwrap();
        let _false = parts
            .bind_scoped(
                &mut scope,
                &[],
                eq(Expr::nat_lit(0), Expr::nat_lit(1)),
                refl(Expr::nat_lit(0)),
            )
            .unwrap();
        let sealed = parts
            .seal_scoped_definition(&scope, &[], &[], nat(), Expr::nat_lit(0))
            .unwrap();
        TypeChecker::new(&env)
            .check_type(&sealed.value, &sealed.type_)
            .unwrap();
        let goal = Expr::const_str("True");
        let bundle = parts
            .close_scoped(
                &scope,
                Expr::const_str("True.intro"),
                goal.clone(),
                Default::default(),
            )
            .unwrap();
        assert!(bundle.replay(&env, &goal, 2_000_000).is_err());
    }

    #[test]
    fn sealing_refuses_foreign_duplicate_and_unaccounted_repeated_work() {
        let mut scope = LocalScope::new();
        let value = scope.try_local(nat()).unwrap();
        let mut foreign = LocalScope::new();
        let other = foreign.try_local(nat()).unwrap();
        assert_eq!(value.id(), other.id());
        let mut parts = ProofComponents::new(
            "seal.bounds",
            ProofLimits {
                operations: 256,
                ..Default::default()
            },
        );
        parts.set_base(&scope, vec![]).unwrap();
        assert!(
            parts
                .seal_scoped_definition(
                    &scope,
                    &[OwnedProofCapture::Parameter(other.clone())],
                    &[],
                    nat(),
                    value.term().clone()
                )
                .is_err()
        );
        assert!(
            parts
                .seal_scoped_definition(&scope, &[], &[other], nat(), Expr::nat_lit(0))
                .is_err()
        );
        let capture = OwnedProofCapture::Parameter(value.clone());
        assert!(
            parts
                .seal_scoped_definition(
                    &scope,
                    &[capture.clone(), capture],
                    &[],
                    nat(),
                    value.term().clone()
                )
                .is_err()
        );
        assert!(
            parts
                .seal_scoped_definition(
                    &scope,
                    &[],
                    &[value.clone(), value],
                    nat(),
                    Expr::nat_lit(0)
                )
                .is_err()
        );
        let mut refused = false;
        for _ in 0..256 {
            if parts
                .seal_scoped_definition(&scope, &[], &[], nat(), Expr::nat_lit(0))
                .is_err()
            {
                refused = true;
                break;
            }
        }
        assert!(
            refused,
            "sealing must retain the same cumulative work budget"
        );
        assert!(parts.analysis_visits <= parts.limits.operations);
        assert!(parts.analysis_words <= parts.limits.operations);
        let before = (parts.analysis_visits, parts.analysis_words);
        assert!(
            parts
                .seal_scoped_definition(&scope, &[], &[], nat(), Expr::nat_lit(0))
                .is_err()
        );
        assert_eq!(before, (parts.analysis_visits, parts.analysis_words));
    }
}

impl ProofComponents {
    /// Close the transitive support of a candidate without any forbidden free
    /// local. Every selected type and defining value participates. This does
    /// not discard, replace, check or authorize any original declaration.
    pub fn seal_scoped_definition(
        &mut self,
        scope: &LocalScope,
        dynamic: &[OwnedProofCapture],
        forbidden: &[ScopedLocal],
        type_: Expr,
        value: Expr,
    ) -> Result<SealedScopedDefinition, String> {
        if self.analysis_visits >= self.limits.operations
            || self.analysis_words >= self.limits.operations
        {
            return Err("aggregate scoped sealing work limit".into());
        }
        let mut entries = self.normalization_entries(scope)?;
        let mut ids = entries
            .iter()
            .map(|(local, _)| local.id())
            .collect::<HashSet<_>>();
        for capture in dynamic {
            if !scope.owns(capture.local()) || !ids.insert(capture.local().id()) {
                return Err("foreign or duplicate sealing capture".into());
            }
            let definition = match capture {
                OwnedProofCapture::Parameter(_) => None,
                OwnedProofCapture::Definition { value, .. } => Some(value.as_ref().clone()),
            };
            entries.push((capture.local().clone(), definition));
        }
        if entries.len() > self.limits.contexts.saturating_add(self.limits.captures) {
            return Err("sealing declaration inventory limit".into());
        }
        let mut denied = HashSet::new();
        for local in forbidden {
            if !scope.owns(local) || !denied.insert(local.id()) {
                return Err("foreign or duplicate forbidden sealing local".into());
            }
        }
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
        for (local, definition) in entries.iter().rev() {
            if walker.contains(local.id()) {
                walker.scan(local.ty())?;
                if let Some(definition) = definition {
                    walker.scan(definition)?;
                }
                selected.push((local, definition));
            }
        }
        if forbidden.iter().any(|local| walker.contains(local.id())) {
            return Err("sealed definition depends on a forbidden local".into());
        }
        drop(walker);
        let mut closed_type = type_;
        let mut closed_value = value;
        let mut arguments = Vec::new();
        // Reverse declaration order wraps the preceding telescope faithfully.
        for (local, definition) in &selected {
            if let Some(definition) = definition {
                closed_type = local.let_(definition.clone(), closed_type);
                closed_value = local.let_(definition.clone(), closed_value);
            } else {
                closed_type = local.pi(closed_type);
                closed_value = local.lam(closed_value);
                arguments.push((*local).clone());
            }
        }
        arguments.reverse();
        let (closed, stats) = scope.close_external_forest_with_limits(
            &[closed_type, closed_value],
            &[],
            &[0, 0],
            crate::term_scope::TermScopeLimits {
                max_visits: self.limits.operations.saturating_sub(self.analysis_visits),
                max_depth: 16_384,
            },
        );
        self.analysis_visits = self
            .analysis_visits
            .checked_add(stats.visits)
            .ok_or("aggregate sealing closure work overflow")?;
        if self.analysis_visits > self.limits.operations {
            return Err("aggregate sealing closure work limit".into());
        }
        let mut closed = closed.map_err(|error| error.to_string())?.into_iter();
        Ok(SealedScopedDefinition {
            type_: closed.next().ok_or("sealing lost its type")?,
            value: closed.next().ok_or("sealing lost its value")?,
            arguments,
        })
    }
}
