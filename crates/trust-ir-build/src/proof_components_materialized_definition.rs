// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//! Reuse only this component's actual, explicitly materialized definitions.
//! Retained declarations are append-only. Base extension clears every entry;
//! a future operation that reorders that prefix must invalidate it as well.
//! Cached values also retain and recheck each exact preceding scoped handle.
use super::*;

#[derive(Clone)]
pub(super) struct MaterializedDefinition {
    index: usize,
    base_len: usize,
    original_type: Expr,
    original_value: Expr,
    prefix: Vec<ScopedLocal>,
    type_: Expr,
    value: Expr,
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::term_scope::TermScopeLimits;
    use clean_kernel::{Environment, Level, TypeChecker};

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

    fn environment() -> Environment {
        let mut env = Environment::new();
        env.init_nat().unwrap();
        env.init_eq().unwrap();
        env.init_true_false().unwrap();
        env
    }

    fn deferred_value(scope: &mut LocalScope, count: usize) -> Expr {
        let mut value = Expr::nat_lit(3);
        for _ in 0..count {
            let local = scope.try_local(n()).unwrap();
            value = local.let_(Expr::nat_lit(0), value);
        }
        value
    }

    #[test]
    fn explicit_owned_materialization_reuses_exact_data_and_keeps_complete_replay() {
        let env = environment();
        let mut scope = LocalScope::new();
        let value = deferred_value(&mut scope, 64);
        let mut parts = ProofComponents::new("materialized.definition", ProofLimits::default());
        parts.set_base(&scope, vec![]).unwrap();
        let definition = parts
            .bind_scoped_owned(&mut scope, &[], n(), value.clone())
            .unwrap();
        let (cold, _, before) = parts
            .untrusted_normalization_context_profiled(&scope, &[definition.reference.clone()])
            .unwrap();
        let materialized = parts
            .materialize_owned_definition(&scope, &definition.local)
            .unwrap();
        let after_first = parts.counts();
        assert_eq!(
            materialized,
            parts
                .materialize_owned_definition(&scope, &definition.local)
                .unwrap()
        );
        assert!(parts.counts().3 > after_first.3, "cache hits are charged");
        let (warm, _, after) = parts
            .untrusted_normalization_context_profiled(&scope, &[definition.reference.clone()])
            .unwrap();
        assert_eq!(before.cached_definition_visits, 0);
        assert!(after.cached_definition_visits > 0);
        assert!(after.materialization_visits < before.materialization_visits);
        assert!(after.total().unwrap() < before.total().unwrap());
        assert_eq!(
            TypeChecker::with_context(&env, cold).whnf(&definition.reference),
            TypeChecker::with_context(&env, warm).whnf(&definition.reference)
        );
        let claim = scope.close(&eq(value, Expr::nat_lit(3))).unwrap();
        let goal = eq(definition.reference.clone(), Expr::nat_lit(3));
        let bundle = parts
            .close_scoped(
                &scope,
                refl(definition.reference),
                goal,
                TermScopeLimits::default(),
            )
            .unwrap();
        let wire = bundle.encode_with_claim(&claim).unwrap();
        let (decoded, transported) = ScopedProofComponentBundle::decode_with_claim(&wire).unwrap();
        assert_eq!(transported, claim);
        decoded.replay(&env, &claim, 2_000_000).unwrap();
        eprintln!("owned definition context cold={before:?}; warm={after:?}");
    }

    #[test]
    fn materialized_definition_preserves_dynamic_parameter_telescope_and_replay() {
        let env = environment();
        let mut wires = Vec::new();
        for warm in [false, true] {
            let mut scope = LocalScope::new();
            let input = scope.try_local(n()).unwrap();
            let mut parts = ProofComponents::new("materialized.dynamic", ProofLimits::default());
            parts.set_base(&scope, vec![]).unwrap();
            let definition = parts
                .bind_scoped_owned(
                    &mut scope,
                    &[OwnedProofCapture::Parameter(input.clone())],
                    n(),
                    input.term().clone(),
                )
                .unwrap();
            assert_eq!(definition.reference.get_app_num_args(), 1);
            if warm {
                let materialized = parts
                    .materialize_owned_definition(&scope, &definition.local)
                    .unwrap();
                assert_eq!(
                    materialized,
                    scope.close(&input.lam(input.term().clone())).unwrap()
                );
            }
            let (context, _, work) = parts
                .untrusted_normalization_context_profiled(
                    &scope,
                    &[definition.local.term().clone()],
                )
                .unwrap();
            assert_eq!(work.cached_definition_visits > 0, warm);
            assert_eq!(
                TypeChecker::with_context(&env, context).whnf(&Expr::app(
                    definition.local.term().clone(),
                    Expr::nat_lit(3),
                )),
                Expr::nat_lit(3)
            );
            let claim = scope
                .close(&input.pi(eq(input.term().clone(), input.term().clone())))
                .unwrap();
            let bundle = parts
                .close_scoped(
                    &scope,
                    input.lam(refl(input.term().clone())),
                    input.pi(eq(definition.reference, input.term().clone())),
                    TermScopeLimits::default(),
                )
                .unwrap();
            let wire = bundle.encode_with_claim(&claim).unwrap();
            let (decoded, transported) =
                ScopedProofComponentBundle::decode_with_claim(&wire).unwrap();
            assert_eq!(transported, claim);
            decoded.replay(&env, &claim, 2_000_000).unwrap();
            wires.push(wire);
        }
        assert_eq!(wires[0], wires[1]);
    }

    #[test]
    fn interleaved_materialized_definitions_preserve_context_and_complete_wire() {
        fn padded(scope: &mut LocalScope, mut body: Expr, count: usize) -> Expr {
            for _ in 0..count {
                let unused = scope.try_local(n()).unwrap();
                body = unused.let_(Expr::nat_lit(0), body);
            }
            body
        }
        fn succ(value: Expr) -> Expr {
            Expr::app(Expr::const_str("Nat.succ"), value)
        }

        let env = environment();
        for correct in [true, false] {
            let mut results = Vec::new();
            for warm in [false, true] {
                let mut scope = LocalScope::new();
                let input = scope.try_local(n()).unwrap();
                let mut parts =
                    ProofComponents::new("materialized.interleaved", ProofLimits::default());
                parts
                    .set_base(&scope, vec![OwnedProofCapture::Parameter(input.clone())])
                    .unwrap();

                // Exact retained order: base input, cached first, uncached middle,
                // cached last. Both cached and uncached definitions are needed.
                let first_value = padded(&mut scope, input.term().clone(), 32);
                let first = parts
                    .bind_scoped_owned(&mut scope, &[], n(), first_value)
                    .unwrap();
                let middle = parts
                    .bind_scoped_owned(&mut scope, &[], n(), succ(first.reference.clone()))
                    .unwrap();
                let last_value = padded(&mut scope, succ(middle.reference.clone()), 48);
                let last = parts
                    .bind_scoped_owned(&mut scope, &[], n(), last_value)
                    .unwrap();
                if warm {
                    let _first = parts
                        .materialize_owned_definition(&scope, &first.local)
                        .unwrap();
                    let _last = parts
                        .materialize_owned_definition(&scope, &last.local)
                        .unwrap();
                    assert_eq!(parts.materialized_definitions.len(), 2);
                    assert!(
                        parts
                            .materialized_definitions
                            .contains_key(&first.local.id())
                    );
                    assert!(
                        !parts
                            .materialized_definitions
                            .contains_key(&middle.local.id())
                    );
                    assert!(
                        parts
                            .materialized_definitions
                            .contains_key(&last.local.id())
                    );
                } else {
                    assert!(parts.materialized_definitions.is_empty());
                }

                let (context, _, work) = parts
                    .untrusted_normalization_context_profiled(&scope, &[last.reference.clone()])
                    .unwrap();
                let expected_middle = succ(input.term().clone());
                let expected_last = succ(expected_middle.clone());
                let wrong_last = succ(expected_last.clone());
                let checker = TypeChecker::with_context(&env, context);
                // Inspect all three declarations, not only the final reduction:
                // a shifted forest iterator must not accidentally pass by aliasing
                // two equal values or using a cached result in the wrong slot.
                assert!(checker.is_def_eq(&first.reference, input.term()));
                assert!(checker.is_def_eq(&middle.reference, &expected_middle));
                assert!(checker.is_def_eq(&last.reference, &expected_last));
                assert!(!checker.is_def_eq(&last.reference, &wrong_last));
                assert_eq!(work.cached_definition_visits > 0, warm);
                assert!(
                    work.materialization_visits > 0,
                    "base and middle remain cold"
                );

                let target = if correct {
                    expected_last.clone()
                } else {
                    wrong_last
                };
                let claim = scope
                    .close(&input.pi(eq(expected_last, target.clone())))
                    .unwrap();
                let bundle = parts
                    .close_scoped(
                        &scope,
                        input.lam(refl(last.reference.clone())),
                        eq(last.reference, target),
                        TermScopeLimits::default(),
                    )
                    .unwrap();
                let wire = bundle.encode_with_claim(&claim).unwrap();
                let (decoded, transported) =
                    ScopedProofComponentBundle::decode_with_claim(&wire).unwrap();
                assert_eq!(transported, claim);
                let replay = decoded.replay(&env, &claim, 2_000_000);
                if correct {
                    replay.unwrap();
                } else {
                    let error = replay
                        .err()
                        .expect("the changed target must fail complete kernel replay");
                    assert!(error.contains("TypeMismatch"));
                    assert!(!error.contains("BudgetExhausted"));
                }
                results.push((work, wire));
            }
            assert_eq!(
                results[0].1, results[1].1,
                "cache state is absent from the wire"
            );
            assert_eq!(results[0].0.cached_definition_visits, 0);
            assert!(results[1].0.cached_definition_visits > 0);
            assert!(results[1].0.materialization_visits < results[0].0.materialization_visits);
        }
    }

    #[test]
    fn materialized_definition_rejects_foreign_component_and_scope_owners() {
        let mut scope = LocalScope::new();
        let mut owner = ProofComponents::new("materialized.owner", ProofLimits::default());
        let mut peer = ProofComponents::new("materialized.peer", ProofLimits::default());
        owner.set_base(&scope, vec![]).unwrap();
        peer.set_base(&scope, vec![]).unwrap();
        let definition = owner
            .bind_scoped_owned(&mut scope, &[], n(), Expr::nat_lit(1))
            .unwrap();
        assert!(
            peer.materialize_owned_definition(&scope, &definition.local)
                .unwrap_err()
                .contains("not retained")
        );
        peer.extend_base_definition(OwnedProofCapture::Definition {
            local: definition.local.clone(),
            value: Arc::new(Expr::nat_lit(1)),
        })
        .unwrap();
        assert!(
            peer.materialize_owned_definition(&scope, &definition.local)
                .unwrap_err()
                .contains("not retained"),
            "visibility in another component's base does not transfer ownership"
        );
        let foreign = LocalScope::new();
        assert!(
            owner
                .materialize_owned_definition(&foreign, &definition.local)
                .unwrap_err()
                .contains("scope owner")
        );
        assert!(owner.materialized_definitions.is_empty());
        assert!(peer.materialized_definitions.is_empty());
    }

    #[test]
    fn materialized_definition_rejects_missing_prefix_and_stale_original_body() {
        let mut scope = LocalScope::new();
        let missing = scope.try_local(n()).unwrap();
        let mut parts = ProofComponents::new("materialized.prefix", ProofLimits::default());
        parts.set_base(&scope, vec![]).unwrap();
        let invalid = parts
            .bind_scoped_owned(&mut scope, &[], n(), missing.term().clone())
            .unwrap();
        assert!(
            parts
                .materialize_owned_definition(&scope, &invalid.local)
                .is_err()
        );
        assert!(parts.materialized_definitions.is_empty());
        let good = parts
            .bind_scoped_owned(&mut scope, &[], n(), Expr::nat_lit(3))
            .unwrap();
        let _materialized = parts
            .materialize_owned_definition(&scope, &good.local)
            .unwrap();
        parts.bindings.last_mut().unwrap().1 = Expr::nat_lit(4);
        assert!(
            parts
                .materialize_owned_definition(&scope, &good.local)
                .unwrap_err()
                .contains("stale")
        );
        assert!(
            parts
                .untrusted_normalization_context_profiled(&scope, &[good.reference])
                .err()
                .expect("a changed original body must not reuse an older result")
                .contains("stale")
        );
    }

    #[test]
    fn base_extension_invalidates_materialized_prefix_and_loose_bvars_never_enter() {
        let mut scope = LocalScope::new();
        let mut parts = ProofComponents::new("materialized.base", ProofLimits::default());
        parts.set_base(&scope, vec![]).unwrap();
        let value = deferred_value(&mut scope, 4);
        let definition = parts
            .bind_scoped_owned(&mut scope, &[], n(), value)
            .unwrap();
        let _materialized = parts
            .materialize_owned_definition(&scope, &definition.local)
            .unwrap();
        let new_base = scope.try_local(n()).unwrap();
        parts
            .extend_base(OwnedProofCapture::Parameter(new_base))
            .unwrap();
        assert!(parts.materialized_definitions.is_empty());
        let _materialized = parts
            .materialize_owned_definition(&scope, &definition.local)
            .unwrap();
        let bad = parts
            .bind_scoped_owned(&mut scope, &[], n(), Expr::bvar(0))
            .unwrap();
        assert!(
            parts
                .materialize_owned_definition(&scope, &bad.local)
                .is_err()
        );
        assert!(!parts.materialized_definitions.contains_key(&bad.local.id()));
    }

    #[test]
    fn materialized_invalid_body_still_fails_complete_kernel_replay() {
        let mut scope = LocalScope::new();
        let mut parts = ProofComponents::new("materialized.invalid", ProofLimits::default());
        parts.set_base(&scope, vec![]).unwrap();
        let definition = parts
            .bind_scoped_owned(&mut scope, &[], n(), Expr::const_str("True.intro"))
            .unwrap();
        for _ in 0..2 {
            let _materialized = parts
                .materialize_owned_definition(&scope, &definition.local)
                .unwrap();
        }
        let claim = Expr::const_str("True");
        let bundle = parts
            .close_scoped(
                &scope,
                Expr::const_str("True.intro"),
                claim.clone(),
                TermScopeLimits::default(),
            )
            .unwrap();
        let wire = bundle.encode_with_claim(&claim).unwrap();
        let (decoded, _) = ScopedProofComponentBundle::decode_with_claim(&wire).unwrap();
        let error = decoded
            .replay(&environment(), &claim, 2_000_000)
            .err()
            .expect("the original invalid definition must reach the kernel");
        assert!(error.contains("TypeMismatch") && !error.contains("BudgetExhausted"));
    }

    #[test]
    fn materialized_definition_rechecks_the_exact_preceding_scope() {
        let mut scope = LocalScope::new();
        let mut parts = ProofComponents::new("materialized.preceding", ProofLimits::default());
        parts.set_base(&scope, vec![]).unwrap();
        let first = parts
            .bind_scoped_owned(&mut scope, &[], n(), Expr::nat_lit(3))
            .unwrap();
        let second = parts
            .bind_scoped_owned(&mut scope, &[], n(), first.reference)
            .unwrap();
        let _materialized = parts
            .materialize_owned_definition(&scope, &second.local)
            .unwrap();
        // Exercise a stale internal prefix directly. No public builder method
        // mutates preceding bindings, but even this cannot authorize a hit.
        parts.bindings[0].0 = scope.try_local(n()).unwrap();
        assert!(
            parts
                .materialize_owned_definition(&scope, &second.local)
                .unwrap_err()
                .contains("preceding scope")
        );
        assert!(
            parts
                .untrusted_normalization_context_profiled(&scope, &[second.reference])
                .is_err()
        );
    }

    #[test]
    fn materialized_definition_keeps_depth_work_and_self_reference_refusals() {
        let mut narrow = LocalScope::with_limits(crate::scoped_local::LocalScopeLimits {
            closing: TermScopeLimits {
                max_depth: 8,
                max_visits: 10_000,
            },
            ..Default::default()
        });
        let value = deferred_value(&mut narrow, 20);
        let mut parts = ProofComponents::new("materialized.depth", ProofLimits::default());
        parts.set_base(&narrow, vec![]).unwrap();
        let deep = parts
            .bind_scoped_owned(&mut narrow, &[], n(), value)
            .unwrap();
        let before = parts.counts().3;
        assert!(
            parts
                .materialize_owned_definition(&narrow, &deep.local)
                .is_err()
        );
        assert!(parts.counts().3 > before);
        assert!(parts.materialized_definitions.is_empty());

        let mut scope = LocalScope::new();
        let mut parts = ProofComponents::new(
            "materialized.budget",
            ProofLimits {
                operations: 256,
                ..Default::default()
            },
        );
        parts.set_base(&scope, vec![]).unwrap();
        let good = parts
            .bind_scoped_owned(&mut scope, &[], n(), Expr::nat_lit(3))
            .unwrap();
        let _materialized = parts
            .materialize_owned_definition(&scope, &good.local)
            .unwrap();
        parts
            .spend_context_work(parts.context_work_remaining().unwrap())
            .unwrap();
        assert!(
            parts
                .materialize_owned_definition(&scope, &good.local)
                .is_err()
        );

        let mut scope = LocalScope::new();
        let mut parts = ProofComponents::new("materialized.self", ProofLimits::default());
        parts.set_base(&scope, vec![]).unwrap();
        let self_id = FVarId::new(0);
        let bad = parts
            .bind_scoped_owned(&mut scope, &[], n(), Expr::fvar(self_id))
            .unwrap();
        assert_eq!(bad.local.id(), self_id);
        assert!(
            parts
                .materialize_owned_definition(&scope, &bad.local)
                .is_err()
        );
        assert!(parts.materialized_definitions.is_empty());
    }

    #[test]
    fn materialized_definition_does_not_capture_an_outer_bvar_with_a_named_binder() {
        let mut scope = LocalScope::new();
        let mut parts = ProofComponents::new("materialized.named.bvar", ProofLimits::default());
        parts.set_base(&scope, vec![]).unwrap();
        let argument = scope.try_local(n()).unwrap();
        let named = parts
            .bind_scoped_owned(
                &mut scope,
                &[],
                Expr::arrow(n(), n()),
                argument.lam(Expr::bvar(0)),
            )
            .unwrap();
        assert!(
            parts
                .materialize_owned_definition(&scope, &named.local)
                .unwrap_err()
                .contains("loose ordinary")
        );
        let ordinary = parts
            .bind_scoped_owned(
                &mut scope,
                &[],
                Expr::arrow(n(), n()),
                Expr::lam(clean_kernel::BinderInfo::Default, n(), Expr::bvar(0)),
            )
            .unwrap();
        let closed = parts
            .materialize_owned_definition(&scope, &ordinary.local)
            .unwrap();
        assert!(!closed.has_loose_bvars());
        assert!(
            !parts
                .materialized_definitions
                .contains_key(&named.local.id())
        );
    }
}

impl ProofComponents {
    /// Materialize the exact retained declaration, including its dynamic
    /// capture telescope, under its actual preceding component scope.
    ///
    /// The first closure and every later lookup spend the existing component
    /// work budget. Subsequent projected normalization may reuse this result
    /// with charged identity checks. This supplies no typechecking, equation,
    /// opacity or admission: all original bodies remain in complete replay.
    pub fn materialize_owned_definition(
        &mut self,
        scope: &LocalScope,
        local: &ScopedLocal,
    ) -> Result<Expr, String> {
        self.spend_context_work(1)?;
        if !self
            .owner
            .as_ref()
            .is_some_and(|owner| owner.matches(&scope.memo_owner()))
            || !scope.owns(local)
        {
            return Err("materialized definition has another scope owner".into());
        }
        let mut found = None;
        for index in 0..self.bindings.len() {
            self.spend_context_work(1)?;
            if self.bindings[index].0.id() == local.id() {
                found = Some(index);
                break;
            }
        }
        let index = found.ok_or("materialized definition is not retained by this component")?;
        let (actual, value) = self.bindings[index].clone();
        if !same_graph(actual.ty(), local.ty()) {
            return Err("materialized definition has another retained type".into());
        }
        let mut lookup_work = 0;
        let cached =
            self.cached_materialized_definition(scope, index, &actual, &value, &mut lookup_work);
        self.spend_context_work(lookup_work)?;
        if let Some((_, value)) = cached? {
            return Ok(value);
        }
        let mut external = self
            .base
            .iter()
            .map(|capture| capture.local().clone())
            .collect::<Vec<_>>();
        external.extend(
            self.bindings[..index]
                .iter()
                .map(|(local, _)| local.clone()),
        );
        let roots = [actual.ty().clone(), value.clone()];
        let mut materialized =
            self.charged_materialize_forest(scope, &external, &roots, &[external.len(); 2])?;
        let value_ = materialized
            .pop()
            .ok_or("materialized definition lost value")?;
        let type_ = materialized
            .pop()
            .ok_or("materialized definition lost type")?;
        if !materialized.is_empty() {
            return Err("materialized definition has extra roots".into());
        }
        // General TermScope closing deliberately preserves an outer ordinary
        // BVar context. A retained top-level declaration has no such context.
        // Check after closing too: a named binder must not capture BVar(0).
        if type_.has_loose_bvars() || value_.has_loose_bvars() {
            return Err("materialized definition retains loose ordinary bound variables".into());
        }
        self.materialized_definitions.insert(
            local.id(),
            MaterializedDefinition {
                index,
                base_len: self.base.len(),
                original_type: actual.ty().clone(),
                original_value: value,
                prefix: external,
                type_,
                value: value_.clone(),
            },
        );
        Ok(value_)
    }

    pub(super) fn cached_materialized_definition(
        &self,
        scope: &LocalScope,
        index: usize,
        local: &ScopedLocal,
        value: &Expr,
        work: &mut usize,
    ) -> Result<Option<(Expr, Expr)>, String> {
        let charge = |work: &mut usize, amount: usize| -> Result<(), String> {
            *work = work
                .checked_add(amount)
                .filter(|total| *total <= self.limits.operations)
                .ok_or("materialized definition lookup work limit")?;
            Ok(())
        };
        charge(work, 1)?;
        let Some(cached) = self.materialized_definitions.get(&local.id()) else {
            return Ok(None);
        };
        charge(work, 9)?;
        let Some((actual, actual_value)) = self.bindings.get(index) else {
            return Err("materialized definition lost its retained declaration".into());
        };
        if !self
            .owner
            .as_ref()
            .is_some_and(|owner| owner.matches(&scope.memo_owner()))
            || !scope.owns(local)
            || cached.index != index
            || cached.base_len != self.base.len()
            || cached.prefix.len() != self.base.len().saturating_add(index)
            || actual.id() != local.id()
            || !same_graph(actual.ty(), local.ty())
            || !same_graph(actual_value, value)
            || !same_graph(&cached.original_type, local.ty())
            || !same_graph(&cached.original_value, value)
        {
            return Err("materialized definition has stale owner, prefix or body".into());
        }
        let prefix = self
            .base
            .iter()
            .map(OwnedProofCapture::local)
            .chain(self.bindings.iter().take(index).map(|(local, _)| local));
        for (old, current) in cached.prefix.iter().zip(prefix) {
            charge(work, 3)?;
            if !scope.owns(current)
                || old.id() != current.id()
                || !same_graph(old.ty(), current.ty())
            {
                return Err("materialized definition has a changed preceding scope".into());
            }
        }
        Ok(Some((cached.type_.clone(), cached.value.clone())))
    }
}
