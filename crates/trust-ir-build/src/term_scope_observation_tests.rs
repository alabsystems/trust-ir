// Copyright 2026 Andrew Yates | Licensed under the Apache License, Version 2.0

//! Observations cannot change closure, scope errors, limits, or proof authority.

use super::*;
use clean_kernel::{BinderInfo, Environment, KernelTypeError, Level, TypeChecker};

fn id(raw: u64) -> FVarId {
    FVarId::new(raw)
}
fn nat() -> Expr {
    Expr::const_str("Nat")
}
fn ordinary(body: Expr) -> Expr {
    Expr::lam(BinderInfo::Default, nat(), body)
}
fn wrap(scope: &mut TermScope, names: &[u64], ordinary_count: usize, shared: &Arc<Expr>) -> Expr {
    // The inspected input remains an actual shared child, not a copied body root.
    let mut term = Expr::app_arc(Arc::new(Expr::const_str("Nat.succ")), shared.clone());
    for raw in names.iter().rev() {
        term = scope.lam(id(*raw), BinderInfo::Default, nat(), term);
    }
    for _ in 0..ordinary_count {
        term = ordinary(term);
    }
    term
}
fn partition(report: &TermScopeCloseReport) {
    let cache = report.diagnostics.cache;
    assert_eq!(
        cache.successful_dependency_probe_visits + cache.rejected_dependency_probe_visits,
        report.stats.context_check_visits
    );
    assert_eq!(
        cache.successful_declaration_probe_visits + cache.rejected_declaration_probe_visits,
        report.stats.scope_check_visits
    );
    assert_eq!(
        cache.ordinary_closed_hits
            + cache.exact_context_hits
            + cache.named_closed_hits
            + cache.contextual_hits,
        report.stats.memo_hits
    );
}
fn parity(scope: &TermScope, input: &Expr, limits: TermScopeLimits) -> TermScopeCloseReport {
    let mut plain = Closer::new(scope, limits, false);
    assert!(plain.observations.is_none());
    let term = input.fold_opt_or_clone(&mut plain);
    let result = plain.error.clone().map_or(Ok(term), Err);
    assert!(plain.observations.is_none());
    assert!(plain.diagnostic_report().first_stop.is_none());
    assert_eq!(
        plain.diagnostic_report().cache,
        TermScopeCacheDiagnostics::default()
    );
    let observed = scope.close_with_diagnostics(input, limits);
    assert_eq!(observed.result, result);
    assert_eq!(observed.stats, plain.stats);
    assert_eq!(
        scope
            .close_with_limits(input, limits)
            .map(|closed| closed.term),
        result
    );
    partition(&observed);
    if observed.result.is_ok() {
        assert!(observed.diagnostics.first_stop.is_none());
    } else {
        let stop = observed
            .diagnostics
            .first_stop
            .as_ref()
            .expect("one refusal record");
        assert_eq!(Some(&stop.error), observed.result.as_ref().err());
        assert_eq!(stop.charged_visits, observed.stats.visits);
    }
    observed
}
#[test]
fn declaration_free_screening_counts_same_depth_without_authorizing_reuse() {
    let mut scope = TermScope::new();
    let shared = Arc::new(Expr::app(Expr::const_str("Nat.succ"), Expr::fvar(id(1))));
    let first = wrap(&mut scope, &[1, 2], 0, &shared);
    let second = wrap(&mut scope, &[1], 1, &shared);
    let input = Expr::apps(Expr::const_str("structural"), [first, second]);
    let report = parity(&scope, &input, TermScopeLimits::default());
    assert!(
        report
            .diagnostics
            .cache
            .declaration_free_same_depth_shape_misses
            > 0
    );
    assert!(
        report
            .diagnostics
            .cache
            .declaration_free_primary_shape_misses
            > 0
    );
    let body = |index| {
        ordinary(ordinary(Expr::app(
            Expr::const_str("Nat.succ"),
            Expr::app(Expr::const_str("Nat.succ"), Expr::bvar(index)),
        )))
    };
    assert_eq!(
        report.result.unwrap(),
        Expr::apps(Expr::const_str("structural"), [body(1), body(0)]),
        "same depth and no declarations are not a named-dependency check"
    );
    for cap in 0..=report.stats.visits {
        parity(
            &scope,
            &input,
            TermScopeLimits {
                max_visits: cap,
                ..TermScopeLimits::default()
            },
        );
    }
}

#[test]
fn declaration_free_screening_observes_both_slots_and_depth_directions() {
    let mut scope = TermScope::new();
    let shared = Arc::new(Expr::app(Expr::const_str("Nat.succ"), Expr::fvar(id(1))));
    let first = wrap(&mut scope, &[1, 2, 3], 0, &shared);
    let second = wrap(&mut scope, &[1, 4], 0, &shared);
    let third = wrap(&mut scope, &[1, 5, 6, 7], 0, &shared);
    let input = Expr::apps(Expr::const_str("structural"), [first, second, third]);
    let report = parity(&scope, &input, TermScopeLimits::default());
    let cache = report.diagnostics.cache;
    assert!(cache.declaration_free_primary_shape_misses > 0);
    assert!(cache.declaration_free_spare_shape_misses > 0);
    assert!(cache.declaration_free_outward_shape_misses > 0);
    assert!(cache.declaration_free_inward_shape_misses > 0);
    assert_eq!(cache.declaration_free_same_depth_shape_misses, 0);
    assert_eq!(
        cache.dependency_shape_rejections, 0,
        "no new probe was performed"
    );
    for cap in 0..=report.stats.visits {
        parity(
            &scope,
            &input,
            TermScopeLimits {
                max_visits: cap,
                ..TermScopeLimits::default()
            },
        );
    }
}

#[test]
fn declaration_free_screening_excludes_hidden_named_binders_and_original_loose_reads() {
    for hidden_named in [false, true] {
        let mut scope = TermScope::new();
        let body = if hidden_named {
            scope.lam(id(9), BinderInfo::Default, nat(), Expr::bvar(0))
        } else {
            Expr::app(Expr::const_str("Nat.succ"), Expr::bvar(9))
        };
        assert_eq!(body.has_loose_bvars_quick(), !hidden_named);
        let shared = Arc::new(body);
        let first = wrap(&mut scope, &[1, 2], 1, &shared);
        let second = wrap(&mut scope, &[1], 0, &shared);
        let input = Expr::apps(Expr::const_str("structural"), [first, second]);
        let report = parity(&scope, &input, TermScopeLimits::default());
        assert!(report.result.is_ok());
        let cache = report.diagnostics.cache;
        assert!(cache.contextual_shape_misses > 0);
        if hidden_named {
            assert!(cache.shape_misses_without_loose_bvars > 0);
        }
        assert_eq!(cache.declaration_free_primary_shape_misses, 0);
        assert_eq!(cache.declaration_free_spare_shape_misses, 0);
        assert_eq!(cache.declaration_free_same_depth_shape_misses, 0);
        assert_eq!(cache.declaration_free_outward_shape_misses, 0);
        assert_eq!(cache.declaration_free_inward_shape_misses, 0);
        for cap in 0..=report.stats.visits {
            parity(
                &scope,
                &input,
                TermScopeLimits {
                    max_visits: cap,
                    ..TermScopeLimits::default()
                },
            );
        }
    }
}

#[test]
fn observations_keep_plain_observer_absent_and_classify_direct_cache_routes() {
    let mut scope = TermScope::new();
    let data = Arc::new(Expr::app(Expr::const_str("Nat.succ"), Expr::nat_lit(0u64)));
    let below = wrap(&mut scope, &[1], 0, &data);
    let report = parity(
        &scope,
        &Expr::app_arc(data, Arc::new(below)),
        TermScopeLimits::default(),
    );
    assert!(report.diagnostics.cache.ordinary_closed_hits > 0);
    let leaf = Arc::new(Expr::fvar(id(1)));
    let repeated = Expr::app_arc(leaf.clone(), leaf);
    let open = scope.lam(id(1), BinderInfo::Default, nat(), repeated);
    let report = parity(&scope, &open, TermScopeLimits::default());
    assert!(report.diagnostics.cache.exact_context_hits > 0);
    let helper = Arc::new(scope.lam(id(9), BinderInfo::Default, nat(), Expr::fvar(id(9))));
    let below = wrap(&mut scope, &[1], 0, &helper);
    let open = Expr::app_arc(helper, Arc::new(below));
    let report = parity(&scope, &open, TermScopeLimits::default());
    assert!(report.diagnostics.cache.named_closed_hits > 0);
    assert!(report.diagnostics.cache.successful_declaration_probe_visits > 0);
}

#[test]
fn observations_classify_primary_spare_and_shape_misses_on_actual_shared_edges() {
    let mut scope = TermScope::new();
    let shared = Arc::new(Expr::app(Expr::const_str("Nat.succ"), Expr::fvar(id(1))));
    let frames: &[&[u64]] = &[&[1, 2], &[1, 3, 4], &[1, 5], &[6, 1], &[1, 7, 8], &[9, 1]];
    let arms = frames
        .iter()
        .map(|names| wrap(&mut scope, names, 0, &shared))
        .collect::<Vec<_>>();
    let open = Expr::apps(Expr::const_str("structural"), arms);
    let report = parity(&scope, &open, TermScopeLimits::default());
    let expected = frames
        .iter()
        .zip([1, 2, 1, 0, 2, 0])
        .map(|(names, index)| {
            let mut body = Expr::app(
                Expr::const_str("Nat.succ"),
                Expr::app(Expr::const_str("Nat.succ"), Expr::bvar(index)),
            );
            for _ in *names {
                body = ordinary(body);
            }
            body
        })
        .collect::<Vec<_>>();
    assert_eq!(
        report.result.unwrap(),
        Expr::apps(Expr::const_str("structural"), expected)
    );
    let cache = report.diagnostics.cache;
    assert!(cache.primary_exact_attempts > 0 && cache.spare_exact_attempts > 0);
    assert!(cache.contextual_hits > 0 && cache.contextual_shape_misses > 0);
    assert!(cache.shape_misses_without_loose_bvars > 0);
    assert!(cache.named_dependency_moved > 0 && cache.rejected_dependency_probe_visits > 0);
}

#[test]
fn observations_classify_outward_routes_without_capturing_loose_indices() {
    let mut scope = TermScope::new();
    let shared = Arc::new(Expr::app(Expr::fvar(id(1)), Expr::bvar(9)));
    let frames: &[(&[u64], usize)] = &[(&[1], 4), (&[1, 2], 4), (&[1], 2), (&[1], 1)];
    let arms = frames
        .iter()
        .map(|(names, count)| wrap(&mut scope, names, *count, &shared))
        .collect::<Vec<_>>();
    let report = parity(
        &scope,
        &Expr::apps(Expr::const_str("structural"), arms),
        TermScopeLimits::default(),
    );
    let expected = frames
        .iter()
        .map(|(names, count)| {
            let mut body = Expr::app(
                Expr::const_str("Nat.succ"),
                Expr::app(
                    Expr::bvar((names.len() - 1) as u32),
                    Expr::bvar(9 + names.len() as u32),
                ),
            );
            for _ in 0..names.len() + *count {
                body = ordinary(body);
            }
            body
        })
        .collect::<Vec<_>>();
    let closed = report.result.unwrap();
    assert_eq!(closed, Expr::apps(Expr::const_str("structural"), expected));
    assert!(
        closed.has_loose_bvars_quick(),
        "this is a structural fixture, not a closed theorem"
    );
    let cache = report.diagnostics.cache;
    assert!(cache.primary_outward_attempts > 0 && cache.spare_outward_attempts > 0);
    assert!(cache.contextual_hits > 0 && cache.successful_dependency_probe_visits > 0);
    // D6/O5 -> D4/O3 -> D2/O1: the last primary's low minimum now screens;
    // the retained spare is only shape-observed, never selected or probed.
    let shared = Arc::new(Expr::app(Expr::const_str("Nat.succ"), Expr::fvar(id(1))));
    let first = wrap(&mut scope, &[1], 5, &shared);
    let mut middle = wrap(&mut scope, &[], 3, &shared);
    middle = scope.lam(id(1), BinderInfo::Default, nat(), middle);
    let last = wrap(&mut scope, &[1], 1, &shared);
    let input = Expr::apps(Expr::const_str("structural"), [first, middle, last]);
    let report = parity(&scope, &input, TermScopeLimits::default());
    let cache = report.diagnostics.cache;
    assert!(cache.rejected_contextual_with_alternate_shape > 0);
    assert!(cache.ordinary_depth_screen_rejections > 0);
    assert_eq!(cache.dependency_rebase_underflow, 0);
    assert!(cache.primary_outward_attempts > 0);
    assert_eq!(cache.spare_outward_attempts, 0);
    let observed = report.result.unwrap();
    let plain = scope.close(&input).unwrap();
    let mut env = Environment::new();
    env.init_nat().unwrap();
    fn child(mut term: &Expr, depth: usize) -> &Arc<Expr> {
        for _ in 0..depth {
            let ExprKind::Lam(_, _, body) = term.kind() else {
                panic!("actual binder")
            };
            term = body;
        }
        let ExprKind::App(_, child) = term.kind() else {
            panic!("actual shared child")
        };
        child
    }
    for closed in [&plain, &observed] {
        let arms = closed.get_app_args();
        assert_eq!(child(arms[0], 6), child(arms[2], 2));
        // Independent rebuilds now share completed output nodes. The original
        // spare-attempt/probe assertions below still prohibit a candidate retry.
        assert!(Arc::ptr_eq(child(arms[0], 6), child(arms[2], 2)));
        assert!(cache.output_node_intern_hits > 0);
        for (arm, depth) in arms.into_iter().zip([6, 4, 2]) {
            let mut ty = nat();
            for _ in 0..depth {
                ty = Expr::arrow(nat(), ty);
            }
            let mut checker = TypeChecker::new(&env);
            checker.set_allow_unsafe(false);
            checker.set_allow_partial(false);
            checker.check_type(arm, &ty).unwrap();
        }
    }
}

#[test]
fn observations_reject_missing_named_and_moved_ordinary_dependencies() {
    let mut scope = TermScope::new();
    let shared = Arc::new(Expr::fvar(id(1)));
    let good = wrap(&mut scope, &[1, 2], 0, &shared);
    let missing = wrap(&mut scope, &[3, 4], 0, &shared);
    let report = parity(
        &scope,
        &Expr::app(good, missing),
        TermScopeLimits::default(),
    );
    assert_eq!(report.result, Err(TermScopeError::OutOfScope(id(1))));
    assert!(report.diagnostics.cache.named_dependency_missing > 0);
    let loose = Arc::new(Expr::bvar(0));
    let left_body = ordinary(Expr::app_arc(loose.clone(), loose.clone()));
    let left = scope.lam(id(7), BinderInfo::Default, nat(), left_body);
    let right_body = Expr::app_arc(loose.clone(), loose);
    let right = scope.lam(id(8), BinderInfo::Default, nat(), right_body);
    let report = parity(
        &scope,
        &Expr::app(left, ordinary(right)),
        TermScopeLimits::default(),
    );
    assert_eq!(
        report.result.unwrap(),
        Expr::app(
            ordinary(ordinary(Expr::app(Expr::bvar(0), Expr::bvar(0)))),
            ordinary(ordinary(Expr::app(Expr::bvar(1), Expr::bvar(1)))),
        )
    );
    assert!(report.diagnostics.cache.ordinary_dependency_moved > 0);
}

#[test]
fn observations_keep_hidden_declarations_and_first_error_order() {
    for typed in [false, true] {
        let mut scope = TermScope::new();
        let hidden = scope.lam(
            id(9),
            BinderInfo::Default,
            if typed { Expr::fvar(id(100)) } else { nat() },
            Expr::fvar(id(1)),
        );
        let shared = Arc::new(hidden);
        let warm = if typed { &[100, 1][..] } else { &[1, 2][..] };
        let first = wrap(&mut scope, warm, 0, &shared);
        let last = wrap(&mut scope, &[1, 9], 0, &shared);
        let report = parity(&scope, &Expr::app(first, last), TermScopeLimits::default());
        let error = if typed {
            TermScopeError::OutOfScope(id(100))
        } else {
            TermScopeError::ShadowedLocal(id(9))
        };
        assert_eq!(report.result, Err(error.clone()));
        let stop = report.diagnostics.first_stop.unwrap();
        assert_eq!(stop.error, error);
        assert_eq!(
            stop.phase,
            if typed {
                TermScopeStopPhase::Expression
            } else {
                TermScopeStopPhase::BinderEntry
            }
        );
        assert!(
            stop.candidate.is_none(),
            "fallback errors must not inherit a probe's candidate"
        );
        if !typed {
            assert!(report.diagnostics.cache.declaration_collisions > 0);
            assert!(report.diagnostics.cache.rejected_declaration_probe_visits > 0);
        }
    }
}

fn joined_outward() -> (TermScope, Expr) {
    let mut scope = TermScope::new();
    let shared = Arc::new(Expr::app(Expr::fvar(id(1)), Expr::fvar(id(2))));
    let deep = wrap(&mut scope, &[1, 2], 1, &shared);
    let low = wrap(&mut scope, &[1, 2], 0, &shared);
    (scope, Expr::app(deep, low))
}

#[test]
fn observations_report_partial_rebase_growth_without_publishing_a_result() {
    let (scope, open) = joined_outward();
    let complete = parity(&scope, &open, TermScopeLimits::default());
    assert!(complete.result.is_ok());
    let mut saw_partial = false;
    for max_visits in 0..complete.stats.visits {
        let report = parity(
            &scope,
            &open,
            TermScopeLimits {
                max_visits,
                ..TermScopeLimits::default()
            },
        );
        assert_eq!(report.result, Err(TermScopeError::VisitLimit));
        if report.diagnostics.cache.failed_rebase_dependency_nodes > 0 {
            saw_partial = true;
            let stop = report.diagnostics.first_stop.unwrap();
            assert_eq!(stop.phase, TermScopeStopPhase::RelativeDependency);
            assert!(matches!(
                stop.candidate,
                Some(TermScopeCacheRoute::PrimaryOutward | TermScopeCacheRoute::SpareOutward)
            ));
            assert_eq!(stop.cached_binder_depth, Some(3));
            assert_eq!(stop.cached_ordinary_count, Some(1));
            assert!(report.diagnostics.cache.dependency_budget_rejections > 0);
            assert!(report.diagnostics.cache.rejected_dependency_probe_visits > 0);
        }
    }
    assert!(
        saw_partial,
        "the charged join must expose a refused partial rebase"
    );
}

#[test]
fn observations_preserve_every_visit_and_depth_boundary_and_probe_partition() {
    let mut scope = TermScope::new();
    let shared = Arc::new(Expr::fvar(id(1)));
    let left = wrap(&mut scope, &[2], 0, &shared);
    let right = wrap(&mut scope, &[3], 0, &shared);
    let open = scope.lam(id(1), BinderInfo::Default, nat(), Expr::app(left, right));
    let helper = Arc::new(scope.lam(id(9), BinderInfo::Default, nat(), Expr::fvar(id(9))));
    let below = wrap(&mut scope, &[8], 0, &helper);
    let declarations = Expr::app_arc(helper, Arc::new(below));
    let mut saw_exact = false;
    let mut saw_declaration = false;
    for input in [&open, &declarations] {
        let complete = parity(&scope, input, TermScopeLimits::default());
        assert!(complete.result.is_ok());
        for max_visits in 0..=complete.stats.visits {
            let report = parity(
                &scope,
                input,
                TermScopeLimits {
                    max_visits,
                    ..TermScopeLimits::default()
                },
            );
            assert_eq!(report.stats.visits, max_visits);
            if max_visits == complete.stats.visits {
                assert_eq!(report.result, complete.result);
                assert!(report.diagnostics.first_stop.is_none());
            } else {
                assert_eq!(report.result, Err(TermScopeError::VisitLimit));
                let stop = report.diagnostics.first_stop.unwrap();
                saw_exact |= stop.phase == TermScopeStopPhase::ExactDependency;
                saw_declaration |= stop.phase == TermScopeStopPhase::Declaration;
                if max_visits == 0 {
                    assert_eq!(stop.phase, TermScopeStopPhase::Expression);
                    assert_eq!(stop.last_charged_input_hash, None);
                    assert_eq!(report.diagnostics.distinct_input_nodes, 0);
                }
            }
        }
    }
    assert!(saw_exact && saw_declaration);
    let report = parity(
        &scope,
        &open,
        TermScopeLimits {
            max_depth: 0,
            ..TermScopeLimits::default()
        },
    );
    assert_eq!(report.result, Err(TermScopeError::DepthLimit));
    let stop = report.diagnostics.first_stop.unwrap();
    assert_eq!(stop.phase, TermScopeStopPhase::Expression);
    assert_eq!(stop.charged_visits, 1);
    assert_eq!(stop.walk_depth, 0);
    assert_eq!(stop.last_charged_input_hash, Some(open.hash_cached()));
}

#[test]
fn observations_preserve_strict_mixed_proof_and_lossless_dag_replay() {
    let mut scope = TermScope::new();
    let eq = |left, right| {
        Expr::apps(
            Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
            [nat(), left, right],
        )
    };
    let shared = Arc::new(Expr::apps(
        Expr::const_(
            Name::from_string("Eq.refl"),
            vec![Level::succ(Level::zero())],
        ),
        [nat(), Expr::fvar(id(1))],
    ));
    let mut arms = Vec::new();
    let mut oracle = Vec::new();
    for count in [3, 1] {
        let body = Expr::let_named(
            Name::from_string("retained_proof"),
            Expr::pi(
                BinderInfo::Default,
                nat(),
                eq(Expr::fvar(id(1)), Expr::fvar(id(1))),
            ),
            Expr::lam_arc(BinderInfo::Default, Arc::new(nat()), shared.clone()),
            Expr::app(Expr::bvar(0), Expr::nat_lit(0u64)),
            false,
        );
        let mut expected = Expr::app(ordinary(body.abstract_fvar(id(1))), Expr::nat_lit(0u64));
        let mut actual = Expr::app(
            scope.lam(id(1), BinderInfo::Default, nat(), body),
            Expr::nat_lit(0u64),
        );
        for _ in 0..count {
            actual = Expr::app(ordinary(actual), Expr::nat_lit(0u64));
            expected = Expr::app(ordinary(expected), Expr::nat_lit(0u64));
        }
        arms.push(actual);
        oracle.push(expected);
    }
    let trans = |arms: Vec<Expr>| {
        Expr::apps(
            Expr::const_(
                Name::from_string("Eq.trans"),
                vec![Level::succ(Level::zero())],
            ),
            [
                vec![
                    nat(),
                    Expr::nat_lit(0u64),
                    Expr::nat_lit(0u64),
                    Expr::nat_lit(0u64),
                ],
                arms,
            ]
            .concat(),
        )
    };
    let report = parity(&scope, &trans(arms), TermScopeLimits::default());
    let proof = report.result.unwrap();
    assert_eq!(proof, trans(oracle));
    assert!(!proof.has_fvar_quick() && !proof.has_loose_bvars_quick());
    assert!(report.diagnostics.cache.contextual_hits > 0);
    let bytes = trust_ir::proof::encode_clean_expr_dag_v2(&proof).unwrap();
    let decoded = trust_ir::proof::decode_clean_expr_dag_v2(&bytes).unwrap();
    assert_eq!(decoded, proof);
    assert_eq!(
        trust_ir::proof::encode_clean_expr_dag_v2(&decoded).unwrap(),
        bytes
    );
    let mut env = Environment::default();
    env.init_eq().unwrap();
    env.init_nat().unwrap();
    for candidate in [&proof, &decoded] {
        for (right, accepted) in [(0u64, true), (1u64, false)] {
            let claim = eq(Expr::nat_lit(0u64), Expr::nat_lit(right));
            let mut checker = TypeChecker::new(&env);
            checker.set_allow_unsafe(false);
            checker.set_allow_partial(false);
            checker.set_heartbeat_limit(2_000_000);
            let checked = checker.check_type(candidate, &claim);
            if accepted {
                checked.unwrap();
                let audit = env.audit_certification(&claim, candidate);
                assert!(audit.is_certified(), "{audit:#?}");
                for dependency in &audit.dependencies {
                    assert!(env.axiom_deps(dependency).unwrap().is_empty());
                    assert!(env.trust_marker_deps(dependency).unwrap().is_empty());
                }
            } else {
                assert!(matches!(checked, Err(KernelTypeError::TypeMismatch { .. })));
            }
            assert!(!checker.heartbeat_spent());
        }
    }
}
