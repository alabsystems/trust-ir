// Copyright 2026 Andrew Yates | Licensed under the Apache License, Version 2.0

//! Rejected contextual suffixes are private; accepted dependency IDs stay live.

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
fn add(left: Expr, right: Expr) -> Expr {
    Expr::apps(Expr::const_str("Nat.add"), [left, right])
}
fn value(x: Expr, stable: Expr, second_stable: Expr, y: Expr) -> Expr {
    // Three distinct reads retain genuine joins before moved y rejects even
    // when repeated named leaves are canonical. Do not pad the rollback
    // census with duplicate leaf allocations or relax its >8 assertion.
    let mut sum = x;
    for _ in 0..8 {
        sum = add(sum, stable.clone());
        sum = add(sum, second_stable.clone());
    }
    add(sum, y)
}
fn arm(scope: &mut TermScope, names: &[u64], count: usize, body: Expr) -> Expr {
    let mut result = body;
    for raw in names.iter().rev() {
        result = scope.lam(id(*raw), BinderInfo::Default, nat(), result);
    }
    for _ in 0..count {
        result = ordinary(result);
    }
    result
}
fn child_body(shared: &Arc<Expr>) -> Expr {
    Expr::app_arc(Arc::new(Expr::const_str("Nat.succ")), shared.clone())
}
fn proof_body(shared: &Arc<Expr>, value: Expr) -> Expr {
    let ty = eq(value.clone(), value);
    Expr::app_arc(
        Arc::new(Expr::lam(BinderInfo::Default, ty, Expr::bvar(0))),
        shared.clone(),
    )
}
fn apply_zeros(mut term: Expr, count: usize) -> Expr {
    for _ in 0..count {
        term = Expr::app(term, Expr::nat_lit(0u64));
    }
    term
}
fn compose(arms: Vec<Expr>) -> Expr {
    arms.into_iter()
        .reduce(|left, right| {
            Expr::apps(
                Expr::const_(
                    Name::from_string("Eq.trans"),
                    vec![Level::succ(Level::zero())],
                ),
                [
                    nat(),
                    Expr::nat_lit(0u64),
                    Expr::nat_lit(0u64),
                    Expr::nat_lit(0u64),
                    left,
                    right,
                ],
            )
        })
        .expect("nonempty proof chain")
}
fn leaves<'a>(proof: &'a Expr, count: usize, output: &mut Vec<&'a Expr>) {
    if count == 1 {
        output.push(proof);
    } else {
        let args = proof.get_app_args();
        assert_eq!(args.len(), 6);
        leaves(args[4], count - 1, output);
        output.push(args[5]);
    }
}
fn output_child(mut applied: &Expr, depth: usize) -> &Arc<Expr> {
    for _ in 0..depth {
        let ExprKind::App(function, _) = applied.kind() else {
            panic!("applied arm")
        };
        applied = function;
    }
    for _ in 0..depth {
        let ExprKind::Lam(_, _, body) = applied.kind() else {
            panic!("ordinary output binder")
        };
        applied = body;
    }
    let ExprKind::App(_, child) = applied.kind() else {
        panic!("actual shared proof root")
    };
    child
}
fn retained_ids(closer: &Closer<'_>) {
    let len = closer.dependencies.len();
    let check = |root: Option<usize>| assert!(root.is_none_or(|index| index < len));
    check(closer.dependency);
    for entry in closer.memo.values() {
        check(entry.dependencies());
    }
    for entry in closer.named_closed.values() {
        check(entry.entry.dependencies());
    }
    let (primary, spare) = closer.contextual.maps();
    for entry in primary.values().chain(spare.values()) {
        check(entry.entry.dependencies());
    }
    for (index, node) in closer.dependencies.iter().enumerate() {
        if let Dependency::Join(left, right) = node.dependency {
            assert!(
                left < index && right < index,
                "dependency edges must point backward"
            );
        }
    }
}
fn partition(closer: &Closer<'_>) {
    let cache = closer.diagnostic_report().cache;
    assert_eq!(
        cache.successful_dependency_probe_visits + cache.rejected_dependency_probe_visits,
        closer.stats.context_check_visits,
    );
    assert_eq!(
        cache.successful_declaration_probe_visits + cache.rejected_declaration_probe_visits,
        closer.stats.scope_check_visits,
    );
}

#[test]
fn rejected_rebases_preserve_later_outward_and_exact_proof_aliases() {
    let mut scope = TermScope::new();
    let source_value = value(
        Expr::fvar(id(1)),
        Expr::fvar(id(4)),
        Expr::fvar(id(5)),
        Expr::fvar(id(2)),
    );
    let shared = Arc::new(refl(source_value.clone()));
    let rows: &[(usize, &[u64])] = &[
        (5, &[1, 4, 5, 2, 3]),
        (4, &[1, 4, 5, 3, 2]),
        (3, &[1, 4, 5, 2, 3]),
        (2, &[1, 4, 5, 3, 2]),
        (1, &[1, 4, 5, 3, 2]),
        (0, &[1, 4, 5, 3, 2]),
        (4, &[1, 4, 5, 3, 2]),
    ];
    let mut actual = Vec::new();
    let mut expected = Vec::new();
    for (count, names) in rows {
        let body = proof_body(&shared, source_value.clone());
        actual.push(apply_zeros(arm(&mut scope, names, *count, body), count + 5));
        let y = if names[3] == 2 { 1 } else { 0 };
        let oracle_value = value(Expr::bvar(4), Expr::bvar(3), Expr::bvar(2), Expr::bvar(y));
        let oracle_shared = Arc::new(refl(oracle_value.clone()));
        let mut oracle = proof_body(&oracle_shared, oracle_value);
        for _ in 0..count + 5 {
            oracle = ordinary(oracle);
        }
        expected.push(apply_zeros(oracle, count + 5));
    }
    let input = compose(actual);
    let mut closer = Closer::new(&scope, TermScopeLimits::default(), true);
    let proof = input.fold_opt_or_clone(&mut closer);
    assert!(closer.error.is_none());
    assert_eq!(
        proof,
        compose(expected),
        "independent ordinary-binder oracle"
    );
    retained_ids(&closer);
    partition(&closer);
    let cache = closer.diagnostic_report().cache;
    // Canonical exact dependencies avoid the old allocation churn. Rejections
    // still consume probes, and every retained canonical hint must remain live.
    assert!(cache.dependency_node_intern_hits > 0);
    assert!(closer.dependency_nodes.iter().all(|(value, index)| {
        closer
            .dependencies
            .get(*index)
            .is_some_and(|node| node.dependency == *value)
    }));
    assert!(cache.rejected_dependency_probe_visits > 0);
    assert!(cache.successful_dependency_probe_visits > 0);
    assert!(cache.named_dependency_moved > 0 && cache.primary_outward_attempts > 0);
    assert!(cache.exact_context_hits > 0);
    let mut output = Vec::new();
    leaves(&proof, rows.len(), &mut output);
    assert!(Arc::ptr_eq(
        output_child(output[3], 7),
        output_child(output[4], 6)
    ));
    assert!(Arc::ptr_eq(
        output_child(output[4], 6),
        output_child(output[5], 5)
    ));
    assert!(Arc::ptr_eq(
        output_child(output[1], 9),
        output_child(output[6], 9)
    ));
    let report = scope.close_with_diagnostics(&input, TermScopeLimits::default());
    let plain = scope
        .close_with_limits(&input, TermScopeLimits::default())
        .unwrap();
    assert_eq!(report.result, Ok(proof.clone()));
    assert_eq!(report.stats, closer.stats);
    assert_eq!(plain.term, proof);
    assert_eq!(plain.stats, closer.stats);
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
        for (endpoint, accepted) in [(0u64, true), (1u64, false)] {
            let goal = eq(Expr::nat_lit(0u64), Expr::nat_lit(endpoint));
            let mut checker = TypeChecker::new(&env);
            checker.set_allow_unsafe(false);
            checker.set_allow_partial(false);
            checker.set_heartbeat_limit(2_000_000);
            let checked = checker.check_type(candidate, &goal);
            if accepted {
                checked.unwrap();
                let audit = env.audit_certification(&goal, candidate);
                assert!(audit.is_certified(), "{audit:#?}");
                for name in &audit.dependencies {
                    assert!(env.axiom_deps(name).unwrap().is_empty());
                    assert!(env.trust_marker_deps(name).unwrap().is_empty());
                }
            } else {
                assert!(matches!(checked, Err(KernelTypeError::TypeMismatch { .. })));
            }
            assert!(!checker.heartbeat_spent());
        }
    }
}

#[test]
fn declaration_rejection_discards_completed_rebase_before_original_first_error() {
    for kind in 0..3 {
        let mut scope = TermScope::new();
        let hidden = match kind {
            0 => scope.lam(id(9), BinderInfo::Default, nat(), Expr::fvar(id(1))),
            1 => scope.lam(
                id(9),
                BinderInfo::Default,
                Expr::fvar(id(100)),
                Expr::fvar(id(1)),
            ),
            _ => scope.let_named(
                id(9),
                Name::anon(),
                nat(),
                Expr::fvar(id(100)),
                Expr::fvar(id(1)),
                false,
            ),
        };
        let shared = Arc::new(hidden);
        let names = if kind == 0 {
            &[1, 2][..]
        } else {
            &[100, 1, 2][..]
        };
        let target = if kind == 0 {
            &[1, 9][..]
        } else {
            &[3, 1, 9][..]
        };
        let prime = arm(&mut scope, names, 3, child_body(&shared));
        let bad = arm(&mut scope, target, 1, child_body(&shared));
        let mut closer = Closer::new(&scope, TermScopeLimits::default(), true);
        let _ = prime.fold_opt_or_clone(&mut closer);
        assert!(closer.error.is_none());
        let checkpoint = closer.dependencies.len();
        let _ = bad.fold_opt_or_clone(&mut closer);
        let error = if kind == 0 {
            TermScopeError::ShadowedLocal(id(9))
        } else {
            TermScopeError::OutOfScope(id(100))
        };
        assert_eq!(closer.error, Some(error.clone()));
        assert_eq!(
            closer.dependencies.len(),
            checkpoint,
            "no unadmitted suffix survives"
        );
        retained_ids(&closer);
        partition(&closer);
        let diagnostic = closer.diagnostic_report();
        let stop = diagnostic.first_stop.unwrap();
        assert!(stop.candidate.is_none());
        if kind == 0 {
            // The cached helper has one external dependency: its completed
            // rebase appended a node before its unused declaration collided.
            assert_eq!(checkpoint, 1);
            assert!(diagnostic.cache.successful_dependency_probe_visits > 0);
            assert!(diagnostic.cache.declaration_collisions > 0);
            assert!(diagnostic.cache.rejected_declaration_probe_visits > 0);
            assert_eq!(stop.phase, TermScopeStopPhase::BinderEntry);
        } else {
            assert_eq!(stop.phase, TermScopeStopPhase::Expression);
        }
        let input = Expr::app(prime, bad);
        let report = scope.close_with_diagnostics(&input, TermScopeLimits::default());
        assert_eq!(report.result, Err(error.clone()));
        assert_eq!(scope.close(&input), Err(error));
    }
}

#[test]
fn every_partial_rebase_cap_keeps_live_ids_and_original_probe_charges() {
    let mut scope = TermScope::new();
    let shared = Arc::new(add(Expr::fvar(id(1)), Expr::fvar(id(2))));
    let prime = arm(&mut scope, &[1, 2, 3], 1, child_body(&shared));
    let target = arm(&mut scope, &[1, 2, 3], 0, child_body(&shared));
    let mut complete = Closer::new(&scope, TermScopeLimits::default(), true);
    let first = prime.fold_opt_or_clone(&mut complete);
    let seed_visits = complete.stats.visits;
    let seed_len = complete.dependencies.len();
    let seed_probes = complete.stats.context_check_visits;
    let second = target.fold_opt_or_clone(&mut complete);
    assert!(complete.error.is_none());
    assert_eq!(complete.stats.context_check_visits - seed_probes, 3);
    assert_eq!(complete.dependencies.len(), seed_len + 3);
    retained_ids(&complete);
    partition(&complete);
    let ExprKind::Lam(_, _, first_body) = first.kind() else {
        panic!("ordinary prefix")
    };
    fn child(mut term: &Expr) -> &Arc<Expr> {
        for _ in 0..3 {
            let ExprKind::Lam(_, _, body) = term.kind() else {
                panic!("named output")
            };
            term = body;
        }
        let ExprKind::App(_, shared) = term.kind() else {
            panic!("actual shared child")
        };
        shared
    }
    assert!(Arc::ptr_eq(child(first_body), child(&second)));
    let mut saw_partial = false;
    for cap in 0..=complete.stats.visits {
        let limits = TermScopeLimits {
            max_visits: cap,
            ..TermScopeLimits::default()
        };
        let mut observed = Closer::new(&scope, limits, true);
        let mut plain = Closer::new(&scope, limits, false);
        let observed_first = prime.fold_opt_or_clone(&mut observed);
        let plain_first = prime.fold_opt_or_clone(&mut plain);
        let before = observed.dependencies.len();
        let before_cache = observed
            .contextual
            .get(shared.as_ref() as *const Expr as usize, 4, 1)
            .cloned();
        let observed_second = target.fold_opt_or_clone(&mut observed);
        let plain_second = target.fold_opt_or_clone(&mut plain);
        assert_eq!(observed_first, plain_first);
        assert_eq!(observed_second, plain_second);
        assert_eq!(observed.error, plain.error);
        assert_eq!(observed.stats, plain.stats);
        assert_eq!(observed.dependencies.len(), plain.dependencies.len());
        assert!(plain.observations.is_none());
        assert_eq!(observed.stats.visits, cap);
        retained_ids(&observed);
        retained_ids(&plain);
        partition(&observed);
        let diagnostic = observed.diagnostic_report();
        if cap == complete.stats.visits {
            assert!(observed.error.is_none());
            assert_eq!(observed_first, first);
            assert_eq!(observed_second, second);
            assert_eq!(observed.stats, complete.stats);
            assert!(diagnostic.first_stop.is_none());
        } else {
            assert_eq!(observed.error, Some(TermScopeError::VisitLimit));
            let stop = diagnostic.first_stop.unwrap();
            assert_eq!(stop.charged_visits, cap);
            if cap >= seed_visits && diagnostic.cache.failed_rebase_dependency_nodes > 0 {
                saw_partial = true;
                assert_eq!(stop.phase, TermScopeStopPhase::RelativeDependency);
                assert_eq!(observed.dependencies.len(), before);
                assert_eq!(before, seed_len);
                let cached = observed
                    .contextual
                    .get(shared.as_ref() as *const Expr as usize, 4, 1)
                    .unwrap();
                let prior = before_cache.unwrap();
                assert_eq!(cached.context, prior.context);
                assert_eq!(cached.entry.dependencies, prior.entry.dependencies);
                assert_eq!(cached.binder_depth, prior.binder_depth);
                assert_eq!(cached.ordinary_count, prior.ordinary_count);
                assert!(Arc::ptr_eq(
                    cached.entry.replacement.as_ref().unwrap(),
                    prior.entry.replacement.as_ref().unwrap()
                ));
                assert!(
                    !observed
                        .memo
                        .contains_key(&(shared.as_ref() as *const Expr as usize, stop.context))
                );
                assert!(diagnostic.cache.rejected_dependency_probe_visits > 0);
                assert!(diagnostic.cache.dependency_budget_rejections > 0);
            }
        }
    }
    assert!(
        saw_partial,
        "a charged, partially allocated rejected join must be exercised"
    );
}
