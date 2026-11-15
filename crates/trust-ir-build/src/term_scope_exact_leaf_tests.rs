// Copyright 2026 Andrew Yates | Licensed under the Apache License, Version 2.0

//! Exact leaf roots retain the charged Join walk's validation and stamp rules.
//! Stack capacity is a private allocation observation, not total memory usage.

use super::*;
use clean_kernel::{BinderInfo, Environment, Level, TypeChecker};

fn id(raw: u64) -> FVarId {
    FVarId::new(raw)
}

fn accounted(closer: &Closer<'_>) {
    let cache = closer.diagnostic_report().cache;
    assert_eq!(
        cache.successful_dependency_probe_visits + cache.rejected_dependency_probe_visits,
        closer.stats.context_check_visits
    );
    assert_eq!(
        cache.successful_declaration_probe_visits + cache.rejected_declaration_probe_visits,
        closer.stats.scope_check_visits
    );
    for (index, node) in closer.dependencies.iter().enumerate() {
        if let Dependency::Join(left, right) = node.dependency {
            assert!(left < index && right < index);
        }
    }
    let check = |entry: &MemoEntry| {
        assert!(
            entry
                .dependencies()
                .is_none_or(|i| i < closer.dependencies.len())
        );
        assert!(
            entry
                .declarations()
                .is_none_or(|i| i < closer.footprints.len())
        );
    };
    for entry in closer.memo.values() {
        check(entry);
    }
    for entry in closer.named_closed.values() {
        check(&entry.entry);
    }
    let (primary, spare) = closer.contextual.maps();
    for entry in primary.values().chain(spare.values()) {
        check(&entry.entry);
    }
}

#[test]
fn exact_named_and_ordinary_leaf_roots_match_join_validation_without_stack_growth() {
    for ordinary in [false, true] {
        for actual in [None, Some(1), Some(2)] {
            for joined in [false, true] {
                let scope = TermScope::new();
                let mut closer = Closer::new(&scope, TermScopeLimits::default(), true);
                closer.stats.visits = 7; // An enclosing expression has already charged.
                closer.binder_depth = 5;
                if ordinary {
                    closer.ordinary.extend(actual);
                } else if let Some(depth) = actual {
                    closer.active.insert(id(1), depth);
                }
                let leaf = closer.dependency_node(if ordinary {
                    Dependency::Ordinary(0, 1)
                } else {
                    Dependency::Named(id(1), 1)
                });
                let root = if joined {
                    let internal = closer.dependency_node(Dependency::Named(id(99), 5));
                    closer.dependency_node(Dependency::Join(leaf, internal))
                } else {
                    leaf
                };
                let nodes = closer.dependencies.len();
                assert_eq!(closer.probe_stack.capacity(), 0);
                assert_eq!(closer.same_dependencies(Some(root)), actual == Some(1));
                let charges = if joined {
                    if actual == Some(1) { 3 } else { 2 }
                } else {
                    1
                };
                assert_eq!(closer.stats.visits, 7 + charges);
                assert_eq!(closer.stats.context_check_visits, charges);
                assert_eq!(closer.dependencies[leaf].last_probe, 7);
                assert_eq!(closer.dependencies.len(), nodes);
                assert_eq!(closer.probe_stack.capacity() == 0, !joined);
                let cache = closer.diagnostic_report().cache;
                assert_eq!(
                    cache.named_dependency_missing,
                    usize::from(!ordinary && actual.is_none())
                );
                assert_eq!(
                    cache.named_dependency_moved,
                    usize::from(!ordinary && actual == Some(2))
                );
                assert_eq!(
                    cache.ordinary_dependency_missing,
                    usize::from(ordinary && actual.is_none())
                );
                assert_eq!(
                    cache.ordinary_dependency_moved,
                    usize::from(ordinary && actual == Some(2))
                );
                assert!(closer.error.is_none());
                accounted(&closer);
            }
        }
    }
}

#[test]
fn exact_leaf_no_root_internal_and_previous_probe_cutoffs_keep_their_charges() {
    for seed in [0, 7] {
        for ordinary in [false, true] {
            for (depth, stamp) in [(5, 99), (u32::MAX, 99), (1, seed)] {
                let scope = TermScope::new();
                let mut closer = Closer::new(&scope, TermScopeLimits::default(), true);
                closer.stats.visits = seed;
                closer.binder_depth = 5;
                assert!(closer.same_dependencies(None));
                assert_eq!(closer.stats.visits, seed);
                let leaf = closer.dependency_node(if ordinary {
                    Dependency::Ordinary(usize::MAX, depth)
                } else {
                    Dependency::Named(id(99), depth)
                });
                closer.dependencies[leaf].last_probe = stamp;
                // Seed zero is a legacy private-call boundary, not a public
                // authorization path: its previous-probe stamp still skips.
                assert!(closer.same_dependencies(Some(leaf)));
                assert_eq!(closer.stats.visits, seed + 1);
                assert_eq!(closer.stats.context_check_visits, 1);
                assert_eq!(closer.dependencies[leaf].last_probe, stamp);
                assert_eq!(closer.probe_stack.capacity(), 0);
                assert!(closer.error.is_none());
                accounted(&closer);
            }
        }
    }
}

#[test]
fn exact_leaf_caps_charge_before_cutoffs_and_leave_first_stop_and_nodes_unchanged() {
    for internal in [false, true] {
        for joined in [false, true] {
            for cap in 0..=3 {
                let scope = TermScope::new();
                let mut closer = Closer::new(
                    &scope,
                    TermScopeLimits {
                        max_visits: 1 + cap,
                        ..TermScopeLimits::default()
                    },
                    true,
                );
                closer.stats.visits = 1;
                closer.binder_depth = 5;
                closer.active.insert(id(1), 1);
                let leaf =
                    closer.dependency_node(Dependency::Named(id(1), if internal { 5 } else { 1 }));
                let root = if joined {
                    let other = closer.dependency_node(Dependency::Ordinary(usize::MAX, 5));
                    closer.dependency_node(Dependency::Join(leaf, other))
                } else {
                    leaf
                };
                let nodes = closer.dependencies.len();
                let needed = if joined && !internal { 3 } else { 1 };
                assert_eq!(closer.same_dependencies(Some(root)), cap >= needed);
                assert_eq!(closer.stats.visits, 1 + cap.min(needed));
                assert_eq!(closer.stats.context_check_visits, cap.min(needed));
                assert_eq!(closer.dependencies.len(), nodes);
                assert_eq!(
                    closer.error,
                    (cap < needed).then_some(TermScopeError::VisitLimit)
                );
                let report = closer.diagnostic_report();
                assert_eq!(
                    report.cache.dependency_budget_rejections,
                    usize::from(cap < needed)
                );
                if cap < needed {
                    let stop = report.first_stop.unwrap();
                    assert_eq!(stop.phase, TermScopeStopPhase::ExactDependency);
                    assert_eq!(stop.charged_visits, 1 + cap);
                } else {
                    assert!(report.first_stop.is_none());
                }
                accounted(&closer);
            }
        }
    }
}

#[test]
fn exact_join_duplicate_edges_keep_preorder_charges_and_leaf_clears_old_work() {
    let scope = TermScope::new();
    let mut closer = Closer::new(&scope, TermScopeLimits::default(), true);
    closer.stats.visits = 1;
    closer.binder_depth = 5;
    closer.active.insert(id(1), 1);
    let leaf = closer.dependency_node(Dependency::Named(id(1), 1));
    let pair = closer.dependency_node(Dependency::Join(leaf, leaf));
    let diamond = closer.dependency_node(Dependency::Join(pair, pair));
    assert!(closer.same_dependencies(Some(diamond)));
    assert_eq!(closer.stats.visits, 6);
    assert_eq!(closer.stats.context_check_visits, 5);
    assert_eq!(closer.dependencies[leaf].last_probe, 1);
    assert_eq!(closer.dependencies[pair].last_probe, 1);
    let capacity = closer.probe_stack.capacity();
    assert!(capacity > 0);
    closer.probe_stack.extend([pair, diamond]);
    assert!(closer.same_dependencies(Some(leaf)));
    assert!(closer.probe_stack.is_empty());
    assert_eq!(closer.probe_stack.capacity(), capacity);
    assert_eq!(closer.dependencies[leaf].last_probe, 6);
    assert_eq!(closer.stats.context_check_visits, 6);
    closer.active.insert(id(1), 2);
    assert!(!closer.same_dependencies(Some(leaf)));
    assert_eq!(closer.dependencies[leaf].last_probe, 7);
    assert_eq!(closer.diagnostic_report().cache.named_dependency_moved, 1);
    accounted(&closer);
}

#[test]
fn exact_source_leaf_reuse_keeps_strict_proof_and_public_cap_parity() {
    let nat = || Expr::const_str("Nat");
    let eq = |left, right| {
        Expr::apps(
            Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
            [nat(), left, right],
        )
    };
    let value = Expr::fvar(id(1));
    let shared = Arc::new(Expr::apps(
        Expr::const_(
            Name::from_string("Eq.refl"),
            vec![Level::succ(Level::zero())],
        ),
        [nat(), value.clone()],
    ));
    let mut scope = TermScope::new();
    let mut inputs = Vec::new();
    let mut oracle = Vec::new();
    for outer in [9, 8] {
        let shell = Expr::lam(
            BinderInfo::Default,
            eq(value.clone(), value.clone()),
            Expr::bvar(0),
        );
        let mut term = Expr::app_arc(Arc::new(shell), shared.clone());
        let mut expected = term.clone();
        for raw in [1, outer] {
            term = scope.lam(id(raw), BinderInfo::Default, nat(), term);
            expected = Expr::lam(BinderInfo::Default, nat(), expected.abstract_fvar(id(raw)));
        }
        inputs.push(term);
        oracle.push(expected);
    }
    let mut closer = Closer::new(&scope, TermScopeLimits::default(), true);
    let first = inputs[0].fold_opt_or_clone(&mut closer);
    let address = shared.as_ref() as *const Expr as usize;
    let entry = closer.contextual.maps().0[&address].clone();
    let leaf = entry.entry.dependencies().unwrap();
    assert!(matches!(
        closer.dependencies[leaf].dependency,
        Dependency::Named(_, 1)
    ));
    let before = closer.diagnostic_report().cache.primary_exact_attempts;
    let last = inputs[1].fold_opt_or_clone(&mut closer);
    assert!(closer.error.is_none());
    assert!(closer.diagnostic_report().cache.primary_exact_attempts > before);
    let updated = &closer.contextual.maps().0[&address];
    assert_ne!(entry.context, updated.context);
    assert_eq!(updated.entry.dependencies(), Some(leaf));
    assert!(Arc::ptr_eq(
        entry.entry.replacement.as_ref().unwrap(),
        updated.entry.replacement.as_ref().unwrap()
    ));
    accounted(&closer);
    let mut env = Environment::new();
    env.init_eq().unwrap();
    env.init_nat().unwrap();
    let ty = Expr::arrow(
        nat(),
        Expr::pi(BinderInfo::Default, nat(), eq(Expr::bvar(0), Expr::bvar(0))),
    );
    let forged = Expr::arrow(
        nat(),
        Expr::pi(
            BinderInfo::Default,
            nat(),
            eq(
                Expr::bvar(0),
                Expr::app(Expr::const_str("Nat.succ"), Expr::bvar(0)),
            ),
        ),
    );
    for (arm, expected) in [first, last].into_iter().zip(oracle) {
        assert_eq!(arm, expected);
        let mut checker = TypeChecker::new(&env);
        checker.set_allow_unsafe(false);
        checker.set_allow_partial(false);
        checker.check_type(&arm, &ty).unwrap();
        let inferred = checker.infer_type(&arm).unwrap();
        assert!(!checker.is_def_eq(&inferred, &forged));
        let bytes = trust_ir::proof::encode_clean_expr_dag_v2(&arm).unwrap();
        let decoded = trust_ir::proof::decode_clean_expr_dag_v2(&bytes).unwrap();
        assert_eq!(decoded, arm);
        assert!(env.audit_certification(&ty, &decoded).is_certified());
        assert!(!env.audit_certification(&forged, &decoded).is_certified());
    }
    let input = Expr::apps(Expr::const_str("structural"), inputs);
    let full = scope.close_with_diagnostics(&input, TermScopeLimits::default());
    assert!(full.result.is_ok());
    for cap in 0..=full.stats.visits {
        let limits = TermScopeLimits {
            max_visits: cap,
            ..TermScopeLimits::default()
        };
        let mut observed = Closer::new(&scope, limits, true);
        let mut plain = Closer::new(&scope, limits, false);
        let actual = input.fold_opt_or_clone(&mut observed);
        let expected = input.fold_opt_or_clone(&mut plain);
        assert_eq!(actual, expected);
        assert_eq!(observed.error, plain.error);
        assert_eq!(observed.stats, plain.stats);
        accounted(&observed);
        let public = scope.close_with_diagnostics(&input, limits);
        assert_eq!(public.stats, observed.stats);
        assert_eq!(
            public.result,
            observed.error.clone().map_or(Ok(actual), Err)
        );
        assert_eq!(
            scope.close_with_limits(&input, limits).map(|out| out.term),
            public.result
        );
    }
}
