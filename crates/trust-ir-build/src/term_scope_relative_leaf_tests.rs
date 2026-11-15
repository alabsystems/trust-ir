// Copyright 2026 Andrew Yates | Licensed under the Apache License, Version 2.0

//! Leaf roots use the same charged rules as leaves in the retained Join walk.
//! Charges, reasons and IDs retain the immutable IR9b56 contract except for
//! the later, separately tested Ordinary low-minimum rejection policy below.
//! There is no second closer or copied rebase implementation.

use super::*;
use clean_kernel::{BinderInfo, Environment, Level, TypeChecker};

fn id(raw: u64) -> FVarId {
    FVarId::new(raw)
}
fn nat() -> Expr {
    Expr::const_str("Nat")
}
fn cached(root: Option<usize>, depth: u32, ordinary: usize) -> ContextEntry {
    ContextEntry {
        entry: MemoEntry {
            replacement: None,
            declarations: None,
            dependencies: MemoEntry::compact(root),
        },
        context: 99,
        binder_depth: depth,
        ordinary_count: ordinary,
    }
}
fn root(closer: &mut Closer<'_>, leaf: Dependency, joined: bool, old: u32) -> (usize, usize) {
    let leaf = closer.dependency_node(leaf);
    let root = if joined {
        let internal = closer.dependency_node(Dependency::Ordinary(0, old));
        closer.dependency_node(Dependency::Join(leaf, internal))
    } else {
        leaf
    };
    (root, leaf)
}
fn retained(closer: &Closer<'_>) {
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
    assert!(
        closer
            .dependency
            .is_none_or(|i| i < closer.dependencies.len())
    );
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
    for (index, node) in closer.dependencies.iter().enumerate() {
        if let Dependency::Join(left, right) = node.dependency {
            assert!(left < index && right < index);
        }
    }
    let cache = closer.diagnostic_report().cache;
    assert_eq!(
        cache.successful_dependency_probe_visits + cache.rejected_dependency_probe_visits,
        closer.stats.context_check_visits
    );
    assert_eq!(
        cache.successful_declaration_probe_visits + cache.rejected_declaration_probe_visits,
        closer.stats.scope_check_visits
    );
}
fn charges(closer: &Closer<'_>, visits: usize) {
    assert_eq!(closer.stats.visits, visits);
    assert_eq!(closer.stats.context_check_visits, visits);
    retained(closer);
}
fn wrap(scope: &mut TermScope, names: &[u64], ordinary: usize, shared: &Arc<Expr>) -> Expr {
    let mut term = Expr::app_arc(Arc::new(Expr::const_str("Nat.succ")), shared.clone());
    for raw in names.iter().rev() {
        term = scope.lam(id(*raw), BinderInfo::Default, nat(), term);
    }
    for _ in 0..ordinary {
        term = Expr::lam(BinderInfo::Default, nat(), term);
    }
    term
}
fn child(mut term: &Expr, depth: usize) -> &Arc<Expr> {
    for _ in 0..depth {
        let ExprKind::Lam(_, _, body) = term.kind() else {
            panic!("actual binder spine")
        };
        term = body;
    }
    let ExprKind::App(_, child) = term.kind() else {
        panic!("actual shared child edge")
    };
    child
}

#[test]
fn named_leaf_and_join_keep_mode_specific_zero_offset_ids_and_exact_charges() {
    for named_only in [false, true] {
        for removed in [0, 1] {
            for joined in [false, true] {
                let scope = TermScope::new();
                let mut closer = Closer::new(&scope, TermScopeLimits::default(), true);
                closer.binder_depth = 2;
                closer.active.insert(id(1), 0);
                let mode = if named_only {
                    RebaseMode::NamedOnly
                } else {
                    RebaseMode::Ordinary
                };
                let (root, leaf) = root(
                    &mut closer,
                    Dependency::Named(id(1), removed),
                    joined,
                    2 + removed,
                );
                let before = closer.dependencies.len();
                let output = closer
                    .relative_dependencies(
                        &cached(
                            Some(root),
                            2 + removed,
                            if named_only { 0 } else { removed as usize },
                        ),
                        mode,
                    )
                    .unwrap()
                    .unwrap();
                let retains_id = named_only && removed == 0;
                assert_eq!(output, if retains_id { leaf } else { before });
                assert_eq!(closer.dependencies.len(), before + usize::from(!retains_id));
                assert!(matches!(closer.dependencies[output].dependency,
                    Dependency::Named(local, 0) if local == id(1)));
                assert_eq!(closer.dependencies[output].min_depth, 0);
                assert!(closer.error.is_none());
                charges(&closer, if joined { 3 } else { 1 });
            }
        }
    }
}

#[test]
fn ordinary_leaf_and_join_always_append_even_at_zero_offset() {
    for removed in [0, 1] {
        for joined in [false, true] {
            let scope = TermScope::new();
            let mut closer = Closer::new(&scope, TermScopeLimits::default(), true);
            closer.binder_depth = 2;
            closer.ordinary.push(0);
            let (root, _) = root(
                &mut closer,
                Dependency::Ordinary(removed as usize, removed),
                joined,
                2 + removed,
            );
            let before = closer.dependencies.len();
            let output = closer
                .relative_dependencies(
                    &cached(Some(root), 2 + removed, 1 + removed as usize),
                    RebaseMode::Ordinary,
                )
                .unwrap()
                .unwrap();
            assert_eq!(output, before);
            assert_eq!(closer.dependencies.len(), before + 1);
            assert!(matches!(
                closer.dependencies[output].dependency,
                Dependency::Ordinary(0, 0)
            ));
            assert!(closer.error.is_none());
            charges(&closer, if joined { 3 } else { 1 });
        }
    }
}

#[test]
fn join_diamond_duplicate_charges_and_mode_specific_join_ids_stay_unchanged() {
    for named_only in [false, true] {
        for removed in [0, 1] {
            let scope = TermScope::new();
            let mut closer = Closer::new(&scope, TermScopeLimits::default(), true);
            closer.binder_depth = 3;
            closer.active.extend([(id(1), 0), (id(2), 1)]);
            let left = closer.dependency_node(Dependency::Named(id(1), removed));
            let right = closer.dependency_node(Dependency::Named(id(2), 1 + removed));
            let pair = closer.dependency_node(Dependency::Join(left, right));
            let diamond = closer.dependency_node(Dependency::Join(pair, pair));
            let before = closer.dependencies.len();
            let mode = if named_only {
                RebaseMode::NamedOnly
            } else {
                RebaseMode::Ordinary
            };
            let output = closer
                .relative_dependencies(
                    &cached(
                        Some(diamond),
                        3 + removed,
                        if named_only { 0 } else { removed as usize },
                    ),
                    mode,
                )
                .unwrap()
                .unwrap();
            let retained = named_only && removed == 0;
            assert_eq!(output, if retained { pair } else { before + 2 });
            assert_eq!(
                closer.dependencies.len(),
                before + if retained { 0 } else { 3 }
            );
            let Dependency::Join(left, right) = closer.dependencies[output].dependency else {
                panic!("both validated named dependencies survive")
            };
            assert!(
                matches!(closer.dependencies[left].dependency, Dependency::Named(local, 0) if local == id(1))
            );
            assert!(
                matches!(closer.dependencies[right].dependency, Dependency::Named(local, 1) if local == id(2))
            );
            // Root, pair, two leaves, then the duplicate pair request; finish
            // actions are uncharged and the duplicate must not expand again.
            charges(&closer, 5);
        }
    }
}

#[test]
fn named_leaf_and_join_refusals_preserve_reason_and_screen_accounting() {
    for case in 0..4 {
        for joined in [false, true] {
            let scope = TermScope::new();
            let mut closer = Closer::new(&scope, TermScopeLimits::default(), true);
            closer.binder_depth = 2;
            if case == 1 {
                closer.active.insert(id(1), 1);
            }
            if case >= 2 {
                closer.active.insert(id(1), 0);
            }
            let (root, _) = root(
                &mut closer,
                Dependency::Named(id(1), u32::from(case < 2)),
                joined,
                3,
            );
            let mode = if case == 2 {
                RebaseMode::Ordinary
            } else {
                RebaseMode::NamedOnly
            };
            let before = closer.dependencies.len();
            assert_eq!(
                closer.relative_dependencies(&cached(Some(root), 3, usize::from(case == 2)), mode),
                None
            );
            assert!(closer.error.is_none());
            assert_eq!(closer.dependencies.len(), before);
            let cache = closer.diagnostic_report().cache;
            assert_eq!(
                [
                    cache.named_dependency_missing,
                    cache.named_dependency_moved,
                    cache.dependency_rebase_underflow,
                    cache.named_only_depth_screen_rejections,
                    cache.ordinary_depth_screen_rejections
                ],
                [
                    usize::from(case == 0),
                    usize::from(case == 1),
                    0,
                    usize::from(case == 3),
                    usize::from(case == 2),
                ]
            );
            assert_eq!(cache.failed_rebase_dependency_nodes, 0);
            charges(
                &closer,
                if case >= 2 {
                    0
                } else if joined {
                    2
                } else {
                    1
                },
            );
        }
    }
}

#[test]
fn ordinary_leaf_and_join_refusals_preserve_position_depth_and_mode_checks() {
    for case in 0..6 {
        for joined in [false, true] {
            let scope = TermScope::new();
            let mut closer = Closer::new(&scope, TermScopeLimits::default(), true);
            closer.binder_depth = 2;
            if matches!(case, 1 | 2) {
                closer.ordinary.push(0);
            }
            if case == 4 {
                closer.ordinary.push(1);
            }
            let position = usize::from(matches!(case, 2..=4));
            let depth = u32::from(!matches!(case, 2 | 5));
            let (root, _) = root(
                &mut closer,
                Dependency::Ordinary(position, depth),
                joined,
                3,
            );
            let named_only = matches!(case, 0 | 5);
            let mode = if named_only {
                RebaseMode::NamedOnly
            } else {
                RebaseMode::Ordinary
            };
            let count = if named_only {
                0
            } else {
                closer.ordinary.len() + 1
            };
            let before = closer.dependencies.len();
            assert_eq!(
                closer.relative_dependencies(&cached(Some(root), 3, count), mode),
                None
            );
            assert!(closer.error.is_none());
            assert_eq!(closer.dependencies.len(), before);
            let cache = closer.diagnostic_report().cache;
            assert_eq!(cache.named_only_ordinary_rejections, usize::from(case == 0));
            assert_eq!(cache.dependency_rebase_underflow, usize::from(case == 1));
            // Case 1 remains a charged position underflow at depth==delta;
            // case 2's depth<delta now refuses before any probe.
            assert_eq!(
                cache.ordinary_depth_screen_rejections,
                usize::from(case == 2)
            );
            assert_eq!(cache.ordinary_dependency_missing, usize::from(case == 3));
            assert_eq!(cache.ordinary_dependency_moved, usize::from(case == 4));
            assert_eq!(
                cache.named_only_depth_screen_rejections,
                usize::from(case == 5)
            );
            charges(
                &closer,
                if matches!(case, 2 | 5) {
                    0
                } else if joined {
                    2
                } else {
                    1
                },
            );
        }
    }
}

#[test]
fn no_root_internal_and_maximum_boundaries_preserve_charged_relative_guards() {
    let scope = TermScope::new();
    let mut closer = Closer::new(&scope, TermScopeLimits::default(), true);
    closer.binder_depth = 2;
    assert_eq!(
        closer.relative_dependencies(&cached(None, 3, 0), RebaseMode::NamedOnly),
        Some(None)
    );
    for dependency in [Dependency::Named(id(1), 3), Dependency::Ordinary(0, 3)] {
        for joined in [false, true] {
            let (root, _) = root(&mut closer, dependency, joined, 3);
            let before = closer.stats.context_check_visits;
            assert_eq!(
                closer.relative_dependencies(&cached(Some(root), 3, 0), RebaseMode::NamedOnly),
                Some(None)
            );
            assert_eq!(closer.stats.context_check_visits, before + 1);
        }
    }
    closer.active.insert(id(1), 1);
    for joined in [false, true] {
        // This external depth is >= newD but < oldD: pruning at newD would
        // incorrectly discard it, in either the leaf path or Join walker.
        let (root, _) = root(&mut closer, Dependency::Named(id(1), 2), joined, 3);
        let before = closer.stats.context_check_visits;
        let output = closer
            .relative_dependencies(&cached(Some(root), 3, 0), RebaseMode::NamedOnly)
            .unwrap()
            .unwrap();
        assert!(
            matches!(closer.dependencies[output].dependency, Dependency::Named(local, 1) if local == id(1))
        );
        assert_eq!(
            closer.stats.context_check_visits,
            before + if joined { 3 } else { 1 }
        );
    }
    closer.active.remove(&id(1));
    let before = closer.stats;
    // An empty dependency footprint permits inward reuse without a leaf
    // probe. Declaration and Ordinary shape refusals below remain unchanged.
    assert_eq!(
        closer.relative_dependencies(&cached(None, 1, 0), RebaseMode::NamedOnly),
        Some(None)
    );
    let declaration = closer.declarations(Declarations::Local(id(9)));
    let mut entry = cached(None, 3, 0);
    entry.entry.declarations = MemoEntry::compact(Some(declaration));
    assert_eq!(
        closer.relative_dependencies(&entry, RebaseMode::NamedOnly),
        None
    );
    closer.ordinary.push(0);
    assert_eq!(
        closer.relative_dependencies(&cached(None, 3, 0), RebaseMode::Ordinary),
        None
    );
    assert_eq!(closer.stats, before);
    assert_eq!(
        closer.diagnostic_report().cache.dependency_shape_rejections,
        2
    );
    retained(&closer);
    // First tuple is Clean's valid binder-depth boundary; the second is only
    // private arithmetic metadata, not a reachable production-depth claim.
    for old in [Expr::MAX_BVAR_INDEX + 1, u32::MAX] {
        let mut closer = Closer::new(&scope, TermScopeLimits::default(), true);
        closer.binder_depth = 1;
        closer.active.insert(id(1), 0);
        let (root, _) = root(&mut closer, Dependency::Named(id(1), old - 1), false, old);
        let output = closer
            .relative_dependencies(&cached(Some(root), old, 0), RebaseMode::NamedOnly)
            .unwrap()
            .unwrap();
        assert!(matches!(
            closer.dependencies[output].dependency,
            Dependency::Named(_, 0)
        ));
        charges(&closer, 1);
    }
}

#[test]
fn leaf_and_join_caps_charge_requests_and_do_not_own_suffix_rollback() {
    for named_only in [false, true] {
        for removed in [0, 1] {
            for joined in [false, true] {
                for cap in 0..=3 {
                    let scope = TermScope::new();
                    let mut closer = Closer::new(
                        &scope,
                        TermScopeLimits {
                            max_visits: cap,
                            ..TermScopeLimits::default()
                        },
                        true,
                    );
                    closer.binder_depth = 2;
                    closer.active.insert(id(1), 0);
                    let (root, _) = root(
                        &mut closer,
                        Dependency::Named(id(1), removed),
                        joined,
                        2 + removed,
                    );
                    let before = closer.dependencies.len();
                    let mode = if named_only {
                        RebaseMode::NamedOnly
                    } else {
                        RebaseMode::Ordinary
                    };
                    let result = closer.relative_dependencies(
                        &cached(
                            Some(root),
                            2 + removed,
                            if named_only { 0 } else { removed as usize },
                        ),
                        mode,
                    );
                    let needed = if joined { 3 } else { 1 };
                    assert_eq!(result.is_some(), cap >= needed);
                    assert_eq!(
                        closer.error,
                        (cap < needed).then_some(TermScopeError::VisitLimit)
                    );
                    let stop = closer.diagnostic_report().first_stop;
                    if cap < needed {
                        let stop = stop.unwrap();
                        assert_eq!(stop.phase, TermScopeStopPhase::RelativeDependency);
                        assert_eq!(stop.charged_visits, cap);
                    } else {
                        assert!(stop.is_none());
                    }
                    charges(&closer, cap.min(needed));
                    let appended =
                        (!named_only || removed != 0) && cap >= if joined { 2 } else { 1 };
                    // A direct relative guard leaves a valid prefix private;
                    // only fold_shared's common checkpoint owns its rollback.
                    assert_eq!(closer.dependencies.len(), before + usize::from(appended));
                    let cache = closer.diagnostic_report().cache;
                    assert_eq!(
                        cache.dependency_budget_rejections,
                        usize::from(cap < needed)
                    );
                    assert_eq!(
                        cache.failed_rebase_dependency_nodes,
                        usize::from(appended && cap < needed)
                    );
                }
            }
        }
    }
}

#[test]
fn actual_leaf_boundary_reuses_strict_proof_arc_and_caps_preserve_public_parity() {
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
    for (first_names, first_o, last_names, last_o) in [
        (vec![9, 1], 0, vec![1], 1),
        (vec![9, 8, 1], 0, vec![1], 0),
        (vec![1], 2, vec![1], 1),
    ] {
        let mut scope = TermScope::new();
        let mut inputs = Vec::new();
        let mut oracle = Vec::new();
        for (names, ordinary) in [(&first_names, first_o), (&last_names, last_o)] {
            let shell = Expr::lam(
                BinderInfo::Default,
                eq(value.clone(), value.clone()),
                Expr::bvar(0),
            );
            let mut term = Expr::app_arc(Arc::new(shell), shared.clone());
            let mut expected = term.clone();
            for raw in names.iter().rev() {
                term = scope.lam(id(*raw), BinderInfo::Default, nat(), term);
                expected = Expr::lam(BinderInfo::Default, nat(), expected.abstract_fvar(id(*raw)));
            }
            for _ in 0..ordinary {
                term = Expr::lam(BinderInfo::Default, nat(), term);
                expected = Expr::lam(BinderInfo::Default, nat(), expected);
            }
            inputs.push(term);
            oracle.push(expected);
        }
        let mut closer = Closer::new(&scope, TermScopeLimits::default(), true);
        let first = inputs[0].fold_opt_or_clone(&mut closer);
        let address = shared.as_ref() as *const Expr as usize;
        let root = closer.contextual.maps().0[&address]
            .entry
            .dependencies()
            .unwrap();
        assert!(matches!(
            closer.dependencies[root].dependency,
            Dependency::Named(_, _)
        ));
        let before = closer.stats.context_check_visits;
        let last = inputs[1].fold_opt_or_clone(&mut closer);
        assert!(closer.error.is_none());
        assert!(closer.stats.context_check_visits > before);
        assert!(Arc::ptr_eq(
            child(&first, first_names.len() + first_o),
            child(&last, last_names.len() + last_o)
        ));
        retained(&closer);
        let mut env = Environment::new();
        env.init_eq().unwrap();
        env.init_nat().unwrap();
        for ((arm, expected), depth) in [first, last]
            .into_iter()
            .zip(oracle)
            .zip([first_names.len() + first_o, last_names.len() + last_o])
        {
            assert_eq!(arm, expected);
            let mut ty = Expr::pi(BinderInfo::Default, nat(), eq(Expr::bvar(0), Expr::bvar(0)));
            let mut forged = Expr::pi(
                BinderInfo::Default,
                nat(),
                eq(
                    Expr::bvar(0),
                    Expr::app(Expr::const_str("Nat.succ"), Expr::bvar(0)),
                ),
            );
            for _ in 1..depth {
                ty = Expr::arrow(nat(), ty);
                forged = Expr::arrow(nat(), forged);
            }
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
            retained(&observed);
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
}

#[test]
fn actual_leaf_declaration_failure_and_partial_cap_roll_back_private_suffix() {
    let mut scope = TermScope::new();
    let shared = Arc::new(scope.lam(id(2), BinderInfo::Default, nat(), Expr::fvar(id(1))));
    let first = wrap(&mut scope, &[9, 1], 2, &shared);
    let last = wrap(&mut scope, &[2, 1], 1, &shared);
    let address = shared.as_ref() as *const Expr as usize;
    let mut full = Closer::new(&scope, TermScopeLimits::default(), true);
    let _ = first.fold_opt_or_clone(&mut full);
    let warm_visits = full.stats.visits;
    let warm_nodes = full.dependencies.len();
    let root = full.contextual.maps().0[&address]
        .entry
        .dependencies()
        .unwrap();
    assert!(matches!(
        full.dependencies[root].dependency,
        Dependency::Named(_, 3)
    ));
    let _ = last.fold_opt_or_clone(&mut full);
    assert_eq!(full.error, Some(TermScopeError::ShadowedLocal(id(2))));
    assert_eq!(full.dependencies.len(), warm_nodes);
    assert!(full.diagnostic_report().cache.declaration_collisions > 0);
    retained(&full);
    let mut interrupted_declaration = 0;
    for cap in warm_visits..full.stats.visits {
        let mut closer = Closer::new(&scope, TermScopeLimits::default(), true);
        let _ = first.fold_opt_or_clone(&mut closer);
        let nodes = closer.dependencies.len();
        let probes = closer.stats.context_check_visits;
        closer.limits.max_visits = cap;
        let _ = last.fold_opt_or_clone(&mut closer);
        retained(&closer);
        let report = closer.diagnostic_report();
        if let Some(stop) = report.first_stop
            && stop.phase == TermScopeStopPhase::Declaration
        {
            assert_eq!(closer.error, Some(TermScopeError::VisitLimit));
            assert_eq!(closer.stats.context_check_visits, probes + 1);
            assert_eq!(closer.dependencies.len(), nodes);
            assert!(!closer.memo.contains_key(&(address, stop.context)));
            assert_eq!(closer.contextual.maps().0[&address].binder_depth, 4);
            interrupted_declaration += 1;
        }
    }
    assert!(interrupted_declaration > 0);
}

#[test]
fn actual_selected_leaf_rejection_keeps_the_valid_spare_unprobed() {
    let shared = Arc::new(Expr::app(Expr::const_str("Nat.succ"), Expr::fvar(id(1))));
    let mut scope = TermScope::new();
    let first = wrap(&mut scope, &[9, 8, 7, 1], 0, &shared);
    let middle = wrap(&mut scope, &[8, 1, 7], 0, &shared);
    let last = wrap(&mut scope, &[8, 1], 0, &shared);
    let mut closer = Closer::new(&scope, TermScopeLimits::default(), true);
    let first = first.fold_opt_or_clone(&mut closer);
    let _ = middle.fold_opt_or_clone(&mut closer);
    let address = shared.as_ref() as *const Expr as usize;
    let (primary, spare) = closer.contextual.maps();
    assert_eq!(
        (primary[&address].binder_depth, spare[&address].binder_depth),
        (3, 4)
    );
    let spare_root = spare[&address].entry.dependencies().unwrap();
    assert!(matches!(
        closer.dependencies[spare_root].dependency,
        Dependency::Named(_, 3)
    ));
    assert!(closer.contextual.get(address, 2, 0).is_none());
    let before = closer.diagnostic_report().cache;
    let last = last.fold_opt_or_clone(&mut closer);
    assert!(closer.error.is_none());
    assert_eq!(child(&first, 4), child(&last, 2));
    // The completed inverse restores the original output directly. The original
    // spare-attempt/probe assertions below still prohibit a candidate retry.
    assert!(Arc::ptr_eq(child(&first, 4), child(&last, 2)));

    let after = closer.diagnostic_report().cache;
    assert!(after.primary_named_only_attempts > before.primary_named_only_attempts);
    assert!(after.named_dependency_moved > before.named_dependency_moved);
    assert_eq!(
        after.spare_named_only_attempts,
        before.spare_named_only_attempts
    );
    assert_eq!(
        after.named_only_depth_screen_rejections,
        before.named_only_depth_screen_rejections
    );
    retained(&closer);
}
