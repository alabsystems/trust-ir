// Copyright 2026 Andrew Yates | Licensed under the Apache License, Version 2.0

//! Minimum-depth metadata rejects one selected slot, never admits an output.

use super::*;
use clean_kernel::{BinderInfo, Environment, Level, TypeChecker};

fn id(raw: u64) -> FVarId {
    FVarId::new(raw)
}
fn nat() -> Expr {
    Expr::const_str("Nat")
}
fn add(left: Arc<Expr>, right: Arc<Expr>) -> Expr {
    Expr::app_arc(
        Arc::new(Expr::app_arc(Arc::new(Expr::const_str("Nat.add")), left)),
        right,
    )
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
        panic!("actual shared child")
    };
    child
}
fn cached(root: Option<usize>, depth: u32, ordinary: usize) -> ContextEntry {
    ContextEntry {
        entry: MemoEntry {
            // Direct footprint controls do not manufacture an output proof.
            replacement: None,
            declarations: None,
            dependencies: MemoEntry::compact(root),
        },
        context: 99,
        binder_depth: depth,
        ordinary_count: ordinary,
    }
}
fn partition(closer: &Closer<'_>) {
    let report = closer.diagnostic_report();
    assert_eq!(
        report.cache.successful_dependency_probe_visits
            + report.cache.rejected_dependency_probe_visits,
        closer.stats.context_check_visits
    );
    assert_eq!(
        report.cache.successful_declaration_probe_visits
            + report.cache.rejected_declaration_probe_visits,
        closer.stats.scope_check_visits
    );
}
fn retained_ids(closer: &Closer<'_>) {
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
    partition(closer);
}
fn diamond() -> Arc<Expr> {
    let mut prefix = Arc::new(Expr::fvar(id(1)));
    for step in 0..48 {
        // Canonical leaves no longer pad the arena: retain >40 ACTUAL joins.
        // Three distinct already-bound reads keep a genuine long prefix:
        // alternating9/8 is not the previous union's immediate last member.
        // Do not depend on redundant repeated9 unions surviving absorption.
        prefix = Arc::new(add(
            prefix,
            Arc::new(Expr::fvar(id(if step % 2 == 0 { 9 } else { 8 }))),
        ));
    }
    Arc::new(add(
        prefix.clone(),
        Arc::new(add(prefix, Arc::new(Expr::fvar(id(2))))),
    ))
}

#[test]
fn selected_low_minimum_skips_actual_long_diamond_without_probe_or_arena_growth() {
    let shared = diamond();
    let mut scope = TermScope::new();
    let first = wrap(&mut scope, &[2, 9, 8, 1], 0, &shared);
    let mut closer = Closer::new(&scope, TermScopeLimits::default(), true);
    let first_out = first.fold_opt_or_clone(&mut closer);
    assert!(closer.error.is_none());
    let mut expected = Expr::app_arc(Arc::new(Expr::const_str("Nat.succ")), shared.clone());
    for raw in [2, 9, 8, 1].into_iter().rev() {
        // Independent ordinary abstraction, not the dependency union builder.
        expected = Expr::lam(BinderInfo::Default, nat(), expected.abstract_fvar(id(raw)));
    }
    assert_eq!(first_out, expected);
    let address = shared.as_ref() as *const Expr as usize;
    let entry = closer.contextual.maps().0[&address].clone();
    let root = entry.entry.dependencies().unwrap();
    assert_eq!(closer.dependencies[root].min_depth, 0);
    assert!(closer.dependencies.len() > 40);
    assert!(
        closer.dependencies.iter().any(|node| {
            matches!(node.dependency, Dependency::Join(left, right)
            if matches!(closer.dependencies[right].dependency,
                Dependency::Join(shared_left, _) if left == shared_left))
        }),
        "the retained dependency graph actually has a diamond"
    );
    closer.binder_depth = 3;
    closer.active.extend([(id(9), 0), (id(8), 1), (id(1), 2)]);
    assert!(closer.contextual.get(address, 3, 0).is_none());
    let (selected, route) = closer.contextual.named_only(address, 3, &shared).unwrap();
    assert_eq!(route, TermScopeCacheRoute::PrimaryNamedOnly);
    assert_eq!(selected.entry.dependencies(), Some(root));
    let before = closer.stats;
    let nodes = closer.dependencies.len();
    assert_eq!(
        closer.relative_dependencies(&entry, RebaseMode::NamedOnly),
        None
    );
    assert_eq!(closer.stats, before);
    assert_eq!(closer.dependencies.len(), nodes);
    assert!(closer.error.is_none());
    let cache = closer.diagnostic_report().cache;
    assert_eq!(cache.named_only_depth_screen_rejections, 1);
    assert_eq!(cache.dependency_rebase_underflow, 0);
    assert_eq!(cache.failed_rebase_dependency_nodes, 0);
    // The later Ordinary-screen policy now rejects this same impossible root
    // without the formerly charged/appended left prefix. No work is refunded.
    let mut ordinary = entry;
    ordinary.ordinary_count = 1;
    assert_eq!(
        closer.relative_dependencies(&ordinary, RebaseMode::Ordinary),
        None
    );
    assert_eq!(closer.stats, before);
    assert_eq!(closer.dependencies.len(), nodes);
    let cache = closer.diagnostic_report().cache;
    assert_eq!(cache.ordinary_depth_screen_rejections, 1);
    assert_eq!(cache.dependency_rebase_underflow, 0);
    assert_eq!(cache.failed_rebase_dependency_nodes, 0);
    retained_ids(&closer);
}

#[test]
fn equality_zero_offset_and_maximum_depth_keep_full_validation_and_identity() {
    // u32::MAX is a private arithmetic extreme, not a reachable depth claim;
    // the original Expr::MAX_BVAR_INDEX route is exercised separately below.
    for (old, new, depth) in [(3, 2, 1), (2, 2, 0), (u32::MAX, 1, u32::MAX - 1)] {
        let scope = TermScope::new();
        let mut closer = Closer::new(&scope, TermScopeLimits::default(), true);
        closer.binder_depth = new;
        closer.active.insert(id(1), 0);
        let root = closer.dependency_node(Dependency::Named(id(1), depth));
        let entry = cached(Some(root), old, 0);
        let result = closer
            .relative_dependencies(&entry, RebaseMode::NamedOnly)
            .unwrap()
            .unwrap();
        assert!(
            matches!(closer.dependencies[result].dependency, Dependency::Named(local, 0) if local == id(1))
        );
        assert_eq!(closer.stats.visits, 1);
        assert_eq!(closer.stats.context_check_visits, 1);
        assert_eq!(
            closer
                .diagnostic_report()
                .cache
                .named_only_depth_screen_rejections,
            0
        );
        assert_eq!(result == root, old == new);
        retained_ids(&closer);
    }
}

#[test]
fn no_root_internal_reads_and_inward_missing_binding_keep_their_guards() {
    let scope = TermScope::new();
    let mut closer = Closer::new(&scope, TermScopeLimits::default(), true);
    closer.binder_depth = 2;
    assert_eq!(
        closer.relative_dependencies(&cached(None, 3, 0), RebaseMode::NamedOnly),
        Some(None)
    );
    assert_eq!(closer.stats.visits, 0);
    for dependency in [Dependency::Named(id(1), 3), Dependency::Ordinary(0, 3)] {
        let root = closer.dependency_node(dependency);
        let before = closer.stats.context_check_visits;
        assert_eq!(
            closer.relative_dependencies(&cached(Some(root), 3, 0), RebaseMode::NamedOnly),
            Some(None)
        );
        assert_eq!(closer.stats.context_check_visits, before + 1);
    }
    let external = closer.dependency_node(Dependency::Named(id(1), 2));
    let internal = closer.dependency_node(Dependency::Ordinary(0, 3));
    let mixed = closer.dependency_node(Dependency::Join(external, internal));
    closer.active.insert(id(1), 1);
    let before = closer.stats.context_check_visits;
    let surviving = closer
        .relative_dependencies(&cached(Some(mixed), 3, 0), RebaseMode::NamedOnly)
        .unwrap()
        .unwrap();
    assert!(matches!(closer.dependencies[surviving].dependency,
        Dependency::Named(local, 1) if local == id(1)));
    assert_eq!(closer.stats.context_check_visits, before + 3);
    closer.active.remove(&id(1));
    let before = closer.stats.context_check_visits;
    assert_eq!(
        closer.relative_dependencies(&cached(Some(mixed), 3, 0), RebaseMode::NamedOnly),
        None
    );
    assert_eq!(closer.stats.context_check_visits, before + 2);
    assert_eq!(closer.diagnostic_report().cache.named_dependency_missing, 1);
    let root = closer.dependency_node(Dependency::Named(id(1), 0));
    let before = closer.stats;
    assert_eq!(
        closer.relative_dependencies(&cached(Some(root), 1, 0), RebaseMode::NamedOnly),
        None
    );
    assert_eq!(closer.stats.visits, before.visits + 1);
    assert_eq!(
        closer.stats.context_check_visits,
        before.context_check_visits + 1
    );
    let cache = closer.diagnostic_report().cache;
    assert_eq!(cache.dependency_shape_rejections, 0);
    assert_eq!(cache.named_dependency_missing, 2);
    assert_eq!(cache.named_only_depth_screen_rejections, 0);
    assert_eq!(cache.named_only_ordinary_rejections, 0);
    retained_ids(&closer);
}

#[test]
fn external_ordinary_low_depth_screens_but_equal_depth_still_probes_and_refuses() {
    for depth in [0, 1] {
        let scope = TermScope::new();
        let mut closer = Closer::new(&scope, TermScopeLimits::default(), true);
        closer.binder_depth = 2;
        let root = closer.dependency_node(Dependency::Ordinary(0, depth));
        assert_eq!(
            closer.relative_dependencies(&cached(Some(root), 3, 0), RebaseMode::NamedOnly),
            None
        );
        let cache = closer.diagnostic_report().cache;
        assert_eq!(
            cache.named_only_depth_screen_rejections,
            usize::from(depth == 0)
        );
        assert_eq!(
            cache.named_only_ordinary_rejections,
            usize::from(depth == 1)
        );
        assert_eq!(closer.stats.context_check_visits, usize::from(depth == 1));
        assert!(closer.error.is_none());
        retained_ids(&closer);
    }
}

#[test]
fn selected_missing_or_moved_primary_does_not_retry_a_genuinely_valid_spare() {
    for missing in [false, true] {
        let shared = Arc::new(Expr::app(Expr::const_str("Nat.succ"), Expr::fvar(id(1))));
        let mut scope = TermScope::new();
        let first = wrap(&mut scope, &[9, 8, 7, 1], 0, &shared);
        let middle = wrap(&mut scope, &[8, 1, 7], 0, &shared);
        let last = wrap(&mut scope, &[8, 1], 0, &shared);
        let mut closer = Closer::new(&scope, TermScopeLimits::default(), true);
        let first_out = first.fold_opt_or_clone(&mut closer);
        let _ = middle.fold_opt_or_clone(&mut closer);
        let address = shared.as_ref() as *const Expr as usize;
        let spare = closer.contextual.maps().1[&address].clone();
        assert_eq!(spare.binder_depth, 4);
        assert!(
            matches!(closer.dependencies[spare.entry.dependencies().unwrap()].dependency,
            Dependency::Named(local, 3) if local == id(1))
        );
        // Last binds id1 at1: this genuine spare can rebase3-(4-2)==1.
        if missing {
            // Deliberately corrupted private metadata must not admit a stale
            // output or license a retry. No public producer can inject this.
            let bad = closer.dependency_node(Dependency::Named(id(99), 1));
            let mut primary = closer.contextual.maps().0[&address].clone();
            primary.entry.dependencies = MemoEntry::compact(Some(bad));
            closer.contextual.insert(address, primary);
        }
        assert!(closer.contextual.get(address, 2, 0).is_none());
        let before = closer.diagnostic_report().cache;
        let last_out = last.fold_opt_or_clone(&mut closer);
        assert!(closer.error.is_none());
        assert_eq!(child(&first_out, 4), child(&last_out, 2));
        // The completed inverse restores the original output directly. The original
        // spare-attempt/probe assertions below still prohibit a candidate retry.
        assert!(Arc::ptr_eq(child(&first_out, 4), child(&last_out, 2)));

        let after = closer.diagnostic_report().cache;
        assert_eq!(
            after.spare_named_only_attempts,
            before.spare_named_only_attempts
        );
        assert_eq!(
            after.named_only_depth_screen_rejections,
            before.named_only_depth_screen_rejections
        );
        assert!(after.primary_named_only_attempts > before.primary_named_only_attempts);
        assert!(if missing {
            after.named_dependency_missing > before.named_dependency_missing
        } else {
            after.named_dependency_moved > before.named_dependency_moved
        });
        retained_ids(&closer);
    }
}

#[test]
fn original_selection_failure_inward_and_maximum_loose_read_do_not_use_the_screen() {
    for case in 0..3 {
        let shared = Arc::new(Expr::app(
            Expr::const_str("Nat.succ"),
            if case == 2 {
                Expr::bvar(Expr::MAX_BVAR_INDEX)
            } else {
                Expr::fvar(id(1))
            },
        ));
        let mut scope = TermScope::new();
        let arms = match case {
            0 => {
                let first = wrap(&mut scope, &[1], 5, &shared);
                let body = wrap(&mut scope, &[], 3, &shared);
                let middle = scope.lam(id(1), BinderInfo::Default, nat(), body);
                vec![first, middle, wrap(&mut scope, &[1], 1, &shared)]
            }
            1 => vec![
                wrap(&mut scope, &[1], 0, &shared),
                wrap(&mut scope, &[9, 8, 1], 0, &shared),
            ],
            _ => vec![
                wrap(&mut scope, &[], 1, &shared),
                wrap(&mut scope, &[1], 0, &shared),
            ],
        };
        let report = scope.close_with_diagnostics(
            &Expr::apps(Expr::const_str("structural"), arms),
            TermScopeLimits::default(),
        );
        if case == 2 {
            assert_eq!(report.result, Err(TermScopeError::IndexOverflow));
        } else {
            assert!(report.result.is_ok());
        }
        if case == 1 {
            assert!(report.diagnostics.cache.primary_named_only_attempts > 0);
            assert!(report.diagnostics.cache.named_only_contextual_hits > 0);
        } else {
            assert_eq!(report.diagnostics.cache.primary_named_only_attempts, 0);
        }
        assert_eq!(report.diagnostics.cache.spare_named_only_attempts, 0);
        assert_eq!(
            report.diagnostics.cache.named_only_depth_screen_rejections,
            0
        );
        if case == 0 {
            assert!(
                report
                    .diagnostics
                    .cache
                    .rejected_contextual_with_alternate_shape
                    > 0
            );
        }
    }
}

#[test]
fn zero_probe_rejection_is_not_a_budget_refund_and_public_caps_keep_observed_plain_parity() {
    let scope = TermScope::new();
    for depth in [0, 1] {
        let mut closer = Closer::new(
            &scope,
            TermScopeLimits {
                max_visits: 0,
                ..TermScopeLimits::default()
            },
            true,
        );
        closer.binder_depth = 2;
        closer.active.insert(id(1), 0);
        let root = closer.dependency_node(Dependency::Named(id(1), depth));
        assert_eq!(
            closer.relative_dependencies(&cached(Some(root), 3, 0), RebaseMode::NamedOnly),
            None
        );
        assert_eq!(closer.stats.visits, 0);
        assert_eq!(
            closer.error,
            (depth == 1).then_some(TermScopeError::VisitLimit)
        );
        assert_eq!(
            closer
                .diagnostic_report()
                .cache
                .named_only_depth_screen_rejections,
            usize::from(depth == 0)
        );
    }
    let shared = diamond();
    let mut scope = TermScope::new();
    let first = wrap(&mut scope, &[2, 9, 8, 1], 0, &shared);
    let last = wrap(&mut scope, &[9, 8, 1], 0, &shared);
    let input = Expr::apps(Expr::const_str("structural"), [first, last]);
    let full = scope.close_with_diagnostics(&input, TermScopeLimits::default());
    assert_eq!(full.result, Err(TermScopeError::OutOfScope(id(2))));
    assert!(full.diagnostics.cache.named_only_depth_screen_rejections > 0);
    let mut stopped_after_screen = 0;
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
        assert!(plain.observations.is_none());
        assert_eq!(
            plain.diagnostic_report().cache,
            TermScopeCacheDiagnostics::default()
        );
        retained_ids(&observed);
        let public = scope.close_with_diagnostics(&input, limits);
        assert_eq!(public.stats, observed.stats);
        assert_eq!(
            public.result,
            observed.error.clone().map_or(Ok(actual), Err)
        );
        assert_eq!(
            scope
                .close_with_limits(&input, limits)
                .map(|closed| closed.term),
            public.result
        );
        stopped_after_screen += usize::from(
            observed.error == Some(TermScopeError::VisitLimit)
                && public.diagnostics.cache.named_only_depth_screen_rejections > 0,
        );
    }
    assert!(stopped_after_screen > 0);
}

#[test]
fn actual_equal_minimum_boundary_reuses_strict_proof_arc_and_replays_dag() {
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
    let mut arms = Vec::new();
    let mut oracle = Vec::new();
    for names in [&[9, 8, 1][..], &[1][..]] {
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
        arms.push(term);
        oracle.push(expected);
    }
    let input = Expr::apps(Expr::const_str("structural"), arms);
    let report = scope.close_with_diagnostics(&input, TermScopeLimits::default());
    let output = report.result.unwrap();
    let arms = output.get_app_args();
    assert!(Arc::ptr_eq(child(arms[0], 3), child(arms[1], 1)));
    assert_eq!(
        report.diagnostics.cache.named_only_depth_screen_rejections,
        0
    );
    assert!(report.diagnostics.cache.named_only_contextual_hits > 0);
    assert!(report.diagnostics.cache.successful_dependency_probe_visits > 0);
    let mut env = Environment::new();
    env.init_eq().unwrap();
    env.init_nat().unwrap();
    for ((arm, expected), depth) in arms.into_iter().zip(oracle).zip([3, 1]) {
        assert_eq!(*arm, expected);
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
        checker.check_type(arm, &ty).unwrap();
        let inferred = checker.infer_type(arm).unwrap();
        assert!(!checker.is_def_eq(&inferred, &forged));
        let bytes = trust_ir::proof::encode_clean_expr_dag_v2(arm).unwrap();
        let decoded = trust_ir::proof::decode_clean_expr_dag_v2(&bytes).unwrap();
        assert_eq!(&decoded, arm);
        assert!(env.audit_certification(&ty, &decoded).is_certified());
        assert!(!env.audit_certification(&forged, &decoded).is_certified());
    }
}
