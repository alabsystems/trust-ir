// Copyright 2026 Andrew Yates | Licensed under the Apache License, Version 2.0

//! Exact inward projections, not unconditional reuse in deeper contexts.

use super::*;
use clean_kernel::{BinderInfo, Environment, Level, TypeChecker};

fn id(raw: u64) -> FVarId {
    FVarId::new(raw)
}
fn nat() -> Expr {
    Expr::const_str("Nat")
}
fn ordinary(body: Expr) -> Expr {
    Expr::lam(BinderInfo::Default, nat(), body)
}
fn wrap(
    scope: &mut TermScope,
    names: &[u64],
    ordinary_count: usize,
    shared: &Arc<Expr>,
    shell: &Expr,
) -> Expr {
    let mut term = Expr::app_arc(Arc::new(shell.clone()), shared.clone());
    for raw in names.iter().rev() {
        term = scope.lam(id(*raw), BinderInfo::Default, nat(), term);
    }
    for _ in 0..ordinary_count {
        term = ordinary(term);
    }
    term
}
fn reference(names: &[u64], ordinary_count: usize, shared: &Expr, shell: &Expr) -> Expr {
    let mut term = Expr::app(shell.clone(), shared.clone());
    for raw in names.iter().rev() {
        term = ordinary(term.abstract_fvar(id(*raw)));
    }
    for _ in 0..ordinary_count {
        term = ordinary(term);
    }
    term
}
fn child(mut term: &Expr, depth: usize) -> &Arc<Expr> {
    for _ in 0..depth {
        let ExprKind::Lam(_, _, body) = term.kind() else {
            panic!("actual binder")
        };
        term = body;
    }
    let ExprKind::App(_, child) = term.kind() else {
        panic!("actual shared edge")
    };
    child
}
fn check(term: &Expr, goal: &Expr) {
    let mut env = Environment::new();
    env.init_eq().unwrap();
    env.init_nat().unwrap();
    let mut checker = TypeChecker::new(&env);
    checker.set_allow_unsafe(false);
    checker.set_allow_partial(false);
    checker.check_type(term, goal).unwrap();
    assert!(!checker.heartbeat_spent());
}
fn arrow(mut goal: Expr, count: usize) -> Expr {
    for _ in 0..count {
        goal = Expr::arrow(nat(), goal);
    }
    goal
}
fn eq(left: Expr, right: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
        [nat(), left, right],
    )
}
fn retained(closer: &Closer<'_>) {
    let valid = |entry: &MemoEntry| {
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
        valid(entry);
    }
    for entry in closer.named_closed.values() {
        valid(&entry.entry);
    }
    let (primary, spare) = closer.contextual.maps();
    for entry in primary.values().chain(spare.values()) {
        valid(&entry.entry);
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
}

#[test]
fn shallow_and_deep_first_named_projections_reuse_exact_typed_arcs() {
    // The ordinary read is INTERNAL to the shared subtree. Pruning at the
    // deeper new parent would wrongly discard its external named companion.
    let shared = Arc::new(Expr::app(
        ordinary(Expr::apps(
            Expr::const_str("Nat.add"),
            [Expr::bvar(0), Expr::fvar(id(1))],
        )),
        Expr::nat_lit(0u64),
    ));
    assert!(!shared.has_loose_bvars_quick());
    let shell = Expr::const_str("Nat.succ");
    for names in [[vec![1], vec![9, 8, 1]], [vec![9, 8, 1], vec![1]]] {
        let mut scope = TermScope::new();
        let arms = names
            .iter()
            .map(|names| wrap(&mut scope, names, 0, &shared, &shell))
            .collect::<Vec<_>>();
        let report = scope.close_with_diagnostics(
            &Expr::apps(Expr::const_str("structural"), arms),
            TermScopeLimits::default(),
        );
        let closed = report.result.unwrap();
        let arms = closed.get_app_args();
        for (arm, names) in arms.iter().zip(&names) {
            assert_eq!(**arm, reference(names, 0, &shared, &shell));
            check(arm, &arrow(nat(), names.len()));
        }
        assert!(Arc::ptr_eq(
            child(arms[0], names[0].len()),
            child(arms[1], names[1].len())
        ));
        assert!(report.diagnostics.cache.named_only_contextual_hits > 0);
        assert!(report.stats.context_check_visits > 0);
    }
}

#[test]
fn inward_typed_proofs_keep_strict_kernel_and_lossless_dag_obligations() {
    let local = Expr::fvar(id(1));
    let shared = Arc::new(Expr::apps(
        Expr::const_(
            Name::from_string("Eq.refl"),
            vec![Level::succ(Level::zero())],
        ),
        [nat(), local.clone()],
    ));
    let shell = Expr::lam(BinderInfo::Default, eq(local.clone(), local), Expr::bvar(0));
    let mut scope = TermScope::new();
    let names = [vec![1], vec![9, 8, 1]];
    let arms = names
        .iter()
        .map(|names| wrap(&mut scope, names, 0, &shared, &shell))
        .collect::<Vec<_>>();
    let report = scope.close_with_diagnostics(
        &Expr::apps(Expr::const_str("structural"), arms),
        TermScopeLimits::default(),
    );
    let closed = report.result.unwrap();
    let arms = closed.get_app_args();
    assert!(Arc::ptr_eq(child(arms[0], 1), child(arms[1], 3)));
    let mut env = Environment::new();
    env.init_eq().unwrap();
    env.init_nat().unwrap();
    for (arm, names) in arms.iter().zip(&names) {
        assert_eq!(**arm, reference(names, 0, &shared, &shell));
        let mut goal = Expr::pi(BinderInfo::Default, nat(), eq(Expr::bvar(0), Expr::bvar(0)));
        let mut wrong = Expr::pi(
            BinderInfo::Default,
            nat(),
            eq(
                Expr::bvar(0),
                Expr::app(Expr::const_str("Nat.succ"), Expr::bvar(0)),
            ),
        );
        for _ in 1..names.len() {
            goal = Expr::arrow(nat(), goal);
            wrong = Expr::arrow(nat(), wrong);
        }
        check(arm, &goal);
        assert!(env.audit_certification(&goal, arm).is_certified());
        assert!(!env.audit_certification(&wrong, arm).is_certified());
        let bytes = trust_ir::proof::encode_clean_expr_dag_v2(arm).unwrap();
        let decoded = trust_ir::proof::decode_clean_expr_dag_v2(&bytes).unwrap();
        assert_eq!(&decoded, *arm);
        assert_eq!(
            trust_ir::proof::encode_clean_expr_dag_v2(&decoded).unwrap(),
            bytes
        );
        assert!(env.audit_certification(&goal, &decoded).is_certified());
        assert!(!env.audit_certification(&wrong, &decoded).is_certified());
    }
    assert!(report.diagnostics.cache.named_only_contextual_hits > 0);
}

#[test]
fn fixed_outer_and_inexactly_moved_named_bindings_rebuild_instead_of_capture() {
    let shared = Arc::new(Expr::app(Expr::const_str("Nat.succ"), Expr::fvar(id(1))));
    let shell = Expr::const_str("Nat.succ");
    for last_names in [vec![1, 9], vec![9, 1, 8]] {
        let mut scope = TermScope::new();
        let first = wrap(&mut scope, &[1], 0, &shared, &shell);
        let last = wrap(&mut scope, &last_names, 0, &shared, &shell);
        let report = scope.close_with_diagnostics(
            &Expr::apps(Expr::const_str("structural"), [first, last]),
            TermScopeLimits::default(),
        );
        let closed = report.result.unwrap();
        let arms = closed.get_app_args();
        assert_eq!(*arms[0], reference(&[1], 0, &shared, &shell));
        assert_eq!(*arms[1], reference(&last_names, 0, &shared, &shell));
        check(arms[0], &arrow(nat(), 1));
        check(arms[1], &arrow(nat(), last_names.len()));
        assert!(!Arc::ptr_eq(
            child(arms[0], 1),
            child(arms[1], last_names.len())
        ));
        assert!(report.diagnostics.cache.named_dependency_moved > 0);
    }
}

#[test]
fn missing_named_bindings_and_hidden_shadowing_still_report_actual_scope_errors() {
    let shell = Expr::const_str("Nat.succ");
    let mut scope = TermScope::new();
    let shared = Arc::new(Expr::app(shell.clone(), Expr::fvar(id(1))));
    let first = wrap(&mut scope, &[1], 0, &shared, &shell);
    let missing = wrap(&mut scope, &[9, 8, 2], 0, &shared, &shell);
    let report = scope.close_with_diagnostics(
        &Expr::apps(Expr::const_str("structural"), [first, missing]),
        TermScopeLimits::default(),
    );
    assert_eq!(report.result, Err(TermScopeError::OutOfScope(id(1))));
    assert!(report.diagnostics.cache.named_dependency_missing > 0);

    let shared = Arc::new(scope.lam(id(7), BinderInfo::Default, nat(), Expr::fvar(id(1))));
    let first = wrap(&mut scope, &[1], 0, &shared, &shell);
    let shadow = wrap(&mut scope, &[7, 9, 1], 0, &shared, &shell);
    let mut closer = Closer::new(&scope, TermScopeLimits::default(), true);
    let _ = closer.fold_shared(&first);
    let address = shared.as_ref() as *const Expr as usize;
    assert!(
        closer.contextual.maps().0[&address]
            .entry
            .declarations()
            .is_some()
    );
    assert!(closer.contextual.named_only(address, 4, &shared).is_none());
    let report = scope.close_with_diagnostics(
        &Expr::apps(Expr::const_str("structural"), [first, shadow]),
        TermScopeLimits::default(),
    );
    assert_eq!(report.result, Err(TermScopeError::ShadowedLocal(id(7))));
}

#[test]
fn original_loose_reads_are_excluded_and_keep_index_overflow() {
    let shell = Expr::const_str("Nat.succ");
    let shared = Arc::new(Expr::apps(
        Expr::const_str("Nat.add"),
        [Expr::fvar(id(1)), Expr::bvar(0)],
    ));
    let mut scope = TermScope::new();
    let first = wrap(&mut scope, &[1], 1, &shared, &shell);
    let last = wrap(&mut scope, &[9, 1], 2, &shared, &shell);
    let mut closer = Closer::new(&scope, TermScopeLimits::default(), true);
    let _ = closer.fold_shared(&first);
    let address = shared.as_ref() as *const Expr as usize;
    assert!(closer.contextual.named_only(address, 4, &shared).is_none());
    let report = scope.close_with_diagnostics(
        &Expr::apps(Expr::const_str("structural"), [first, last]),
        TermScopeLimits::default(),
    );
    let closed = report.result.unwrap();
    let arms = closed.get_app_args();
    assert_eq!(*arms[0], reference(&[1], 1, &shared, &shell));
    assert_eq!(*arms[1], reference(&[9, 1], 2, &shared, &shell));
    check(arms[0], &arrow(nat(), 2));
    check(arms[1], &arrow(nat(), 4));
    // Eligible descendants may reuse independently; the original loose root
    // itself must rebuild because its ordinary read changes output index.
    assert!(!Arc::ptr_eq(child(arms[0], 2), child(arms[1], 4)));
    assert_ne!(child(arms[0], 2), child(arms[1], 4));

    let shared = Arc::new(Expr::app(shell.clone(), Expr::bvar(Expr::MAX_BVAR_INDEX)));
    let overflow = wrap(&mut scope, &[1], 0, &shared, &shell);
    assert_eq!(scope.close(&overflow), Err(TermScopeError::IndexOverflow));
}

#[test]
fn one_failed_inward_primary_never_retries_a_valid_spare() {
    let shared = Arc::new(Expr::app(Expr::const_str("Nat.succ"), Expr::fvar(id(1))));
    let shell = Expr::const_str("Nat.succ");
    let mut scope = TermScope::new();
    let names = [vec![1], vec![1, 9], vec![9, 8, 1]];
    let input = Expr::apps(
        Expr::const_str("structural"),
        names
            .iter()
            .map(|names| wrap(&mut scope, names, 0, &shared, &shell))
            .collect::<Vec<_>>(),
    );
    let report = scope.close_with_diagnostics(&input, TermScopeLimits::default());
    let output = report.result.unwrap();
    let arms = output.get_app_args();
    for (arm, names) in arms.iter().zip(&names) {
        assert_eq!(**arm, reference(names, 0, &shared, &shell));
    }
    assert_eq!(child(arms[0], 1), child(arms[2], 3));
    // The completed inverse restores the original output directly. The original
    // spare-attempt/probe assertions below still prohibit a candidate retry.
    assert!(Arc::ptr_eq(child(arms[0], 1), child(arms[2], 3)));
    assert!(report.diagnostics.cache.named_dependency_moved > 0);
    assert_eq!(report.diagnostics.cache.spare_named_only_attempts, 0);
}

#[test]
fn inward_dependency_boundaries_keep_cached_depth_pruning_and_checked_addition() {
    // Private u32 boundaries are arithmetic controls, not giant public scopes.
    let scope = TermScope::new();
    let mut closer = Closer::new(&scope, TermScopeLimits::default(), true);
    closer.binder_depth = u32::MAX;
    closer.active.insert(id(1), u32::MAX - 1);
    let external = closer.dependency_node(Dependency::Named(id(1), 1));
    let internal = closer.dependency_node(Dependency::Ordinary(usize::MAX, 2));
    let root = closer.dependency_node(Dependency::Join(external, internal));
    let cached = ContextEntry {
        entry: MemoEntry {
            replacement: None,
            declarations: None,
            dependencies: MemoEntry::compact(Some(root)),
        },
        context: 1,
        binder_depth: 2,
        ordinary_count: 0,
    };
    let result = closer
        .relative_dependencies(&cached, RebaseMode::NamedOnly)
        .unwrap()
        .unwrap();
    assert!(
        matches!(closer.dependencies[result].dependency, Dependency::Named(local, depth) if local == id(1) && depth == u32::MAX - 1)
    );
    assert_eq!(closer.stats.context_check_visits, 3);
    assert_eq!(
        closer
            .diagnostic_report()
            .cache
            .named_only_ordinary_rejections,
        0
    );
    // A genuine external depth is below cachedD; addedD=newD-cachedD thus
    // cannot overflow u32. Checked addition remains fail-closed regardless.
    let external_ordinary = closer.dependency_node(Dependency::Ordinary(0, 1));
    let mut cached = cached;
    cached.entry.dependencies = MemoEntry::compact(Some(external_ordinary));
    assert_eq!(
        closer.relative_dependencies(&cached, RebaseMode::NamedOnly),
        None
    );
    assert_eq!(
        closer
            .diagnostic_report()
            .cache
            .named_only_ordinary_rejections,
        1
    );
    retained(&closer);
}

#[test]
fn incomplete_inward_probes_roll_back_and_never_publish_an_alias() {
    let shared = Arc::new(Expr::apps(
        Expr::const_str("Nat.add"),
        [Expr::fvar(id(1)), Expr::fvar(id(2))],
    ));
    let shell = Expr::const_str("Nat.succ");
    let mut scope = TermScope::new();
    let first = wrap(&mut scope, &[1, 2], 0, &shared, &shell);
    let last = wrap(&mut scope, &[9, 8, 1, 2], 0, &shared, &shell);
    let input = Expr::apps(Expr::const_str("structural"), [first.clone(), last]);
    let full = scope
        .close_with_limits(&input, TermScopeLimits::default())
        .unwrap();
    for cap in 0..=full.stats.visits {
        let report = scope.close_with_diagnostics(
            &input,
            TermScopeLimits {
                max_visits: cap,
                ..TermScopeLimits::default()
            },
        );
        if cap < full.stats.visits {
            assert_eq!(report.result, Err(TermScopeError::VisitLimit));
            assert_eq!(report.stats.visits, cap);
        } else {
            assert_eq!(report.result, Ok(full.term.clone()));
        }
    }
    let address = shared.as_ref() as *const Expr as usize;
    for probe_cap in 0..3 {
        let mut closer = Closer::new(&scope, TermScopeLimits::default(), true);
        let _ = closer.fold_shared(&first);
        assert!(closer.error.is_none());
        let nodes = closer.dependencies.len();
        let initial = closer.stats.visits;
        // Isolate the actual completed child's inward guard. These private
        // frame fields model the final named prefix, not a second closer.
        closer.context = usize::MAX;
        closer.binder_depth = 4;
        closer.active.insert(id(1), 2);
        closer.active.insert(id(2), 3);
        closer.limits.max_visits = initial + 1 + probe_cap;
        let _ = closer.fold_shared(&shared);
        assert_eq!(closer.error, Some(TermScopeError::VisitLimit));
        assert_eq!(closer.stats.visits, closer.limits.max_visits);
        assert_eq!(closer.dependencies.len(), nodes);
        assert!(!closer.memo.contains_key(&(address, usize::MAX)));
        assert_eq!(
            closer.diagnostic_report().first_stop.unwrap().phase,
            TermScopeStopPhase::RelativeDependency
        );
        retained(&closer);
    }
}
