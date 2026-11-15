// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Bounded contextual retention controls, not proof or timing authority.

use super::*;
use clean_kernel::{BinderInfo, Environment, TypeChecker};

fn nat() -> Expr {
    Expr::const_str("Nat")
}

fn successors(mut child: Arc<Expr>, count: usize) -> Arc<Expr> {
    for _ in 0..count {
        child = Arc::new(Expr::app_arc(Arc::new(Expr::const_str("Nat.succ")), child));
    }
    child
}

fn let_body(expression: &Expr) -> &Arc<Expr> {
    let ExprKind::Let(_, _, _, body, _) = expression.kind() else {
        panic!("expected actual retained let")
    };
    body
}

fn alternating_depths(depth: usize, pairs: usize) -> (TermScope, Expr, Expr) {
    let mut scope = TermScope::new();
    let shared = successors(Arc::new(Expr::fvar(FVarId::new(1))), depth);
    let mut open = Expr::nat_lit(0u64);
    let mut expected = open.clone();
    for ordinal in (0..2 * pairs).rev() {
        let lets = 1 + ordinal % 2;
        // The shared root is a real child edge, not a newly allocated named
        // binder body root. Fresh sibling IDs force distinct exact contexts.
        let mut arm = Expr::app_arc(Arc::new(Expr::const_str("Nat.succ")), shared.clone());
        let mut wanted = Expr::app(
            Expr::const_str("Nat.succ"),
            successors(Arc::new(Expr::bvar(lets as u32)), depth)
                .as_ref()
                .clone(),
        );
        for level in 0..lets {
            arm = scope.let_named(
                FVarId::new(2 + (ordinal * 2 + level) as u64),
                Name::anon(),
                nat(),
                Expr::nat_lit(0u64),
                arm,
                false,
            );
            wanted = Expr::let_named(Name::anon(), nat(), Expr::nat_lit(0u64), wanted, false);
        }
        open = Expr::apps(Expr::const_str("Nat.add"), [arm, open]);
        expected = Expr::apps(Expr::const_str("Nat.add"), [wanted, expected]);
    }
    let open = scope.lam(FVarId::new(1), BinderInfo::Default, nat(), open);
    let expected = Expr::lam(BinderInfo::Default, nat(), expected);
    (scope, open, expected)
}

fn named_arm(scope: &mut TermScope, locals: &[u64], shared: &Arc<Expr>) -> Expr {
    let mut body = Expr::app_arc(Arc::new(Expr::const_str("Nat.succ")), shared.clone());
    for local in locals.iter().rev() {
        body = scope.lam(FVarId::new(*local), BinderInfo::Default, nat(), body);
    }
    body
}

fn arguments(expression: &Expr) -> Vec<&Arc<Expr>> {
    let mut result = Vec::new();
    let mut cursor = expression;
    while let ExprKind::App(function, argument) = cursor.kind() {
        result.push(argument);
        cursor = function;
    }
    result.reverse();
    result
}

fn arm_child(mut expression: &Expr, depth: usize) -> &Arc<Expr> {
    for _ in 0..depth {
        expression = match expression.kind() {
            ExprKind::Lam(_, _, body) | ExprKind::Let(_, _, _, body, _) => body,
            _ => panic!("expected exact binder spine"),
        };
    }
    let ExprKind::App(_, shared) = expression.kind() else {
        panic!("expected actual shared edge")
    };
    shared
}

#[test]
fn alternating_depths_retain_typed_open_child_variants() {
    let (scope, open, expected) = alternating_depths(64, 12);
    let mut env = Environment::new();
    env.init_nat().unwrap();
    let ty = Expr::arrow(nat(), nat());
    let mut checker = TypeChecker::new(&env);
    checker.set_heartbeat_limit(2_000_000);
    // Independent ordinary-kernel oracle is validated before the performance
    // assertion, so a cache miss cannot conceal a changed source result.
    checker.check_type(&expected, &ty).unwrap();
    let closed = scope
        .close_with_limits(&open, TermScopeLimits::default())
        .unwrap();
    assert_eq!(closed.term, expected);
    checker.check_type(&closed.term, &ty).unwrap();
    eprintln!(
        "alternating-depths typed oracle PASS; work={:?}",
        closed.stats
    );
    let ExprKind::Lam(_, _, body) = closed.term.kind() else {
        panic!("expected outer lambda")
    };
    let mut cursor = body;
    let mut retained: [Option<Arc<Expr>>; 2] = [None, None];
    for ordinal in 0..24 {
        let ExprKind::App(function, tail) = cursor.kind() else {
            panic!("expected actual Nat.add")
        };
        let ExprKind::App(_, arm) = function.kind() else {
            panic!("expected actual Nat.add argument")
        };
        let mut result = arm;
        for _ in 0..1 + ordinal % 2 {
            result = let_body(result);
        }
        let ExprKind::App(_, shared) = result.kind() else {
            panic!("expected shared child")
        };
        if let Some(previous) = &retained[ordinal % 2] {
            assert!(
                Arc::ptr_eq(previous, shared),
                "projection {} was needlessly transformed again at arm {ordinal}",
                ordinal % 2
            );
        } else {
            retained[ordinal % 2] = Some(shared.clone());
        }
        cursor = tail;
    }
    assert!(!Arc::ptr_eq(
        retained[0].as_ref().unwrap(),
        retained[1].as_ref().unwrap()
    ));
}

#[test]
fn alternating_ordinary_counts_keep_typed_distinct_denotations() {
    let mut scope = TermScope::new();
    let shared = Arc::new(Expr::apps(
        Expr::const_str("Nat.add"),
        [
            successors(Arc::new(Expr::fvar(FVarId::new(1))), 32)
                .as_ref()
                .clone(),
            Expr::bvar(0),
        ],
    ));
    let mut actual = Expr::nat_lit(0u64);
    let mut expected = actual.clone();
    for ordinal in (0..16).rev() {
        let mut arm = Expr::app_arc(Arc::new(Expr::const_str("Nat.succ")), shared.clone());
        let mut wanted = Expr::app(
            Expr::const_str("Nat.succ"),
            Expr::apps(
                Expr::const_str("Nat.add"),
                [
                    successors(Arc::new(Expr::bvar(2)), 32).as_ref().clone(),
                    Expr::bvar(if ordinal % 2 == 0 { 3 } else { 0 }),
                ],
            ),
        );
        for level in 0..2 {
            wanted = Expr::let_named(Name::anon(), nat(), Expr::nat_lit(0u64), wanted, false);
            arm = if ordinal % 2 == 1 && level == 0 {
                Expr::let_named(Name::anon(), nat(), Expr::nat_lit(0u64), arm, false)
            } else {
                scope.let_named(
                    FVarId::new(2 + (ordinal * 2 + level) as u64),
                    Name::anon(),
                    nat(),
                    Expr::nat_lit(0u64),
                    arm,
                    false,
                )
            };
        }
        actual = Expr::apps(Expr::const_str("Nat.add"), [arm, actual]);
        expected = Expr::apps(Expr::const_str("Nat.add"), [wanted, expected]);
    }
    let actual = scope.lam(FVarId::new(1), BinderInfo::Default, nat(), actual);
    let actual = Expr::lam(BinderInfo::Default, nat(), actual);
    let expected = Expr::lam(
        BinderInfo::Default,
        nat(),
        Expr::lam(BinderInfo::Default, nat(), expected),
    );
    let closed = scope
        .close_with_limits(&actual, TermScopeLimits::default())
        .unwrap();
    assert_eq!(closed.term, expected);
    let mut env = Environment::new();
    env.init_nat().unwrap();
    TypeChecker::new(&env)
        .check_type(&closed.term, &Expr::arrow(nat(), Expr::arrow(nat(), nat())))
        .unwrap();
    let mut cursor = &closed.term;
    for _ in 0..2 {
        let ExprKind::Lam(_, _, body) = cursor.kind() else {
            panic!("outer lambda")
        };
        cursor = body;
    }
    let mut retained: [Option<Arc<Expr>>; 2] = [None, None];
    for ordinal in 0..16 {
        let ExprKind::App(function, tail) = cursor.kind() else {
            panic!("sum")
        };
        let ExprKind::App(_, arm) = function.kind() else {
            panic!("sum argument")
        };
        let child = arm_child(arm, 2);
        if let Some(previous) = &retained[ordinal % 2] {
            assert!(Arc::ptr_eq(previous, child));
        } else {
            retained[ordinal % 2] = Some(child.clone());
        }
        cursor = tail;
    }
    assert_ne!(retained[0], retained[1]);
    eprintln!("alternating-ordinary-counts work={:?}", closed.stats);
}

#[test]
fn failed_primary_dependency_rebuild_keeps_distinct_spare() {
    // Transformation-only controls below deliberately need no type/admission
    // authority; the independent typed workloads above supply that oracle.
    let mut scope = TermScope::new();
    let shared = successors(Arc::new(Expr::fvar(FVarId::new(1))), 3);
    let frames: &[&[u64]] = &[&[1, 2], &[1, 3, 4], &[1, 5], &[6, 1], &[1, 7, 8], &[9, 1]];
    let arms: Vec<_> = frames
        .iter()
        .map(|ids| named_arm(&mut scope, ids, &shared))
        .collect();
    let closed = scope
        .close(&Expr::apps(Expr::const_str("structural"), arms))
        .unwrap();
    let arms = arguments(&closed);
    let outputs: Vec<_> = arms
        .iter()
        .zip(frames)
        .map(|(arm, ids)| arm_child(arm, ids.len()))
        .collect();
    for (output, index) in outputs.iter().zip([1, 2, 1, 0, 2, 0]) {
        assert_eq!(
            output.as_ref(),
            successors(Arc::new(Expr::bvar(index)), 3).as_ref()
        );
    }
    assert!(Arc::ptr_eq(outputs[0], outputs[2]));
    assert!(Arc::ptr_eq(outputs[1], outputs[4]));
    assert!(Arc::ptr_eq(outputs[3], outputs[5]));
}

#[test]
fn spare_checks_missing_and_hidden_declarations_in_original_order() {
    for typed_dependency in [false, true] {
        let mut scope = TermScope::new();
        let hidden = scope.lam(
            FVarId::new(9),
            BinderInfo::Default,
            if typed_dependency {
                Expr::fvar(FVarId::new(100))
            } else {
                nat()
            },
            Expr::fvar(FVarId::new(1)),
        );
        let shared = Arc::new(hidden);
        let frames: &[&[u64]] = if typed_dependency {
            &[&[100, 1], &[100, 1, 2]]
        } else {
            &[&[1, 2], &[1, 3, 4]]
        };
        let warm: Vec<_> = frames
            .iter()
            .map(|ids| named_arm(&mut scope, ids, &shared))
            .collect();
        for (last, expected) in [
            (
                &[1, 9][..],
                if typed_dependency {
                    TermScopeError::OutOfScope(FVarId::new(100))
                } else {
                    TermScopeError::ShadowedLocal(FVarId::new(9))
                },
            ),
            (
                &[5, 6][..],
                TermScopeError::OutOfScope(FVarId::new(if typed_dependency { 100 } else { 1 })),
            ),
        ] {
            let mut arms = warm.clone();
            arms.push(named_arm(&mut scope, last, &shared));
            assert_eq!(
                scope.close(&Expr::apps(Expr::const_str("structural"), arms)),
                Err(expected)
            );
        }
    }
}

#[test]
fn spare_checks_actual_ordinary_positions_and_overflow() {
    let mut scope = TermScope::new();
    let shared = successors(Arc::new(Expr::bvar(0)), 1);
    let wrapped = || Expr::app_arc(Arc::new(Expr::const_str("Nat.succ")), shared.clone());
    let ordinary = |body| Expr::lam(BinderInfo::Default, nat(), body);
    let a = ordinary(wrapped());
    let a = scope.lam(FVarId::new(7), BinderInfo::Default, nat(), a);
    let b = ordinary(wrapped());
    let b = scope.lam(FVarId::new(9), BinderInfo::Default, nat(), b);
    let b = scope.lam(FVarId::new(8), BinderInfo::Default, nat(), b);
    let last = scope.lam(FVarId::new(10), BinderInfo::Default, nat(), wrapped());
    let closed = scope
        .close(&Expr::apps(
            Expr::const_str("structural"),
            [a, b, ordinary(last)],
        ))
        .unwrap();
    let arms = arguments(&closed);
    assert_eq!(
        arm_child(arms[2], 2).as_ref(),
        &Expr::app(Expr::const_str("Nat.succ"), Expr::bvar(1))
    );
    let max = successors(Arc::new(Expr::bvar(Expr::MAX_BVAR_INDEX)), 1);
    let ordinary_max = ordinary(Expr::app_arc(
        Arc::new(Expr::const_str("Nat.succ")),
        max.clone(),
    ));
    let named_max = named_arm(&mut scope, &[20], &max);
    assert_eq!(
        scope.close(&Expr::apps(
            Expr::const_str("structural"),
            [max.as_ref().clone(), ordinary_max, named_max]
        )),
        Err(TermScopeError::IndexOverflow)
    );
}

#[test]
fn partial_guard_does_not_promote_or_publish_exact_alias() {
    let mut scope = TermScope::new();
    let shared = Arc::new(scope.lam(
        FVarId::new(9),
        BinderInfo::Default,
        nat(),
        Expr::fvar(FVarId::new(1)),
    ));
    let a = named_arm(&mut scope, &[1, 2], &shared);
    let b = named_arm(&mut scope, &[1, 3, 4], &shared);
    let last = named_arm(&mut scope, &[1, 5], &shared);
    let address = shared.as_ref() as *const Expr as usize;
    let mut complete = Closer::new(&scope, TermScopeLimits::default(), false);
    let _ = complete.fold_shared(&a);
    let _ = complete.fold_shared(&b);
    assert!(complete.error.is_none());
    let warm_visits = complete.stats.visits;
    let mut limited = Closer::new(
        &scope,
        TermScopeLimits {
            max_visits: warm_visits + 8,
            ..TermScopeLimits::default()
        },
        false,
    );
    let _ = limited.fold_shared(&a);
    let _ = limited.fold_shared(&b);
    let snapshot = |closer: &Closer<'_>| {
        let (primary, spare) = closer.contextual.maps();
        (
            primary[&address].context,
            spare[&address].context,
            primary.len(),
            spare.len(),
        )
    };
    let before = snapshot(&limited);
    let probes = limited.stats.context_check_visits;
    let _ = limited.fold_shared(&last);
    assert_eq!(limited.error, Some(TermScopeError::VisitLimit));
    assert_eq!(limited.stats.visits, warm_visits + 8);
    assert_eq!(limited.stats.context_check_visits, probes + 1);
    assert_eq!(snapshot(&limited), before);
    let outer = limited.contexts[&(0, ContextFrame::Named(FVarId::new(1)))];
    let failed_context = limited.contexts[&(outer, ContextFrame::Named(FVarId::new(5)))];
    assert!(!limited.memo.contains_key(&(address, failed_context)));
}

#[test]
fn two_way_storage_is_sparse_bounded_and_scoped_to_each_close() {
    let (scope, open, expected) = alternating_depths(4, 2);
    let mut closer = Closer::new(&scope, TermScopeLimits::default(), false);
    assert_eq!(open.fold_opt_or_clone(&mut closer), expected);
    assert!(closer.error.is_none());
    let (primary, spare) = closer.contextual.maps();
    assert!(!spare.is_empty() && spare.len() <= primary.len());
    assert!(primary.len() + spare.len() <= 2 * closer.stats.transformed_nodes);
    eprintln!(
        "two-way storage primary={}/{} spare={}/{} memo={} dependencies={} footprints={} entry_bytes={} key_entry_bytes={} empty_maps_bytes={}",
        primary.len(),
        primary.capacity(),
        spare.len(),
        spare.capacity(),
        closer.memo.len(),
        closer.dependencies.len(),
        closer.footprints.len(),
        std::mem::size_of::<ContextEntry>(),
        std::mem::size_of::<(usize, ContextEntry)>(),
        std::mem::size_of::<ContextCandidates>()
    );
    let complete = scope.close_with_diagnostics(&open, TermScopeLimits::default());
    for cap in 0..complete.stats.visits {
        let report = scope.close_with_diagnostics(
            &open,
            TermScopeLimits {
                max_visits: cap,
                ..TermScopeLimits::default()
            },
        );
        assert_eq!(report.result, Err(TermScopeError::VisitLimit));
        assert_eq!(report.stats.visits, cap);
    }
    let again = scope.close_with_diagnostics(&open, TermScopeLimits::default());
    assert_eq!(again.result, complete.result);
    assert_eq!(again.stats, complete.stats);
    assert_eq!(TermScope::new().close(&expected).unwrap(), expected);
    let mut depth_scope = TermScope::new();
    let leaf = Arc::new(Expr::fvar(FVarId::new(1)));
    let a = named_arm(&mut depth_scope, &[1, 2], &leaf);
    let b = named_arm(&mut depth_scope, &[1, 3, 4], &leaf);
    let deep = successors(leaf.clone(), 20);
    let last = named_arm(&mut depth_scope, &[1, 5], &deep);
    let input = Expr::apps(Expr::const_str("structural"), [a, b, last]);
    let mut depth_closer = Closer::new(
        &depth_scope,
        TermScopeLimits {
            max_depth: 16,
            ..TermScopeLimits::default()
        },
        false,
    );
    let _ = input.fold_opt_or_clone(&mut depth_closer);
    assert_eq!(depth_closer.error, Some(TermScopeError::DepthLimit));
    let address = leaf.as_ref() as *const Expr as usize;
    assert!(depth_closer.contextual.get(address, 2, 0).is_some());
    assert!(depth_closer.contextual.get(address, 3, 0).is_some());
    assert!(depth_scope.close(&input).is_ok());
    let mut mono_scope = TermScope::new();
    let shared = successors(Arc::new(Expr::fvar(FVarId::new(1))), 4);
    let mono = named_arm(&mut mono_scope, &[1], &shared);
    let mut mono_closer = Closer::new(&mono_scope, TermScopeLimits::default(), false);
    let _ = mono.fold_opt_or_clone(&mut mono_closer);
    assert!(mono_closer.error.is_none());
    assert_eq!(mono_closer.contextual.maps().1.len(), 0);
    assert_eq!(mono_closer.contextual.maps().1.capacity(), 0);
    let mut cache = ContextCandidates::default();
    let entry = |depth| ContextEntry {
        entry: MemoEntry {
            replacement: Some(Arc::new(Expr::bvar(0))),
            declarations: None,
            dependencies: None,
        },
        context: depth as usize,
        binder_depth: depth,
        ordinary_count: 0,
    };
    cache.insert(1, entry(2));
    cache.insert(1, entry(2));
    assert_eq!(cache.maps().1.capacity(), 0);
    cache.insert(1, entry(3));
    let promoted = cache.get(1, 2, 0).unwrap().clone();
    cache.insert(1, promoted);
    cache.insert(1, entry(2));
    assert!(cache.get(1, 3, 0).is_some());
    cache.insert(1, entry(4));
    assert!(cache.get(1, 3, 0).is_none());
    assert!(cache.get(1, 2, 0).is_some());
    assert_eq!((cache.maps().0.len(), cache.maps().1.len()), (1, 1));
}
