// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Scope transformation controls; only the explicitly checked fixture below
//! claims well-typedness. Sharing or a successful close is not proof authority.

use super::*;
use clean_kernel::{BinderInfo, Environment, TypeChecker};

fn id(value: u64) -> FVarId {
    FVarId::new(value)
}

fn lam(scope: &mut TermScope, local: u64, body: Expr) -> Expr {
    scope.lam(id(local), BinderInfo::Default, Expr::const_str("Nat"), body)
}

fn ordinary(body: Expr) -> Expr {
    Expr::lam(BinderInfo::Default, Expr::const_str("Nat"), body)
}

#[test]
fn sibling_contexts_reuse_open_dag_and_preserve_exact_kernel_type() {
    for (depth, count) in [(64usize, 64u64), (128, 128)] {
        let mut scope = TermScope::new();
        let mut shared = Arc::new(Expr::fvar(id(1)));
        for _ in 0..depth {
            shared = Arc::new(Expr::app_arc(Arc::new(Expr::const_str("Nat.succ")), shared));
        }
        let mut body = Expr::nat_lit(0u64);
        for local in 2..count + 2 {
            let value = scope.let_named(
                id(local),
                Name::anon(),
                Expr::const_str("Nat"),
                Expr::nat_lit(0u64),
                (*shared).clone(),
                false,
            );
            body = Expr::apps(Expr::const_str("Nat.add"), [value, body]);
        }
        let expected = ordinary(body.abstract_fvar(id(1)));
        let open = lam(&mut scope, 1, body);
        let bound = 4 * depth + 14 * count as usize + 30;
        let report = scope.close_with_diagnostics(
            &open,
            TermScopeLimits {
                max_visits: bound,
                ..TermScopeLimits::default()
            },
        );
        let closed = report.result.unwrap();
        assert!(report.stats.context_check_visits >= count as usize - 1);
        assert!(report.stats.visits <= bound);
        assert_eq!(closed, expected);
        let mut env = Environment::new();
        env.init_nat().unwrap();
        let mut checker = TypeChecker::new(&env);
        checker.set_heartbeat_limit(2_000_000);
        checker
            .check_type(
                &closed,
                &Expr::arrow(Expr::const_str("Nat"), Expr::const_str("Nat")),
            )
            .unwrap();
    }
}

#[test]
fn equal_depth_contexts_do_not_conflate_changed_or_missing_named_bindings() {
    let mut scope = TermScope::new();
    let shared = Arc::new(Expr::app(Expr::fvar(id(1)), Expr::fvar(id(1))));
    let left = lam(&mut scope, 2, (*shared).clone());
    let left = lam(&mut scope, 1, left);
    let right = lam(&mut scope, 1, (*shared).clone());
    let right = lam(&mut scope, 2, right);
    let open = Expr::app(left.clone(), right);
    let expected = Expr::app(
        ordinary(ordinary(Expr::app(Expr::bvar(1), Expr::bvar(1)))),
        ordinary(ordinary(Expr::app(Expr::bvar(0), Expr::bvar(0)))),
    );
    assert_eq!(scope.close(&open).unwrap(), expected);
    let escaped = lam(&mut scope, 3, (*shared).clone());
    let escaped = lam(&mut scope, 4, escaped);
    assert_eq!(
        scope.close(&Expr::app(left, escaped)),
        Err(TermScopeError::OutOfScope(id(1)))
    );
}

#[test]
fn equal_binder_counts_keep_ordinary_stack_positions_and_depth_changes() {
    let mut scope = TermScope::new();
    // No named-variable read participates: the ordinary-stack check alone
    // must distinguish these equal-depth/equal-count contexts.
    let bvar = Arc::new(Expr::bvar(0));
    let pair = Expr::app_arc(bvar.clone(), bvar);
    let left = lam(&mut scope, 7, ordinary(pair.clone()));
    let right = ordinary(lam(&mut scope, 8, pair));
    assert_eq!(
        scope.close(&Expr::app(left, right)).unwrap(),
        Expr::app(
            ordinary(ordinary(Expr::app(Expr::bvar(0), Expr::bvar(0)))),
            ordinary(ordinary(Expr::app(Expr::bvar(1), Expr::bvar(1)))),
        )
    );
    let shared = Arc::new(Expr::app(Expr::fvar(id(1)), Expr::bvar(0)));
    let left = lam(&mut scope, 1, ordinary((*shared).clone()));
    let right = ordinary(lam(&mut scope, 1, (*shared).clone()));
    assert_eq!(
        scope.close(&Expr::app(left, right)).unwrap(),
        Expr::app(
            ordinary(ordinary(Expr::app(Expr::bvar(1), Expr::bvar(0)))),
            ordinary(ordinary(Expr::app(Expr::bvar(0), Expr::bvar(1)))),
        )
    );
    let nested = lam(&mut scope, 2, (*shared).clone());
    let open = Expr::app_arc(shared, Arc::new(nested));
    let open = lam(&mut scope, 1, open);
    assert_eq!(
        scope.close(&open).unwrap(),
        ordinary(Expr::app(
            Expr::app(Expr::bvar(0), Expr::bvar(1)),
            ordinary(Expr::app(Expr::bvar(1), Expr::bvar(2))),
        ))
    );
}

#[test]
fn overlapping_dependency_diamonds_probe_once_and_retain_open_sharing() {
    let mut scope = TermScope::new();
    let (depth, count) = (64usize, 32u64);
    let x = Arc::new(Expr::fvar(id(1)));
    let y = Arc::new(Expr::fvar(id(2)));
    let z = Arc::new(Expr::fvar(id(3)));
    let mut left = Arc::new(Expr::app_arc(x, y.clone()));
    let mut right = Arc::new(Expr::app_arc(y, z));
    for _ in 0..depth {
        // Fibonacci-shaped overlap defeats a tree walk of both expression and
        // dependency edges. Both graphs remain linear in physical allocations.
        let next = Arc::new(Expr::app_arc(left.clone(), right));
        right = left;
        left = next;
    }
    let mut body = Expr::nat_lit(0u64);
    for local in 100..100 + count {
        let sibling = lam(&mut scope, local, (*left).clone());
        body = Expr::app(sibling, body);
    }
    for local in (1..=3).rev() {
        body = lam(&mut scope, local, body);
    }
    let bound = 32 * depth + count as usize * (8 * depth + 30) + 100;
    let report = scope.close_with_diagnostics(
        &body,
        TermScopeLimits {
            max_visits: bound,
            ..TermScopeLimits::default()
        },
    );
    let closed = report.result.unwrap();
    assert!(!closed.has_fvar_quick());
    assert!(report.stats.context_check_visits > count as usize);
    assert!(report.stats.visits < bound);
    assert!(report.stats.transformed_nodes < 8 * depth + 10 * count as usize + 100);
    // Inspect only a fixed number of edges, never expand the diamond to a tree.
    let ExprKind::Lam(_, _, closed) = closed.kind() else {
        panic!("x")
    };
    let ExprKind::Lam(_, _, closed) = closed.kind() else {
        panic!("y")
    };
    let ExprKind::Lam(_, _, closed) = closed.kind() else {
        panic!("z")
    };
    let ExprKind::App(first, rest) = closed.kind() else {
        panic!("first")
    };
    let ExprKind::App(second, _) = rest.kind() else {
        panic!("second")
    };
    let ExprKind::Lam(_, _, first) = first.kind() else {
        panic!("first lambda")
    };
    let ExprKind::Lam(_, _, second) = second.kind() else {
        panic!("second lambda")
    };
    let ExprKind::App(first, _) = first.kind() else {
        panic!("first body")
    };
    let ExprKind::App(second, _) = second.kind() else {
        panic!("second body")
    };
    let ExprKind::App(first, _) = first.kind() else {
        panic!("first shared child")
    };
    let ExprKind::App(second, _) = second.kind() else {
        panic!("second shared child")
    };
    assert!(
        Arc::ptr_eq(first, second),
        "transformed descendants stay shared"
    );
}

#[test]
fn context_hits_propagate_dependencies_and_hidden_declarations_to_parents() {
    let mut scope = TermScope::new();
    let leaf = Arc::new(Expr::fvar(id(1)));
    let inner = lam(
        &mut scope,
        9,
        Expr::app_arc(leaf.clone(), Arc::new(Expr::fvar(id(9)))),
    );
    let shared = Arc::new(inner);
    // The parent first observes its external local solely through a cache hit.
    let parent = Arc::new(Expr::app_arc(shared.clone(), shared.clone()));
    let primed = Expr::app_arc(shared.clone(), parent.clone());
    let left = lam(&mut scope, 2, primed);
    let right = lam(&mut scope, 3, (*parent).clone());
    let valid = lam(&mut scope, 1, Expr::app(left.clone(), right));
    let result = scope
        .close_with_limits(&valid, TermScopeLimits::default())
        .unwrap();
    assert!(result.stats.context_check_visits > 0);
    let shadow = lam(&mut scope, 9, (*parent).clone());
    let shadow = lam(&mut scope, 1, Expr::app(left.clone(), shadow));
    assert_eq!(
        scope.close(&shadow),
        Err(TermScopeError::ShadowedLocal(id(9)))
    );
    let escaped = lam(&mut scope, 3, (*parent).clone());
    let escaped = lam(&mut scope, 4, escaped);
    let left = lam(&mut scope, 1, left);
    assert_eq!(
        scope.close(&Expr::app(left, escaped)),
        Err(TermScopeError::OutOfScope(id(1)))
    );
}

#[test]
fn context_dependency_probes_are_charged_and_caches_do_not_survive_close() {
    let mut scope = TermScope::new();
    let shared = Arc::new(Expr::fvar(id(1)));
    let left = lam(&mut scope, 2, Expr::app_arc(shared.clone(), shared.clone()));
    let right = lam(&mut scope, 3, Expr::app_arc(shared.clone(), shared.clone()));
    let open = lam(&mut scope, 1, Expr::app(left, right));
    let complete = scope.close_with_diagnostics(&open, TermScopeLimits::default());
    assert!(complete.result.is_ok());
    assert!(complete.stats.context_check_visits > 0);
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
    assert_eq!(scope.close(&shared), Err(TermScopeError::OutOfScope(id(1))));
    let loose = lam(&mut scope, 1, Expr::bvar(Expr::MAX_BVAR_INDEX));
    assert_eq!(scope.close(&loose), Err(TermScopeError::IndexOverflow));
}

fn alias_arm(scope: &mut TermScope, outer: u64, inner: u64, shared: &Arc<Expr>) -> Expr {
    // The builder allocates each binder body separately. Keep the actual
    // shared input at a child edge so a copied body root cannot hide the hit.
    let body = Expr::app_arc(Arc::new(Expr::const_str("Nat.succ")), shared.clone());
    let body = lam(scope, inner, body);
    lam(scope, outer, body)
}

fn alias_arms(scope: &mut TermScope, shared: &Arc<Expr>) -> Vec<Expr> {
    [(1, 2), (1, 3), (3, 1), (1, 3)]
        .into_iter()
        .map(|(outer, inner)| alias_arm(scope, outer, inner, shared))
        .collect()
}

fn select_last_arm(arms: Vec<Expr>) -> Expr {
    let nat = Expr::const_str("Nat");
    let arm_type = Expr::arrow(nat.clone(), Expr::arrow(nat.clone(), nat));
    let mut selector = Expr::bvar(0);
    for _ in 0..arms.len() {
        selector = Expr::lam(BinderInfo::Default, arm_type.clone(), selector);
    }
    Expr::apps(selector, arms)
}

fn shared_arm_output(arm: &Expr) -> &Arc<Expr> {
    let ExprKind::Lam(_, _, inner) = arm.kind() else {
        panic!("outer binder")
    };
    let ExprKind::Lam(_, _, body) = inner.kind() else {
        panic!("inner binder")
    };
    let ExprKind::App(_, shared) = body.kind() else {
        panic!("shared child")
    };
    shared
}

#[test]
fn validated_context_alias_survives_an_intervening_different_binding() {
    let mut scope = TermScope::new();
    let shared = Arc::new(Expr::app(Expr::const_str("Nat.succ"), Expr::fvar(id(1))));
    let open = select_last_arm(alias_arms(&mut scope, &shared));
    let report = scope.close_with_diagnostics(&open, TermScopeLimits::default());
    let closed = report.result.unwrap();
    assert!(report.stats.context_check_visits > 0);
    eprintln!(
        "validated_context_alias_stats visits={} transformed_nodes={} memo_hits={} context_check_visits={}",
        report.stats.visits,
        report.stats.transformed_nodes,
        report.stats.memo_hits,
        report.stats.context_check_visits,
    );
    let expected = select_last_arm(
        [1, 1, 0, 1]
            .into_iter()
            .map(|index| {
                ordinary(ordinary(Expr::app(
                    Expr::const_str("Nat.succ"),
                    Expr::app(Expr::const_str("Nat.succ"), Expr::bvar(index)),
                )))
            })
            .collect(),
    );
    assert_eq!(closed, expected);

    let mut cursor = &closed;
    let mut arms = Vec::new();
    while let ExprKind::App(function, argument) = cursor.kind() {
        arms.push(argument);
        cursor = function;
    }
    arms.reverse();
    assert_eq!(arms.len(), 4);
    let outputs: Vec<_> = arms.iter().map(|arm| shared_arm_output(arm)).collect();
    for (output, index) in outputs.iter().zip([1, 1, 0, 1]) {
        assert_eq!(
            output.as_ref(),
            &Expr::app(Expr::const_str("Nat.succ"), Expr::bvar(index))
        );
    }
    assert!(Arc::ptr_eq(outputs[0], outputs[1]), "A1 -> equivalent A2");
    assert!(!Arc::ptr_eq(outputs[1], outputs[2]), "B changes x's index");
    assert!(
        Arc::ptr_eq(outputs[1], outputs[3]),
        "A2 must retain its validated exact alias when B replaces the contextual entry"
    );
    // Independent kernel replay checks every function argument, even though
    // the selector returns the last one. Sharing alone is not this oracle.
    let mut env = Environment::new();
    env.init_nat().unwrap();
    let nat = Expr::const_str("Nat");
    TypeChecker::new(&env)
        .check_type(
            &closed,
            &Expr::arrow(nat.clone(), Expr::arrow(nat.clone(), nat)),
        )
        .unwrap();
}

#[test]
fn validated_context_alias_does_not_admit_shadowed_or_missing_binders() {
    let mut scope = TermScope::new();
    let hidden = lam(&mut scope, 9, Expr::fvar(id(1)));
    let shared = Arc::new(hidden);
    let warm = alias_arms(&mut scope, &shared);
    // Transformation-only negatives: an extra named declaration inside the
    // cached open subtree must still be checked in every new exact context.
    let shadow = alias_arm(&mut scope, 1, 9, &shared);
    let escaped = alias_arm(&mut scope, 4, 3, &shared);
    for (last, expected) in [
        (shadow, TermScopeError::ShadowedLocal(id(9))),
        (escaped, TermScopeError::OutOfScope(id(1))),
    ] {
        let mut arms = warm.clone();
        arms.push(last);
        assert_eq!(scope.close(&select_last_arm(arms)), Err(expected));
    }
    assert_eq!(scope.close(&shared), Err(TermScopeError::OutOfScope(id(1))));
}

#[test]
fn validated_context_alias_keeps_request_limits_and_per_close_lifetime() {
    let mut scope = TermScope::new();
    let shared = Arc::new(Expr::app(Expr::const_str("Nat.succ"), Expr::fvar(id(1))));
    let open = select_last_arm(alias_arms(&mut scope, &shared));
    let complete = scope.close_with_diagnostics(&open, TermScopeLimits::default());
    assert!(complete.result.is_ok());
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
    assert_eq!(again.stats, complete.stats, "no memo survives a close");
    assert_eq!(scope.close(&shared), Err(TermScopeError::OutOfScope(id(1))));

    // Warm the same three contexts, then put A2's shared edge much deeper in
    // the syntax without adding a binder. An exact memo hit cannot waive the
    // ordinary request-depth guard that precedes all memo lookups.
    let mut arms = alias_arms(&mut scope, &shared);
    let ExprKind::App(successor, _) = shared.kind() else {
        panic!("shared successor")
    };
    let mut deep = shared.clone();
    // The fourth argument is entered at walk depth one; its two named
    // binders add two. Thirteen applications put the warmed child at 16.
    for _ in 0..13 {
        deep = Arc::new(Expr::app_arc(successor.clone(), deep));
    }
    let deep = lam(&mut scope, 3, deep.as_ref().clone());
    arms[3] = lam(&mut scope, 1, deep);
    let deep = select_last_arm(arms);
    let refused = scope.close_with_diagnostics(
        &deep,
        TermScopeLimits {
            max_depth: 16,
            ..TermScopeLimits::default()
        },
    );
    assert_eq!(refused.result, Err(TermScopeError::DepthLimit));
    assert!(
        refused.stats.context_check_visits > 0,
        "alias was warmed first"
    );
    assert!(scope.close(&deep).is_ok());
}
