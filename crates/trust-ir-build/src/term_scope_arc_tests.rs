// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Exact output-edge sharing, not a claim that every graph is context-linear.

use super::*;
use clean_kernel::{BinderInfo, Environment, TypeChecker};

fn id(value: u64) -> FVarId {
    FVarId::new(value)
}

fn body(expression: &Expr) -> &Arc<Expr> {
    match expression.kind() {
        ExprKind::Lam(_, _, body) | ExprKind::Pi(_, _, body) | ExprKind::Let(_, _, _, body, _) => {
            body
        }
        _ => panic!("expected binder"),
    }
}

fn pair(expression: &Expr, index: u32) -> &Arc<Expr> {
    let ExprKind::App(left, right) = expression.kind() else {
        panic!("expected shared pair")
    };
    assert!(
        Arc::ptr_eq(left, right),
        "changed roots, not just descendants, must share"
    );
    assert_eq!(left.as_ref(), &Expr::bvar(index));
    left
}

#[test]
fn transformed_diamond_keeps_child_arcs_and_second_close_work() {
    let mut scope = TermScope::new();
    let depth = 20;
    let mut dag = Arc::new(Expr::fvar(id(1)));
    for _ in 0..depth {
        dag = Arc::new(Expr::app_arc(dag.clone(), dag));
    }
    let open = scope.lam(
        id(1),
        BinderInfo::Default,
        Expr::type_(),
        dag.as_ref().clone(),
    );
    let closed = scope
        .close_with_limits(&open, TermScopeLimits::default())
        .unwrap();
    // These are the original first-walk counters: no request is omitted or
    // discounted by changing the representation of an already computed result.
    assert_eq!(closed.stats.visits, 43);
    assert_eq!(closed.stats.transformed_nodes, 23);
    assert_eq!(closed.stats.memo_hits, 20);
    let mut cursor = body(&closed.term);
    for _ in 0..depth {
        let ExprKind::App(left, right) = cursor.kind() else {
            panic!("diamond edge")
        };
        assert!(Arc::ptr_eq(left, right));
        cursor = left;
    }
    assert_eq!(cursor.as_ref(), &Expr::bvar(0));

    // Independently construct the old replacement shape: two shallow root
    // allocations per edge, with their descendants shared. No new folder is
    // needed to show that this shape costs 81 requests under the same closer.
    let mut copied = Expr::bvar(0);
    for _ in 0..depth {
        copied = Expr::app_arc(Arc::new(copied.clone()), Arc::new(copied));
    }
    let copied = Expr::lam(BinderInfo::Default, Expr::type_(), copied);
    let copied = TermScope::new()
        .close_with_limits(&copied, TermScopeLimits::default())
        .unwrap();
    assert_eq!(copied.stats.visits, 81);

    // A fresh close has no prior memo or named bindings. The original first-
    // walk 43-request envelope also suffices for this output, without discounts.
    let second = TermScope::new()
        .close_with_limits(
            &closed.term,
            TermScopeLimits {
                max_visits: closed.stats.visits,
                ..TermScopeLimits::default()
            },
        )
        .unwrap();
    assert_eq!(second.stats.visits, 43);
    assert_eq!(second.stats.transformed_nodes, 23);
    assert_eq!(second.stats.memo_hits, 20);
    assert!(Arc::ptr_eq(body(&second.term), body(&closed.term)));
}

#[test]
fn changed_arc_sharing_preserves_an_independent_kernel_type() {
    let mut scope = TermScope::new();
    let add = Arc::new(Expr::const_str("Nat.add"));
    let mut shared = Arc::new(Expr::fvar(id(1)));
    for _ in 0..8 {
        let function = Arc::new(Expr::app_arc(add.clone(), shared.clone()));
        shared = Arc::new(Expr::app_arc(function, shared));
    }
    let open = scope.lam(
        id(1),
        BinderInfo::Default,
        Expr::const_str("Nat"),
        shared.as_ref().clone(),
    );
    let closed = scope.close(&open).unwrap();
    let mut cursor = body(&closed);
    for _ in 0..8 {
        let ExprKind::App(function, right) = cursor.kind() else {
            panic!("add result")
        };
        let ExprKind::App(_, left) = function.kind() else {
            panic!("add function")
        };
        assert!(Arc::ptr_eq(left, right));
        cursor = right;
    }
    assert_eq!(cursor.as_ref(), &Expr::bvar(0));
    let mut env = Environment::new();
    env.init_nat().unwrap();
    TypeChecker::new(&env)
        .check_type(
            &closed,
            &Expr::arrow(Expr::const_str("Nat"), Expr::const_str("Nat")),
        )
        .unwrap();
}

#[test]
fn named_and_ordinary_binder_children_keep_changed_arcs() {
    for named in [false, true] {
        for kind in 0..3 {
            let mut scope = TermScope::new();
            let shared = Arc::new(Expr::fvar(id(1)));
            let diamond = Expr::app_arc(shared.clone(), shared);
            let inner = match (named, kind) {
                (true, 0) => scope.lam(id(2), BinderInfo::Default, Expr::type_(), diamond),
                (true, 1) => scope.pi(id(2), BinderInfo::Default, Expr::type_(), diamond),
                (true, 2) => scope.let_named(
                    id(2),
                    Name::anon(),
                    Expr::type_(),
                    Expr::fvar(id(1)),
                    diamond,
                    false,
                ),
                (false, 0) => Expr::lam(BinderInfo::Default, Expr::type_(), diamond),
                (false, 1) => Expr::pi(BinderInfo::Default, Expr::type_(), diamond),
                (false, 2) => Expr::let_named(
                    Name::anon(),
                    Expr::type_(),
                    Expr::fvar(id(1)),
                    diamond,
                    false,
                ),
                _ => unreachable!(),
            };
            let open = scope.lam(id(1), BinderInfo::Default, Expr::type_(), inner);
            let closed = scope.close(&open).unwrap();
            let inner = body(&closed);
            pair(body(inner), 1);
            if let ExprKind::Let(_, _, value, _, _) = inner.kind() {
                assert_eq!(
                    value.as_ref(),
                    &Expr::bvar(0),
                    "let value is outside its own binder"
                );
            }
        }
    }
}

#[test]
fn changed_arc_memo_does_not_conflate_named_or_ordinary_contexts() {
    for ordinary in [false, true] {
        let mut scope = TermScope::new();
        let leaf = Arc::new(if ordinary {
            Expr::bvar(0)
        } else {
            Expr::fvar(id(1))
        });
        let shared = Expr::app_arc(leaf.clone(), leaf);
        let (left, right) = if ordinary {
            let left = Expr::lam(BinderInfo::Default, Expr::type_(), shared.clone());
            let left = scope.lam(id(2), BinderInfo::Default, Expr::type_(), left);
            let right = scope.lam(id(2), BinderInfo::Default, Expr::type_(), shared);
            let right = Expr::lam(BinderInfo::Default, Expr::type_(), right);
            (left, right)
        } else {
            let left = scope.lam(id(2), BinderInfo::Default, Expr::type_(), shared.clone());
            let left = scope.lam(id(1), BinderInfo::Default, Expr::type_(), left);
            let right = scope.lam(id(1), BinderInfo::Default, Expr::type_(), shared);
            let right = scope.lam(id(2), BinderInfo::Default, Expr::type_(), right);
            (left, right)
        };
        let closed = scope.close(&Expr::app(left, right)).unwrap();
        let ExprKind::App(left, right) = closed.kind() else {
            panic!("two contexts")
        };
        let (left_index, right_index) = if ordinary { (0, 1) } else { (1, 0) };
        let left = pair(body(body(left)), left_index);
        let right = pair(body(body(right)), right_index);
        assert!(!Arc::ptr_eq(left, right));
    }
}

#[test]
fn arc_hits_keep_failure_order_and_visit_depth_limits() {
    let mut scope = TermScope::new();
    let leaf = Arc::new(Expr::fvar(id(1)));
    let diamond = Expr::app_arc(leaf.clone(), leaf.clone());
    let valid = scope.lam(id(1), BinderInfo::Default, Expr::type_(), diamond.clone());
    let complete = scope.close_with_diagnostics(&valid, TermScopeLimits::default());
    assert!(complete.result.is_ok());
    assert_eq!(complete.stats.visits, 5);
    for cap in 0..complete.stats.visits {
        let report = scope.close_with_diagnostics(
            &valid,
            TermScopeLimits {
                max_visits: cap,
                ..TermScopeLimits::default()
            },
        );
        assert_eq!(report.result, Err(TermScopeError::VisitLimit));
        assert_eq!(report.stats.visits, cap);
    }
    for cap in 0..3 {
        let report = scope.close_with_diagnostics(
            &valid,
            TermScopeLimits {
                max_depth: cap,
                ..TermScopeLimits::default()
            },
        );
        assert_eq!(report.result, Err(TermScopeError::DepthLimit));
    }
    // A changed result was already hit in the valid sibling; it must neither
    // escape its named context nor survive into a subsequent closing call.
    let escaped = Expr::app(valid.clone(), diamond);
    assert_eq!(
        scope.close(&escaped),
        Err(TermScopeError::OutOfScope(id(1)))
    );
    assert_eq!(scope.close(&leaf), Err(TermScopeError::OutOfScope(id(1))));
    let shadow = scope.lam(id(1), BinderInfo::Default, Expr::type_(), valid);
    assert_eq!(
        scope.close(&shadow),
        Err(TermScopeError::ShadowedLocal(id(1)))
    );
    let overflow = scope.lam(
        id(1),
        BinderInfo::Default,
        Expr::type_(),
        Expr::bvar(Expr::MAX_BVAR_INDEX),
    );
    assert_eq!(scope.close(&overflow), Err(TermScopeError::IndexOverflow));
}
