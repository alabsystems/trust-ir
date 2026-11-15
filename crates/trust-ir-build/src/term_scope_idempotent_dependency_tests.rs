// Copyright 2026 Andrew Yates | Licensed under the Apache License, Version 2.0

//! Exact dependency values, not arena allocation identity, define idempotence.
//! These exercise the real closer; no successful probe bypasses its guards.

use super::*;
use clean_kernel::{BinderInfo, Environment, TypeChecker};

fn id(raw: u64) -> FVarId {
    FVarId::new(raw)
}
fn nat() -> Expr {
    Expr::const_str("Nat")
}
fn accumulated(closer: &mut Closer<'_>, left: Dependency, right: Dependency) -> (usize, usize) {
    let left = closer.dependency_node(left);
    let right = closer.dependency_node(right);
    assert_ne!(left, right, "the construction allocations really differ");
    closer.include_dependency(Some(left));
    closer.include_dependency(Some(right));
    (left, right)
}

#[test]
fn equal_named_dependencies_do_not_allocate_a_redundant_join() {
    let scope = TermScope::new();
    let mut closer = Closer::new(&scope, TermScopeLimits::default(), true);
    let (_, right) = accumulated(
        &mut closer,
        Dependency::Named(id(7), 3),
        Dependency::Named(id(7), 3),
    );
    assert_eq!(closer.dependencies.len(), 2);
    assert_eq!(closer.dependency, Some(right));
    assert_eq!(closer.dependencies[right].min_depth, 3);
    closer.binder_depth = 5;
    assert!(
        closer.visit(),
        "charge the enclosing expression before probing"
    );
    closer.active.insert(id(7), 3);
    assert!(closer.same_dependencies(closer.dependency));
    assert_eq!(closer.stats.context_check_visits, 1);
    closer.active.insert(id(7), 2);
    assert!(!closer.same_dependencies(closer.dependency));
    closer.active.clear();
    assert!(!closer.same_dependencies(closer.dependency));
    assert!(
        closer.error.is_none(),
        "failed reuse remains a rewalk, not admission"
    );
}

#[test]
fn equal_ordinary_dependencies_keep_exact_position_and_depth_guards() {
    let scope = TermScope::new();
    let mut closer = Closer::new(&scope, TermScopeLimits::default(), true);
    let (_, right) = accumulated(
        &mut closer,
        Dependency::Ordinary(0, 1),
        Dependency::Ordinary(0, 1),
    );
    assert_eq!(closer.dependencies.len(), 2);
    assert_eq!(closer.dependency, Some(right));
    closer.binder_depth = 3;
    assert!(
        closer.visit(),
        "charge the enclosing expression before probing"
    );
    closer.ordinary.push(1);
    assert!(closer.same_dependencies(closer.dependency));
    assert_eq!(closer.stats.context_check_visits, 1);
    closer.ordinary[0] = 0;
    assert!(!closer.same_dependencies(closer.dependency));
    closer.ordinary.clear();
    assert!(!closer.same_dependencies(closer.dependency));
}

#[test]
fn different_named_depths_and_ordinary_positions_are_not_collapsed() {
    for (left, right) in [
        (Dependency::Named(id(7), 1), Dependency::Named(id(7), 2)),
        (Dependency::Named(id(7), 1), Dependency::Named(id(8), 1)),
        (Dependency::Ordinary(0, 1), Dependency::Ordinary(1, 1)),
        (Dependency::Ordinary(0, 1), Dependency::Ordinary(0, 2)),
        (Dependency::Named(id(7), 1), Dependency::Ordinary(0, 1)),
    ] {
        let scope = TermScope::new();
        let mut closer = Closer::new(&scope, TermScopeLimits::default(), true);
        let (left, right) = accumulated(&mut closer, left, right);
        assert_eq!(closer.dependencies.len(), 3);
        let root = closer.dependency.unwrap();
        assert!(matches!(closer.dependencies[root].dependency,
            Dependency::Join(a, b) if a == left && b == right));
    }
}

#[test]
fn idempotent_dependencies_preserve_original_nested_binder_term_and_kernel_type() {
    let mut scope = TermScope::new();
    let nested = scope.lam(id(2), BinderInfo::Default, nat(), Expr::fvar(id(1)));
    let body = Expr::apps(
        Expr::const_str("Nat.add"),
        [Expr::app(nested, Expr::nat_lit(0_u64)), Expr::fvar(id(1))],
    );
    let open = scope.lam(id(1), BinderInfo::Default, nat(), body);
    let expected = Expr::lam(
        BinderInfo::Default,
        nat(),
        Expr::apps(
            Expr::const_str("Nat.add"),
            [
                Expr::app(
                    Expr::lam(BinderInfo::Default, nat(), Expr::bvar(1)),
                    Expr::nat_lit(0_u64),
                ),
                Expr::bvar(0),
            ],
        ),
    );
    let actual = scope.close(&open).unwrap();
    assert_eq!(actual, expected);
    let mut env = Environment::new();
    env.init_nat().unwrap();
    let mut checker = TypeChecker::new(&env);
    checker.set_allow_unsafe(false);
    checker.set_allow_partial(false);
    checker
        .check_type(&actual, &Expr::arrow(nat(), nat()))
        .unwrap();

    let escaped = scope.lam(id(3), BinderInfo::Default, nat(), Expr::fvar(id(1)));
    assert_eq!(
        scope.close(&escaped),
        Err(TermScopeError::OutOfScope(id(1)))
    );
    let duplicate = scope.lam(id(1), BinderInfo::Default, nat(), Expr::fvar(id(1)));
    let shadowed = scope.lam(id(1), BinderInfo::Default, nat(), duplicate);
    assert_eq!(
        scope.close(&shadowed),
        Err(TermScopeError::ShadowedLocal(id(1)))
    );
}

#[test]
fn idempotent_leaf_still_charges_and_refuses_when_probe_budget_is_spent() {
    let scope = TermScope::new();
    let mut closer = Closer::new(
        &scope,
        TermScopeLimits {
            max_visits: 0,
            ..TermScopeLimits::default()
        },
        true,
    );
    accumulated(
        &mut closer,
        Dependency::Named(id(7), 1),
        Dependency::Named(id(7), 1),
    );
    closer.binder_depth = 3;
    closer.active.insert(id(7), 1);
    assert!(!closer.same_dependencies(closer.dependency));
    assert_eq!(closer.error, Some(TermScopeError::VisitLimit));
    assert_eq!(closer.stats.context_check_visits, 0);
}
