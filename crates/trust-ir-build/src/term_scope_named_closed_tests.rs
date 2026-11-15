// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Closed-result reuse preserves named scope checks and bounds its own work.

use super::*;
use clean_kernel::{BinderInfo, Environment, TypeChecker};

fn id(value: u64) -> FVarId {
    FVarId::new(value)
}

#[test]
fn named_closed_helper_is_transformed_once_across_unrelated_scopes() {
    for size in [64usize, 128] {
        let mut scope = TermScope::new();
        let natural = Expr::const_str("Nat");
        let mut helper_body = Expr::fvar(id(1));
        let mut expected_helper = Expr::bvar(0);
        for _ in 0..size {
            helper_body = Expr::app(Expr::const_str("Nat.succ"), helper_body);
            expected_helper = Expr::app(Expr::const_str("Nat.succ"), expected_helper);
        }
        let helper = Arc::new(scope.lam(id(1), BinderInfo::Default, natural.clone(), helper_body));
        let expected_helper = Arc::new(Expr::lam(
            BinderInfo::Default,
            natural.clone(),
            expected_helper,
        ));
        let mut body = Expr::nat_lit(0u64);
        let mut expected = body.clone();
        for index in 0..size {
            let argument = Arc::new(Expr::nat_lit(index as u64));
            body = scope.let_named(
                id(100 + index as u64),
                Name::anon(),
                natural.clone(),
                Expr::app_arc(helper.clone(), argument.clone()),
                body,
                false,
            );
            expected = Expr::let_named(
                Name::anon(),
                natural.clone(),
                Expr::app_arc(expected_helper.clone(), argument),
                expected,
                false,
            );
        }
        let closed = scope
            .close_with_limits(
                &body,
                TermScopeLimits {
                    max_visits: 16 * size + 50,
                    ..TermScopeLimits::default()
                },
            )
            .expect("helper size times caller count must not be re-traversed");
        assert_eq!(closed.term, expected);
        assert!(closed.stats.closed_memo_hits >= size - 1);
        assert_eq!(closed.stats.scope_check_visits, size - 1);
        let mut env = Environment::new();
        env.init_nat().unwrap();
        TypeChecker::new(&env)
            .check_type(&closed.term, &natural)
            .unwrap();
        eprintln!("named helper size={size}: {:?}", closed.stats);
    }
}

#[test]
fn transformed_closed_hits_retain_unused_declarations_and_error_order() {
    let mut scope = TermScope::new();
    let natural = Expr::const_str("Nat");
    let named = scope.lam(
        id(1),
        BinderInfo::Default,
        natural.clone(),
        Expr::fvar(id(1)),
    );
    // The second, UNUSED binder is still a scope constraint after the first
    // binder causes the cached output to differ from its input.
    let unused = scope.lam(id(2), BinderInfo::Default, natural.clone(), named);
    let shared = Arc::new(unused);
    let wrapper = Arc::new(Expr::app_arc(shared.clone(), shared.clone()));
    // Prime closed cache, then build a parent entirely from cache hits.
    let primed = Expr::app_arc(shared, wrapper.clone());
    let bad = scope.lam(
        id(2),
        BinderInfo::Default,
        natural,
        Expr::app_arc(Arc::new(Expr::nat_lit(0u64)), wrapper),
    );
    assert_eq!(
        scope.close(&Expr::app(primed, bad)).err(),
        Some(TermScopeError::ShadowedLocal(id(2)))
    );

    // A cache conflict must fall back, not eagerly report shadowing. Reuse a
    // valid closed helper under a binder whose TYPE has an out-of-scope local.
    let mut scope = TermScope::new();
    let helper = Arc::new(scope.lam(
        id(8),
        BinderInfo::Default,
        Expr::const_str("Nat"),
        Expr::nat_lit(0u64),
    ));
    let invalid_type = scope.lam(
        id(9),
        BinderInfo::Default,
        Expr::fvar(id(9)),
        Expr::app_arc(helper.clone(), helper.clone()),
    );
    let shadowing = scope.lam(id(8), BinderInfo::Default, Expr::type_(), invalid_type);
    assert_eq!(
        scope
            .close(&Expr::app_arc(helper, Arc::new(shadowing)))
            .err(),
        Some(TermScopeError::OutOfScope(id(9)))
    );
}

#[test]
fn named_pi_and_let_outputs_preserve_names_flags_and_outer_capture() {
    let mut scope = TermScope::new();
    let natural = Expr::const_str("Nat");
    let named_pi = Arc::new(scope.pi(
        id(1),
        BinderInfo::Implicit,
        natural.clone(),
        Expr::app(Expr::const_str("Nat.succ"), Expr::fvar(id(1))),
    ));
    let name = Name::from_string("preserved");
    let named_let = Arc::new(scope.let_named(
        id(2),
        name.clone(),
        natural.clone(),
        Expr::nat_lit(3u64),
        Expr::fvar(id(2)),
        true,
    ));
    // Structural syntax test: this Pi's codomain is deliberately not a type.
    // No claim of kernel well-typedness is made for that input.
    let shared = Arc::new(Expr::app_arc(named_pi, named_let));
    let under = scope.lam(
        id(3),
        BinderInfo::Default,
        natural.clone(),
        (*shared).clone(),
    );
    let result = scope
        .close(&Expr::app_arc(shared, Arc::new(under)))
        .unwrap();
    let expected = Expr::app(
        Expr::pi(
            BinderInfo::Implicit,
            natural.clone(),
            Expr::app(Expr::const_str("Nat.succ"), Expr::bvar(0)),
        ),
        Expr::let_named(
            name,
            natural.clone(),
            Expr::nat_lit(3u64),
            Expr::bvar(0),
            true,
        ),
    );
    assert_eq!(
        result,
        Expr::app(
            expected.clone(),
            Expr::lam(BinderInfo::Default, natural.clone(), expected)
        )
    );

    let captured = Arc::new(scope.lam(
        id(4),
        BinderInfo::Default,
        natural.clone(),
        Expr::fvar(id(5)),
    ));
    let deep = scope.lam(
        id(6),
        BinderInfo::Default,
        natural.clone(),
        (*captured).clone(),
    );
    let body = scope.lam(
        id(5),
        BinderInfo::Default,
        natural.clone(),
        Expr::app_arc(captured, Arc::new(deep)),
    );
    let expected = Expr::lam(
        BinderInfo::Default,
        natural.clone(),
        Expr::app(
            Expr::lam(BinderInfo::Default, natural.clone(), Expr::bvar(1)),
            Expr::lam(
                BinderInfo::Default,
                natural.clone(),
                Expr::lam(BinderInfo::Default, natural, Expr::bvar(2)),
            ),
        ),
    );
    assert_eq!(scope.close(&body).unwrap(), expected);
}

#[test]
fn declaration_dag_probe_is_deduplicated_and_charged() {
    let mut scope = TermScope::new();
    let mut shared =
        Arc::new(scope.lam(id(1), BinderInfo::Default, Expr::type_(), Expr::fvar(id(1))));
    for _ in 0..20 {
        // Its expression tree is exponential, but both the input and its
        // declaration footprint share their repeated children.
        shared = Arc::new(Expr::app_arc(shared.clone(), shared));
    }
    let under = scope.lam(id(2), BinderInfo::Default, Expr::type_(), (*shared).clone());
    let input = Expr::app_arc(shared, Arc::new(under));
    let closed = scope
        .close_with_limits(
            &input,
            TermScopeLimits {
                max_visits: 200,
                max_depth: 100,
            },
        )
        .unwrap();
    assert!(closed.stats.scope_check_visits > 0);
    assert!(closed.stats.scope_check_visits < 20);
    assert_eq!(
        scope
            .close_with_limits(
                &input,
                TermScopeLimits {
                    max_visits: closed.stats.visits - 1,
                    max_depth: 100,
                },
            )
            .err(),
        Some(TermScopeError::VisitLimit),
        "the last scope-check/memo request must still be charged",
    );
    assert!(
        scope
            .close_with_limits(
                &input,
                TermScopeLimits {
                    max_visits: closed.stats.visits,
                    max_depth: 100
                },
            )
            .is_ok()
    );
}
