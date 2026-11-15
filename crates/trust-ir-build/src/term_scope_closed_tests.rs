// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Cross-context reuse must not conflate ordinary closure with named binding.

use super::*;
use clean_kernel::{BinderInfo, Environment, TypeChecker};

fn id(value: u64) -> FVarId {
    FVarId::new(value)
}

fn shared_natural(depth: usize) -> Arc<Expr> {
    let succ = Arc::new(Expr::const_str("Nat.succ"));
    let mut value = Arc::new(Expr::nat_lit(0u64));
    for _ in 0..depth {
        value = Arc::new(Expr::app_arc(succ.clone(), value));
    }
    value
}

#[test]
fn closed_data_is_visited_once_across_distinct_named_contexts() {
    for (depth, count) in [(64usize, 128u64), (128, 256)] {
        let mut scope = TermScope::new();
        let data = shared_natural(depth);
        let mut open = Expr::nat_lit(0u64);
        for index in 0..count {
            // A cloned expression preserves the shared descendant Arcs. Its
            // surrounding named-let context differs at every occurrence.
            open = scope.let_named(
                id(index),
                Name::anon(),
                Expr::const_str("Nat"),
                (*data).clone(),
                open,
                false,
            );
        }
        let bound = 4 * depth + 5 * usize::try_from(count).unwrap() + 10;
        let result = scope
            .close_with_limits(
                &open,
                TermScopeLimits {
                    max_visits: bound,
                    ..TermScopeLimits::default()
                },
            )
            .expect("closed data must not be rewalked for each unrelated binder");
        assert_eq!(result.term, open, "unused named lets preserve exact syntax");
        assert!(result.stats.visits <= bound);
        assert!(result.stats.memo_hits >= usize::try_from(count).unwrap() - 1);
        eprintln!("depth={depth} count={count} stats={:?}", result.stats);
        let mut env = Environment::new();
        env.init_nat().unwrap();
        let mut checker = TypeChecker::new(&env);
        checker.set_heartbeat_limit(2_000_000);
        checker
            .check_type(&result.term, &Expr::const_str("Nat"))
            .unwrap();
    }
}

#[test]
fn ordinary_closed_binders_are_safe_in_unrelated_external_contexts() {
    let mut scope = TermScope::new();
    let identity = Expr::lam(BinderInfo::Default, Expr::const_str("Nat"), Expr::bvar(0));
    let identity_type = Expr::arrow(Expr::const_str("Nat"), Expr::const_str("Nat"));
    let mut open = Expr::nat_lit(7u64);
    for index in 0..128 {
        open = scope.let_named(
            id(index),
            Name::anon(),
            identity_type.clone(),
            identity.clone(),
            open,
            false,
        );
    }
    let closed = scope.close(&open).unwrap();
    assert_eq!(closed, open);
    let mut env = Environment::new();
    env.init_nat().unwrap();
    TypeChecker::new(&env)
        .check_type(&closed, &Expr::const_str("Nat"))
        .unwrap();
}

#[test]
fn cached_unused_named_binders_still_reject_shadowing() {
    let mut scope = TermScope::new();
    let named = Arc::new(scope.lam(
        id(1),
        BinderInfo::Default,
        Expr::const_str("Nat"),
        Expr::nat_lit(0u64),
    ));
    assert!(!named.has_fvar_quick());
    assert!(!named.has_loose_bvars_quick());
    // First visit the named binder outside any binding of id(1). Every child
    // of `parent` is then a same-context memo hit: it must retain the named
    // descendant flag rather than becoming an incorrectly neutral subtree.
    let parent = Arc::new(Expr::app_arc(named.clone(), named.clone()));
    let prefix = Arc::new(Expr::app_arc(named, parent.clone()));
    let nested = scope.lam(
        id(1),
        BinderInfo::Default,
        Expr::const_str("Nat"),
        Expr::app_arc(Arc::new(Expr::nat_lit(0u64)), parent),
    );
    let open = Expr::app_arc(prefix, Arc::new(nested));
    assert!(matches!(
        scope.close(&open),
        Err(TermScopeError::ShadowedLocal(local)) if local == id(1)
    ));
}

#[test]
fn loose_bound_variables_remain_context_sensitive() {
    let mut scope = TermScope::new();
    let shared = Arc::new(Expr::bvar(0));
    let under_named = scope.lam(
        id(1),
        BinderInfo::Default,
        Expr::type_(),
        Expr::app_arc(shared.clone(), shared.clone()),
    );
    let open = Expr::app_arc(shared, Arc::new(under_named));
    let closed = scope.close(&open).unwrap();
    let expected = Expr::app(
        Expr::bvar(0),
        Expr::lam(
            BinderInfo::Default,
            Expr::type_(),
            Expr::app(Expr::bvar(1), Expr::bvar(1)),
        ),
    );
    assert_eq!(closed, expected);
}

#[test]
fn named_binders_in_type_and_let_value_children_cannot_become_neutral() {
    // These are structural scope controls, not assertions that arbitrary
    // binder types/values below are well-typed programs. A scope error must
    // still be detected before the independent kernel checks those types.
    for position in ["lambda_type", "pi_type", "let_type", "let_value"] {
        let mut scope = TermScope::new();
        let named = Arc::new(scope.lam(
            id(7),
            BinderInfo::Default,
            Expr::const_str("Nat"),
            Expr::nat_lit(0u64),
        ));
        let natural = Arc::new(Expr::const_str("Nat"));
        let zero = Arc::new(Expr::nat_lit(0u64));
        let wrapper = Arc::new(match position {
            "lambda_type" => Expr::lam_arc(BinderInfo::Default, named.clone(), zero),
            "pi_type" => Expr::pi_arc(BinderInfo::Default, named.clone(), natural),
            "let_type" => {
                Expr::let_named_arc(Name::anon(), named.clone(), zero.clone(), zero, false)
            }
            "let_value" => Expr::let_named_arc(Name::anon(), natural, named.clone(), zero, false),
            _ => unreachable!(),
        });
        assert!(!wrapper.has_fvar_quick());
        assert!(!wrapper.has_loose_bvars_quick());
        // Prime the contextual memo with `named`. The first traversal of the
        // wrapper then encounters that binder ONLY through a memo hit in its
        // type/value child, and must retain its named-descendant flag.
        let prefix = Arc::new(Expr::app_arc(named, wrapper.clone()));
        let nested = scope.lam(
            id(7),
            BinderInfo::Default,
            Expr::const_str("Nat"),
            Expr::app_arc(Arc::new(Expr::nat_lit(1u64)), wrapper),
        );
        let open = Expr::app_arc(prefix, Arc::new(nested));
        assert!(
            matches!(scope.close(&open), Err(TermScopeError::ShadowedLocal(local)) if local == id(7)),
            "named binder hidden in {position} must not bypass shadow checking"
        );
    }
}

#[test]
fn shared_free_variables_keep_their_actual_named_binding_depth() {
    let mut scope = TermScope::new();
    let shared = Arc::new(Expr::fvar(id(1)));
    let nested = scope.lam(
        id(2),
        BinderInfo::Default,
        Expr::const_str("Nat"),
        Expr::app_arc(shared.clone(), shared.clone()),
    );
    let open = scope.lam(
        id(1),
        BinderInfo::Default,
        Expr::const_str("Nat"),
        Expr::app_arc(shared.clone(), Arc::new(nested)),
    );
    let result = scope.close(&open).unwrap();
    let expected = Expr::lam(
        BinderInfo::Default,
        Expr::const_str("Nat"),
        Expr::app(
            Expr::bvar(0),
            Expr::lam(
                BinderInfo::Default,
                Expr::const_str("Nat"),
                Expr::app(Expr::bvar(1), Expr::bvar(1)),
            ),
        ),
    );
    assert_eq!(result, expected);
    // The same input pointer cannot retain its successful contextual answer
    // in a later close where the registered local has no enclosing binder.
    assert!(matches!(
        scope.close(&shared),
        Err(TermScopeError::OutOfScope(local)) if local == id(1)
    ));
}

#[test]
fn later_registration_rechecks_a_previously_unknown_outer_free_variable() {
    let mut scope = TermScope::new();
    let shared = Arc::new(Expr::fvar(id(19)));
    let open = Expr::app_arc(shared.clone(), shared);
    let first = scope
        .close_with_limits(&open, TermScopeLimits::default())
        .unwrap();
    assert_eq!(first.term, open, "unregistered outer locals remain free");
    assert_eq!(first.stats.memo_hits, 1);
    let unused = scope.lam(
        id(19),
        BinderInfo::Default,
        Expr::const_str("Nat"),
        Expr::nat_lit(0u64),
    );
    // This registration is not even part of `open`: it changes whether that
    // free local may escape, so no cache may survive the first closing call.
    assert!(matches!(
        scope.close(&open),
        Err(TermScopeError::OutOfScope(local)) if local == id(19)
    ));
    assert!(scope.close(&unused).is_ok());
    let bound = scope.lam(id(19), BinderInfo::Default, Expr::const_str("Nat"), open);
    assert_eq!(
        scope.close(&bound).unwrap(),
        Expr::lam(
            BinderInfo::Default,
            Expr::const_str("Nat"),
            Expr::app(Expr::bvar(0), Expr::bvar(0)),
        )
    );
}

#[test]
fn exact_visit_and_depth_limits_are_checked_before_neutral_hits() {
    let scope = TermScope::new();
    let shared = Arc::new(Expr::nat_lit(0u64));
    let repeated = Expr::app_arc(shared.clone(), shared.clone());
    // Requests: App, first leaf, second (neutral-cached) leaf. The hit still
    // consumes the third visit; moving cache lookup before the limit fails.
    assert!(matches!(
        scope.close_with_limits(
            &repeated,
            TermScopeLimits {
                max_visits: 2,
                max_depth: 2
            },
        ),
        Err(TermScopeError::VisitLimit)
    ));
    let exact = scope
        .close_with_limits(
            &repeated,
            TermScopeLimits {
                max_visits: 3,
                max_depth: 2,
            },
        )
        .unwrap();
    assert_eq!(exact.term, repeated);
    assert_eq!(exact.stats.visits, 3);
    assert_eq!(exact.stats.transformed_nodes, 2);
    assert_eq!(exact.stats.memo_hits, 1);

    // First cache the leaf at depth 1, then request that exact pointer at
    // depth 2 under a new App. The failing request is itself a neutral hit,
    // not a fresh child that would incidentally exercise the depth guard.
    let nested = Expr::app_arc(
        shared.clone(),
        Arc::new(Expr::app_arc(shared.clone(), shared)),
    );
    assert!(matches!(
        scope.close_with_limits(
            &nested,
            TermScopeLimits {
                max_visits: 5,
                max_depth: 2
            },
        ),
        Err(TermScopeError::DepthLimit)
    ));
    let exact = scope
        .close_with_limits(
            &nested,
            TermScopeLimits {
                max_visits: 5,
                max_depth: 3,
            },
        )
        .unwrap();
    assert_eq!(exact.term, nested);
    assert_eq!(exact.stats.visits, 5);
    assert_eq!(exact.stats.transformed_nodes, 3);
    assert_eq!(exact.stats.memo_hits, 2);
}
