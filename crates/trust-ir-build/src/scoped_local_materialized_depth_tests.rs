// Copyright 2026 Andrew Yates | Licensed under the Apache License, Version 2.0
//! Different-depth reuse remains only a bounded structural optimization.
use super::*;
use clean_kernel::{Environment, TypeChecker};

fn identity_chain(ty: Expr, count: usize) -> Expr {
    let identity = Expr::lam(BinderInfo::Default, ty.clone(), Expr::bvar(0));
    let mut body = Expr::bvar(0);
    for _ in 0..count {
        body = Expr::app(identity.clone(), body);
    }
    Expr::lam(BinderInfo::Default, ty, body)
}

#[test]
fn unchanged_closed_subtree_reuses_across_binder_depth_with_same_free_inventory() {
    let mut scope = LocalScope::new();
    let ty = scope.try_local(Expr::type_()).unwrap();
    let binder = scope.try_local(ty.term().clone()).unwrap();
    let shared = identity_chain(ty.term().clone(), 96);
    assert!(!shared.has_loose_bvars() && shared.has_fvar_quick());
    let nested = Expr::lam(BinderInfo::Default, ty.term().clone(), shared.clone());
    let external = [ty.clone()];
    let mut cache = MaterializedCache::default();
    let mut work = 0;
    validate_materialized_cached(&scope, &external, &shared, &mut work, 10_000, &mut cache)
        .unwrap();
    let before = work;
    let reused = abstract_materialized_cached(
        &scope, &external, &binder, &nested, &mut work, 10_000, &mut cache,
    )
    .unwrap();
    let mut fresh_work = 0;
    let fresh = abstract_materialized(&scope, &external, &binder, &nested, &mut fresh_work, 10_000)
        .unwrap();
    assert_eq!(reused, fresh);
    eprintln!(
        "materialized nested reuse: warm={} cold={fresh_work}",
        work - before
    );
    assert!(
        work - before < fresh_work / 8,
        "warm={} fresh={fresh_work}",
        work - before
    );
    let proof = scope.close(&ty.lam(reused)).unwrap();
    let _inferred_type = TypeChecker::new(&Environment::new())
        .infer_type(&proof)
        .unwrap();
}

#[test]
fn different_depth_reuse_keeps_targets_and_removed_free_dependencies() {
    let mut scope = LocalScope::new();
    let ty = scope.try_local(Expr::type_()).unwrap();
    let x = scope.try_local(ty.term().clone()).unwrap();
    let shared = Expr::lam(BinderInfo::Default, ty.term().clone(), x.term().clone());
    let nested = Expr::lam(BinderInfo::Default, ty.term().clone(), shared.clone());
    let mut cache = MaterializedCache::default();
    let mut work = 0;
    validate_materialized_cached(
        &scope,
        &[ty.clone(), x.clone()],
        &shared,
        &mut work,
        10_000,
        &mut cache,
    )
    .unwrap();
    let abstraction = abstract_materialized_cached(
        &scope,
        std::slice::from_ref(&ty),
        &x,
        &nested,
        &mut work,
        10_000,
        &mut cache,
    )
    .unwrap();
    assert_eq!(
        abstraction,
        Expr::lam(
            BinderInfo::Default,
            ty.term().clone(),
            Expr::lam(
                BinderInfo::Default,
                ty.term().clone(),
                Expr::lam(BinderInfo::Default, ty.term().clone(), Expr::bvar(2),),
            )
        ),
    );
    let error = validate_materialized_cached(&scope, &[ty], &nested, &mut work, 10_000, &mut cache)
        .unwrap_err();
    assert!(error.contains("unauthorized free variable"), "{error}");
}

#[test]
fn changed_abstraction_and_loose_local_are_never_reused_at_another_depth() {
    let mut scope = LocalScope::new();
    let x = scope.try_local(Expr::type_()).unwrap();
    let mut cache = MaterializedCache::default();
    let mut work = 0;
    let first =
        abstract_materialized_cached(&scope, &[], &x, x.term(), &mut work, 1000, &mut cache)
            .unwrap();
    assert_eq!(
        first,
        Expr::lam(BinderInfo::Default, Expr::type_(), Expr::bvar(0))
    );
    let nested = Expr::lam(BinderInfo::Default, Expr::type_(), x.term().clone());
    let second =
        abstract_materialized_cached(&scope, &[], &x, &nested, &mut work, 1000, &mut cache)
            .unwrap();
    assert_eq!(
        second,
        Expr::lam(
            BinderInfo::Default,
            Expr::type_(),
            Expr::lam(BinderInfo::Default, Expr::type_(), Expr::bvar(1),)
        )
    );
    let loose = Expr::bvar(1);
    let inside = Expr::lam(
        BinderInfo::Default,
        Expr::type_(),
        Expr::lam(BinderInfo::Default, Expr::type_(), loose.clone()),
    );
    validate_materialized_cached(&scope, &[], &inside, &mut work, 1000, &mut cache).unwrap();
    let shifted = Expr::lam(BinderInfo::Default, Expr::type_(), loose);
    assert!(
        validate_materialized_cached(&scope, &[], &shifted, &mut work, 1000, &mut cache,)
            .unwrap_err()
            .contains("loose bound variable")
    );
}

#[test]
fn different_depth_hit_keeps_depth_and_aggregate_limits() {
    let scope = LocalScope::with_limits(super::super::LocalScopeLimits {
        closing: super::super::TermScopeLimits {
            max_visits: 1000,
            max_depth: 5,
        },
        ..Default::default()
    });
    let shared = Expr::lam(
        BinderInfo::Default,
        Expr::type_(),
        Expr::lam(BinderInfo::Default, Expr::type_(), Expr::bvar(0)),
    );
    let at_limit = Expr::lam(
        BinderInfo::Default,
        Expr::type_(),
        Expr::lam(BinderInfo::Default, Expr::type_(), shared.clone()),
    );
    let too_deep = Expr::lam(BinderInfo::Default, Expr::type_(), at_limit.clone());
    let mut cache = MaterializedCache::default();
    let mut work = 0;
    validate_materialized_cached(&scope, &[], &shared, &mut work, 1000, &mut cache).unwrap();
    validate_materialized_cached(&scope, &[], &at_limit, &mut work, 1000, &mut cache).unwrap();
    for fresh in [false, true] {
        let mut empty = MaterializedCache::default();
        let selected = if fresh { &mut empty } else { &mut cache };
        assert!(
            validate_materialized_cached(&scope, &[], &too_deep, &mut work, 1000, selected,)
                .unwrap_err()
                .contains("traversal depth limit")
        );
    }
    let before = work;
    assert!(
        validate_materialized_cached(&scope, &[], &at_limit, &mut work, before + 1, &mut cache,)
            .unwrap_err()
            .contains("aggregate abstraction limit")
    );
    assert_eq!(work, before + 1);
}

#[test]
fn same_binder_depth_hits_still_bound_deeper_application_nesting() {
    let scope = LocalScope::with_limits(super::super::LocalScopeLimits {
        closing: super::super::TermScopeLimits {
            max_visits: 1000,
            max_depth: 5,
        },
        ..Default::default()
    });
    let ty = Expr::type_();
    let shared = Expr::app(ty.clone(), Expr::app(ty.clone(), ty.clone()));
    let at_limit = Expr::app(ty.clone(), Expr::app(ty.clone(), shared.clone()));
    // The left arm fills the same-depth walk memo before the deeper right arm.
    // All nodes keep BVar depth zero; only structural nesting increases.
    let too_deep = Expr::app(shared.clone(), at_limit.clone());
    for warm in [false, true] {
        let mut cache = MaterializedCache::default();
        let mut work = 0;
        if warm {
            validate_materialized_cached(&scope, &[], &shared, &mut work, 1000, &mut cache)
                .unwrap();
        }
        assert!(
            validate_materialized_cached(&scope, &[], &too_deep, &mut work, 1000, &mut cache,)
                .unwrap_err()
                .contains("traversal depth limit")
        );
        validate_materialized_cached(&scope, &[], &at_limit, &mut work, 1000, &mut cache).unwrap();
        let beyond = Expr::app(ty.clone(), at_limit.clone());
        assert!(
            validate_materialized_cached(&scope, &[], &beyond, &mut work, 1000, &mut cache,)
                .unwrap_err()
                .contains("traversal depth limit")
        );
    }
}

#[test]
fn unchanged_cache_refuses_stale_owner_and_does_not_typecheck_invalid_bodies() {
    let shared = identity_chain(Expr::type_(), 32);
    let mut cache = MaterializedCache::default();
    let mut work = 0;
    {
        let scope = LocalScope::new();
        validate_materialized_cached(&scope, &[], &shared, &mut work, 10_000, &mut cache).unwrap();
    }
    let scope = LocalScope::new();
    assert!(
        validate_materialized_cached(&scope, &[], &shared, &mut work, 10_000, &mut cache,)
            .unwrap_err()
            .contains("foreign materialized cache owner")
    );

    // Syntactic validation deliberately cannot certify a definition's type.
    // Even a warm unchanged hit leaves the complete body for the kernel.
    let invalid = Expr::app(Expr::type_(), Expr::type_());
    let mut cache = MaterializedCache::default();
    validate_materialized_cached(&scope, &[], &invalid, &mut work, 10_000, &mut cache).unwrap();
    let nested = Expr::lam(BinderInfo::Default, Expr::type_(), invalid);
    validate_materialized_cached(&scope, &[], &nested, &mut work, 10_000, &mut cache).unwrap();
    assert!(
        TypeChecker::new(&Environment::new())
            .infer_type(&nested)
            .is_err()
    );
}
