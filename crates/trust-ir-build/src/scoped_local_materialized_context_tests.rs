// Copyright 2026 Andrew Yates | Licensed under the Apache License, Version 2.0
//! Ordinary materialization consumers keep exact scope/depth/cap refusals.
use super::*;
use crate::{scoped_local::LocalScopeLimits, term_scope::TermScopeLimits};
const LIMIT: usize = 262_144;

#[test]
fn one_inventory_reuses_authorization_without_authorizing_removed_or_foreign_locals() {
    let mut scope = LocalScope::new();
    let locals = (0..135)
        .map(|_| scope.try_local(Expr::type_()).unwrap())
        .collect::<Vec<_>>();
    let mut roots = Vec::new();
    let mut root = locals[134].term().clone();
    for _ in 0..24 {
        root = Expr::lam(BinderInfo::Default, Expr::type_(), root);
        roots.push(root.clone());
    }
    let mut fresh_cache = MaterializedCache::default();
    let mut fresh_work = 0;
    for root in &roots {
        validate_materialized_cached(
            &scope,
            &locals,
            root,
            &mut fresh_work,
            LIMIT,
            &mut fresh_cache,
        )
        .unwrap();
    }
    let mut cache = MaterializedCache::default();
    let mut work = 0;
    {
        let mut context =
            MaterializedValidationContext::new(&scope, &locals, &mut work, LIMIT, &mut cache)
                .unwrap();
        for root in &roots {
            validate_materialized_in_context_cached(
                &mut context,
                root,
                &mut work,
                LIMIT,
                &mut cache,
            )
            .unwrap();
        }
    }
    assert!(
        work > 0 && work < fresh_work,
        "actual authorization work must be saved, not reset"
    );
    // A fresh narrowed context must recheck a warm expression's dependency.
    let narrowed = &locals[..134];
    let mut context =
        MaterializedValidationContext::new(&scope, narrowed, &mut work, LIMIT, &mut cache).unwrap();
    assert!(
        validate_materialized_in_context_cached(
            &mut context,
            roots.last().unwrap(),
            &mut work,
            LIMIT,
            &mut cache
        )
        .unwrap_err()
        .contains("unauthorized")
    );
    let mut foreign = LocalScope::new();
    let other = foreign.try_local(Expr::type_()).unwrap();
    let foreign_handles = vec![other.clone()];
    assert!(
        MaterializedValidationContext::new(&scope, &foreign_handles, &mut work, LIMIT, &mut cache)
            .err()
            .unwrap()
            .contains("foreign")
    );
    assert!(
        MaterializedValidationContext::new(
            &foreign,
            &foreign_handles,
            &mut work,
            LIMIT,
            &mut cache
        )
        .err()
        .unwrap()
        .contains("cache owner")
    );
    let duplicate = vec![locals[0].clone(), locals[0].clone()];
    assert!(
        MaterializedValidationContext::new(&scope, &duplicate, &mut work, LIMIT, &mut cache)
            .is_err()
    );
}

#[test]
fn reused_inventory_keeps_named_loose_unknown_depth_and_exhaustion_refusals() {
    let mut scope = LocalScope::with_limits(LocalScopeLimits {
        closing: TermScopeLimits {
            max_visits: 1000,
            max_depth: 12,
        },
        ..Default::default()
    });
    let permitted = scope.try_local(Expr::type_()).unwrap();
    let unknown = scope.try_local(Expr::type_()).unwrap();
    let external = vec![permitted.clone()];
    let ordinary = Expr::lam(BinderInfo::Default, Expr::type_(), Expr::bvar(0));
    let mut cache = MaterializedCache::default();
    let mut work = 0;
    let mut context =
        MaterializedValidationContext::new(&scope, &external, &mut work, LIMIT, &mut cache)
            .unwrap();
    validate_materialized_in_context_cached(&mut context, &ordinary, &mut work, LIMIT, &mut cache)
        .unwrap();
    let named = permitted.lam(permitted.term().clone());
    for (root, needle) in [
        (named, "deferred"),
        (Expr::bvar(0), "loose"),
        (unknown.term().clone(), "unauthorized"),
    ] {
        assert!(
            validate_materialized_in_context_cached(
                &mut context,
                &root,
                &mut work,
                LIMIT,
                &mut cache
            )
            .unwrap_err()
            .contains(needle)
        );
    }
    let mut deep = ordinary;
    for _ in 0..16 {
        deep = Expr::lam(BinderInfo::Default, Expr::type_(), deep);
    }
    assert!(
        validate_materialized_in_context_cached(&mut context, &deep, &mut work, LIMIT, &mut cache)
            .unwrap_err()
            .contains("depth")
    );
    // Other work in the same producer can consume the remaining allowance.
    work = LIMIT;
    for _ in 0..2 {
        assert!(
            validate_materialized_in_context_cached(
                &mut context,
                permitted.term(),
                &mut work,
                LIMIT,
                &mut cache
            )
            .is_err()
        );
        assert_eq!(
            work, LIMIT,
            "a cached authorization cannot reset the exhausted ledger"
        );
    }
}

#[test]
fn prepared_inventory_keeps_owner_visit_floor_and_failed_preparation_is_not_reused() {
    let mut scope = LocalScope::with_limits(LocalScopeLimits {
        closing: TermScopeLimits {
            max_visits: 1,
            max_depth: 12,
        },
        ..Default::default()
    });
    let local = scope.try_local(Expr::type_()).unwrap();
    let external = vec![local.clone()];
    let mut cache = MaterializedCache::default();
    let mut work = 0;
    let mut context =
        MaterializedValidationContext::new(&scope, &external, &mut work, LIMIT, &mut cache)
            .unwrap();
    for _ in 0..2 {
        assert!(
            validate_materialized_in_context_cached(
                &mut context,
                local.term(),
                &mut work,
                LIMIT,
                &mut cache
            )
            .unwrap_err()
            .contains("owner visit limit")
        );
    }
    let mut remaining = 0;
    assert!(
        MaterializedValidationContext::new(&scope, &external, &mut remaining, 0, &mut cache)
            .is_err()
    );
    assert_eq!(remaining, 0);
    // A failed constructor returns no context; a real later preparation still
    // has to authenticate and spend its inventory charge.
    let _context =
        MaterializedValidationContext::new(&scope, &external, &mut remaining, LIMIT, &mut cache)
            .unwrap();
    assert_eq!(remaining, external.len());
}

#[test]
fn interrupted_inventory_permission_never_becomes_authorization() {
    let mut scope = LocalScope::with_limits(LocalScopeLimits {
        closing: TermScopeLimits {
            max_visits: 8,
            max_depth: 12,
        },
        ..Default::default()
    });
    let external = (0..5)
        .map(|_| scope.try_local(Expr::type_()).unwrap())
        .collect::<Vec<_>>();
    let mut cache = MaterializedCache::default();
    let mut work = 0;
    // Warm expression entry with a different authenticated Rc inventory.
    validate_materialized_cached(
        &scope,
        &external,
        external[4].term(),
        &mut work,
        LIMIT,
        &mut cache,
    )
    .unwrap();
    let mut context =
        MaterializedValidationContext::new(&scope, &external, &mut work, LIMIT, &mut cache)
            .unwrap();
    let mut previous = work;
    for _ in 0..2 {
        // Five inventory slots + root/cache/permission probes consume all8
        // owner visits before the first subset element can be checked.
        assert!(
            validate_materialized_in_context_cached(
                &mut context,
                external[4].term(),
                &mut work,
                LIMIT,
                &mut cache
            )
            .unwrap_err()
            .contains("owner visit limit")
        );
        assert!(
            work > previous,
            "a retry is charged and cannot use partial authorization"
        );
        previous = work;
    }
}
