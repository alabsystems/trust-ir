// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Closing erases deferred identities from OUTPUT, not the original input.

use super::*;
use clean_kernel::{BinderInfo, Environment, TypeChecker};

fn id(value: u64) -> FVarId {
    FVarId::new(value)
}

fn named(scope: &mut TermScope, kind: usize, ty: Expr, value: Expr, body: Expr) -> Expr {
    match kind {
        0 => scope.lam(id(2), BinderInfo::Implicit, ty, body),
        1 => scope.pi(id(2), BinderInfo::Implicit, ty, body),
        2 => scope.let_named(id(2), Name::from_string("unused"), ty, value, body, true),
        _ => unreachable!(),
    }
}

fn ordinary(kind: usize, ty: Expr, value: Expr, body: Expr) -> Expr {
    match kind {
        0 => Expr::lam(BinderInfo::Implicit, ty, body),
        1 => Expr::pi(BinderInfo::Implicit, ty, body),
        2 => Expr::let_named(Name::from_string("unused"), ty, value, body, true),
        _ => unreachable!(),
    }
}

fn body(term: &Expr) -> &Arc<Expr> {
    match term.kind() {
        ExprKind::Lam(_, _, body) | ExprKind::Pi(_, _, body) | ExprKind::Let(_, _, _, body, _) => {
            body
        }
        _ => panic!("expected binder"),
    }
}

fn checked(actual: &Expr, expected: &Expr) {
    assert_eq!(actual, expected);
    assert!(!actual.has_fvar_quick());
    assert!(!actual.has_loose_bvars_quick());
    let mut env = Environment::new();
    env.init_nat().unwrap();
    let checker = TypeChecker::new(&env);
    let claim = checker.infer_type(expected).unwrap();
    checker.check_type(actual, &claim).unwrap();
}

#[test]
fn unused_closed_binders_can_be_reembedded_under_the_original_local() {
    for kind in 0..3 {
        let mut scope = TermScope::new();
        let natural = Expr::const_str("Nat");
        let open = named(
            &mut scope,
            kind,
            natural.clone(),
            Expr::nat_lit(7u64),
            natural.clone(),
        );
        let closed = scope.close(&open).unwrap();
        assert!(
            !Arc::ptr_eq(body(&open), body(&closed)),
            "output must shed its registered body Arc"
        );
        assert_eq!(scope.close(&closed).unwrap(), closed);

        let nested = scope.lam(id(2), BinderInfo::Default, natural.clone(), closed);
        let expected = Expr::lam(
            BinderInfo::Default,
            natural.clone(),
            ordinary(kind, natural.clone(), Expr::nat_lit(7u64), natural.clone()),
        );
        checked(&scope.close(&nested).unwrap(), &expected);

        // Do not erase the INPUT registry as a shortcut: an actual deferred
        // duplicate is still malformed, even after its earlier successful close.
        let invalid = scope.lam(id(2), BinderInfo::Default, natural, open);
        assert_eq!(
            scope.close(&invalid).err(),
            Some(TermScopeError::ShadowedLocal(id(2)))
        );
    }
}

#[test]
fn type_only_changes_also_detach_unused_named_bodies() {
    for kind in 0..3 {
        let mut scope = TermScope::new();
        let natural = Expr::const_str("Nat");
        // This type reduces to Type but mentions the outer Nat parameter.
        // Closing changes only the inner binder's type, not value or body.
        let family = Expr::lam(BinderInfo::Default, natural.clone(), Expr::type_());
        let open_ty = Expr::app(family.clone(), Expr::fvar(id(1)));
        let inner = named(&mut scope, kind, open_ty, natural.clone(), natural.clone());
        let open = scope.lam(id(1), BinderInfo::Default, natural.clone(), inner.clone());
        let closed = scope.close(&open).unwrap();
        assert!(!Arc::ptr_eq(body(&inner), body(body(&closed))));
        let nested = scope.lam(id(2), BinderInfo::Default, natural.clone(), closed);
        let expected = Expr::lam(
            BinderInfo::Default,
            natural.clone(),
            Expr::lam(
                BinderInfo::Default,
                natural.clone(),
                ordinary(
                    kind,
                    Expr::app(family, Expr::bvar(0)),
                    natural.clone(),
                    natural.clone(),
                ),
            ),
        );
        checked(&scope.close(&nested).unwrap(), &expected);
        let invalid = scope.lam(id(2), BinderInfo::Default, natural, open);
        assert_eq!(
            scope.close(&invalid).err(),
            Some(TermScopeError::ShadowedLocal(id(2)))
        );
    }
}

#[test]
fn value_only_changes_also_detach_unused_named_let_bodies() {
    let mut scope = TermScope::new();
    let natural = Expr::const_str("Nat");
    let inner = named(
        &mut scope,
        2,
        natural.clone(),
        Expr::fvar(id(1)),
        natural.clone(),
    );
    let open = scope.lam(id(1), BinderInfo::Default, natural.clone(), inner.clone());
    let closed = scope.close(&open).unwrap();
    assert!(!Arc::ptr_eq(body(&inner), body(body(&closed))));
    let nested = scope.lam(id(2), BinderInfo::Default, natural.clone(), closed);
    let expected = Expr::lam(
        BinderInfo::Default,
        natural.clone(),
        Expr::lam(
            BinderInfo::Default,
            natural.clone(),
            ordinary(2, natural.clone(), Expr::bvar(0), natural.clone()),
        ),
    );
    checked(&scope.close(&nested).unwrap(), &expected);
    let invalid = scope.lam(id(2), BinderInfo::Default, natural, open);
    assert_eq!(
        scope.close(&invalid).err(),
        Some(TermScopeError::ShadowedLocal(id(2)))
    );
}

#[test]
fn detached_outputs_keep_dag_sharing_budgets_and_cached_input_shadow_checks() {
    for kind in 0..3 {
        let mut scope = TermScope::new();
        let natural = Expr::const_str("Nat");
        let open = Arc::new(named(
            &mut scope,
            kind,
            natural.clone(),
            Expr::nat_lit(7u64),
            natural.clone(),
        ));
        // Structural DAG fixture only; the applications need not type-check.
        let shared = Expr::app_arc(open.clone(), open.clone());
        let limits = TermScopeLimits::default();
        let closed = scope.close_with_limits(&shared, limits).unwrap();
        let ExprKind::App(left, right) = closed.term.kind() else {
            panic!("pair")
        };
        assert!(
            Arc::ptr_eq(left, right),
            "detach once per transformed node, not per incoming edge"
        );
        assert!(!Arc::ptr_eq(body(&open), body(left)));
        assert_eq!(scope.close(&closed.term).unwrap(), closed.term);
        assert!(closed.stats.memo_hits > 0);
        assert!(
            scope
                .close_with_limits(
                    &shared,
                    TermScopeLimits {
                        max_visits: closed.stats.visits,
                        ..limits
                    }
                )
                .is_ok()
        );
        assert_eq!(
            scope
                .close_with_limits(
                    &shared,
                    TermScopeLimits {
                        max_visits: closed.stats.visits - 1,
                        ..limits
                    }
                )
                .err(),
            Some(TermScopeError::VisitLimit)
        );
        assert_eq!(
            scope
                .close_with_limits(
                    &shared,
                    TermScopeLimits {
                        max_depth: 1,
                        ..limits
                    }
                )
                .err(),
            Some(TermScopeError::DepthLimit)
        );

        // Warm the within-close cache before revisiting the ORIGINAL open DAG
        // in a conflicting context. Closed output is reusable; input isn't.
        let invalid = scope.lam(id(2), BinderInfo::Default, natural, shared.clone());
        assert_eq!(
            scope.close(&Expr::app(shared, invalid)).err(),
            Some(TermScopeError::ShadowedLocal(id(2)))
        );
    }
}
