// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Adversarial structural checks for declaration-DAG reuse. The application
//! diamonds are deliberately not well-typed programs; their scope behavior,
//! sharing and charged work are the assertions, not kernel inhabitation.

use super::*;
use clean_kernel::BinderInfo;

fn id(value: u64) -> FVarId {
    FVarId::new(value)
}

fn diamond(scope: &mut TermScope, size: usize) -> Arc<Expr> {
    let mut left = Arc::new(scope.lam(
        id(1),
        BinderInfo::Default,
        Expr::const_str("Nat"),
        Expr::fvar(id(1)),
    ));
    let mut right = Arc::new(scope.lam(
        id(3),
        BinderInfo::Default,
        Expr::const_str("Nat"),
        Expr::fvar(id(3)),
    ));
    for _ in 0..size {
        // Unlike app(shared, shared), these make DISTINCT Join footprints
        // whose previous-level children overlap. Probe de-duplication, not
        // include(previous == incoming), must prevent exponential work.
        let next_left = Arc::new(Expr::app_arc(left.clone(), right.clone()));
        let next_right = Arc::new(Expr::app_arc(right, left));
        left = next_left;
        right = next_right;
    }
    left
}

#[test]
fn overlapping_join_diamonds_probe_linearly_and_reject_active_declarations() {
    let mut previous_visits = None;
    for size in [32usize, 64] {
        let mut scope = TermScope::new();
        let shared = diamond(&mut scope, size);
        let reused = scope.lam(
            // This ID lies inside the declaration envelope [1, 3] but is not
            // declared. Exact DAG probing, not disjoint-range skipping, is
            // deliberately required by the structural work assertions below.
            id(2),
            BinderInfo::Default,
            Expr::const_str("Nat"),
            Expr::app_arc(Arc::new(Expr::nat_lit(0u64)), shared.clone()),
        );
        let input = Expr::app_arc(shared.clone(), Arc::new(reused));
        let limits = TermScopeLimits {
            max_visits: 32 * size + 100,
            max_depth: 256,
        };
        let closed = scope.close_with_limits(&input, limits).unwrap();
        assert!(!closed.term.has_fvar_quick());
        assert!(!closed.term.has_loose_bvars_quick());
        assert!(closed.stats.scope_check_visits > size);
        assert!(closed.stats.scope_check_visits <= 8 * size + 20);
        if let Some(previous) = previous_visits {
            assert!(closed.stats.visits <= 2 * previous + 50);
        }
        previous_visits = Some(closed.stats.visits);

        let ExprKind::App(first, under) = closed.term.kind() else {
            panic!("root application")
        };
        let ExprKind::Lam(_, _, body) = under.kind() else {
            panic!("unrelated named binder")
        };
        let ExprKind::App(_, second) = body.kind() else {
            panic!("cached helper application")
        };
        // The transformed cache reuses child Arcs, so this equality does not
        // compare two independently allocated exponential expression trees.
        assert_eq!(first, second);
        let mut pending = vec![first.as_ref()];
        let mut seen = HashSet::new();
        let mut lambdas = 0;
        while let Some(node) = pending.pop() {
            if !seen.insert(node as *const Expr as usize) {
                continue;
            }
            match node.kind() {
                ExprKind::App(left, right) => {
                    pending.push(left);
                    pending.push(right);
                }
                ExprKind::Lam(_, ty, body) => {
                    assert_eq!(ty.as_ref(), &Expr::const_str("Nat"));
                    assert_eq!(body.as_ref(), &Expr::bvar(0));
                    lambdas += 1;
                }
                _ => panic!("diamond was not preserved"),
            }
        }
        // ExprFolderOpt returns an owned Option<Expr>. Replacing a parent's
        // changed edge wraps that Expr in a fresh Arc even when a cache hit
        // retained all of its child Arcs. Each diamond node has at most two
        // incoming edges, so each distinct lambda can have two root wrappers.
        // Require bounded DAG growth, not canonical pointer interning.
        assert!((2..=4).contains(&lambdas));
        assert!(seen.len() <= 4 * size + 4);
        assert_eq!(
            scope
                .close_with_limits(
                    &input,
                    TermScopeLimits {
                        max_visits: closed.stats.visits - 1,
                        ..limits
                    }
                )
                .err(),
            Some(TermScopeError::VisitLimit),
        );
        assert!(
            scope
                .close_with_limits(
                    &input,
                    TermScopeLimits {
                        max_visits: closed.stats.visits,
                        ..limits
                    }
                )
                .is_ok()
        );

        for conflict in [1u64, 3] {
            let under = scope.lam(
                id(conflict),
                BinderInfo::Default,
                Expr::const_str("Nat"),
                Expr::app_arc(Arc::new(Expr::nat_lit(0u64)), shared.clone()),
            );
            let bad = Expr::app_arc(shared.clone(), Arc::new(under));
            assert_eq!(
                scope.close(&bad).err(),
                Some(TermScopeError::ShadowedLocal(id(conflict)))
            );
        }
        eprintln!("overlapping footprint size={size}: {:?}", closed.stats);
    }
}

#[test]
fn apparently_closed_named_input_with_original_bvar_is_not_output_closed() {
    let mut scope = TermScope::new();
    let natural = Expr::const_str("Nat");
    // Input metadata sees a lambda around BVar0. TermScope must NOT treat that
    // BVar as the deferred named binder: it refers to the outer ordinary one.
    let shared = Arc::new(scope.lam(id(1), BinderInfo::Default, natural.clone(), Expr::bvar(0)));
    assert!(!shared.has_fvar_quick());
    assert!(!shared.has_loose_bvars_quick());
    let deeper = scope.lam(
        id(2),
        BinderInfo::Default,
        natural.clone(),
        Expr::app_arc(Arc::new(Expr::nat_lit(0u64)), shared.clone()),
    );
    let input = Expr::lam(
        BinderInfo::Default,
        natural.clone(),
        Expr::app_arc(shared, Arc::new(deeper)),
    );
    let closed = scope.close(&input).unwrap();
    let expected = Expr::lam(
        BinderInfo::Default,
        natural.clone(),
        Expr::app(
            Expr::lam(BinderInfo::Default, natural.clone(), Expr::bvar(1)),
            Expr::lam(
                BinderInfo::Default,
                natural.clone(),
                Expr::app(
                    Expr::nat_lit(0u64),
                    Expr::lam(BinderInfo::Default, natural, Expr::bvar(2)),
                ),
            ),
        ),
    );
    assert_eq!(closed, expected);
    assert!(!closed.has_fvar_quick());
    assert!(!closed.has_loose_bvars_quick());
}
