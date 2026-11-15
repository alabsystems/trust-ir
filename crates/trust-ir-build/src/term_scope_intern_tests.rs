// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The shared close must produce the SAME term as the unshared one, and must
//! never merge two deferred binder identities to get there.

use super::*;
use crate::scoped_local::{LocalScope, LocalScopeLimits};
use clean_kernel::{BinderInfo, Environment, TypeChecker};

fn id(value: u64) -> FVarId {
    FVarId::new(value)
}

fn nat() -> Expr {
    Expr::const_str("Nat")
}

/// A freshly allocated copy of one structure, every node distinct. Building the
/// same shape twice is exactly the producer behaviour this pass collapses.
fn fresh_chain(depth: usize, leaf: Expr) -> Expr {
    (0..depth).fold(leaf, |inner, _| {
        Expr::app(
            Expr::app(Expr::const_str("Nat.add"), inner),
            Expr::nat_lit(1),
        )
    })
}

fn body_arc(expression: &Expr) -> &Arc<Expr> {
    match expression.kind() {
        ExprKind::Lam(_, _, body) | ExprKind::Pi(_, _, body) | ExprKind::Let(_, _, _, body, _) => {
            body
        }
        _ => panic!("expected a binder"),
    }
}

#[test]
fn duplicates_inside_a_registered_body_become_one_allocation_and_close_identically() {
    let mut scope = TermScope::new();
    // Twelve independently built copies of the same 24-node chain, all sealed
    // INSIDE a registered lambda body where no consumer-side pass may rebuild.
    let copies: Vec<Expr> = (0..12)
        .map(|_| fresh_chain(12, Expr::fvar(id(1))))
        .collect();
    let spine = copies
        .into_iter()
        .reduce(|left, right| Expr::app(Expr::app(Expr::const_str("Nat.add"), left), right))
        .unwrap();
    let open = scope.lam(id(1), BinderInfo::Default, nat(), spine);

    let unshared = scope
        .close_with_limits(&open, TermScopeLimits::default())
        .unwrap();
    let interned = scope
        .intern_with_limits(&open, TermScopeLimits::default())
        .unwrap();
    let shared = scope
        .close_with_limits(&interned.term, TermScopeLimits::default())
        .unwrap();

    // Exactness: the interned INPUT is the same term, and it closes to the
    // same term. Nothing is approximated, dropped or reordered.
    assert_eq!(interned.term, open);
    assert_eq!(shared.term, unshared.term);

    // And the point of the pass: the closing walk sees far less work.
    assert!(interned.stats.shared > 0, "{:?}", interned.stats);
    assert!(interned.stats.rebound > 0, "no body was re-registered");
    assert!(
        shared.stats.visits * 4 < unshared.stats.visits,
        "shared {:?} vs unshared {:?}",
        shared.stats,
        unshared.stats
    );
    assert!(shared.stats.transformed_nodes < unshared.stats.transformed_nodes);
}

#[test]
fn the_original_graph_still_closes_to_the_same_term_after_a_pass() {
    let mut scope = TermScope::new();
    let spine = Expr::app(
        fresh_chain(4, Expr::fvar(id(2))),
        fresh_chain(4, Expr::fvar(id(2))),
    );
    let open = scope.lam(id(2), BinderInfo::Default, nat(), spine);
    let before = scope.close(&open).unwrap();
    let interned = scope.intern(&open).unwrap();
    // Earlier registrations are retained, so the untouched original graph is
    // still closable. This is what lets a caller A/B the two representations.
    let after = scope.close(&open).unwrap();
    assert_eq!(before, after);
    assert_eq!(scope.close(&interned).unwrap(), before);
}

#[test]
fn two_registered_binders_with_structurally_equal_bodies_keep_their_own_identities() {
    let mut scope = TermScope::new();
    // Both bodies are the SAME structure, `FVar(7)`, and both are binder-free:
    // a pass that interned binder bodies would merge them. One is binder 7's
    // own body; the other belongs to binder 9 and refers to an OUTER 7.
    let own = scope.lam(id(7), BinderInfo::Default, nat(), Expr::fvar(id(7)));
    let inner = scope.lam(id(9), BinderInfo::Default, nat(), Expr::fvar(id(7)));
    let outer = scope.lam(id(7), BinderInfo::Default, nat(), inner);
    let open = Expr::app(own, outer);

    let unshared = scope.close(&open).unwrap();
    let interned = scope.intern(&open).unwrap();
    assert_eq!(interned, open);
    // Merging the two bodies cannot produce this term: under binder 9 the
    // registry would read binder 7 and refuse with ShadowedLocal, and the
    // other way round `FVar(7)` under binder 9 alone is OutOfScope.
    assert_eq!(scope.close(&interned).unwrap(), unshared);
    assert_eq!(
        unshared,
        Expr::app(
            Expr::lam(BinderInfo::Default, nat(), Expr::bvar(0)),
            Expr::lam(
                BinderInfo::Default,
                nat(),
                Expr::lam(BinderInfo::Default, nat(), Expr::bvar(1))
            )
        )
    );
}

#[test]
fn a_registered_body_is_never_given_an_ordinary_node_s_allocation() {
    let mut scope = TermScope::new();
    // An ordinary kernel lambda and a registered one whose bodies are the same
    // structure. The ordinary body may be interned; the registered one may not
    // share an allocation with it, or that ordinary binder would start reading
    // as binder 3.
    let ordinary = Expr::lam(BinderInfo::Default, nat(), nat());
    let named = scope.lam(id(3), BinderInfo::Default, nat(), nat());
    let open = Expr::app(ordinary, named);
    let interned = scope.intern(&open).unwrap();
    assert_eq!(interned, open);
    let ExprKind::App(left, right) = interned.kind() else {
        panic!("expected the application back")
    };
    assert!(
        !Arc::ptr_eq(body_arc(left), body_arc(right)),
        "a registered body must keep its own allocation"
    );
    assert_eq!(scope.close(&interned).unwrap(), scope.close(&open).unwrap());
}

#[test]
fn a_graph_without_duplicates_is_returned_unshared_and_unregistered() {
    let mut scope = TermScope::new();
    let open = scope.lam(
        id(5),
        BinderInfo::Default,
        nat(),
        Expr::app(Expr::fvar(id(5)), Expr::nat_lit(2)),
    );
    let interned = scope
        .intern_with_limits(&open, TermScopeLimits::default())
        .unwrap();
    assert_eq!(interned.term, open);
    assert_eq!(interned.stats.shared, 0);
    assert_eq!(interned.stats.rebound, 0);
    assert_eq!(interned.stats.rebuilt, 0);
}

#[test]
fn interning_refuses_over_its_own_visit_and_depth_limits() {
    let mut scope = TermScope::new();
    let open = scope.lam(
        id(6),
        BinderInfo::Default,
        nat(),
        fresh_chain(6, Expr::fvar(id(6))),
    );
    assert_eq!(
        scope
            .intern_with_limits(
                &open,
                TermScopeLimits {
                    max_visits: 3,
                    max_depth: 1_000
                }
            )
            .err(),
        Some(TermScopeError::VisitLimit)
    );
    assert_eq!(
        scope
            .intern_with_limits(
                &open,
                TermScopeLimits {
                    max_visits: 1_000,
                    max_depth: 2
                }
            )
            .err(),
        Some(TermScopeError::DepthLimit)
    );
}

#[test]
fn a_duplicate_split_across_a_let_value_and_a_registered_body_is_shared_and_still_checks() {
    // The sharp shape for this pass: the SAME structure appears once as an
    // ordinary child (a let value, which any consumer pass can rebuild) and
    // once inside a REGISTERED let body (which none can). Sharing them needs
    // the body rebuilt and re-registered under its own binder.
    let mut scope = LocalScope::with_limits(LocalScopeLimits::default());
    let t = scope.try_local(Expr::type_()).unwrap();
    let f = scope
        .try_local(Expr::pi(
            BinderInfo::Default,
            t.term().clone(),
            t.term().clone(),
        ))
        .unwrap();
    let x = scope.try_local(t.term().clone()).unwrap();
    let alias = scope.try_local(t.term().clone()).unwrap();
    let duplicated = || {
        Expr::app(
            f.term().clone(),
            Expr::app(f.term().clone(), x.term().clone()),
        )
    };
    let inner = alias.let_(duplicated(), Expr::app(f.term().clone(), duplicated()));
    let proof = t.lam(f.lam(x.lam(inner)));
    let claim = t.pi(f.pi(x.pi(t.term().clone())));

    let closed_proof = scope.close(&proof).unwrap();
    let interned = scope
        .intern_shared_with_limits(&proof, TermScopeLimits::default())
        .unwrap();
    assert_eq!(interned.term, proof);
    assert!(interned.stats.shared > 0, "{:?}", interned.stats);
    assert!(
        interned.stats.rebound > 0,
        "the let body must have been rebuilt and re-registered: {:?}",
        interned.stats
    );
    assert_eq!(scope.close(&interned.term).unwrap(), closed_proof);

    // The closed term is an ordinary kernel term either way, and both check.
    let closed_claim = scope.close(&claim).unwrap();
    TypeChecker::new(&Environment::new())
        .check_type(&closed_proof, &closed_claim)
        .unwrap();
    TypeChecker::new(&Environment::new())
        .check_type(&scope.close(&interned.term).unwrap(), &closed_claim)
        .unwrap();
}

#[test]
fn sharing_reaches_across_sibling_roots_that_no_consumer_pass_could_enter() {
    let mut scope = TermScope::new();
    // Two independent roots, each with its own binder, each sealing its own
    // copy of the same closed subterm. Only the registry owner can share them.
    let first = scope.lam(
        id(11),
        BinderInfo::Default,
        nat(),
        Expr::app(fresh_chain(8, Expr::nat_lit(0)), Expr::fvar(id(11))),
    );
    let second = scope.lam(
        id(12),
        BinderInfo::Default,
        nat(),
        Expr::app(fresh_chain(8, Expr::nat_lit(0)), Expr::fvar(id(12))),
    );
    let open = Expr::app(first, second);
    let unshared = scope
        .close_with_limits(&open, TermScopeLimits::default())
        .unwrap();
    let interned = scope
        .intern_with_limits(&open, TermScopeLimits::default())
        .unwrap();
    let shared = scope
        .close_with_limits(&interned.term, TermScopeLimits::default())
        .unwrap();
    assert_eq!(interned.term, open);
    assert_eq!(shared.term, unshared.term);
    assert!(interned.stats.shared > 0, "{:?}", interned.stats);
    assert!(
        shared.stats.transformed_nodes < unshared.stats.transformed_nodes,
        "shared {:?} vs unshared {:?}",
        shared.stats,
        unshared.stats
    );
}
