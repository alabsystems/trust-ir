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

#[test]
fn completed_exact_application_shells_charge_every_root_without_rewalking_children() {
    let function = Arc::new(Expr::const_str("Nat.succ"));
    let argument = Arc::new(Expr::nat_lit(0));
    let roots: Vec<_> = (0..192)
        .map(|_| Expr::app_arc(function.clone(), argument.clone()))
        .collect();
    let limits = TermScopeLimits {
        max_visits: roots.len() + 2,
        max_depth: 2,
    };
    let mut scope = TermScope::new();
    let prepared = scope.intern_forest_with_limits(&roots, limits).unwrap();
    assert_eq!(prepared.terms, roots, "all actual roots remain");
    assert_eq!(prepared.stats.visits, limits.max_visits);
    assert_eq!(prepared.stats.examined, roots.len() + 2);
    assert_eq!(prepared.stats.shared, roots.len() - 1);
    assert_eq!(prepared.stats.canonical, 3);
    assert_eq!(prepared.stats.rebuilt, 0);
    assert_eq!(prepared.stats.max_depth, 2);
    let failure = TermScope::new()
        .intern_forest_with_diagnostics(
            &roots,
            TermScopeLimits {
                max_visits: limits.max_visits - 1,
                ..limits
            },
        )
        .err()
        .unwrap();
    assert_eq!(failure.error, TermScopeError::VisitLimit);
    assert_eq!(failure.stats.visits, limits.max_visits - 1);
    assert_eq!(failure.completed_roots, roots.len() - 1);
    assert_eq!(failure.phase, TermScopeInternPhase::Node);
    assert_eq!(failure.walk_depth, 0);
    assert_eq!(TermScopeLimits::default().max_visits, 1_000_000);
    assert_eq!(TermScopeLimits::default().max_depth, 16_384);
}

#[test]
fn equal_but_fresh_application_children_are_visited_and_fresh_shell_depth_is_checked() {
    let function = Arc::new(Expr::const_str("Nat.succ"));
    let argument = Arc::new(Expr::nat_lit(0));
    let first = Expr::app_arc(function.clone(), argument.clone());
    let fresh = Expr::app_arc(
        Arc::new(function.as_ref().clone()),
        Arc::new(argument.as_ref().clone()),
    );
    assert_eq!(first, fresh);
    let refusal = TermScope::new()
        .intern_forest_with_diagnostics(
            &[first.clone(), fresh],
            TermScopeLimits {
                max_visits: 4,
                max_depth: 100,
            },
        )
        .err()
        .unwrap();
    assert_eq!(refusal.error, TermScopeError::VisitLimit);
    assert_eq!(refusal.completed_roots, 1);
    assert_eq!(refusal.stats.visits, 4);
    let nested = Expr::app_arc(
        function.clone(),
        Arc::new(Expr::app_arc(function, Arc::new(first.clone()))),
    );
    let refusal = TermScope::new()
        .intern_forest_with_diagnostics(
            &[first, nested],
            TermScopeLimits {
                max_visits: 100,
                max_depth: 2,
            },
        )
        .err()
        .unwrap();
    assert_eq!(refusal.error, TermScopeError::DepthLimit);
    assert_eq!(refusal.completed_roots, 1);
    assert_eq!(refusal.walk_depth, 2);
}

#[test]
fn completed_application_shells_never_reuse_registered_body_roots_or_named_ancestors() {
    let mut scope = TermScope::new();
    let function = Arc::new(Expr::const_str("Nat.succ"));
    let argument = Arc::new(Expr::fvar(id(7)));
    let app = || Expr::app_arc(function.clone(), argument.clone());
    let ordinary = Expr::lam(BinderInfo::Default, nat(), app());
    let own = scope.lam(id(7), BinderInfo::Default, nat(), app());
    let inner = scope.lam(id(9), BinderInfo::Default, nat(), app());
    let outer = scope.lam(id(7), BinderInfo::Default, nat(), inner);
    let roots = [ordinary, own, outer];
    let original = [
        scope.close(&roots[1]).unwrap(),
        scope.close(&roots[2]).unwrap(),
    ];
    let prepared = scope
        .intern_forest_with_limits(&roots, TermScopeLimits::default())
        .unwrap();
    assert_eq!(prepared.terms, roots);
    assert!(!Arc::ptr_eq(
        body_arc(&prepared.terms[0]),
        body_arc(&prepared.terms[1])
    ));
    assert!(!Arc::ptr_eq(
        body_arc(&prepared.terms[1]),
        body_arc(body_arc(&prepared.terms[2]))
    ));
    assert_eq!(
        scope.close(&prepared.terms[0]).err(),
        scope.close(&roots[0]).err()
    );
    assert!(
        scope.close(&prepared.terms[0]).is_err(),
        "the ordinary binder cannot capture named 7"
    );
    assert_eq!(scope.close(&prepared.terms[1]).unwrap(), original[0]);
    assert_eq!(scope.close(&prepared.terms[2]).unwrap(), original[1]);

    let named = Arc::new(scope.lam(id(21), BinderInfo::Default, nat(), Expr::fvar(id(21))));
    let argument = Arc::new(Expr::nat_lit(0));
    let roots = [
        Expr::app_arc(named.clone(), argument.clone()),
        Expr::app_arc(named, argument),
    ];
    let prepared = scope
        .intern_forest_with_limits(&roots, TermScopeLimits::default())
        .unwrap();
    assert_eq!(prepared.terms, roots);
    assert_eq!(
        prepared.stats.visits, 8,
        "named-containing shells retain the original charged child dispatch"
    );
}

#[test]
fn completed_application_shells_preserve_independent_ordinary_kernel_claims_and_refusals() {
    let function = Arc::new(Expr::bvar(1));
    let argument = Arc::new(Expr::bvar(0));
    let function_type = Expr::pi(BinderInfo::Default, Expr::bvar(0), Expr::bvar(1));
    let roots: Vec<_> = (0..32)
        .map(|_| {
            Expr::lam(
                BinderInfo::Default,
                Expr::type_(),
                Expr::lam(
                    BinderInfo::Default,
                    function_type.clone(),
                    Expr::lam(
                        BinderInfo::Default,
                        Expr::bvar(1),
                        Expr::app_arc(function.clone(), argument.clone()),
                    ),
                ),
            )
        })
        .collect();
    let claim = Expr::pi(
        BinderInfo::Default,
        Expr::type_(),
        Expr::pi(
            BinderInfo::Default,
            function_type.clone(),
            Expr::pi(BinderInfo::Default, Expr::bvar(1), Expr::bvar(2)),
        ),
    );
    let wrong_claim = Expr::pi(
        BinderInfo::Default,
        Expr::type_(),
        Expr::pi(
            BinderInfo::Default,
            function_type,
            Expr::pi(BinderInfo::Default, Expr::bvar(1), Expr::type_()),
        ),
    );
    let mut scope = TermScope::new();
    let prepared = scope
        .intern_forest_with_limits(&roots, TermScopeLimits::default())
        .unwrap();
    assert_eq!(prepared.terms, roots);
    assert_eq!(prepared.terms.len(), 32);
    let environment = Environment::new();
    for (original, prepared) in roots.iter().zip(&prepared.terms) {
        let original = scope.close(original).unwrap();
        let prepared = scope.close(prepared).unwrap();
        assert_eq!(original, prepared);
        TypeChecker::new(&environment)
            .check_type(&original, &claim)
            .unwrap();
        TypeChecker::new(&environment)
            .check_type(&prepared, &claim)
            .unwrap();
        let error = TypeChecker::new(&environment)
            .check_type(&prepared, &wrong_claim)
            .unwrap_err();
        let reason = format!("{error:?}");
        assert!(reason.contains("TypeMismatch"), "{reason}");
        assert!(
            !reason.contains("BudgetExhausted") && !reason.contains("HeartbeatExceeded"),
            "{reason}"
        );
    }
}

#[test]
fn a_registered_body_aliased_as_an_ordinary_argument_is_never_a_canonical_body() {
    let mut scope = TermScope::new();
    let function = Arc::new(Expr::const_str("Nat.succ"));
    let argument = Arc::new(Expr::fvar(id(7)));
    let named = scope.lam(
        id(7),
        BinderInfo::Default,
        nat(),
        Expr::app_arc(function.clone(), argument.clone()),
    );
    // First visit the exact registered body allocation as an ordinary App child.
    let aliased_body = body_arc(&named).clone();
    let first = Expr::app_arc(Arc::new(Expr::const_str("wrapper")), aliased_body);
    // This body's root is fresh; its children are the exact same allocations.
    let ordinary = Expr::lam(
        BinderInfo::Default,
        nat(),
        Expr::app_arc(function, argument),
    );
    let original = scope.close(&ordinary);
    assert!(
        original.is_err(),
        "ordinary binder must not capture named local 7"
    );
    let prepared = scope
        .intern_forest_with_limits(&[first, ordinary, named], TermScopeLimits::default())
        .unwrap();
    assert!(
        scope.close(&prepared.terms[1]).is_err(),
        "ordinary argument alias must not enter the canonical table and turn an ordinary binder into named 7"
    );
}

#[test]
fn a_registered_body_aliased_inside_a_valid_root_cannot_capture_an_ordinary_binder() {
    let mut scope = TermScope::new();
    let a = Expr::fvar(id(1));
    let function_type = Expr::pi(BinderInfo::Default, a.clone(), a.clone());
    let function = Arc::new(Expr::fvar(id(2)));
    let argument = Arc::new(Expr::fvar(id(7)));
    let named = scope.lam(
        id(7),
        BinderInfo::Default,
        a.clone(),
        Expr::app_arc(function.clone(), argument.clone()),
    );
    let first = scope.lam(
        id(7),
        BinderInfo::Default,
        a.clone(),
        Expr::app_arc(function.clone(), body_arc(&named).clone()),
    );
    let ordinary = Expr::lam(BinderInfo::Default, a, Expr::app_arc(function, argument));
    let wrap = |scope: &mut TermScope, inner| {
        let f = scope.lam(id(2), BinderInfo::Default, function_type.clone(), inner);
        scope.lam(id(1), BinderInfo::Default, Expr::type_(), f)
    };
    let roots = [
        wrap(&mut scope, first),
        wrap(&mut scope, ordinary),
        wrap(&mut scope, named),
    ];
    let original_error = scope.close(&roots[1]).unwrap_err();
    assert_eq!(original_error, TermScopeError::OutOfScope(id(7)));
    let function_type = Expr::pi(BinderInfo::Default, Expr::bvar(0), Expr::bvar(1));
    let claim = Expr::pi(
        BinderInfo::Default,
        Expr::type_(),
        Expr::pi(
            BinderInfo::Default,
            function_type,
            Expr::pi(BinderInfo::Default, Expr::bvar(1), Expr::bvar(2)),
        ),
    );
    let environment = Environment::new();
    for index in [0, 2] {
        TypeChecker::new(&environment)
            .check_type(&scope.close(&roots[index]).unwrap(), &claim)
            .unwrap();
    }
    assert!(
        scope
            .close_external_forest(&roots, &[], &[0; 3], TermScopeLimits::default())
            .0
            .is_err()
    );
    let prepared = scope
        .intern_forest_with_limits(&roots, TermScopeLimits::default())
        .unwrap();
    assert_eq!(prepared.terms, roots, "retain every original forest term");
    assert_eq!(
        scope.close(&prepared.terms[1]).unwrap_err(),
        original_error,
        "preparation must not capture escaped local 7"
    );
    assert!(
        scope
            .close_external_forest(&prepared.terms, &[], &[0; 3], TermScopeLimits::default())
            .0
            .is_err()
    );
    for index in [0, 2] {
        let original = scope.close(&roots[index]).unwrap();
        let actual = scope.close(&prepared.terms[index]).unwrap();
        assert_eq!(actual, original);
        TypeChecker::new(&environment)
            .check_type(&actual, &claim)
            .unwrap();
    }
}
