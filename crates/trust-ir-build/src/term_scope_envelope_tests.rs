// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Exact-output and refusal controls for conservative declaration envelopes.
//! Only the explicit Nat/let fixture is kernel-typed; the application fixtures
//! test structural closure, not kernel inhabitation or proof authority.

use super::*;
use clean_kernel::{BinderInfo, Environment, TypeChecker};

fn id(value: u64) -> FVarId {
    FVarId::new(value)
}

fn natural() -> Expr {
    Expr::const_str("Nat")
}

fn lam(body: Expr) -> Expr {
    Expr::lam(BinderInfo::Default, natural(), body)
}

// Build a closed helper with all IDs declared (including unused declarations)
// and an independent ordinary-binder oracle. The innermost variable is used.
fn helper(scope: &mut TermScope, ids: &[u64]) -> (Arc<Expr>, Expr) {
    let mut open = Expr::fvar(id(*ids.last().expect("nonempty helper")));
    let mut expected = Expr::bvar(0);
    for &local in ids.iter().rev() {
        open = scope.lam(id(local), BinderInfo::Default, natural(), open);
        expected = lam(expected);
    }
    (Arc::new(open), expected)
}

// The shared helper remains an actual Arc child, not a fresh clone of its root.
fn applied(shared: &Arc<Expr>) -> Expr {
    Expr::app_arc(Arc::new(Expr::nat_lit(0u64)), shared.clone())
}

fn expected_application(helper: Expr) -> Expr {
    Expr::app(Expr::nat_lit(0u64), helper)
}

#[test]
fn disjoint_helper_footprints_cost_one_probe_per_reuse_not_one_per_declaration() {
    for size in [4usize, 32, 64] {
        let count = size;
        let mut scope = TermScope::new();
        let ids = (1000..1000 + size as u64).collect::<Vec<_>>();
        let (shared, expected_helper) = helper(&mut scope, &ids);
        let mut helper_type = natural();
        for _ in 0..size {
            helper_type = Expr::arrow(natural(), helper_type);
        }
        let mut input = Expr::nat_lit(7u64);
        let mut expected = input.clone();
        for index in (0..count).rev() {
            // All currently active named IDs lie below 1000. A whole helper
            // footprint is disjoint even as its declaration count grows.
            input = scope.let_named(
                id(index as u64),
                Name::anon(),
                helper_type.clone(),
                Expr::app_arc(
                    Arc::new(Expr::lam(
                        BinderInfo::Default,
                        helper_type.clone(),
                        Expr::bvar(0),
                    )),
                    shared.clone(),
                ),
                input,
                false,
            );
            expected = Expr::let_named(
                Name::anon(),
                helper_type.clone(),
                Expr::app(
                    Expr::lam(BinderInfo::Default, helper_type.clone(), Expr::bvar(0)),
                    expected_helper.clone(),
                ),
                expected,
                false,
            );
        }
        let closed = scope
            .close_with_limits(
                &input,
                TermScopeLimits {
                    max_visits: 24 * (size + count) + 100,
                    ..TermScopeLimits::default()
                },
            )
            .expect("helper declaration count times reuse count is not traversal work");
        assert_eq!(closed.term, expected);
        assert_eq!(closed.stats.scope_check_visits, count - 1);
        assert!(closed.stats.closed_memo_hits >= count - 1);
        assert!(!closed.term.has_fvar_quick());
        assert!(!closed.term.has_loose_bvars_quick());
        if size == 4 {
            let mut env = Environment::new();
            env.init_nat().unwrap();
            TypeChecker::new(&env)
                .check_type(&closed.term, &natural())
                .unwrap();
        }
    }
}

#[test]
fn overlapping_envelopes_with_a_membership_gap_use_exact_children_and_accept() {
    let mut scope = TermScope::new();
    let (shared, expected_helper) = helper(&mut scope, &[10, 30]);
    let under = scope.lam(id(20), BinderInfo::Default, natural(), applied(&shared));
    let input = Expr::app_arc(shared, Arc::new(under));
    let closed = scope
        .close_with_limits(&input, TermScopeLimits::default())
        .unwrap();
    assert_eq!(
        closed.term,
        Expr::app(
            expected_helper.clone(),
            lam(expected_application(expected_helper)),
        )
    );
    // [10,30] overlaps [20,20]. Probe the Join and both exact Local leaves;
    // overlap cannot be mistaken either for disjointness or for an actual clash.
    assert_eq!(closed.stats.scope_check_visits, 3);
}

#[test]
fn envelope_equality_and_interior_collisions_keep_the_original_shadow_refusal() {
    for declarations in [vec![10u64, 20, 30], vec![0, u64::MAX]] {
        let mut scope = TermScope::new();
        let (shared, _) = helper(&mut scope, &declarations);
        for &conflict in &declarations {
            for ordinary in [false, true] {
                let body = if ordinary {
                    lam(applied(&shared))
                } else {
                    applied(&shared)
                };
                let under = scope.lam(id(conflict), BinderInfo::Default, natural(), body);
                let input = Expr::app_arc(shared.clone(), Arc::new(under));
                let error = TermScopeError::ShadowedLocal(id(conflict));
                assert_eq!(scope.close(&input).err(), Some(error.clone()));
                assert_eq!(
                    scope
                        .close_with_diagnostics(&input, TermScopeLimits::default())
                        .result,
                    Err(error)
                );
            }
        }
    }
}

#[test]
fn envelope_probe_cannot_reorder_an_earlier_bad_type_or_let_value() {
    for in_value in [false, true] {
        let mut scope = TermScope::new();
        let (shared, _) = helper(&mut scope, &[10, 30]);
        let bad = if in_value {
            scope.let_named(
                id(40),
                Name::anon(),
                natural(),
                Expr::fvar(id(40)),
                applied(&shared),
                false,
            )
        } else {
            scope.lam(
                id(40),
                BinderInfo::Default,
                Expr::fvar(id(40)),
                applied(&shared),
            )
        };
        let shadowing = scope.lam(id(10), BinderInfo::Default, natural(), bad);
        let input = Expr::app_arc(shared, Arc::new(shadowing));
        let error = TermScopeError::OutOfScope(id(40));
        assert_eq!(scope.close(&input).err(), Some(error.clone()));
        assert_eq!(
            scope
                .close_with_diagnostics(&input, TermScopeLimits::default())
                .result,
            Err(error)
        );
    }
}

#[test]
fn active_envelope_is_restored_across_nonmonotone_named_and_ordinary_binders() {
    let mut scope = TermScope::new();
    let (shared, expected_helper) = helper(&mut scope, &[150, 160]);
    let highest = scope.lam(
        id(u64::MAX),
        BinderInfo::Default,
        natural(),
        lam(applied(&shared)),
    );
    let lowest = scope.lam(id(0), BinderInfo::Default, natural(), highest);
    let body = Expr::app(lowest, lam(applied(&shared)));
    let root = scope.lam(id(100), BinderInfo::Default, natural(), body);
    let input = Expr::app_arc(shared.clone(), Arc::new(Expr::app(root, (*shared).clone())));
    let expected = Expr::app(
        expected_helper.clone(),
        Expr::app(
            lam(Expr::app(
                lam(lam(lam(expected_application(expected_helper.clone())))),
                lam(expected_application(expected_helper.clone())),
            )),
            expected_helper,
        ),
    );
    let closed = scope
        .close_with_limits(&input, TermScopeLimits::default())
        .unwrap();
    assert_eq!(closed.term, expected);
    // The first reuse sees [0,MAX], requiring Join+two Local probes. After
    // popping MAX then 0, only ID100 remains and the second reuse costs one.
    // Ordinary binders must neither reset nor widen this named-ID envelope.
    assert_eq!(closed.stats.scope_check_visits, 4);
}

#[test]
fn disjoint_probe_is_still_charged_and_diagnostics_preserve_every_budget_result() {
    let mut scope = TermScope::new();
    let (shared, expected_helper) = helper(&mut scope, &[10, 11]);
    let under = scope.lam(id(1), BinderInfo::Default, natural(), applied(&shared));
    let input = Expr::app_arc(shared, Arc::new(under));
    let expected = Expr::app(
        expected_helper.clone(),
        lam(expected_application(expected_helper)),
    );
    let complete = scope.close_with_diagnostics(&input, TermScopeLimits::default());
    assert_eq!(complete.result, Ok(expected));
    assert_eq!(complete.stats.scope_check_visits, 1);
    for cap in 0..=complete.stats.visits {
        let limits = TermScopeLimits {
            max_visits: cap,
            ..TermScopeLimits::default()
        };
        let report = scope.close_with_diagnostics(&input, limits);
        let ordinary = scope.close_with_limits(&input, limits);
        if cap < complete.stats.visits {
            assert_eq!(report.result, Err(TermScopeError::VisitLimit));
            assert_eq!(ordinary.err(), Some(TermScopeError::VisitLimit));
            assert_eq!(report.stats.visits, cap);
        } else {
            let ordinary = ordinary.unwrap();
            assert_eq!(report.result.as_ref().unwrap(), &ordinary.term);
            assert_eq!(report.stats, ordinary.stats);
            assert_eq!(report.stats.scope_check_visits, 1);
        }
    }
    // The final operation is the disjoint-footprint probe, not another Expr.
    let just_short = scope.close_with_diagnostics(
        &input,
        TermScopeLimits {
            max_visits: complete.stats.visits - 1,
            ..TermScopeLimits::default()
        },
    );
    assert_eq!(just_short.result, Err(TermScopeError::VisitLimit));
    assert_eq!(just_short.stats.scope_check_visits, 0);
}

#[test]
fn conservative_envelope_union_handles_gaps_adjacency_and_extreme_ids() {
    let zero = IdEnvelope::singleton(id(0));
    let maximum = IdEnvelope::singleton(id(u64::MAX));
    let all = maximum.union(zero);
    assert_eq!(all.min, id(0));
    assert_eq!(all.max, id(u64::MAX));
    for endpoint in [zero, maximum, IdEnvelope::singleton(id(1))] {
        assert!(!all.is_disjoint(endpoint));
        assert!(!endpoint.is_disjoint(all));
    }
    let left = IdEnvelope::singleton(id(10)).union(IdEnvelope::singleton(id(20)));
    let adjacent = IdEnvelope::singleton(id(21));
    assert!(left.is_disjoint(adjacent));
    assert!(adjacent.is_disjoint(left));
    assert!(!left.is_disjoint(IdEnvelope::singleton(id(10))));
    assert!(!left.is_disjoint(IdEnvelope::singleton(id(20))));
    assert!(!left.is_disjoint(IdEnvelope::singleton(id(15))));
}
