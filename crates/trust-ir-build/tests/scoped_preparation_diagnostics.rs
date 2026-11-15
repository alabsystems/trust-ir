// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

use clean_kernel::{BinderInfo, Environment, Expr, expr::FVarId};
use std::sync::Arc;
use trust_ir_build::{
    proof_assembly::ProofLimits,
    proof_components::ProofComponents,
    scoped_local::LocalScope,
    term_scope::{
        TermScope, TermScopeError, TermScopeInternPhase, TermScopeInternStats, TermScopeLimits,
        observed_work,
    },
};

#[test]
fn empty_zero_and_exact_forest_budgets_keep_the_original_refusal_order() {
    let mut scope = TermScope::new();
    let zero = TermScopeLimits {
        max_visits: 0,
        max_depth: 0,
    };
    let empty = scope.intern_forest_with_diagnostics(&[], zero).unwrap();
    assert!(empty.terms.is_empty());
    assert_eq!(empty.stats, TermScopeInternStats::default());
    let roots = [Expr::type_(), Expr::type_()];
    for (limits, error, visits) in [
        (zero, TermScopeError::VisitLimit, 0),
        (
            TermScopeLimits {
                max_visits: 1,
                max_depth: 0,
            },
            TermScopeError::DepthLimit,
            1,
        ),
    ] {
        let failure = scope
            .intern_forest_with_diagnostics(&roots, limits)
            .err()
            .unwrap();
        assert_eq!(failure.error, error);
        assert_eq!(failure.stats.visits, visits);
        assert_eq!(failure.stats.examined, 0);
        assert_eq!(failure.completed_roots, 0);
        assert_eq!(failure.phase, TermScopeInternPhase::Node);
        assert_eq!(failure.walk_depth, 0);
        assert_eq!(
            scope.intern_forest_with_limits(&roots, limits).err(),
            Some(error)
        );
    }
    let limits = TermScopeLimits {
        max_visits: 1,
        max_depth: 1,
    };
    let failure = scope
        .intern_forest_with_diagnostics(&roots, limits)
        .err()
        .unwrap();
    assert_eq!(failure.error, TermScopeError::VisitLimit);
    assert_eq!(failure.completed_roots, 1);
    assert_eq!(failure.stats.visits, 1);
    assert_eq!(failure.stats.examined, 1);
    assert_eq!(failure.stats.canonical, 1);
    let exact = TermScopeLimits {
        max_visits: 2,
        ..limits
    };
    let diagnosed = scope.intern_forest_with_diagnostics(&roots, exact).unwrap();
    let ordinary = scope.intern_forest_with_limits(&roots, exact).unwrap();
    assert_eq!(diagnosed.terms, roots);
    assert_eq!(diagnosed.terms, ordinary.terms);
    assert_eq!(diagnosed.stats, ordinary.stats);
    assert_eq!(diagnosed.stats.visits, 2);
    assert_eq!(diagnosed.stats.canonical, 1);
}

#[test]
fn registered_body_failure_retains_only_the_charged_prefix() {
    let mut scope = TermScope::new();
    let id = FVarId::new(7);
    let input = scope.lam(id, BinderInfo::Default, Expr::type_(), Expr::fvar(id));
    let closed = scope.close(&input).unwrap();
    let limits = TermScopeLimits {
        max_visits: 2,
        max_depth: 100,
    };
    let before = observed_work();
    let failure = scope
        .intern_forest_with_diagnostics(std::slice::from_ref(&input), limits)
        .err()
        .unwrap();
    let after = observed_work();
    assert_eq!(after.interning_calls - before.interning_calls, 1);
    assert_eq!(after.interning_visits - before.interning_visits, 2);
    assert_eq!(failure.error, TermScopeError::VisitLimit);
    assert_eq!(failure.phase, TermScopeInternPhase::RegisteredBody);
    assert_eq!(failure.walk_depth, 1);
    assert_eq!(failure.completed_roots, 0);
    assert_eq!(failure.stats.visits, 2);
    assert_eq!(failure.stats.examined, 2);
    assert_eq!(failure.stats.canonical, 1);
    assert_eq!(scope.close(&input).unwrap(), closed);
}

#[test]
fn registered_body_depth_failure_keeps_its_phase_after_unwinding() {
    let mut scope = TermScope::new();
    let id = FVarId::new(9);
    let named = scope.lam(id, BinderInfo::Default, Expr::type_(), Expr::fvar(id));
    let clean_kernel::ExprKind::Lam(_, ty, _) = named.kind() else {
        panic!("expected named lambda");
    };
    let ty = ty.clone();
    // First cache the exact type allocation. Its memo hit below the later
    // lambda passes at the depth cap; the registered body then refuses there.
    let roots = [
        Expr::app_arc(ty.clone(), ty.clone()),
        Expr::app_arc(ty, Arc::new(named)),
    ];
    let limits = TermScopeLimits {
        max_visits: 100,
        max_depth: 2,
    };
    let failure = scope
        .intern_forest_with_diagnostics(&roots, limits)
        .err()
        .unwrap();
    assert_eq!(failure.error, TermScopeError::DepthLimit);
    assert_eq!(failure.phase, TermScopeInternPhase::RegisteredBody);
    assert_eq!(failure.walk_depth, 2);
    assert_eq!(failure.completed_roots, 1);
    assert_eq!(failure.stats.visits, 8);
    assert_eq!(failure.stats.examined, 4);
    assert_eq!(failure.stats.max_depth, 2);
    assert_eq!(
        scope.intern_forest_with_limits(&roots, limits).err(),
        Some(failure.error)
    );
}

#[test]
fn later_root_refusal_keeps_original_binders_after_partial_reregistration() {
    let mut scope = TermScope::new();
    let input = scope.lam(
        FVarId::new(8),
        BinderInfo::Default,
        Expr::type_(),
        Expr::app(Expr::type_(), Expr::type_()),
    );
    let closed = scope.close(&input).unwrap();
    let failure = scope
        .intern_forest_with_diagnostics(
            &[input.clone(), Expr::type_()],
            TermScopeLimits {
                max_visits: 5,
                max_depth: 100,
            },
        )
        .err()
        .unwrap();
    assert_eq!(failure.error, TermScopeError::VisitLimit);
    assert_eq!(failure.completed_roots, 1);
    assert_eq!(failure.stats.visits, 5);
    assert_eq!(failure.stats.rebound, 1);
    assert_eq!(failure.phase, TermScopeInternPhase::Node);
    assert_eq!(failure.walk_depth, 0);
    assert_eq!(scope.close(&input).unwrap(), closed);
}

#[test]
fn diagnostics_preserve_memo_before_depth_and_every_visit_prefix() {
    // The leaf is first examined at depth two, then hit below the right App
    // at depth three. Memo hits must still precede the depth-limit check.
    let leaf = Arc::new(Expr::type_());
    let input = Expr::app_arc(leaf.clone(), Arc::new(Expr::app_arc(leaf.clone(), leaf)));
    for depth in 0..=3 {
        for visits in 0..=6 {
            let limits = TermScopeLimits {
                max_visits: visits,
                max_depth: depth,
            };
            let mut scope = TermScope::new();
            let before = observed_work();
            let ordinary = scope.intern_forest_with_limits(std::slice::from_ref(&input), limits);
            let middle = observed_work();
            let diagnosed =
                scope.intern_forest_with_diagnostics(std::slice::from_ref(&input), limits);
            let after = observed_work();
            let charged = after.interning_visits - middle.interning_visits;
            assert_eq!(middle.interning_visits - before.interning_visits, charged);
            assert_eq!(after.interning_calls - before.interning_calls, 2);
            match (ordinary, diagnosed) {
                (Ok(ordinary), Ok(diagnosed)) => {
                    assert_eq!(ordinary.terms, diagnosed.terms);
                    assert_eq!(ordinary.stats, diagnosed.stats);
                    assert_eq!(diagnosed.stats.visits as u64, charged);
                    assert_eq!(diagnosed.stats.visits, 5);
                    assert_eq!(diagnosed.stats.max_depth, 2);
                }
                (Err(error), Err(failure)) => {
                    assert_eq!(error, failure.error);
                    assert_eq!(failure.stats.visits as u64, charged);
                    assert_eq!(failure.completed_roots, 0);
                }
                _ => panic!("diagnostics changed the verdict at visits={visits}, depth={depth}"),
            }
        }
    }
}

fn scoped_true(
    observe: bool,
    visits: usize,
) -> Result<trust_ir_build::proof_components::ScopedProofComponentBundle, String> {
    let scope = LocalScope::new();
    let mut plan = ProofComponents::new("OrdinaryTrue", ProofLimits::default());
    plan.set_base(&scope, vec![]).unwrap();
    let limits = TermScopeLimits {
        max_visits: visits,
        max_depth: 100,
    };
    if observe {
        plan.close_scoped_with_diagnostics(
            &scope,
            Expr::const_str("True.intro"),
            Expr::const_str("True"),
            limits,
        )
    } else {
        plan.close_scoped(
            &scope,
            Expr::const_str("True.intro"),
            Expr::const_str("True"),
            limits,
        )
    }
}

#[test]
fn ordinary_scoped_caller_labels_preparation_failure_and_retains_legacy_output() {
    let ordinary = scoped_true(false, 1).err().unwrap();
    assert_eq!(ordinary, TermScopeError::VisitLimit.to_string());
    let diagnostic = scoped_true(true, 1).err().unwrap();
    assert!(diagnostic.contains("complete open goal"), "{diagnostic}");
    assert!(diagnostic.contains("completed_roots: 1"), "{diagnostic}");
    assert!(diagnostic.contains("visits: 1"), "{diagnostic}");
    assert!(diagnostic.contains("phase: Node"), "{diagnostic}");
    assert!(diagnostic.ends_with(&ordinary), "{diagnostic}");
}

#[test]
fn ordinary_scoped_diagnostics_preserve_complete_encoding_and_strict_replay() {
    let ordinary = scoped_true(false, 2).unwrap();
    let diagnosed = scoped_true(true, 2).unwrap();
    let claim = Expr::const_str("True");
    assert_eq!(
        ordinary.encode_with_claim(&claim).unwrap(),
        diagnosed.encode_with_claim(&claim).unwrap()
    );
    assert_eq!(
        ordinary.work.unwrap().preparation,
        diagnosed.work.unwrap().preparation
    );
    assert_eq!(
        ordinary.work.unwrap().closing,
        diagnosed.work.unwrap().closing
    );
    let mut environment = Environment::new();
    environment.init_true_false().unwrap();
    ordinary.replay(&environment, &claim, 10_000).unwrap();
    diagnosed.replay(&environment, &claim, 10_000).unwrap();
    let mut corrupt = diagnosed;
    corrupt.root = Expr::const_str("False.elim");
    assert!(corrupt.replay(&environment, &claim, 10_000).is_err());
}
