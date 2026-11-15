// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

#[test]
fn local_diagnostics_retain_partial_stats_and_exact_budget_error() {
    let mut scope = LocalScope::new();
    let a = scope.try_local(Expr::type_()).unwrap();
    let x = scope.try_local(a.term().clone()).unwrap();
    let input = a.lam(x.lam(x.term().clone()));
    for (visits, depth, error) in [
        (0, 100, TermScopeError::VisitLimit),
        (1, 100, TermScopeError::VisitLimit),
        (100, 1, TermScopeError::DepthLimit),
    ] {
        let limits = TermScopeLimits {
            max_visits: visits,
            max_depth: depth,
        };
        let report = scope.close_with_diagnostics(&input, limits);
        assert_eq!(report.result, Err(LocalScopeError::Closure(error)));
        assert_eq!(
            report.result.err(),
            scope.close_with_limits(&input, limits).err()
        );
        assert!(report.stats.visits <= visits);
        assert!(report.diagnostics.distinct_input_nodes <= report.stats.visits);
        if visits == 1 {
            assert_eq!(report.stats.visits, 1);
            assert_eq!(report.diagnostics.distinct_input_nodes, 1);
        }
    }
    let report = scope.close_with_diagnostics(&input, TermScopeLimits::default());
    let legacy = scope
        .close_with_limits(&input, TermScopeLimits::default())
        .unwrap();
    assert_eq!(report.result.as_ref().unwrap(), &legacy.term);
    assert_eq!(report.stats, legacy.stats);
    let expected = Expr::lam(
        BinderInfo::Default,
        Expr::type_(),
        Expr::lam(BinderInfo::Default, Expr::bvar(0), Expr::bvar(0)),
    );
    assert_eq!(report.result, Ok(expected));
    assert_eq!(scope.allocated(), 2);
}

#[test]
fn local_diagnostics_keep_final_free_variable_and_scope_errors_distinct() {
    let mut scope = LocalScope::new();
    let x = scope.try_local(Expr::type_()).unwrap();
    // Allocation alone does not register a deferred binder with TermScope.
    let free = scope.close_with_diagnostics(x.term(), TermScopeLimits::default());
    assert_eq!(free.result, Err(LocalScopeError::UnboundFreeVariable));
    assert_eq!(free.stats.visits, 1);
    assert_eq!(free.stats.transformed_nodes, 1);
    assert_eq!(free.diagnostics.distinct_input_nodes, 1);

    let bound = x.lam(x.term().clone());
    let escaped = Expr::app(bound, x.term().clone());
    let shadow = x.lam(x.lam(x.term().clone()));
    for (input, error) in [
        (escaped, TermScopeError::OutOfScope(x.id())),
        (shadow, TermScopeError::ShadowedLocal(x.id())),
    ] {
        let report = scope.close_with_diagnostics(&input, TermScopeLimits::default());
        assert_eq!(report.result, Err(LocalScopeError::Closure(error)));
        assert_eq!(report.result.err(), scope.close(&input).err());
        assert!(report.stats.visits > 0);
        assert!(report.diagnostics.distinct_contexts > 1);
    }
}
