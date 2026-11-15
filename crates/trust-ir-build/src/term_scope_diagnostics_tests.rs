// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Structural diagnostics only; application diamonds need not be well-typed.

use super::*;
use clean_kernel::BinderInfo;

fn limits(visits: usize, depth: u32) -> TermScopeLimits {
    TermScopeLimits {
        max_visits: visits,
        max_depth: depth,
    }
}

fn census_is_consistent(report: &TermScopeCloseReport) {
    assert_eq!(
        report
            .diagnostics
            .input_kinds
            .iter()
            .map(|row| row.distinct_input_nodes)
            .sum::<usize>(),
        report.diagnostics.distinct_input_nodes,
    );
    assert!(report.diagnostics.distinct_input_nodes <= report.stats.visits);
    for row in &report.diagnostics.input_kinds {
        assert!(row.distinct_cached_hashes > 0);
        assert!(row.distinct_cached_hashes <= row.distinct_input_nodes);
    }
    assert!(
        report
            .diagnostics
            .input_kinds
            .windows(2)
            .all(|rows| rows[0].kind < rows[1].kind)
    );
}

fn kind_counts(report: &TermScopeCloseReport, kind: &str) -> (usize, usize) {
    let row = report
        .diagnostics
        .input_kinds
        .iter()
        .find(|row| row.kind == kind)
        .unwrap();
    (row.distinct_input_nodes, row.distinct_cached_hashes)
}

#[test]
fn diagnostics_keep_zero_and_partial_budget_errors_without_prewalking() {
    let scope = TermScope::new();
    let input = Expr::app(Expr::type_(), Expr::type_());
    for cap in [0, 1] {
        let report = scope.close_with_diagnostics(&input, limits(cap, 10));
        census_is_consistent(&report);
        assert_eq!(
            report.stats,
            scope.close_impl(&input, limits(cap, 10), false).stats
        );
        if cap == 0 {
            assert!(report.diagnostics.input_kinds.is_empty());
        } else {
            assert_eq!(report.diagnostics.input_kinds.len(), 1);
            assert_eq!(kind_counts(&report, "App"), (1, 1));
        }
        assert_eq!(report.result, Err(TermScopeError::VisitLimit));
        assert_eq!(
            report.result.err(),
            scope.close_with_limits(&input, limits(cap, 10)).err()
        );
        assert_eq!(report.stats.visits, cap);
        assert_eq!(report.stats.transformed_nodes, 0);
        assert_eq!(report.diagnostics.distinct_input_nodes, cap);
        assert_eq!(report.diagnostics.distinct_contexts, 1);
        assert_eq!(report.diagnostics.declaration_footprint_nodes, 0);
    }
    let report = scope.close_with_diagnostics(&input, limits(10, 0));
    census_is_consistent(&report);
    assert_eq!(
        report.stats,
        scope.close_impl(&input, limits(10, 0), false).stats
    );
    assert_eq!(kind_counts(&report, "App"), (1, 1));
    assert_eq!(report.diagnostics.input_kinds.len(), 1);
    assert_eq!(report.result, Err(TermScopeError::DepthLimit));
    assert_eq!(report.stats.visits, 1);
    assert_eq!(report.diagnostics.distinct_input_nodes, 1);
    assert!(
        scope.close(&input).is_ok(),
        "diagnosing does not mutate the scope"
    );
}

#[test]
fn diagnostics_count_shared_inputs_without_changing_success_or_legacy_stats() {
    let mut scope = TermScope::new();
    let id = FVarId::new(1);
    let mut shared = Arc::new(Expr::fvar(id));
    let mut expected = Expr::bvar(0);
    for _ in 0..8 {
        shared = Arc::new(Expr::app_arc(shared.clone(), shared));
        expected = Expr::app(expected.clone(), expected);
    }
    let input = scope.lam(id, BinderInfo::Default, Expr::type_(), (*shared).clone());
    let expected = Expr::lam(BinderInfo::Default, Expr::type_(), expected);
    let report = scope.close_with_diagnostics(&input, limits(100, 100));
    census_is_consistent(&report);
    let legacy = scope.close_with_limits(&input, limits(100, 100)).unwrap();
    assert_eq!(report.result, Ok(expected));
    assert_eq!(report.result.as_ref().unwrap(), &legacy.term);
    assert_eq!(report.stats, legacy.stats);
    assert_eq!(report.stats.visits, 19);
    assert_eq!(report.stats.transformed_nodes, 11);
    assert_eq!(report.stats.memo_hits, 8);
    assert_eq!(report.diagnostics.distinct_input_nodes, 11);
    assert_eq!(report.diagnostics.distinct_contexts, 2);
    assert_eq!(report.diagnostics.declaration_footprint_nodes, 1);
}

#[test]
fn diagnostics_distinguish_context_expansion_and_preserve_captured_indices() {
    let mut scope = TermScope::new();
    let x = FVarId::new(1);
    let y = FVarId::new(2);
    let shared = Arc::new(Expr::fvar(x));
    let pair = Expr::app_arc(shared.clone(), shared);
    let deeper = scope.lam(y, BinderInfo::Default, Expr::type_(), pair.clone());
    let body = Expr::app(pair, deeper);
    let input = scope.lam(x, BinderInfo::Default, Expr::type_(), body);
    let expected = Expr::lam(
        BinderInfo::Default,
        Expr::type_(),
        Expr::app(
            Expr::app(Expr::bvar(0), Expr::bvar(0)),
            Expr::lam(
                BinderInfo::Default,
                Expr::type_(),
                Expr::app(Expr::bvar(1), Expr::bvar(1)),
            ),
        ),
    );
    let report = scope.close_with_diagnostics(&input, limits(100, 100));
    census_is_consistent(&report);
    assert_eq!(report.result, Ok(expected));
    assert_eq!(report.diagnostics.distinct_contexts, 3);
    // The completed named output now shifts without transforming this input
    // again. Keep output work separate from the charged input census.
    assert_eq!(
        report.stats.transformed_nodes,
        report.diagnostics.distinct_input_nodes
    );
    assert_eq!(report.diagnostics.cache.uniform_shift_contextual_hits, 1);
    assert_eq!(report.diagnostics.cache.uniform_shift_output_visits, 1);
    assert_eq!(
        report.diagnostics.cache.uniform_shift_output_changed_nodes,
        1
    );
    assert!(report.stats.memo_hits >= 2);
    assert_eq!(
        report.stats,
        scope
            .close_with_limits(&input, limits(100, 100))
            .unwrap()
            .stats
    );
}

#[test]
fn diagnostics_still_count_input_context_expansion_when_original_loose_reads_require_reclosure() {
    let mut scope = TermScope::new();
    let x = FVarId::new(1);
    let y = FVarId::new(2);
    let shared = Arc::new(Expr::app(Expr::fvar(x), Expr::bvar(0)));
    assert!(shared.has_loose_bvars_quick());
    let pair = Expr::app_arc(shared.clone(), shared);
    let deeper = scope.lam(y, BinderInfo::Default, Expr::type_(), pair.clone());
    let body = Expr::app(pair, deeper);
    let input = scope.lam(x, BinderInfo::Default, Expr::type_(), body);
    let at = |depth| Expr::app(Expr::bvar(depth - 1), Expr::bvar(depth));
    let pair_at = |depth| Expr::app(at(depth), at(depth));
    let expected = Expr::lam(
        BinderInfo::Default,
        Expr::type_(),
        Expr::app(
            pair_at(1),
            Expr::lam(BinderInfo::Default, Expr::type_(), pair_at(2)),
        ),
    );
    let report = scope.close_with_diagnostics(&input, limits(100, 100));
    census_is_consistent(&report);
    assert_eq!(report.result, Ok(expected));
    assert_eq!(report.diagnostics.distinct_contexts, 3);
    assert!(report.stats.transformed_nodes > report.diagnostics.distinct_input_nodes);
    assert_eq!(
        report.stats,
        scope
            .close_with_limits(&input, limits(100, 100))
            .unwrap()
            .stats
    );
}

#[test]
fn diagnostics_retain_charged_declaration_probe_work_on_failure() {
    let mut scope = TermScope::new();
    let helper = Arc::new(scope.lam(
        FVarId::new(1),
        BinderInfo::Default,
        Expr::type_(),
        Expr::fvar(FVarId::new(1)),
    ));
    let reused = scope.lam(
        FVarId::new(2),
        BinderInfo::Default,
        Expr::type_(),
        Expr::app_arc(helper.clone(), helper.clone()),
    );
    let input = Expr::app_arc(helper, Arc::new(reused));
    let complete = scope.close_with_diagnostics(&input, limits(100, 100));
    census_is_consistent(&complete);
    assert!(complete.result.is_ok());
    assert!(complete.stats.scope_check_visits > 0);
    assert!(complete.diagnostics.declaration_footprint_nodes > 0);
    assert!(complete.stats.closed_memo_hits > 0);
    let mut observed_charged_failure = false;
    for cap in 0..complete.stats.visits {
        let report = scope.close_with_diagnostics(&input, limits(cap, 100));
        census_is_consistent(&report);
        assert_eq!(
            report.stats,
            scope.close_impl(&input, limits(cap, 100), false).stats
        );
        assert_eq!(report.result, Err(TermScopeError::VisitLimit));
        assert_eq!(report.stats.visits, cap);
        assert_eq!(
            report.result.err(),
            scope.close_with_limits(&input, limits(cap, 100)).err()
        );
        assert!(report.diagnostics.distinct_input_nodes <= report.stats.visits);
        observed_charged_failure |= report.stats.scope_check_visits > 0;
    }
    assert!(observed_charged_failure);
}

#[test]
fn diagnostics_do_not_change_shadow_escape_or_bvar_refusals() {
    let mut scope = TermScope::new();
    let id = FVarId::new(1);
    let bound = scope.lam(id, BinderInfo::Default, Expr::type_(), Expr::fvar(id));
    let shadow = scope.lam(id, BinderInfo::Default, Expr::type_(), bound);
    let escaped = Expr::fvar(id);
    let overflow = scope.lam(
        FVarId::new(2),
        BinderInfo::Default,
        Expr::type_(),
        Expr::bvar(Expr::MAX_BVAR_INDEX),
    );
    for (input, error) in [
        (shadow, TermScopeError::ShadowedLocal(id)),
        (escaped, TermScopeError::OutOfScope(id)),
        (overflow, TermScopeError::IndexOverflow),
    ] {
        let report = scope.close_with_diagnostics(&input, limits(100, 100));
        census_is_consistent(&report);
        assert_eq!(
            report.stats,
            scope.close_impl(&input, limits(100, 100), false).stats
        );
        assert_eq!(report.result, Err(error));
        assert_eq!(report.result.err(), scope.close(&input).err());
        assert!(report.stats.visits > 0);
        assert!(report.diagnostics.distinct_input_nodes > 0);
    }
}

#[test]
fn diagnostics_distinguish_equal_compound_copies_from_shared_arcs() {
    let scope = TermScope::new();
    let compound = || Expr::app(Expr::const_str("Nat.succ"), Expr::nat_lit(0u64));
    let copies = Expr::app(compound(), compound());
    let child = Arc::new(compound());
    let shared = Expr::app_arc(child.clone(), child);
    assert_eq!(copies, shared);
    let copies_report = scope.close_with_diagnostics(&copies, limits(100, 100));
    let shared_report = scope.close_with_diagnostics(&shared, limits(100, 100));
    for (input, report) in [(&copies, &copies_report), (&shared, &shared_report)] {
        census_is_consistent(report);
        let legacy = scope.close_with_limits(input, limits(100, 100)).unwrap();
        assert_eq!(report.result.as_ref().unwrap(), &legacy.term);
        assert_eq!(report.stats, legacy.stats);
        assert!(
            scope
                .close_impl(input, limits(100, 100), false)
                .diagnostics
                .input_kinds
                .is_empty()
        );
    }
    assert_eq!(copies_report.result, shared_report.result);
    assert_eq!(kind_counts(&copies_report, "App").0, 3);
    assert_eq!(kind_counts(&shared_report, "App").0, 2);
    // We know these fixture expressions are equal independently of the hash.
    // Do not assume unequal expressions have different cached hashes.
    assert_eq!(
        kind_counts(&copies_report, "App").1,
        kind_counts(&shared_report, "App").1
    );
    assert_eq!(kind_counts(&copies_report, "Const"), (2, 1));
    assert_eq!(kind_counts(&shared_report, "Const"), (1, 1));
    assert_eq!(kind_counts(&copies_report, "Lit"), (2, 1));
    assert_eq!(kind_counts(&shared_report, "Lit"), (1, 1));
}

#[test]
fn diagnostics_classify_named_and_ordinary_lam_pi_and_let_by_registry() {
    let mut scope = TermScope::new();
    let ordinary = [
        Expr::lam(BinderInfo::Default, Expr::type_(), Expr::type_()),
        Expr::pi(BinderInfo::Default, Expr::type_(), Expr::type_()),
        Expr::let_named(
            Name::anon(),
            Expr::type_(),
            Expr::type_(),
            Expr::type_(),
            false,
        ),
    ];
    let named = [
        scope.lam(
            FVarId::new(1),
            BinderInfo::Default,
            Expr::type_(),
            Expr::type_(),
        ),
        scope.pi(
            FVarId::new(2),
            BinderInfo::Default,
            Expr::type_(),
            Expr::type_(),
        ),
        scope.let_named(
            FVarId::new(3),
            Name::anon(),
            Expr::type_(),
            Expr::type_(),
            Expr::type_(),
            false,
        ),
    ];
    for (plain, deferred) in ordinary.iter().zip(&named) {
        assert_eq!(plain, deferred);
        assert_eq!(plain.hash_cached(), deferred.hash_cached());
    }
    let input = Expr::apps(
        Expr::const_str("fixture"),
        ordinary.into_iter().chain(named),
    );
    let report = scope.close_with_diagnostics(&input, limits(100, 100));
    census_is_consistent(&report);
    for kind in [
        "Lam.named",
        "Lam.ordinary",
        "Pi.named",
        "Pi.ordinary",
        "Let.named",
        "Let.ordinary",
    ] {
        assert_eq!(kind_counts(&report, kind), (1, 1));
    }
    let legacy = scope.close_with_limits(&input, limits(100, 100)).unwrap();
    assert_eq!(report.result, Ok(legacy.term));
    assert_eq!(report.stats, legacy.stats);
}

#[test]
fn diagnostics_equal_binder_hashes_do_not_admit_escaped_registered_locals() {
    let mut scope = TermScope::new();
    let id = FVarId::new(1);
    let named = scope.lam(id, BinderInfo::Default, Expr::type_(), Expr::fvar(id));
    let ordinary = Expr::lam(BinderInfo::Default, Expr::type_(), Expr::fvar(id));
    assert_eq!(named, ordinary);
    assert_eq!(named.hash_cached(), ordinary.hash_cached());
    assert!(scope.close(&named).is_ok());
    assert_eq!(scope.close(&ordinary), Err(TermScopeError::OutOfScope(id)));
    let input = Expr::app(named, ordinary);
    let report = scope.close_with_diagnostics(&input, limits(100, 100));
    let legacy = scope.close_impl(&input, limits(100, 100), false);
    census_is_consistent(&report);
    assert_eq!(report.result, Err(TermScopeError::OutOfScope(id)));
    assert_eq!(report.result, legacy.result);
    assert_eq!(report.stats, legacy.stats);
    assert_eq!(kind_counts(&report, "Lam.named"), (1, 1));
    assert_eq!(kind_counts(&report, "Lam.ordinary"), (1, 1));
}

#[test]
fn external_forest_diagnostics_preserve_the_visit_limit() {
    let scope = TermScope::new();
    let roots = [Expr::type_(), Expr::type_()];
    let limits = limits(1, 64);
    let (normal, normal_stats) = scope.close_external_forest(&roots, &[], &[0, 0], limits);
    let (observed, observed_stats, diagnostics) =
        scope.close_external_forest_with_diagnostics(&roots, &[], &[0, 0], limits);
    assert!(matches!(normal, Err(TermScopeError::VisitLimit)));
    assert!(matches!(observed, Err(TermScopeError::VisitLimit)));
    assert_eq!(normal_stats.visits, observed_stats.visits);
    assert_eq!(normal_stats.completed_roots, observed_stats.completed_roots);
    assert_eq!(observed_stats.completed_roots, 1);
    assert!(diagnostics.first_stop.is_some());
}
