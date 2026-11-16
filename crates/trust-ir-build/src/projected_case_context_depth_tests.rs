// Copyright 2026 Andrew Yates | Licensed under the Apache License, Version 2.0
//! Reusing cold data cannot bypass the original traversal depth boundary.
use super::*;
fn data() -> Expr {
    (0..32).fold(Expr::nat_lit(0), |value, _| {
        Expr::app(Expr::const_str("Nat.succ"), value)
    })
}
fn search_at(
    checker: &TypeChecker<'_>,
    scope: &crate::scoped_local::LocalScope,
    source: &Expr,
    cache: &mut CaseSupportCache,
    depth: usize,
) -> Result<(), String> {
    let mut work = 0;
    let mut hits = 0;
    let mut support_visits = 0;
    let mut search = Search {
        checker,
        work: &mut work,
        limit: 100_000,
        depth,
        max_depth: 64,
        first: false,
        seen: HashSet::new(),
        found: None,
        error: None,
        scope,
        support: cache,
        support_limit: 1024,
        support_visits: &mut support_visits,
        support_hits: &mut hits,
        visits: 0,
    };
    search.fold_expr_opt(source);
    assert!(search.found.is_none());
    search.error.map_or(Ok(()), |error| Err(error.into()))
}
fn replace_at(
    checker: &TypeChecker<'_>,
    scope: &crate::scoped_local::LocalScope,
    source: &Expr,
    cache: &mut CaseSupportCache,
    depth: usize,
) -> Result<(), String> {
    let target = Expr::const_str("Unit.unit");
    let hole = Expr::nat_lit(0);
    let proper = HashSet::new();
    let mut work = 0;
    let mut hits = 0;
    let mut support_visits = 0;
    let mut materialized_cache = crate::scoped_local::materialized::MaterializedCache::default();
    let mut comparison_visits = 0;
    let mut comparisons = 0;
    let mut comparison_matches = 0;
    let mut reduction_visits = 0;
    let mut reductions = 0;
    let mut replace = Replace {
        checker,
        target: &target,
        proper: &proper,
        hole: &hole,
        work: &mut work,
        limit: 100_000,
        depth,
        max_depth: 64,
        memo: HashMap::new(),
        changed: false,
        error: None,
        scope,
        support: cache,
        support_limit: 1024,
        support_visits: &mut support_visits,
        support_hits: &mut hits,
        visits: 0,
        allowed: &[],
        materialized_cache: &mut materialized_cache,
        validation_context: None,
        validation_mode: MaterializedValidationMode::PerReplace,
        comparison_visits: &mut comparison_visits,
        comparisons: &mut comparisons,
        comparison_matches: &mut comparison_matches,
        reduction_visits: &mut reduction_visits,
        reductions: &mut reductions,
    };
    replace.fold_expr_opt(source);
    replace.error.map_or(Ok(()), |error| Err(error.into()))
}
#[test]
fn cached_data_keeps_search_depth_refusal() {
    let mut env = Environment::new();
    env.init_nat().unwrap();
    let checker = TypeChecker::new(&env);
    let scope = crate::scoped_local::LocalScope::new();
    let source = data();
    let mut cache = CaseSupportCache::default();
    search_at(&checker, &scope, &source, &mut cache, 0).unwrap();
    let cold = search_at(
        &checker,
        &scope,
        &source,
        &mut CaseSupportCache::default(),
        40,
    )
    .unwrap_err();
    let warm = search_at(&checker, &scope, &source, &mut cache, 40).unwrap_err();
    assert_eq!(cold, "projected case-context search depth limit");
    assert_eq!(warm, cold);
}
#[test]
fn cached_data_keeps_replacement_depth_refusal() {
    let mut env = Environment::new();
    env.init_nat().unwrap();
    let checker = TypeChecker::new(&env);
    let scope = crate::scoped_local::LocalScope::new();
    let source = data();
    let mut cache = CaseSupportCache::default();
    search_at(&checker, &scope, &source, &mut cache, 0).unwrap();
    let cold = replace_at(
        &checker,
        &scope,
        &source,
        &mut CaseSupportCache::default(),
        40,
    )
    .unwrap_err();
    let warm = replace_at(&checker, &scope, &source, &mut cache, 40).unwrap_err();
    assert_eq!(cold, "projected case-context replacement depth limit");
    assert_eq!(warm, cold);
}
#[test]
fn unread_lambda_body_is_not_a_replacement_absence_hint() {
    let mut env = Environment::new();
    env.init_nat().unwrap();
    let checker = TypeChecker::new(&env);
    let scope = crate::scoped_local::LocalScope::new();
    let source = Expr::lam(
        clean_kernel::BinderInfo::Default,
        Expr::const_str("Nat"),
        data(),
    );
    let mut cache = CaseSupportCache::default();
    search_at(&checker, &scope, &source, &mut cache, 0).unwrap();
    let mut support_work = 0;
    let mut support_visits = 0;
    let summary = cache
        .summary(
            &checker,
            &scope,
            &source,
            &mut support_work,
            100_000,
            64,
            1024,
            &mut support_visits,
        )
        .unwrap()
        .expect("ordinary lambda support is indexed before replacement");
    assert!(support_visits > 0);
    assert!(summary.search_height < summary.replacement_height);
    let cold = replace_at(
        &checker,
        &scope,
        &source,
        &mut CaseSupportCache::default(),
        40,
    )
    .unwrap_err();
    let warm = replace_at(&checker, &scope, &source, &mut cache, 40).unwrap_err();
    assert_eq!(cold, "projected case-context replacement depth limit");
    assert_eq!(warm, cold);
}

#[test]
fn support_refuses_another_scope_owner() {
    let mut env = Environment::new();
    env.init_nat().unwrap();
    let checker = TypeChecker::new(&env);
    let scope = crate::scoped_local::LocalScope::new();
    let foreign = crate::scoped_local::LocalScope::new();
    let mut cache = CaseSupportCache::default();
    search_at(&checker, &scope, &data(), &mut cache, 0).unwrap();
    let error = search_at(&checker, &foreign, &data(), &mut cache, 0).unwrap_err();
    assert_eq!(error, "foreign case support cache owner");
}

#[test]
fn deferred_named_binder_and_its_application_are_not_indexed() {
    let mut env = Environment::new();
    env.init_nat().unwrap();
    let checker = TypeChecker::new(&env);
    let mut scope = crate::scoped_local::LocalScope::new();
    let value = scope.try_local(Expr::const_str("Nat")).unwrap();
    let named = value.lam(value.term().clone());
    let applied = Expr::app(named.clone(), Expr::nat_lit(0));
    for expression in [named, applied] {
        let mut cache = CaseSupportCache::default();
        let mut work = 0;
        let mut visits = 0;
        let result = cache
            .summary(
                &checker,
                &scope,
                &expression,
                &mut work,
                100_000,
                64,
                1024,
                &mut visits,
            )
            .unwrap();
        assert!(
            result.is_none(),
            "a deferred binder needs its owner's materialization"
        );
    }
}
