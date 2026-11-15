// Copyright 2026 Andrew Yates | Licensed under the Apache License, Version 2.0

//! Canonical allocation is not binding authority; guards remain charged.

use super::*;
use clean_kernel::{BinderInfo, Environment, KernelTypeError, Level, TypeChecker};

fn id(raw: u64) -> FVarId {
    FVarId::new(raw)
}
fn nat() -> Expr {
    Expr::const_str("Nat")
}
fn cached(root: usize, depth: u32) -> ContextEntry {
    ContextEntry {
        entry: MemoEntry {
            replacement: None,
            declarations: None,
            dependencies: MemoEntry::compact(Some(root)),
        },
        context: 99,
        binder_depth: depth,
        ordinary_count: 0,
    }
}
fn backwards(closer: &Closer<'_>) {
    for (index, node) in closer.dependencies.iter().enumerate() {
        if let Dependency::Join(left, right) = node.dependency {
            assert!(left < index && right < index);
        }
    }
}

#[test]
fn live_named_binding_reuses_one_exact_leaf_without_a_probe() {
    let scope = TermScope::new();
    let mut closer = Closer::new(&scope, TermScopeLimits::default(), true);
    closer.active.insert(id(1), 0);
    let first = closer.named_read_dependency(id(1), 0);
    for _ in 0..64 {
        assert_eq!(closer.named_read_dependency(id(1), 0), first);
    }
    assert_eq!(closer.dependencies.len(), 1);
    assert_eq!(closer.stats, TermScopeStats::default());
    // The raw constructor is deliberately still fresh: old stress oracles use it.
    let raw = closer.dependency_node(Dependency::Named(id(1), 0));
    assert_ne!(raw, first);
    assert_eq!(closer.dependencies.len(), 2);
    assert_eq!(closer.named_read_dependency(id(1), 0), first);
    // Ordinary storage and allocation are unchanged by this named-only slice.
    closer.ordinary.push(0);
    let a = closer.dependency_node(Dependency::Ordinary(0, 0));
    let b = closer.dependency_node(Dependency::Ordinary(0, 0));
    assert_ne!(a, b);
    assert_eq!(closer.ordinary.first(), Some(&0));
    backwards(&closer);
}

#[test]
fn named_read_handle_checks_bounds_and_exact_value_after_rollback_and_recycling() {
    for replacement in [
        Dependency::Named(id(2), 0),
        Dependency::Named(id(1), 1),
        Dependency::Ordinary(0, 0),
        Dependency::Join(0, 1),
    ] {
        let scope = TermScope::new();
        let mut closer = Closer::new(&scope, TermScopeLimits::default(), true);
        closer.active.insert(id(1), 0);
        closer.dependency_node(Dependency::Named(id(9), 0));
        closer.dependency_node(Dependency::Named(id(10), 0));
        let original = closer.named_read_dependency(id(1), 0);
        closer.dependencies.truncate(original);
        let recycled = closer.dependency_node(replacement);
        assert_eq!(recycled, original);
        let actual = closer.named_read_dependency(id(1), 0);
        assert_ne!(actual, recycled);
        assert!(closer.dependencies[actual].dependency == Dependency::Named(id(1), 0));
        assert_eq!(closer.named_read_dependency(id(1), 0), actual);
        backwards(&closer);
    }
    let scope = TermScope::new();
    let mut closer = Closer::new(&scope, TermScopeLimits::default(), true);
    closer.active.insert(id(1), 0);
    let old = closer.named_read_dependency(id(1), 0);
    closer.dependencies.truncate(old); // Out-of-bounds hint, no replacement node.
    let fresh = closer.named_read_dependency(id(1), 0);
    assert_eq!(fresh, old);
    assert_eq!(closer.dependencies.len(), 1);
    closer.active.remove(&id(1));
    closer.active.insert(id(1), 0); // A different live sibling binding resets the hint.
    // Resetting the live hint still performs the binding check; equal dependency
    // metadata can then reuse the same owned arena node across sibling scopes.
    assert_eq!(closer.named_read_dependency(id(1), 0), fresh);
}

#[test]
fn failed_named_rebase_retains_no_authority_and_warm_valid_rebase_keeps_every_charge() {
    let scope = TermScope::new();
    let mut closer = Closer::new(&scope, TermScopeLimits::default(), true);
    closer.binder_depth = 1;
    closer.active.insert(id(1), 0);
    let left = closer.dependency_node(Dependency::Named(id(1), 1));
    let right = closer.dependency_node(Dependency::Named(id(2), 1));
    let root = closer.dependency_node(Dependency::Join(left, right));
    let checkpoint = closer.dependencies.len();
    assert!(closer.visit());
    assert_eq!(
        closer.relative_dependencies(&cached(root, 2), RebaseMode::NamedOnly),
        None
    );
    assert_eq!(closer.stats.context_check_visits, 3);
    assert_eq!(closer.diagnostic_report().cache.named_dependency_missing, 1);
    assert_eq!(closer.dependencies.len(), checkpoint + 1);
    // Same production rollback boundary: the successful left leaf was private.
    closer.dependencies.truncate(checkpoint);
    let actual = closer.named_read_dependency(id(1), 0);
    assert_eq!(actual, checkpoint);
    for _ in 0..2 {
        let before = closer.stats;
        let nodes = closer.dependencies.len();
        assert!(closer.visit());
        assert_eq!(
            closer.relative_dependencies(&cached(left, 2), RebaseMode::NamedOnly),
            Some(Some(actual))
        );
        assert_eq!(closer.stats.visits - before.visits, 2);
        assert_eq!(
            closer.stats.context_check_visits - before.context_check_visits,
            1
        );
        assert_eq!(
            closer.dependencies.len(),
            nodes,
            "warm rebase saves allocation, not visits"
        );
    }
    backwards(&closer);
}

#[test]
fn canonical_named_read_never_reorders_missing_or_moved_first_guard_with_finite_caps() {
    for missing in [false, true] {
        for cap in 0..=3 {
            let scope = TermScope::new();
            let mut closer = Closer::new(
                &scope,
                TermScopeLimits {
                    max_visits: 1 + cap,
                    ..TermScopeLimits::default()
                },
                true,
            );
            closer.binder_depth = 4;
            if !missing {
                closer.active.insert(id(1), 2);
            }
            closer.active.insert(id(2), 1);
            // A warm current binding leaf cannot authorize an old mismatched read.
            let warm = closer.named_read_dependency(id(2), 1);
            if !missing {
                closer.named_read_dependency(id(1), 2);
            }
            let left = closer.dependency_node(Dependency::Named(id(1), 1));
            let right = closer.dependency_node(Dependency::Named(id(2), 2));
            let root = closer.dependency_node(Dependency::Join(left, right));
            assert!(closer.visit());
            assert!(!closer.same_dependencies(Some(root)));
            assert_eq!(closer.stats.context_check_visits, cap.min(2));
            assert_eq!(closer.stats.visits, 1 + cap.min(2));
            assert_eq!(
                closer.error,
                (cap < 2).then_some(TermScopeError::VisitLimit)
            );
            assert_eq!(closer.dependencies[right].last_probe, 0);
            assert_eq!(closer.dependencies[warm].last_probe, 0);
            let report = closer.diagnostic_report().cache;
            assert_eq!(
                report.named_dependency_missing,
                usize::from(missing && cap >= 2)
            );
            assert_eq!(
                report.named_dependency_moved,
                usize::from(!missing && cap >= 2)
            );
            backwards(&closer);
        }
    }
}

#[test]
fn canonical_named_reads_preserve_ordinary_proof_oracle_dag_and_scope_errors() {
    let sum = Expr::apps(
        Expr::const_str("Nat.add"),
        [Expr::fvar(id(1)), Expr::fvar(id(2))],
    );
    let sum = Expr::apps(Expr::const_str("Nat.add"), [sum.clone(), sum]);
    let eq = |left, right| {
        Expr::apps(
            Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
            [nat(), left, right],
        )
    };
    let open = Expr::apps(
        Expr::const_(
            Name::from_string("Eq.refl"),
            vec![Level::succ(Level::zero())],
        ),
        [nat(), sum.clone()],
    );
    let mut scope = TermScope::new();
    let proof = scope.lam(id(2), BinderInfo::Default, nat(), open.clone());
    let proof = scope.lam(id(1), BinderInfo::Default, nat(), proof);
    let claim = scope.pi(
        id(2),
        BinderInfo::Default,
        nat(),
        eq(sum.clone(), sum.clone()),
    );
    let claim = scope.pi(id(1), BinderInfo::Default, nat(), claim);
    let wrong = scope.pi(
        id(2),
        BinderInfo::Default,
        nat(),
        eq(sum.clone(), Expr::app(Expr::const_str("Nat.succ"), sum)),
    );
    let wrong = scope.pi(id(1), BinderInfo::Default, nat(), wrong);
    let oracle = Expr::lam(
        BinderInfo::Default,
        nat(),
        Expr::lam(BinderInfo::Default, nat(), open.abstract_fvar(id(2))).abstract_fvar(id(1)),
    );
    let report = scope.close_with_diagnostics(&proof, TermScopeLimits::default());
    let actual = report.result.as_ref().unwrap();
    assert_eq!(actual, &oracle);
    let claim = scope.close(&claim).unwrap();
    let wrong = scope.close(&wrong).unwrap();
    let decoded = trust_ir::proof::decode_clean_expr_dag_v2(
        &trust_ir::proof::encode_clean_expr_dag_v2(actual).unwrap(),
    )
    .unwrap();
    let mut env = Environment::new();
    env.init_eq().unwrap();
    env.init_nat().unwrap();
    for candidate in [actual, &decoded] {
        assert!(!candidate.has_fvar_quick() && !candidate.has_loose_bvars());
        let mut checker = TypeChecker::new(&env);
        checker.set_allow_unsafe(false);
        checker.set_allow_partial(false);
        checker.check_type(candidate, &claim).unwrap();
        assert!(!checker.heartbeat_spent());
        let audit = env.audit_certification(&claim, candidate);
        assert!(audit.is_certified(), "{audit:#?}");
        for dependency in &audit.dependencies {
            assert!(env.axiom_deps(dependency).unwrap().is_empty());
            assert!(env.foundational_axiom_deps(dependency).unwrap().is_empty());
            assert!(env.trust_marker_deps(dependency).unwrap().is_empty());
        }
        let mut checker = TypeChecker::new(&env);
        checker.set_allow_unsafe(false);
        checker.set_allow_partial(false);
        assert!(matches!(
            checker.check_type(candidate, &wrong),
            Err(KernelTypeError::TypeMismatch { .. })
        ));
        assert!(!checker.heartbeat_spent());
    }
    for cap in 0..=report.stats.visits {
        let outcome = scope.close_with_limits(
            &proof,
            TermScopeLimits {
                max_visits: cap,
                ..TermScopeLimits::default()
            },
        );
        if cap < report.stats.visits {
            assert!(matches!(outcome, Err(TermScopeError::VisitLimit)));
        } else {
            assert_eq!(outcome.unwrap().term, *actual);
        }
    }
    let escaped = scope.lam(id(3), BinderInfo::Default, nat(), Expr::fvar(id(1)));
    assert_eq!(
        scope.close(&escaped),
        Err(TermScopeError::OutOfScope(id(1)))
    );
    let inner = scope.lam(id(1), BinderInfo::Default, nat(), Expr::fvar(id(1)));
    let shadow = scope.lam(id(1), BinderInfo::Default, nat(), inner);
    assert_eq!(
        scope.close(&shadow),
        Err(TermScopeError::ShadowedLocal(id(1)))
    );
}
