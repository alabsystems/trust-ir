// Copyright 2026 Andrew Yates | SPDX-License-Identifier: Apache-2.0
//! Returned materialization roots confer no typing or external capture authority.
use super::*;
use clean_kernel::{Environment, Level};
fn n() -> Expr {
    Expr::const_str("Nat")
}
fn succ(value: Expr) -> Expr {
    Expr::app(Expr::const_str("Nat.succ"), value)
}
fn tower(mut value: Expr, count: usize) -> Expr {
    for _ in 0..count {
        value = succ(value);
    }
    value
}
fn eq(a: Expr, b: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
        [n(), a, b],
    )
}
fn refl(value: Expr) -> Expr {
    Expr::apps(
        Expr::const_(
            Name::from_string("Eq.refl"),
            vec![Level::succ(Level::zero())],
        ),
        [n(), value],
    )
}
fn env() -> Environment {
    let mut e = Environment::new();
    e.init_nat().unwrap();
    e.init_eq().unwrap();
    e.init_true_false().unwrap();
    e
}
fn parts(scope: &LocalScope, ambient: &[ScopedLocal]) -> ProofComponents {
    let mut p = ProofComponents::new("materialized.capture", ProofLimits::default());
    p.set_base(
        scope,
        ambient
            .iter()
            .cloned()
            .map(OwnedProofCapture::Parameter)
            .collect(),
    )
    .unwrap();
    p
}
fn replay(
    p: ProofComponents,
    scope: &LocalScope,
    root: Expr,
    goal: Expr,
    claim: &Expr,
) -> Result<(), String> {
    let bundle = p.close_scoped(scope, root, goal, Default::default())?;
    let bytes = bundle.encode_with_claim(claim)?;
    let (decoded, carried) = ScopedProofComponentBundle::decode_with_claim(&bytes)?;
    assert_eq!(&carried, claim);
    decoded.replay(&env(), claim, 2_000_000).map(|_| ())
}

#[test]
fn materialized_capture_prunes_only_actual_bound_inventory_and_replays_frozen_typed_goal() {
    let mut scope = LocalScope::new();
    let a = scope.try_local(n()).unwrap();
    let x = scope.try_local(n()).unwrap();
    let unused = scope.try_local(n()).unwrap();
    let original = tower(
        Expr::apps(
            Expr::const_str("Nat.add"),
            [a.term().clone(), x.term().clone()],
        ),
        32,
    );
    let mut p = parts(&scope, std::slice::from_ref(&a));
    let root = p
        .materialize_scoped_terms(&scope, &[a.clone(), x.clone(), unused.clone()], &[original])
        .unwrap()
        .remove(0);
    assert_eq!(p.materialized_capture_roots, 1);
    let value = x.lam(unused.lam(root));
    let ty = Expr::arrow(n(), Expr::arrow(n(), n()));
    let expected = tower(
        Expr::apps(
            Expr::const_str("Nat.add"),
            [a.term().clone(), Expr::nat_lit(0)],
        ),
        32,
    );
    let arguments = [Expr::nat_lit(0), Expr::nat_lit(1)];
    let frozen = scope
        .close(&a.pi(eq(
            Expr::apps(value.clone(), arguments.clone()),
            expected.clone(),
        )))
        .unwrap();
    let before = p.counts().3;
    let reference = p
        .bind_scoped(&mut scope, &[], ty.clone(), value.clone())
        .unwrap();
    let optimized = p.counts().3 - before;
    assert_eq!(reference.get_app_num_args(), 0);
    let mut canonical = parts(&scope, std::slice::from_ref(&a));
    let before = canonical.counts().3;
    let other = canonical.bind_scoped(&mut scope, &[], ty, value).unwrap();
    let ordinary = canonical.counts().3 - before;
    assert_eq!(other.get_app_num_args(), 0);
    assert!(
        optimized < ordinary,
        "optimized={optimized}, ordinary={ordinary}"
    );
    replay(
        p,
        &scope,
        a.lam(refl(expected.clone())),
        eq(Expr::apps(reference, arguments), expected),
        &frozen,
    )
    .unwrap();
}

#[test]
fn materialized_capture_does_not_cache_ancestor_prunes_or_add_unused_capture_abi() {
    let mut scope = LocalScope::new();
    let x = scope.try_local(n()).unwrap();
    let unused = scope.try_local(n()).unwrap();
    let mut p = parts(&scope, &[]);
    let root = p
        .materialize_scoped_terms(
            &scope,
            &[x.clone(), unused.clone()],
            &[tower(x.term().clone(), 24)],
        )
        .unwrap()
        .remove(0);
    let wrapper = succ(root);
    let _ = p
        .bind_scoped(
            &mut scope,
            &[],
            Expr::arrow(n(), Expr::arrow(n(), n())),
            x.lam(unused.lam(wrapper.clone())),
        )
        .unwrap();
    assert!(
        !p.dependencies.contains_key(&DependencyKey(wrapper.clone())),
        "a context-dependent ancestor must not publish a context-free empty summary"
    );
    let captures = [
        OwnedProofCapture::Parameter(x.clone()),
        OwnedProofCapture::Parameter(unused.clone()),
    ];
    let reference = p
        .bind_scoped(&mut scope, &captures, n(), wrapper.clone())
        .unwrap();
    assert_eq!(
        reference.get_app_num_args(),
        1,
        "outside the actual binder, x is required and unused is still omitted"
    );
    assert_eq!(*reference.get_app_args()[0], *x.term());
    let again = p.bind_scoped(&mut scope, &captures, n(), wrapper).unwrap();
    assert_eq!(again.get_app_num_args(), 1);
}

#[test]
fn materialized_capture_same_spelled_sibling_and_other_component_use_canonical_dependencies() {
    let mut scope = LocalScope::new();
    let x = scope.try_local(n()).unwrap();
    let sibling = scope.try_local(n()).unwrap();
    let unused = scope.try_local(n()).unwrap();
    let mut p = parts(&scope, &[]);
    let root = p
        .materialize_scoped_terms(
            &scope,
            &[x.clone(), unused.clone()],
            &[tower(x.term().clone(), 16)],
        )
        .unwrap()
        .remove(0);
    let value = sibling.lam(unused.lam(root.clone()));
    let captures = [
        OwnedProofCapture::Parameter(x.clone()),
        OwnedProofCapture::Parameter(sibling.clone()),
        OwnedProofCapture::Parameter(unused.clone()),
    ];
    let reference = p
        .bind_scoped(
            &mut scope,
            &captures,
            Expr::arrow(n(), Expr::arrow(n(), n())),
            value,
        )
        .unwrap();
    assert_eq!(reference.get_app_num_args(), 1);
    assert_eq!(*reference.get_app_args()[0], *x.term());
    let mut other = parts(&scope, &[]);
    assert_eq!(other.materialized_capture_roots, 0);
    let raw = other.bind_scoped(&mut scope, &captures, n(), root).unwrap();
    assert_eq!(
        raw.get_app_num_args(),
        1,
        "an Expr crossing components grants no private materialization receipt"
    );
    let foreign = LocalScope::new();
    let before = p.counts();
    assert!(
        p.materialize_scoped_terms(&foreign, &[], &[Expr::nat_lit(0)])
            .is_err()
    );
    assert_eq!(p.counts(), before);
}

fn scan(
    p: &mut ProofComponents,
    scope: &LocalScope,
    expression: &Expr,
    max_depth: u32,
) -> (Result<(), String>, bool, bool) {
    let mut walker = CaptureDependencies {
        scope,
        ambient: &p.base_ids,
        work: &mut p.analysis_visits,
        word_work: &mut p.analysis_words,
        cache: &mut p.dependencies,
        retained_words: &mut p.retained_words,
        retained_sets: &mut p.retained_sets,
        limit: p.limits.operations,
        needed: Arc::new(Vec::new()),
        empty: Arc::new(Vec::new()),
        error: None,
        depth: 0,
        max_depth,
        materialized_reuse: true,
        bound: HashSet::new(),
        pruned: false,
    };
    let result = walker.scan(expression);
    (result, walker.pruned, walker.bound.is_empty())
}
#[test]
fn materialized_capture_complete_height_bound_falls_back_under_a_deeper_reuse() {
    let mut scope = LocalScope::new();
    let x = scope.try_local(n()).unwrap();
    let mut p = parts(&scope, &[]);
    let root = p
        .materialize_scoped_terms(
            &scope,
            std::slice::from_ref(&x),
            &[tower(x.term().clone(), 16)],
        )
        .unwrap()
        .remove(0);
    let value = x.lam(root);
    let (ok, pruned, restored) = scan(&mut p, &scope, &value, 128);
    ok.unwrap();
    assert!(pruned && restored);
    let before = p.counts().3;
    let (failed, pruned, restored) = scan(&mut p, &scope, &value, 10);
    assert!(failed.unwrap_err().contains("depth limit"));
    assert!(!pruned && restored);
    assert!(p.counts().3 > before);
}

#[test]
fn materialized_capture_every_publication_cutoff_is_paid_and_failures_poison_reuse() {
    let mut scope = LocalScope::new();
    let x = scope.try_local(n()).unwrap();
    let input = tower(x.term().clone(), 8);
    let mut successes = 0;
    for cap in 0..=96 {
        let mut p = ProofComponents::new(
            "materialized.capture.cutoff",
            ProofLimits {
                operations: cap,
                ..Default::default()
            },
        );
        p.set_base(&scope, vec![]).unwrap();
        let mut declarations = 0;
        match p.materialize_scoped_terms(
            &scope,
            std::slice::from_ref(&x),
            std::slice::from_ref(&input),
        ) {
            Ok(mut roots) => {
                successes += 1;
                assert_eq!(p.materialized_capture_roots, 1);
                let root = roots.remove(0);
                match p.bind_scoped(&mut scope, &[], Expr::arrow(n(), n()), x.lam(root)) {
                    Ok(reference) => {
                        assert_eq!(reference.get_app_num_args(), 0);
                        declarations = 1;
                    }
                    Err(_) => {
                        assert!(p.materialized_capture_failed);
                        assert_eq!(p.counts().0, 0);
                    }
                }
            }
            Err(_) => {
                assert_eq!(p.materialized_capture_roots, 0);
                assert!(p.materialized_capture_failed);
            }
        }
        assert!(p.counts().3 <= cap, "cap={cap}, counts={:?}", p.counts());
        assert_eq!(p.counts().0, declarations);
    }
    assert!(successes > 0 && successes < 96);
    let mut p = parts(&scope, &[]);
    p.materialize_scoped_terms(&scope, std::slice::from_ref(&x), &[input])
        .unwrap();
    let before = p.materialized_capture_roots;
    let invalid = x.lam(Expr::nat_lit(0)); // even UNUSED named shadow must refuse
    let (canonical, _) = scope.close_external_forest(
        std::slice::from_ref(&invalid),
        std::slice::from_ref(&x),
        &[1],
    );
    let expected = canonical.unwrap_err();
    assert!(
        matches!(&expected, crate::scoped_local::LocalScopeError::Closure(crate::term_scope::TermScopeError::ShadowedLocal(id)) if *id == x.id())
    );
    assert_eq!(
        p.materialize_scoped_terms(&scope, std::slice::from_ref(&x), &[invalid])
            .unwrap_err(),
        expected.to_string(),
    );
    assert!(p.materialized_capture_failed);
    assert_eq!(p.materialized_capture_roots, before);
    let raw = p
        .bind_scoped(
            &mut scope,
            &[OwnedProofCapture::Parameter(x.clone())],
            n(),
            tower(x.term().clone(), 8),
        )
        .unwrap();
    assert_eq!(raw.get_app_num_args(), 1);
}

#[test]
fn materialized_capture_upper_bound_never_certifies_a_cold_invalid_defining_value() {
    let mut scope = LocalScope::new();
    let a = scope.try_local(n()).unwrap();
    let mut p = parts(&scope, std::slice::from_ref(&a));
    let invalid = Expr::apps(
        Expr::const_str("Nat.add"),
        [a.term().clone(), Expr::const_str("True.intro")],
    );
    let root = p
        .materialize_scoped_terms(&scope, std::slice::from_ref(&a), &[invalid])
        .unwrap()
        .remove(0);
    assert_eq!(p.materialized_capture_roots, 1);
    let _ = p.bind_scoped(&mut scope, &[], n(), root).unwrap();
    let claim = scope.close(&a.pi(Expr::const_str("True"))).unwrap();
    let error = replay(
        p,
        &scope,
        a.lam(Expr::const_str("True.intro")),
        Expr::const_str("True"),
        &claim,
    )
    .unwrap_err();
    assert!(
        error.contains("TypeMismatch") && !error.contains("BudgetExhausted"),
        "{error}"
    );
}

#[test]
fn materialized_capture_removed_external_cannot_become_a_hidden_root_assumption() {
    let mut scope = LocalScope::new();
    let x = scope.try_local(n()).unwrap();
    let mut p = parts(&scope, &[]);
    let root = p
        .materialize_scoped_terms(
            &scope,
            std::slice::from_ref(&x),
            &[tower(x.term().clone(), 12)],
        )
        .unwrap()
        .remove(0);
    let _ = p.bind_scoped(&mut scope, &[], n(), root).unwrap();
    let error = p
        .close_scoped(
            &scope,
            Expr::const_str("True.intro"),
            Expr::const_str("True"),
            Default::default(),
        )
        .err()
        .unwrap();
    let expected = crate::term_scope::TermScopeError::OutOfScope(x.id()).to_string();
    assert!(error.contains(&expected), "{error}");
}

#[test]
fn materialized_capture_later_binding_failure_disables_previous_guarded_entries_without_refund() {
    let mut scope = LocalScope::new();
    let x = scope.try_local(n()).unwrap();
    let mut p = ProofComponents::new(
        "materialized.capture.late.failure",
        ProofLimits {
            captures: 0,
            ..Default::default()
        },
    );
    p.set_base(&scope, vec![]).unwrap();
    let root = p
        .materialize_scoped_terms(
            &scope,
            std::slice::from_ref(&x),
            &[tower(x.term().clone(), 8)],
        )
        .unwrap()
        .remove(0);
    let before = p.counts().3;
    assert!(
        p.bind_scoped(&mut scope, &[OwnedProofCapture::Parameter(x)], n(), root)
            .unwrap_err()
            .contains("capture limit")
    );
    assert!(p.materialized_capture_failed);
    assert_eq!(p.counts().0, 0);
    assert!(p.counts().3 > before);
}

#[test]
fn materialized_capture_failed_forest_publishes_no_successful_root_prefix() {
    let mut scope = LocalScope::new();
    let x = scope.try_local(n()).unwrap();
    let missing = scope.try_local(n()).unwrap();
    let mut p = parts(&scope, &[]);
    let roots = [tower(x.term().clone(), 8), missing.term().clone()];
    let (canonical, _) = scope.close_external_forest(&roots, std::slice::from_ref(&x), &[1, 1]);
    let expected = canonical.unwrap_err();
    assert!(
        matches!(&expected, crate::scoped_local::LocalScopeError::Closure(crate::term_scope::TermScopeError::OutOfScope(id)) if *id == missing.id())
    );
    let error = p
        .materialize_scoped_terms(&scope, std::slice::from_ref(&x), &roots)
        .unwrap_err();
    assert_eq!(error, expected.to_string());
    assert!(p.materialized_capture_failed);
    assert_eq!(p.materialized_capture_roots, 0);
    assert!(p.dependencies.is_empty());
    assert!(p.counts().3 > 0);
}

#[test]
fn materialized_capture_existing_prefix_and_fresh_late_root_pay_both_complete_publication_scans() {
    let mut scope = LocalScope::new();
    let x = scope.try_local(n()).unwrap();
    let old = tower(x.term().clone(), 16);
    let fresh = succ(old.clone());
    let mut roots = vec![old.clone(); 31];
    roots.push(fresh.clone());
    let (canonical, stats) =
        scope.close_external_forest(&roots, std::slice::from_ref(&x), &vec![1; roots.len()]);
    canonical.unwrap();
    let mut saw_success = false;
    let mut saw_failed_publication = false;
    for cap in 0..=512 {
        let mut p = ProofComponents::new(
            "materialized.capture.existing.prefix",
            ProofLimits {
                operations: cap,
                ..Default::default()
            },
        );
        p.set_base(&scope, vec![]).unwrap();
        if p.materialize_scoped_terms(&scope, std::slice::from_ref(&x), std::slice::from_ref(&old))
            .is_err()
        {
            assert!(p.counts().3 <= cap);
            assert_eq!(p.materialized_capture_roots, 0);
            continue;
        }
        assert_eq!(p.materialized_capture_roots, 1);
        let before = p.counts().3;
        match p.materialize_scoped_terms(&scope, std::slice::from_ref(&x), &roots) {
            Ok(_) => {
                saw_success = true;
                assert_eq!(p.materialized_capture_roots, 2);
                // Independent canonical traversal accounts for closing. The
                // remaining bill must cover BOTH actual linear root scans,
                // including the already-registered prefix before the new tail.
                assert!(p.counts().3 - before - stats.visits >= 2 * roots.len());
            }
            Err(_) => {
                saw_failed_publication = true;
                assert!(p.materialized_capture_failed);
                assert_eq!(p.materialized_capture_roots, 1);
                assert!(!p.dependencies.contains_key(&DependencyKey(fresh.clone())));
            }
        }
        assert!(p.counts().3 <= cap, "cap={cap}, counts={:?}", p.counts());
        assert_eq!(p.counts().0, 0);
    }
    assert!(saw_success && saw_failed_publication);
}
