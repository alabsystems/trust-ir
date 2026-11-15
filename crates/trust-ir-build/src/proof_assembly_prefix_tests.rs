// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Prefix construction shares evidence, never an owner or proof authority.

use super::*;
use std::sync::Arc;

fn conjunction(parts: &[Expr], tail: Expr) -> Expr {
    parts
        .iter()
        .rev()
        .fold(tail, |tail, part| app("And", [part.clone(), tail]))
}

fn conjunction_proof(parts: &[Expr], proofs: &[Expr]) -> Expr {
    assert_eq!(parts.len(), proofs.len());
    let mut tail_type = c("True");
    let mut tail_proof = c("True.intro");
    for (part, proof) in parts.iter().zip(proofs).rev() {
        tail_proof = app(
            "And.intro",
            [part.clone(), tail_type.clone(), proof.clone(), tail_proof],
        );
        tail_type = app("And", [part.clone(), tail_type]);
    }
    tail_proof
}

fn last_argument(expr: &Expr) -> &Arc<Expr> {
    let ExprKind::App(_, argument) = expr.kind() else {
        panic!("expected a projection application");
    };
    argument
}

fn true_fact(logic: &mut ProofAssembly, count: usize) -> ScopedProofCandidate {
    logic
        .candidate(
            conjunction(&vec![c("True"); count], c("True")),
            c("True.intro"),
        )
        .unwrap()
}

#[test]
fn and_prefix_matches_all_eleven_scalar_fields_and_shares_right_spine() {
    let mut logic = ProofAssembly::new(ProofLimits::default()).unwrap();
    let parts: Vec<_> = (0..11).map(|n| eq(c("Nat"), nat(n), nat(n))).collect();
    let fact = logic
        .candidate(conjunction(&parts, c("True")), c("True.intro"))
        .unwrap();
    let before = logic.operations;
    let fields = logic.and_prefix(&fact, 11).unwrap();
    assert_eq!(logic.operations - before, 21);
    assert_eq!(fields.len(), 11);
    let scalar: Vec<_> = (0..11).map(|i| logic.and_at(&fact, i).unwrap()).collect();
    for ((field, scalar), original) in fields.iter().zip(&scalar).zip(&parts) {
        assert_eq!(field.proposition(), original);
        assert_eq!(field.proposition(), scalar.proposition());
        assert_eq!(field.term(), scalar.term());
    }
    for index in 1..10 {
        // Expr::clone copies its root by value. Each App therefore has a
        // distinct argument Arc, but both copied right-prefix roots retain
        // the SAME immediate child allocations. Root-Arc equality alone is
        // the wrong sharing oracle for this API.
        let used_by_left = last_argument(fields[index].term());
        let used_by_right = last_argument(last_argument(fields[index + 1].term()));
        assert!(!Arc::ptr_eq(used_by_left, used_by_right));
        let (ExprKind::App(lf, la), ExprKind::App(rf, ra)) =
            (used_by_left.kind(), used_by_right.kind())
        else {
            panic!("nonempty shared right prefix");
        };
        assert!(Arc::ptr_eq(lf, rf) && Arc::ptr_eq(la, ra));
        let scalar_left = last_argument(scalar[index].term());
        let scalar_right = last_argument(last_argument(scalar[index + 1].term()));
        let (ExprKind::App(lf, _), ExprKind::App(rf, _)) =
            (scalar_left.kind(), scalar_right.kind())
        else {
            panic!("nonempty scalar right prefix");
        };
        assert!(!Arc::ptr_eq(lf, rf), "scalar calls reconstruct the prefix");
    }
}

#[test]
fn and_prefix_dependent_open_fields_close_replay_and_refuse_forged_lets() {
    let env = environment();
    let mut scope = LocalScope::new();
    let mut logic = ProofAssembly::new(ProofLimits::default()).unwrap();
    let a = scope.try_local(Expr::type_()).unwrap();
    let x = scope.try_local(a.term().clone()).unwrap();
    let mut parts = vec![eq(a.term().clone(), x.term().clone(), x.term().clone())];
    let mut proofs = vec![refl(a.term().clone(), x.term().clone())];
    for n in 0..10 {
        parts.push(eq(c("Nat"), nat(n), nat(n)));
        proofs.push(refl(c("Nat"), nat(n)));
    }
    let original = conjunction(&parts, c("True"));
    let value = conjunction_proof(&parts, &proofs);
    let bound = scope.try_local(original.clone()).unwrap();
    let fact = logic.candidate(original, bound.term().clone()).unwrap();
    let fields = logic.and_prefix(&fact, 11).unwrap();
    let parameters = [a, x];
    for (index, field) in fields.iter().enumerate() {
        let scalar = logic.and_at(&fact, index).unwrap();
        let close = |proof: &Expr| {
            scope
                .close(&lams(&parameters, bound.let_(value.clone(), proof.clone())))
                .unwrap()
        };
        let proof = close(field.term());
        assert_eq!(proof, close(scalar.term()));
        let claim = scope
            .close(&forall(&parameters, parts[index].clone()))
            .unwrap();
        checked(&env, &proof, &claim);
    }
    let claim = scope.close(&forall(&parameters, parts[0].clone())).unwrap();
    let forged_value = scope
        .close(&lams(
            &parameters,
            bound.let_(c("True.intro"), fields[0].term().clone()),
        ))
        .unwrap();
    rejected(&env, &forged_value, &claim);
    let forged_field = logic.candidate(parts[0].clone(), c("True.intro")).unwrap();
    let forged = scope
        .close(&lams(
            &parameters,
            bound.let_(value, forged_field.term().clone()),
        ))
        .unwrap();
    rejected(&env, &forged, &claim);
}

#[test]
fn and_prefix_checks_foreign_and_expired_facts_even_for_zero_count() {
    let mut logic = ProofAssembly::new(ProofLimits::default()).unwrap();
    let mut foreign = ProofAssembly::new(ProofLimits::default()).unwrap();
    let outer = true_fact(&mut logic, 2);
    let other = true_fact(&mut foreign, 2);
    for count in [0, 1, usize::MAX] {
        let before = logic.operations;
        assert_eq!(
            logic.and_prefix(&other, count).err().unwrap(),
            "foreign or expired proof assembly handle"
        );
        assert_eq!(logic.operations, before);
    }
    let mut captured = None;
    let expired = logic
        .with_scope(|logic| {
            let fields = logic.and_prefix(&outer, 2)?;
            for field in &fields {
                logic.check_live(field)?;
            }
            captured = Some(fields[1].clone());
            Ok(fields[0].clone())
        })
        .unwrap();
    for fact in [expired, captured.unwrap()] {
        for count in [0, 1] {
            let before = logic.operations;
            assert!(logic.and_prefix(&fact, count).is_err());
            assert_eq!(logic.operations, before);
        }
        logic
            .with_scope(|logic| {
                assert!(logic.and_prefix(&fact, 0).is_err());
                assert_eq!(logic.and_prefix(&outer, 1)?.len(), 1);
                Ok(())
            })
            .unwrap();
    }
    assert!(logic.in_root_context());
    logic.check_live(&outer).unwrap();
}

#[test]
fn and_prefix_zero_overflow_and_oversize_refuse_without_candidate_charges() {
    let mut logic = ProofAssembly::new(ProofLimits::default()).unwrap();
    let non_and = logic.candidate(c("True"), c("True.intro")).unwrap();
    let before = logic.operations;
    assert!(logic.and_prefix(&non_and, 0).unwrap().is_empty());
    assert_eq!(logic.operations, before);
    assert_eq!(
        logic.and_prefix(&non_and, usize::MAX).err().unwrap(),
        "conjunction prefix cost overflow"
    );
    assert_eq!(
        logic.and_prefix(&non_and, 500_001).err().unwrap(),
        "conjunction prefix exceeds proof budget"
    );
    assert_eq!(logic.operations, before);
    // The largest representable cost is computed exactly, without overflowing
    // an intermediate 2*n. Its budget refusal still precedes shape traversal.
    let mut maximal = ProofAssembly::new(ProofLimits {
        operations: usize::MAX,
        ..ProofLimits::default()
    })
    .unwrap();
    let fact = true_fact(&mut maximal, 1);
    assert_eq!(
        maximal.and_prefix(&fact, usize::MAX / 2 + 1).err().unwrap(),
        "conjunction prefix exceeds proof budget"
    );
    assert_eq!(maximal.operations, 1);
    // Even an enormous admitted count never drives an eager allocation: the
    // short actual conjunction is traversed, charged, then refused normally.
    assert!(maximal.and_prefix(&fact, usize::MAX / 2).is_err());
    assert_eq!(maximal.operations, 3);
}

#[test]
fn and_prefix_exact_budget_and_malformed_prefix_keep_partial_charges() {
    let mut exact = ProofAssembly::new(ProofLimits {
        operations: 6,
        ..ProofLimits::default()
    })
    .unwrap();
    let fact = true_fact(&mut exact, 3);
    assert_eq!(exact.and_prefix(&fact, 3).unwrap().len(), 3);
    assert_eq!(exact.operations, 6);
    assert!(exact.and_prefix(&fact, 0).unwrap().is_empty());
    assert!(exact.and_prefix(&fact, 1).is_err());
    assert_eq!(exact.operations, 6);
    let mut insufficient = ProofAssembly::new(ProofLimits {
        operations: 5,
        ..ProofLimits::default()
    })
    .unwrap();
    let fact = true_fact(&mut insufficient, 3);
    assert!(insufficient.and_prefix(&fact, 3).is_err());
    assert_eq!(
        insufficient.operations, 1,
        "preflight does not partly charge"
    );
    let mut malformed = ProofAssembly::new(ProofLimits::default()).unwrap();
    let fact = true_fact(&mut malformed, 2);
    assert!(malformed.and_prefix(&fact, 3).is_err());
    assert_eq!(
        malformed.operations, 5,
        "two left and two right projections remain charged"
    );
    let bad_arity = malformed
        .candidate(app("And", [c("True")]), c("True.intro"))
        .unwrap();
    let before = malformed.operations;
    assert!(malformed.and_prefix(&bad_arity, 1).is_err());
    assert_eq!(malformed.operations, before);
    assert_eq!(malformed.and_prefix(&fact, 1).unwrap().len(), 1);
    assert_eq!(
        malformed.operations,
        before + 1,
        "failure does not reset or poison the producer"
    );
}

#[test]
fn and_prefix_is_only_a_prefix_not_a_tail_or_truth_validator() {
    let mut logic = ProofAssembly::new(ProofLimits::default()).unwrap();
    let parts = [c("True"), c("False")];
    let fact = logic
        .candidate(conjunction(&parts, c("False")), c("True.intro"))
        .unwrap();
    let fields = logic.and_prefix(&fact, 2).unwrap();
    assert_eq!(fields[0].proposition(), &c("True"));
    assert_eq!(fields[1].proposition(), &c("False"));
    for (index, field) in fields.iter().enumerate() {
        assert_eq!(field.term(), logic.and_at(&fact, index).unwrap().term());
    }
    assert!(logic.and_prefix(&fact, 3).is_err());
    // Correct construction provenance does not confer proof validity.
    rejected(&environment(), fields[1].term(), &c("False"));
}
