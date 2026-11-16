// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use clean_kernel::{Environment, Level, TypeChecker};

fn nat() -> Expr {
    Expr::const_str("Nat")
}
fn eq(left: Expr, right: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
        [nat(), left, right],
    )
}
fn refl(value: Expr) -> Expr {
    Expr::apps(
        Expr::const_(
            Name::from_string("Eq.refl"),
            vec![Level::succ(Level::zero())],
        ),
        [nat(), value],
    )
}

#[test]
fn repeated_contexts_preserve_actual_definitions_and_complete_kernel_replay() {
    let mut env = Environment::new();
    env.init_nat().unwrap();
    env.init_eq().unwrap();
    env.init_true_false().unwrap();
    let mut scope = LocalScope::new();
    let input = scope.try_local(nat()).unwrap();
    let formal = scope.try_local(nat()).unwrap();
    let mut value = Expr::app(formal.lam(formal.term().clone()), input.term().clone());
    for _ in 0..96 {
        let unused = scope.try_local(nat()).unwrap();
        value = unused.let_(Expr::nat_lit(0), value);
    }
    let mut parts = ProofComponents::new("complete.references.repeated", ProofLimits::default());
    parts
        .set_base(&scope, vec![OwnedProofCapture::Parameter(input.clone())])
        .unwrap();
    let definition = parts
        .bind_scoped_owned(&mut scope, &[], nat(), value)
        .unwrap();
    let _materialized = parts
        .materialize_owned_definition(&scope, &definition.local)
        .unwrap();
    let before_request = parts.counts().3;
    parts.enable_normalization_reference_reuse(&scope).unwrap();
    let request_work = parts.counts().3 - before_request;
    assert!(request_work > 0, "owner reuse admission is paid separately");
    let mut work = Vec::new();
    for _ in 0..3 {
        let (context, _, observed) = parts
            .untrusted_normalization_context_profiled(
                &scope,
                std::slice::from_ref(&definition.reference),
            )
            .unwrap();
        assert_eq!(
            TypeChecker::with_context(&env, context).whnf(&definition.reference),
            input.term().clone()
        );
        work.push(observed);
    }
    eprintln!(
        "complete normalization owner admission={request_work}; repeated context work: {work:?}"
    );
    assert!(work.iter().all(|row| row.dependency_visits > 0));
    assert!(work[1].dependency_visits < work[0].dependency_visits);
    assert_eq!(work[2].dependency_visits, work[1].dependency_visits);
    let claim = scope
        .close(&input.pi(eq(input.term().clone(), input.term().clone())))
        .unwrap();
    let bundle = parts
        .close_scoped(
            &scope,
            input.lam(refl(definition.reference.clone())),
            eq(definition.reference.clone(), input.term().clone()),
            crate::term_scope::TermScopeLimits::default(),
        )
        .unwrap();
    let wire = bundle.encode_with_claim(&claim).unwrap();
    let (decoded, transported) = ScopedProofComponentBundle::decode_with_claim(&wire).unwrap();
    assert_eq!(transported, claim);
    decoded.replay(&env, &claim, 2_000_000).unwrap();
    let successor = Expr::app(Expr::const_str("Nat.succ"), input.term().clone());
    let false_claim = scope
        .close(&input.pi(eq(input.term().clone(), successor.clone())))
        .unwrap();
    let mut wrong = bundle;
    wrong.goal = eq(definition.reference, successor);
    let false_wire = wrong.encode_with_claim(&false_claim).unwrap();
    let (decoded, transported) =
        ScopedProofComponentBundle::decode_with_claim(&false_wire).unwrap();
    let error = decoded
        .replay(&env, &transported, 2_000_000)
        .err()
        .expect("the changed complete claim must be rejected");
    assert!(
        error.contains("TypeMismatch") && !error.contains("BudgetExhausted"),
        "{error}"
    );
    if let Some(directory) = std::env::var_os("TRUST_IR_COMPLETE_REFERENCE_ARTIFACT_DIR") {
        let directory = std::path::PathBuf::from(directory);
        std::fs::create_dir_all(&directory).unwrap();
        std::fs::write(directory.join("complete-reference-positive.bin"), &wire).unwrap();
        std::fs::write(directory.join("complete-reference-false.bin"), &false_wire).unwrap();
        std::fs::write(directory.join("complete-reference-false.txt"), error).unwrap();
    }
}

#[test]
fn foreign_scope_refusal_and_base_extension_keep_original_visibility() {
    let mut env = Environment::new();
    env.init_nat().unwrap();
    let mut scope = LocalScope::new();
    let input = scope.try_local(nat()).unwrap();
    let formal = scope.try_local(nat()).unwrap();
    let mut value = Expr::app(formal.lam(formal.term().clone()), input.term().clone());
    for _ in 0..24 {
        let unused = scope.try_local(nat()).unwrap();
        value = unused.let_(Expr::nat_lit(0), value);
    }
    let mut parts = ProofComponents::new("complete.references.owner", ProofLimits::default());
    parts
        .set_base(&scope, vec![OwnedProofCapture::Parameter(input.clone())])
        .unwrap();
    let definition = parts
        .bind_scoped_owned(&mut scope, &[], nat(), value)
        .unwrap();
    parts.enable_normalization_reference_reuse(&scope).unwrap();
    let (first, _, cold) = parts
        .untrusted_normalization_context_profiled(
            &scope,
            std::slice::from_ref(&definition.reference),
        )
        .unwrap();
    assert_eq!(
        TypeChecker::with_context(&env, first).whnf(&definition.reference),
        input.term().clone()
    );
    let mut foreign = LocalScope::new();
    let same_id = foreign.try_local(nat()).unwrap();
    assert_eq!(same_id.id(), input.id());
    assert!(
        parts
            .untrusted_normalization_context_profiled(
                &foreign,
                std::slice::from_ref(&definition.reference),
            )
            .err()
            .unwrap()
            .contains("owner")
    );
    let (_, _, warm) = parts
        .untrusted_normalization_context_profiled(
            &scope,
            std::slice::from_ref(&definition.reference),
        )
        .unwrap();
    assert!(warm.dependency_visits < cold.dependency_visits);
    let extra = scope.try_local(nat()).unwrap();
    let before = parts.counts().3;
    parts
        .extend_base(OwnedProofCapture::Parameter(extra))
        .unwrap();
    assert_eq!(
        parts.counts().3,
        before,
        "cache invalidation refunds no work"
    );
    let (extended, _, again) = parts
        .untrusted_normalization_context_profiled(
            &scope,
            std::slice::from_ref(&definition.reference),
        )
        .unwrap();
    assert!(again.dependency_visits > warm.dependency_visits);
    assert_eq!(
        TypeChecker::with_context(&env, extended).whnf(&definition.reference),
        input.term().clone()
    );
}

#[test]
fn changed_actual_body_recomputes_references_and_still_requires_complete_replay() {
    let mut env = Environment::new();
    env.init_nat().unwrap();
    env.init_eq().unwrap();
    env.init_true_false().unwrap();
    let mut scope = LocalScope::new();
    let first = scope.try_local(nat()).unwrap();
    let second = scope.try_local(nat()).unwrap();
    let mut parts = ProofComponents::new("complete.references.changed", ProofLimits::default());
    parts
        .set_base(
            &scope,
            vec![
                OwnedProofCapture::Parameter(first.clone()),
                OwnedProofCapture::Parameter(second.clone()),
            ],
        )
        .unwrap();
    let definition = parts
        .bind_scoped_owned(&mut scope, &[], nat(), first.term().clone())
        .unwrap();
    parts.enable_normalization_reference_reuse(&scope).unwrap();
    let (original, _, _) = parts
        .untrusted_normalization_context_profiled(
            &scope,
            std::slice::from_ref(&definition.reference),
        )
        .unwrap();
    assert_eq!(
        TypeChecker::with_context(&env, original).whnf(&definition.reference),
        first.term().clone()
    );
    // Test-only corruption of an append-only original: a memo keyed only by
    // declaration ID would omit the newly required second parameter.
    parts.bindings[0].1 = second.term().clone();
    let (changed, _, _) = parts
        .untrusted_normalization_context_profiled(
            &scope,
            std::slice::from_ref(&definition.reference),
        )
        .unwrap();
    assert_eq!(
        TypeChecker::with_context(&env, changed).whnf(&definition.reference),
        second.term().clone()
    );
    let claim = scope
        .close(&first.pi(second.pi(eq(second.term().clone(), first.term().clone()))))
        .unwrap();
    let bundle = parts
        .close_scoped(
            &scope,
            first.lam(second.lam(refl(definition.reference.clone()))),
            eq(definition.reference, first.term().clone()),
            crate::term_scope::TermScopeLimits::default(),
        )
        .unwrap();
    let wire = bundle.encode_with_claim(&claim).unwrap();
    let (decoded, transported) = ScopedProofComponentBundle::decode_with_claim(&wire).unwrap();
    let error = decoded
        .replay(&env, &transported, 2_000_000)
        .err()
        .expect("a changed actual body cannot establish the original value");
    assert!(
        error.contains("TypeMismatch") && !error.contains("BudgetExhausted"),
        "{error}"
    );
}

#[test]
fn explicit_reuse_requires_original_owner_and_never_restarts_a_failed_scan() {
    let mut scope = LocalScope::new();
    let input = scope.try_local(nat()).unwrap();
    let mut parts = ProofComponents::new("complete.references.request", ProofLimits::default());
    parts
        .set_base(&scope, vec![OwnedProofCapture::Parameter(input.clone())])
        .unwrap();
    let definition = parts
        .bind_scoped_owned(&mut scope, &[], nat(), input.term().clone())
        .unwrap();
    assert!(parts.normalization_references.is_none());
    parts
        .untrusted_normalization_context_profiled(
            &scope,
            std::slice::from_ref(&definition.reference),
        )
        .unwrap();
    assert!(
        parts.normalization_references.is_none(),
        "ordinary callers retain no reference cache"
    );
    let mut foreign = LocalScope::new();
    assert_eq!(foreign.try_local(nat()).unwrap().id(), input.id());
    assert!(
        parts
            .enable_normalization_reference_reuse(&foreign)
            .unwrap_err()
            .contains("owner")
    );
    assert!(parts.normalization_references.is_none());
    parts.enable_normalization_reference_reuse(&scope).unwrap();
    let before = parts.counts().3;
    parts.enable_normalization_reference_reuse(&scope).unwrap();
    assert!(parts.counts().3 > before, "idempotent requests are charged");
    let mut stopped =
        complete_references::Scan::new(parts.normalization_references.as_mut().unwrap(), 0)
            .unwrap();
    assert!(stopped.scan(&definition.reference).is_err());
    drop(stopped);
    assert!(
        parts
            .enable_normalization_reference_reuse(&scope)
            .unwrap_err()
            .contains("failed scan")
    );
    let extra = scope.try_local(nat()).unwrap();
    parts
        .extend_base(OwnedProofCapture::Parameter(extra))
        .unwrap();
    assert!(parts.enable_normalization_reference_reuse(&scope).is_err());
    assert!(
        parts
            .untrusted_normalization_context_profiled(&scope, &[definition.reference])
            .err()
            .unwrap()
            .contains("failed scan")
    );
}

#[test]
fn transient_input_graphs_are_released_after_the_context_call() {
    let mut scope = LocalScope::new();
    let input = scope.try_local(nat()).unwrap();
    let mut parts = ProofComponents::new("complete.references.transient", ProofLimits::default());
    parts
        .set_base(&scope, vec![OwnedProofCapture::Parameter(input.clone())])
        .unwrap();
    parts.enable_normalization_reference_reuse(&scope).unwrap();
    let mut closed = Expr::nat_lit(0);
    for _ in 0..256 {
        closed = Expr::app(Expr::const_str("Nat.succ"), closed);
    }
    let temporary = Expr::app(closed, input.term().clone());
    let clean_kernel::ExprKind::App(child, _) = temporary.kind() else {
        unreachable!()
    };
    let child = std::sync::Arc::downgrade(child);
    // This is an untrusted producer input, not a typing premise. Its large
    // closed child is skipped by reference discovery and must not be pinned
    // by a persistent input key once the caller releases the expression.
    parts
        .untrusted_normalization_context_profiled(&scope, std::slice::from_ref(&temporary))
        .unwrap();
    drop(temporary);
    assert!(
        child.upgrade().is_none(),
        "temporary input graph was retained"
    );
}

#[test]
fn producer_and_charged_contexts_share_only_owner_paid_reference_work() {
    let mut env = Environment::new();
    env.init_nat().unwrap();
    let mut scope = LocalScope::new();
    let input = scope.try_local(nat()).unwrap();
    let mut value = input.term().clone();
    for _ in 0..64 {
        let unused = scope.try_local(nat()).unwrap();
        value = unused.let_(Expr::nat_lit(0), value);
    }
    let mut parts = ProofComponents::new("complete.references.interleaved", ProofLimits::default());
    parts
        .set_base(&scope, vec![OwnedProofCapture::Parameter(input.clone())])
        .unwrap();
    let definition = parts
        .bind_scoped_owned(&mut scope, &[], nat(), value)
        .unwrap();
    parts.enable_normalization_reference_reuse(&scope).unwrap();
    let before = parts.counts().3;
    let (producer, _, cold) = parts
        .untrusted_normalization_context_profiled(
            &scope,
            std::slice::from_ref(&definition.reference),
        )
        .unwrap();
    assert_eq!(parts.counts().3 - before, cold.dependency_visits);
    assert!(cold.dependency_visits > 0);
    assert_eq!(
        TypeChecker::with_context(&env, producer).whnf(&definition.reference),
        input.term().clone()
    );
    let before = parts.counts().3;
    let (charged, _) = parts
        .charged_normalization_context_with_opaque(
            &scope,
            std::slice::from_ref(&input),
            std::slice::from_ref(&definition.reference),
            &[],
        )
        .unwrap();
    assert!(
        parts.counts().3 > before,
        "charged reuse must spend owner work too"
    );
    assert_eq!(
        TypeChecker::with_context(&env, charged).whnf(&definition.reference),
        input.term().clone()
    );
    let before = parts.counts().3;
    let (_, _, warm) = parts
        .untrusted_normalization_context_profiled(&scope, &[definition.reference])
        .unwrap();
    assert_eq!(parts.counts().3 - before, warm.dependency_visits);
    assert!(warm.dependency_visits > 0 && warm.dependency_visits < cold.dependency_visits);
}

#[test]
fn failed_producers_pay_completed_scans_and_exhaustion_cannot_warm_a_retry() {
    let mut scope = LocalScope::new();
    let input = scope.try_local(nat()).unwrap();
    let orphan = scope.try_local(nat()).unwrap();
    let mut parts = ProofComponents::new(
        "complete.references.failed.producer",
        ProofLimits::default(),
    );
    parts
        .set_base(&scope, vec![OwnedProofCapture::Parameter(input.clone())])
        .unwrap();
    let definition = parts
        .bind_scoped_owned(&mut scope, &[], nat(), Expr::nat_lit(0))
        .unwrap();
    // Test-only corruption makes closure fail after COMPLETE discovery. The
    // original retained body stays bad on every producer/charged attempt.
    parts.bindings[0].1 = Expr::app(Expr::const_str("Nat.succ"), orphan.term().clone());
    parts.enable_normalization_reference_reuse(&scope).unwrap();
    let before = parts.counts().3;
    assert!(
        parts
            .untrusted_normalization_context_profiled(
                &scope,
                std::slice::from_ref(&definition.reference),
            )
            .is_err()
    );
    let cold_paid = parts.counts().3 - before;
    assert!(cold_paid > 0);
    assert!(
        !parts
            .normalization_references
            .as_ref()
            .unwrap()
            .has_failed(),
        "the scan succeeded; its paid data supplies no closure premise"
    );
    let before = parts.counts().3;
    assert!(
        parts
            .untrusted_normalization_context_profiled(
                &scope,
                std::slice::from_ref(&definition.reference),
            )
            .is_err()
    );
    let warm_paid = parts.counts().3 - before;
    assert!(warm_paid > 0 && warm_paid < cold_paid);
    let before = parts.counts().3;
    assert!(
        parts
            .charged_normalization_context_with_opaque(
                &scope,
                std::slice::from_ref(&input),
                std::slice::from_ref(&definition.reference),
                &[]
            )
            .is_err()
    );
    assert!(parts.counts().3 > before);
    let before = parts.counts().3;
    parts.limits.operations = before + 1; // Lower this control's remaining pot to one.
    assert!(
        parts
            .untrusted_normalization_context_profiled(
                &scope,
                std::slice::from_ref(&definition.reference),
            )
            .is_err()
    );
    assert_eq!(
        parts.counts().3,
        before + 1,
        "failed work is spent before refusal"
    );
    assert_eq!(parts.context_work_remaining().unwrap(), 0);
    assert!(
        parts
            .normalization_references
            .as_ref()
            .unwrap()
            .has_failed()
    );
    assert!(
        parts
            .untrusted_normalization_context_profiled(&scope, &[definition.reference])
            .is_err()
    );
    assert!(parts.enable_normalization_reference_reuse(&scope).is_err());
    assert_eq!(
        parts.counts().3,
        before + 1,
        "retry never refills the owner pot"
    );
}
