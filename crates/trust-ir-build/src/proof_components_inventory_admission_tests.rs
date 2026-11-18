// Copyright 2026 Andrew Yates | SPDX-License-Identifier: Apache-2.0
//! Prepaid dynamic inventory admission; no returned inventory is proof evidence.
use super::*;
use crate::{
    cps_image_replay::ImageReplayLimits,
    projected_equality_replay::{
        ProjectedCaseStrategy, replay_projected_equality_with_diagnostics,
    },
    scoped_local::ScopedLocalAllocator,
    semantic_evaluation,
    term_scope::TermScopeLimits,
};
use clean_kernel::{Environment, Level, TypeChecker};

fn n() -> Expr {
    Expr::const_str("Nat")
}
fn parts(scope: &LocalScope, base: Vec<OwnedProofCapture>) -> ProofComponents {
    let mut parts = ProofComponents::new("inventory.admission", ProofLimits::default());
    parts.set_base(scope, base).unwrap();
    parts
}
fn leave(parts: &mut ProofComponents, work: usize) {
    let remaining = parts.context_work_remaining().unwrap();
    parts
        .spend_context_work(remaining.checked_sub(work).unwrap())
        .unwrap();
}
fn environment() -> Environment {
    let mut env = semantic_evaluation::build_environment().unwrap();
    semantic_evaluation::install_case_maps_into(&mut env).unwrap();
    env.init_nat().unwrap();
    env
}
fn identity(scope: &mut LocalScope) -> Expr {
    let x = scope.allocate_local(n()).unwrap();
    x.lam(x.term().clone())
}
fn eq(left: Expr, right: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
        [n(), left, right],
    )
}

#[test]
fn dynamic_inventory_exact_admission_preserves_order_definitions_and_base() {
    let mut scope = LocalScope::new();
    let original = scope.allocate_local(n()).unwrap();
    let x = scope.allocate_local(n()).unwrap();
    let d = scope.allocate_local(n()).unwrap();
    let dynamic = [
        OwnedProofCapture::Parameter(x.clone()),
        OwnedProofCapture::Definition {
            local: d.clone(),
            value: Arc::new(x.term().clone()),
        },
    ];
    let mut parts = parts(&scope, vec![OwnedProofCapture::Parameter(original.clone())]);
    // The existing admission schedule is one unit per retained declaration
    // plus five per supplied capture, even if a later capture proves invalid.
    leave(&mut parts, 11);
    let before = parts.counts();
    let (entries, admitted) = parts
        .normalization_entries_with_dynamic(&scope, &dynamic)
        .unwrap();
    assert_eq!(admitted, 11);
    assert_eq!(parts.context_work_remaining().unwrap(), 0);
    assert_eq!(
        entries
            .iter()
            .map(|(local, _)| local.id())
            .collect::<Vec<_>>(),
        vec![original.id(), x.id(), d.id()]
    );
    assert_eq!(entries[2].1.as_ref(), Some(x.term()));
    let after = parts.counts();
    assert_eq!((after.0, after.1, after.2), (before.0, before.1, before.2));
    assert_eq!(
        after.3 - before.3,
        admitted,
        "the helper owns exactly one debit"
    );
}

#[test]
fn dynamic_inventory_insufficient_work_precedes_foreign_capture_validation() {
    let scope = LocalScope::new();
    let mut foreign_scope = LocalScope::new();
    let foreign = foreign_scope.allocate_local(n()).unwrap();
    for remaining in [0, 4] {
        let mut parts = parts(&scope, vec![]);
        leave(&mut parts, remaining);
        let before = parts.counts();
        for _ in 0..3 {
            let error = parts
                .normalization_entries_with_dynamic(
                    &scope,
                    &[OwnedProofCapture::Parameter(foreign.clone())],
                )
                .err()
                .expect("the inventory must be admitted before its capture loop");
            assert!(error.contains("inventory admission limit"), "{error}");
            assert_eq!(parts.context_work_remaining().unwrap(), remaining);
            assert_eq!(
                parts.counts(),
                before,
                "an unadmitted inventory performs no paid work"
            );
        }
    }
}

#[test]
fn dynamic_inventory_foreign_duplicate_kind_and_value_errors_keep_prepaid_work() {
    for mutation in ["foreign", "duplicate", "kind", "value"] {
        let mut scope = LocalScope::new();
        let retained = scope.allocate_local(n()).unwrap();
        let original = OwnedProofCapture::Definition {
            local: retained.clone(),
            value: Arc::new(Expr::nat_lit(2)),
        };
        let mut parts = parts(&scope, vec![original.clone()]);
        let mut foreign_scope = LocalScope::new();
        let foreign = foreign_scope.allocate_local(n()).unwrap();
        assert_eq!(foreign.id(), retained.id());
        let dynamic = match mutation {
            "foreign" => vec![OwnedProofCapture::Parameter(foreign)],
            "duplicate" => vec![original.clone(), original],
            "kind" => vec![OwnedProofCapture::Parameter(retained)],
            _ => vec![OwnedProofCapture::Definition {
                local: retained,
                value: Arc::new(Expr::nat_lit(3)),
            }],
        };
        let admitted = if mutation == "duplicate" { 11 } else { 6 };
        leave(&mut parts, 2 * admitted);
        for attempt in 0..2 {
            let before = parts.counts();
            let error = parts
                .normalization_entries_with_dynamic(&scope, &dynamic)
                .err()
                .expect("capture identity, kind and exact value checks remain mandatory");
            let expected = if matches!(mutation, "foreign" | "duplicate") {
                "foreign or duplicate"
            } else {
                "changes a retained declaration kind or value"
            };
            assert!(error.contains(expected), "{mutation}: {error}");
            let after = parts.counts();
            assert_eq!((after.0, after.1, after.2), (before.0, before.1, before.2));
            assert_eq!(
                after.3 - before.3,
                admitted,
                "{mutation}: prepaid failure work"
            );
            assert_eq!(
                parts.context_work_remaining().unwrap(),
                if attempt == 0 { admitted } else { 0 }
            );
        }
        let before = parts.counts();
        let error = parts
            .normalization_entries_with_dynamic(&scope, &dynamic)
            .err()
            .unwrap();
        assert!(
            error.contains("inventory admission limit"),
            "{mutation}: {error}"
        );
        assert_eq!(
            parts.counts(),
            before,
            "exhaustion cannot restart the capture walk"
        );
    }
}

#[test]
fn large_retained_prefix_cannot_repeat_an_unadmitted_inventory_walk() {
    let mut scope = LocalScope::new();
    let original = (0..512)
        .map(|_| OwnedProofCapture::Parameter(scope.allocate_local(n()).unwrap()))
        .collect::<Vec<_>>();
    let mut parts = parts(&scope, original);
    let mut foreign_scope = LocalScope::new();
    let foreign = foreign_scope.allocate_local(n()).unwrap();
    leave(&mut parts, 516);
    let before = parts.counts();
    for _ in 0..4 {
        let error = parts
            .normalization_locals_with_dynamic(
                &scope,
                &[OwnedProofCapture::Parameter(foreign.clone())],
            )
            .err()
            .expect("the 517-unit inventory cannot be admitted with only 516");
        assert!(error.contains("inventory admission limit"), "{error}");
        assert_eq!(parts.context_work_remaining().unwrap(), 516);
        assert_eq!(parts.counts(), before);
    }
}

#[test]
fn projected_source_scope_failure_keeps_its_prepaid_inventory_and_closure_work() {
    let env = environment();
    let mut scope = LocalScope::new();
    let x = scope.allocate_local(n()).unwrap();
    let escaped = scope.allocate_local(n()).unwrap();
    let project = identity(&mut scope);
    let mut parts = parts(&scope, vec![]);
    for _ in 0..2 {
        let before = parts.context_work_remaining().unwrap();
        let (result, work) = replay_projected_equality_with_diagnostics(
            &env,
            &mut scope,
            &[],
            &[OwnedProofCapture::Parameter(x.clone())],
            n(),
            n(),
            project.clone(),
            escaped.term().clone(),
            x.term().clone(),
            Level::zero(),
            ImageReplayLimits::default(),
            &mut parts,
            ProjectedCaseStrategy::Structural,
        );
        let error = result.expect_err("the source still contains an escaped local");
        assert!(error.contains("outside its binder scope"), "{error}");
        assert!(!work.initialization_complete);
        assert!(work.initial_capture_context_visits > 0);
        // Failed initialization has no completed normalization report. The
        // actual owner ledger retains the five prepaid inventory units plus
        // every charged closure operation, even on repeated failure.
        assert_eq!(
            before - parts.context_work_remaining().unwrap(),
            5 + work.initial_capture_context_visits
        );
    }
}

#[test]
fn successful_projected_replay_reports_each_inventory_debit_once() {
    let env = environment();
    let mut scope = LocalScope::new();
    let x = scope.allocate_local(n()).unwrap();
    let project = identity(&mut scope);
    let claim = scope
        .close(&x.pi(eq(x.term().clone(), x.term().clone())))
        .unwrap();
    let mut parts = parts(&scope, vec![]);
    let before = parts.context_work_remaining().unwrap();
    let (result, work) = replay_projected_equality_with_diagnostics(
        &env,
        &mut scope,
        &[],
        &[OwnedProofCapture::Parameter(x.clone())],
        n(),
        n(),
        project,
        x.term().clone(),
        x.term().clone(),
        Level::zero(),
        ImageReplayLimits::default(),
        &mut parts,
        ProjectedCaseStrategy::Structural,
    );
    let candidate = result.unwrap();
    assert!(work.initialization_complete);
    assert_eq!(candidate.cases, 0);
    assert_eq!(
        work.normalization_inventory_visits, 10,
        "the two actual inventory constructions each spend five units"
    );
    assert_eq!(
        before - parts.context_work_remaining().unwrap(),
        work.total_context_visits,
        "reporting an admitted fee must not debit it again"
    );
    let _ = TypeChecker::new(&env).infer_type(&claim).unwrap();
    let bundle = parts
        .close_scoped(
            &scope,
            x.lam(candidate.proof),
            x.pi(candidate.component_proposition),
            TermScopeLimits::default(),
        )
        .unwrap();
    let wire = bundle.encode_with_claim(&claim).unwrap();
    let (decoded, frozen) = ScopedProofComponentBundle::decode_with_claim(&wire).unwrap();
    assert_eq!(frozen, claim);
    decoded.replay(&env, &claim, 2_000_000).unwrap();
}
