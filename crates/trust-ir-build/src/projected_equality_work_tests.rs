// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::{tests::*, *};
use crate::{proof_assembly::ProofLimits, scoped_local::LocalScope, term_scope::TermScopeLimits};

pub(super) fn counted(work: &ProjectedEqualityWork) -> usize {
    work.initial_capture_context_visits
        + work.normalization_dependency_visits
        + work.normalization_materialization_visits
        + work.normalization_inventory_visits
        + work.normalization_cached_definition_visits
        + work.identity_materialization_visits
        + work.comparison_materialization_visits
        + work.replacement_reduction_visits
        + work.case_support_visits
        + work.search_visits
        + work.receiver_visits
        + work.index_visits
        + work.replacement_visits
        + work.abstraction_visits
        + work.computation_materialization_visits
        + work.validation_visits
        + work.structural_visits
}

#[test]
fn owned_definition_materialization_preserves_ordinary_projected_frame_proofs() {
    let env = environment();
    for correct in [true, false] {
        let mut results = Vec::new();
        for warm in [false, true] {
            let mut sc = LocalScope::new();
            let (globals, observed, project, mut source, expected) = fixture(&mut sc);
            for _ in 0..48 {
                let unused = sc.allocate_local(n()).unwrap();
                source = unused.let_(Expr::nat_lit(0), source);
            }
            let expected = if correct { expected } else { Expr::nat_lit(5) };
            let external = eq(
                &Level::zero(),
                n(),
                Expr::app(project.clone(), source.clone()),
                expected.clone(),
            );
            let mut parts =
                ProofComponents::new("projection.owned.materialized", ProofLimits::default());
            parts
                .set_base(
                    &sc,
                    globals
                        .iter()
                        .cloned()
                        .map(OwnedProofCapture::Parameter)
                        .collect(),
                )
                .unwrap();
            let definition = parts
                .bind_scoped_owned(&mut sc, &[], observed.clone(), source)
                .unwrap();
            if warm {
                let _materialized = parts
                    .materialize_owned_definition(&sc, &definition.local)
                    .unwrap();
            }
            let (candidate, work) = replay_projected_equality_with_diagnostics(
                &env,
                &mut sc,
                &globals,
                &[],
                observed,
                n(),
                project,
                definition.reference,
                expected,
                Level::zero(),
                ImageReplayLimits::default(),
                &mut parts,
                ProjectedCaseStrategy::Correlated,
            );
            let candidate = candidate.unwrap();
            assert_eq!(work.total_context_visits, counted(&work));
            let claim = sc
                .close(
                    &globals
                        .iter()
                        .rev()
                        .fold(external, |body, local| local.pi(body)),
                )
                .unwrap();
            let root = globals
                .iter()
                .rev()
                .fold(candidate.proof, |body, local| local.lam(body));
            let bundle = parts
                .close_scoped(
                    &sc,
                    root,
                    candidate.component_proposition,
                    TermScopeLimits::default(),
                )
                .unwrap();
            let wire = bundle.encode_with_claim(&claim).unwrap();
            if let Some(directory) =
                std::env::var_os("TRUST_IR_MATERIALIZED_DEFINITION_ARTIFACT_DIR")
            {
                let directory = std::path::PathBuf::from(directory);
                std::fs::create_dir_all(&directory).unwrap();
                std::fs::write(
                    directory.join(format!("frame-correct-{correct}-warm-{warm}.bin")),
                    &wire,
                )
                .unwrap();
            }
            let (decoded, transported) =
                crate::proof_components::ScopedProofComponentBundle::decode_with_claim(&wire)
                    .unwrap();
            assert_eq!(transported, claim);
            assert_eq!(decoded.replay(&env, &claim, 2_000_000).is_ok(), correct);
            results.push((work, wire));
        }
        assert_eq!(
            results[0].1, results[1].1,
            "warming only changes producer work"
        );
        assert_eq!(results[0].0.normalization_cached_definition_visits, 0);
        assert!(results[1].0.normalization_cached_definition_visits > 0);
        assert!(
            results[1].0.normalization_materialization_visits
                < results[0].0.normalization_materialization_visits
        );
        assert!(results[1].0.total_context_visits < results[0].0.total_context_visits);
        eprintln!(
            "ordinary frame correct={correct}: cold={:?}; warm={:?}",
            results[0].0, results[1].0
        );
    }
}

#[test]
fn diagnostics_account_for_work_without_certifying_a_false_frame() {
    let env = environment();
    for (strategy, correct) in [
        (ProjectedCaseStrategy::Structural, true),
        (ProjectedCaseStrategy::Correlated, true),
        (ProjectedCaseStrategy::Correlated, false),
    ] {
        let mut sc = LocalScope::new();
        let (globals, observed, project, source, expected) = fixture(&mut sc);
        let expected = if correct { expected } else { Expr::nat_lit(5) };
        let mut parts = ProofComponents::new("projection.work", ProofLimits::default());
        parts
            .set_base(
                &sc,
                globals
                    .iter()
                    .cloned()
                    .map(OwnedProofCapture::Parameter)
                    .collect(),
            )
            .unwrap();
        let (candidate, work) = replay_projected_equality_with_diagnostics(
            &env,
            &mut sc,
            &globals,
            &[],
            observed,
            n(),
            project,
            source,
            expected,
            Level::zero(),
            ImageReplayLimits::default(),
            &mut parts,
            strategy,
        );
        let candidate = candidate.unwrap();
        assert!(work.initialization_complete);
        assert!(work.normalization_dependency_visits > 0);
        assert!(work.normalization_materialization_visits > 0);
        assert!(work.identity_materialization_visits > 0);
        assert_eq!(work.total_context_visits, counted(&work));
        assert_eq!(
            work.search_visits,
            work.search_unique_visits + work.search_duplicate_visits
        );
        assert_eq!(
            work.first_search_entry_work.is_some(),
            work.search_calls > 0
        );
        assert_eq!(work.cases, candidate.cases);
        eprintln!("projected work ({strategy:?}, correct={correct}): {work:?}");
        let claim = sc
            .close(
                &globals
                    .iter()
                    .rev()
                    .fold(candidate.proposition, |b, l| l.pi(b)),
            )
            .unwrap();
        let root = globals.iter().rev().fold(candidate.proof, |b, l| l.lam(b));
        let bundle = parts
            .close_scoped(
                &sc,
                root,
                candidate.component_proposition,
                TermScopeLimits::default(),
            )
            .unwrap();
        let wire = bundle.encode_with_claim(&claim).unwrap();
        let (transported, same_claim) =
            crate::proof_components::ScopedProofComponentBundle::decode_with_claim(&wire).unwrap();
        assert_eq!(same_claim, claim);
        assert_eq!(transported.replay(&env, &claim, 2_000_000).is_ok(), correct);
    }
}

#[test]
fn diagnostics_retain_initialization_work_when_search_has_no_remaining_budget() {
    let env = environment();
    let mut sc = LocalScope::new();
    let (globals, observed, project, source, expected) = fixture(&mut sc);
    let mut parts = ProofComponents::new("projection.work.refusal", ProofLimits::default());
    parts
        .set_base(
            &sc,
            globals
                .iter()
                .cloned()
                .map(OwnedProofCapture::Parameter)
                .collect(),
        )
        .unwrap();
    let (candidate, work) = replay_projected_equality_with_diagnostics(
        &env,
        &mut sc,
        &globals,
        &[],
        observed,
        n(),
        project,
        source,
        expected,
        Level::zero(),
        ImageReplayLimits {
            max_cases: 1,
            max_app_args: 4,
            ..ImageReplayLimits::default()
        },
        &mut parts,
        ProjectedCaseStrategy::Correlated,
    );
    assert!(candidate.unwrap_err().contains("search work limit"));
    assert!(work.initialization_complete);
    assert!(work.total_context_visits > 4);
    assert_eq!(work.search_visits, 0);
    assert_eq!(work.search_calls, 1);
    assert_eq!(work.search_unique_visits, 0);
    assert_eq!(work.search_duplicate_visits, 0);
    assert_eq!(
        work.first_search_entry_work,
        Some(work.total_context_visits)
    );
    assert_eq!(work.total_context_visits, counted(&work));
    assert_eq!(work.cases, 0);
    eprintln!("projected work (initialization refusal): {work:?}");
}

#[test]
fn diagnostics_distinguish_unperformed_initialization_from_zero_work() {
    let env = environment();
    let mut sc = LocalScope::new();
    let (globals, observed, project, source, expected) = fixture(&mut sc);
    let mut parts = ProofComponents::new("projection.work.not_started", ProofLimits::default());
    let (candidate, work) = replay_projected_equality_with_diagnostics(
        &env,
        &mut sc,
        &globals,
        &[],
        observed,
        n(),
        project,
        source,
        expected,
        Level::zero(),
        ImageReplayLimits {
            heartbeats: 0,
            ..ImageReplayLimits::default()
        },
        &mut parts,
        ProjectedCaseStrategy::Correlated,
    );
    assert!(candidate.unwrap_err().contains("unsupported"));
    assert!(!work.initialization_complete);
    assert_eq!(work, ProjectedEqualityWork::default());
}

#[test]
fn ordinary_one_shot_keeps_its_previously_admitted_context_budget() {
    let env = environment();
    let mut scope = LocalScope::new();
    let (globals, observed, project, mut source, expected) = fixture(&mut scope);
    for _ in 0..48 {
        let unused = scope.allocate_local(n()).unwrap();
        source = unused.let_(Expr::nat_lit(0), source);
    }
    let external = eq(
        &Level::zero(),
        n(),
        Expr::app(project.clone(), source.clone()),
        expected.clone(),
    );
    let mut parts = ProofComponents::new("projection.one.shot.budget", ProofLimits::default());
    parts
        .set_base(
            &scope,
            globals
                .iter()
                .cloned()
                .map(OwnedProofCapture::Parameter)
                .collect(),
        )
        .unwrap();
    let definition = parts
        .bind_scoped_owned(&mut scope, &[], observed.clone(), source)
        .unwrap();
    // This unchanged ordinary graph needs 419 aggregate visits on the original
    // reference walk. Seven cases times 64 arguments leave 448: a narrow but
    // previously admitted one-shot. No reference reuse was requested here.
    let limits = ImageReplayLimits {
        max_cases: 7,
        ..Default::default()
    };
    let (candidate, work) = replay_projected_equality_with_diagnostics(
        &env,
        &mut scope,
        &globals,
        &[],
        observed,
        n(),
        project,
        definition.reference,
        expected,
        Level::zero(),
        limits,
        &mut parts,
        ProjectedCaseStrategy::Correlated,
    );
    let candidate = candidate.expect("unrequested memo work must not shrink one-shot admission");
    assert_eq!(work.total_context_visits, counted(&work));
    assert!(work.total_context_visits < limits.max_cases * limits.max_app_args);
    let claim = scope
        .close(
            &globals
                .iter()
                .rev()
                .fold(external, |body, local| local.pi(body)),
        )
        .unwrap();
    let root = globals
        .iter()
        .rev()
        .fold(candidate.proof, |body, local| local.lam(body));
    let bundle = parts
        .close_scoped(
            &scope,
            root,
            candidate.component_proposition,
            TermScopeLimits::default(),
        )
        .unwrap();
    let wire = bundle.encode_with_claim(&claim).unwrap();
    let (decoded, transported) =
        crate::proof_components::ScopedProofComponentBundle::decode_with_claim(&wire).unwrap();
    assert_eq!(transported, claim);
    decoded.replay(&env, &claim, 2_000_000).unwrap();
    eprintln!("ordinary default one-shot admitted work: {work:?}");
}
