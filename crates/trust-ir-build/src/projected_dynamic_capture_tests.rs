// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//! Dynamic binders remain distinct from ambient globals and complete replay.
use super::{tests::*, *};
use crate::{proof_assembly::ProofLimits, scoped_local::LocalScope, term_scope::TermScopeLimits};
use std::sync::Arc;

fn check_replay<T>(result: Result<T, String>, valid: bool) {
    if valid {
        result.unwrap();
    } else {
        let error = result
            .err()
            .expect("strict replay must reject the false or invalid carrier");
        assert!(error.contains("TypeMismatch"), "{error}");
        assert!(!error.contains("BudgetExhausted"), "{error}");
        assert!(!error.contains("HeartbeatExceeded"), "{error}");
    }
}

#[test]
fn projected_dynamic_parameter_replays_original_claim_and_cold_invalid_definition() {
    let mut env = environment();
    env.init_true_false().unwrap();
    for strategy in [
        ProjectedCaseStrategy::Structural,
        ProjectedCaseStrategy::Correlated,
    ] {
        for (correct, cold_invalid) in [(true, false), (false, false), (true, true)] {
            let mut scope = LocalScope::new();
            let (parameters, observed, project, source, expected) = fixture(&mut scope);
            let globals = &parameters[..1];
            let dynamic = vec![OwnedProofCapture::Parameter(parameters[1].clone())];
            let expected = if correct { expected } else { Expr::nat_lit(5) };
            let frozen = eq(
                &Level::zero(),
                n(),
                Expr::app(project.clone(), source.clone()),
                expected.clone(),
            );
            let mut parts =
                ProofComponents::new("projection.dynamic.parameter", ProofLimits::default());
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
            if cold_invalid {
                parts
                    .bind_scoped_owned(&mut scope, &[], n(), Expr::const_str("True.intro"))
                    .unwrap();
            }
            let candidate = replay_projected_equality_with_strategy(
                &env,
                &mut scope,
                globals,
                &dynamic,
                observed,
                n(),
                project,
                source,
                expected,
                Level::zero(),
                ImageReplayLimits::default(),
                &mut parts,
                strategy,
            )
            .unwrap();
            let claim = scope
                .close(&parameters.iter().rev().fold(frozen, |body, p| p.pi(body)))
                .unwrap();
            let goal = parameters[1].pi(candidate.component_proposition);
            let root = parameters
                .iter()
                .rev()
                .fold(candidate.proof, |body, p| p.lam(body));
            let bundle = parts
                .close_scoped(&scope, root, goal, TermScopeLimits::default())
                .unwrap();
            let wire = bundle.encode_with_claim(&claim).unwrap();
            let (decoded, transported) =
                crate::proof_components::ScopedProofComponentBundle::decode_with_claim(&wire)
                    .unwrap();
            assert_eq!(transported, claim);
            check_replay(
                decoded.replay(&env, &claim, 2_000_000),
                correct && !cold_invalid,
            );
        }
    }
}

#[test]
fn projected_dynamic_definition_normalizes_real_value_and_rejects_changed_capture_value() {
    let env = environment();
    for strategy in [
        ProjectedCaseStrategy::Structural,
        ProjectedCaseStrategy::Correlated,
    ] {
        for changed in [false, true] {
            let mut scope = LocalScope::new();
            let (parameters, observed, project, source, _) = fixture(&mut scope);
            let globals = &parameters[..1];
            let state = &parameters[1];
            let pair = |last| {
                at(
                    "Prod.mk",
                    vec![Level::zero(); 2],
                    [n(), n(), Expr::nat_lit(1), Expr::nat_lit(last)],
                )
            };
            let actual_value = pair(2);
            let alleged_value = pair(if changed { 3 } else { 2 });
            let expected = Expr::nat_lit(if changed { 3 } else { 2 });
            let frozen = eq(
                &Level::zero(),
                n(),
                Expr::app(project.clone(), source.clone()),
                expected.clone(),
            );
            let dynamic = [OwnedProofCapture::Definition {
                local: state.clone(),
                value: Arc::new(alleged_value),
            }];
            let mut parts =
                ProofComponents::new("projection.dynamic.definition", ProofLimits::default());
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
            // A genuine materialized retained definition must not make a
            // temporary dynamic definition look like a cached component slot.
            let retained = parts
                .bind_scoped_owned(&mut scope, &[], n(), Expr::nat_lit(0))
                .unwrap();
            assert_eq!(
                parts
                    .materialize_owned_definition(&scope, &retained.local)
                    .unwrap(),
                Expr::nat_lit(0)
            );
            let candidate = replay_projected_equality_with_strategy(
                &env,
                &mut scope,
                globals,
                &dynamic,
                observed,
                n(),
                project,
                source,
                expected,
                Level::zero(),
                ImageReplayLimits::default(),
                &mut parts,
                strategy,
            )
            .unwrap();
            let claim = scope
                .close(&globals[0].pi(state.let_(actual_value.clone(), frozen.clone())))
                .unwrap();
            let root = globals[0].lam(state.let_(actual_value.clone(), candidate.proof));
            // Freeze the original goal independently of the producer's
            // proposition under its alleged defining value. A changed value
            // must not avoid the actual body's strict type check.
            let goal = state.let_(actual_value, frozen);
            let bundle = parts
                .close_scoped(&scope, root, goal, TermScopeLimits::default())
                .unwrap();
            let wire = bundle.encode_with_claim(&claim).unwrap();
            let (decoded, transported) =
                crate::proof_components::ScopedProofComponentBundle::decode_with_claim(&wire)
                    .unwrap();
            assert_eq!(transported, claim);
            check_replay(decoded.replay(&env, &claim, 2_000_000), !changed);
        }
    }
}

#[test]
fn projected_dynamic_dependent_telescope_and_lexical_definition_replay() {
    let env = environment();
    for strategy in [
        ProjectedCaseStrategy::Structural,
        ProjectedCaseStrategy::Correlated,
    ] {
        for overlap in [false, true] {
            let mut scope = LocalScope::new();
            let type_ = scope.allocate_local(Expr::type_()).unwrap();
            let value = scope.allocate_local(type_.term().clone()).unwrap();
            let alias = scope.allocate_local(type_.term().clone()).unwrap();
            let input = scope.allocate_local(type_.term().clone()).unwrap();
            let project = input.lam(input.term().clone());
            let frozen = eq(
                &Level::zero(),
                type_.term().clone(),
                Expr::app(project.clone(), alias.term().clone()),
                value.term().clone(),
            );
            let dynamic = [
                OwnedProofCapture::Parameter(type_.clone()),
                OwnedProofCapture::Parameter(value.clone()),
                OwnedProofCapture::Definition {
                    local: alias.clone(),
                    value: Arc::new(value.term().clone()),
                },
            ];
            let mut parts =
                ProofComponents::new("projection.dynamic.dependent", ProofLimits::default());
            let globals = if overlap { vec![type_.clone()] } else { vec![] };
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
            let candidate = replay_projected_equality_with_strategy(
                &env,
                &mut scope,
                &globals,
                &dynamic,
                type_.term().clone(),
                type_.term().clone(),
                project,
                alias.term().clone(),
                value.term().clone(),
                Level::zero(),
                ImageReplayLimits::default(),
                &mut parts,
                strategy,
            )
            .unwrap();
            let close = |body: Expr, proof| {
                let body = alias.let_(value.term().clone(), body);
                if proof {
                    type_.lam(value.lam(body))
                } else {
                    type_.pi(value.pi(body))
                }
            };
            let claim = scope.close(&close(frozen, false)).unwrap();
            let bundle = parts
                .close_scoped(
                    &scope,
                    close(candidate.proof, true),
                    if overlap {
                        value.pi(alias.let_(value.term().clone(), candidate.component_proposition))
                    } else {
                        close(candidate.component_proposition, false)
                    },
                    TermScopeLimits::default(),
                )
                .unwrap();
            let wire = bundle.encode_with_claim(&claim).unwrap();
            let (decoded, transported) =
                crate::proof_components::ScopedProofComponentBundle::decode_with_claim(&wire)
                    .unwrap();
            assert_eq!(transported, claim);
            decoded.replay(&env, &claim, 2_000_000).unwrap();
        }
    }
}

#[test]
fn projected_dynamic_missing_foreign_duplicate_and_forward_captures_refuse() {
    let env = environment();
    for mode in [
        "missing",
        "foreign",
        "duplicate",
        "forward-type",
        "forward-value",
    ] {
        let mut scope = LocalScope::new();
        let (parameters, observed, project, source, expected) = fixture(&mut scope);
        let mut foreign = LocalScope::new();
        let mut dynamic = match mode {
            "missing" => vec![],
            "foreign" => vec![OwnedProofCapture::Parameter(
                foreign.allocate_local(n()).unwrap(),
            )],
            "duplicate" => vec![OwnedProofCapture::Parameter(parameters[1].clone()); 2],
            "forward-type" => {
                let type_ = scope.allocate_local(Expr::type_()).unwrap();
                let value = scope.allocate_local(type_.term().clone()).unwrap();
                vec![
                    OwnedProofCapture::Parameter(value),
                    OwnedProofCapture::Parameter(type_),
                ]
            }
            _ => {
                let a = scope.allocate_local(n()).unwrap();
                let b = scope.allocate_local(n()).unwrap();
                vec![
                    OwnedProofCapture::Definition {
                        local: a,
                        value: Arc::new(b.term().clone()),
                    },
                    OwnedProofCapture::Parameter(b),
                ]
            }
        };
        if mode.starts_with("forward") {
            // Keep every body input valid so only the bad capture telescope
            // can account for this refusal.
            dynamic.insert(0, OwnedProofCapture::Parameter(parameters[1].clone()));
        }
        let mut parts = ProofComponents::new("projection.dynamic.invalid", ProofLimits::default());
        parts
            .set_base(
                &scope,
                vec![OwnedProofCapture::Parameter(parameters[0].clone())],
            )
            .unwrap();
        let error = replay_projected_equality_with_strategy(
            &env,
            &mut scope,
            &parameters[..1],
            &dynamic,
            observed,
            n(),
            project,
            source,
            expected,
            Level::zero(),
            ImageReplayLimits::default(),
            &mut parts,
            ProjectedCaseStrategy::Correlated,
        )
        .unwrap_err();
        assert!(!error.contains("BudgetExhausted"), "{mode}: {error}");
        assert!(!error.contains("HeartbeatExceeded"), "{mode}: {error}");
        if mode.starts_with("forward") || mode == "missing" {
            assert!(
                error.contains("outside its binder scope"),
                "{mode}: {error}"
            );
        } else {
            assert!(error.contains("foreign or duplicate"), "{mode}: {error}");
        }
    }
}

#[test]
fn projected_dynamic_retained_definition_cannot_change_kind_or_value() {
    let env = environment();
    for mutation in ["same", "parameter", "value"] {
        let mut scope = LocalScope::new();
        let mut parts = ProofComponents::new("projection.dynamic.retained", ProofLimits::default());
        parts.set_base(&scope, vec![]).unwrap();
        let original = parts
            .bind_scoped_owned(&mut scope, &[], n(), Expr::nat_lit(2))
            .unwrap();
        let input = scope.allocate_local(n()).unwrap();
        let dynamic = [if mutation == "parameter" {
            OwnedProofCapture::Parameter(original.local)
        } else {
            OwnedProofCapture::Definition {
                local: original.local,
                value: Arc::new(Expr::nat_lit(if mutation == "value" { 3 } else { 2 })),
            }
        }];
        let result = replay_projected_equality_with_strategy(
            &env,
            &mut scope,
            &[],
            &dynamic,
            n(),
            n(),
            input.lam(input.term().clone()),
            original.reference,
            Expr::nat_lit(2),
            Level::zero(),
            ImageReplayLimits::default(),
            &mut parts,
            ProjectedCaseStrategy::Correlated,
        );
        if mutation == "same" {
            let candidate = result.unwrap();
            let claim = eq(&Level::zero(), n(), Expr::nat_lit(2), Expr::nat_lit(2));
            let bundle = parts
                .close_scoped(
                    &scope,
                    candidate.proof,
                    candidate.component_proposition,
                    TermScopeLimits::default(),
                )
                .unwrap();
            let wire = bundle.encode_with_claim(&claim).unwrap();
            let (decoded, transported) =
                crate::proof_components::ScopedProofComponentBundle::decode_with_claim(&wire)
                    .unwrap();
            assert_eq!(transported, claim);
            decoded.replay(&env, &claim, 2_000_000).unwrap();
        } else {
            let error = result.unwrap_err();
            assert!(
                error.contains("retained") && error.contains("capture"),
                "{error}"
            );
        }
    }
}
