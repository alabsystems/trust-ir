// Copyright 2026 Andrew Yates | Licensed under the Apache License, Version 2.0
//! Ordinary consumers of ordered, untrusted call-local capture telescopes.
use super::*;
use crate::{
    proof_assembly::ProofLimits, proof_components::ScopedProofComponentBundle,
    scoped_local::LocalScope, term_scope::TermScopeLimits,
};
use std::sync::Arc;

fn n() -> Expr {
    Expr::const_str("Nat")
}
fn parts(scope: &LocalScope) -> ProofComponents {
    let mut parts = ProofComponents::new("projected.capture", ProofLimits::default());
    parts.set_base(scope, vec![]).unwrap();
    parts
}
fn identity(scope: &mut LocalScope) -> Expr {
    let x = scope.allocate_local(n()).unwrap();
    x.lam(x.term().clone())
}
fn bind(captures: &[OwnedProofCapture], body: Expr, claim: bool) -> Expr {
    captures
        .iter()
        .rev()
        .fold(body, |body, capture| match capture {
            OwnedProofCapture::Parameter(local) => {
                if claim {
                    local.pi(body)
                } else {
                    local.lam(body)
                }
            }
            OwnedProofCapture::Definition { local, value } => {
                local.let_(value.as_ref().clone(), body)
            }
        })
}
fn round_trip(bundle: &ScopedProofComponentBundle, claim: &Expr) -> ScopedProofComponentBundle {
    let wire = bundle.encode_with_claim(claim).unwrap();
    let (decoded, transported) = ScopedProofComponentBundle::decode_with_claim(&wire).unwrap();
    assert_eq!(&transported, claim);
    decoded
}

#[test]
fn dynamic_parameters_replay_actual_branch_frames_under_both_strategies() {
    let env = tests::environment();
    for strategy in [
        ProjectedCaseStrategy::Structural,
        ProjectedCaseStrategy::Correlated,
    ] {
        let mut scope = LocalScope::new();
        let (locals, observed, project, source, expected) = tests::fixture(&mut scope);
        let dynamic = locals
            .into_iter()
            .map(OwnedProofCapture::Parameter)
            .collect::<Vec<_>>();
        let mut parts = parts(&scope);
        let claim = scope
            .close(&bind(
                &dynamic,
                eq(
                    &Level::zero(),
                    n(),
                    Expr::app(project.clone(), source.clone()),
                    expected.clone(),
                ),
                true,
            ))
            .unwrap();
        let (candidate, work) = replay_projected_equality_with_diagnostics(
            &env,
            &mut scope,
            &[],
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
        );
        let candidate = candidate.unwrap();
        assert!(work.initialization_complete && work.initial_capture_context_visits > 0);
        assert_eq!(work.total_context_visits, work_tests::counted(&work));
        assert!(candidate.cases > 0);
        let bundle = parts
            .close_scoped(
                &scope,
                bind(&dynamic, candidate.proof, false),
                bind(&dynamic, candidate.component_proposition, true),
                TermScopeLimits::default(),
            )
            .unwrap();
        round_trip(&bundle, &claim)
            .replay(&env, &claim, 2_000_000)
            .unwrap();
    }
}

#[test]
fn dependent_parameter_and_let_replay_rejects_changed_definition_and_false_property() {
    let env = tests::environment();
    for false_property in [false, true] {
        let mut scope = LocalScope::new();
        let x = scope.allocate_local(n()).unwrap();
        let h = scope
            .allocate_local(eq(&Level::zero(), n(), x.term().clone(), x.term().clone()))
            .unwrap();
        let d = scope.allocate_local(n()).unwrap();
        let source = Expr::app(Expr::const_str("Nat.succ"), x.term().clone());
        let dynamic = vec![
            OwnedProofCapture::Parameter(x.clone()),
            OwnedProofCapture::Parameter(h),
            OwnedProofCapture::Definition {
                local: d.clone(),
                value: Arc::new(source.clone()),
            },
        ];
        let expected = if false_property {
            Expr::app(Expr::const_str("Nat.succ"), d.term().clone())
        } else {
            d.term().clone()
        };
        let project = identity(&mut scope);
        // Freeze the complete public claim from the actual source and caller
        // telescope, independently of either candidate proposition.
        let claim = scope
            .close(&bind(
                &dynamic,
                eq(
                    &Level::zero(),
                    n(),
                    Expr::app(project.clone(), source.clone()),
                    expected.clone(),
                ),
                true,
            ))
            .unwrap();
        let mut parts = parts(&scope);
        let candidate = replay_projected_equality(
            &env,
            &mut scope,
            &[],
            &dynamic,
            n(),
            n(),
            project,
            source,
            expected,
            Level::zero(),
            ImageReplayLimits::default(),
            &mut parts,
        )
        .unwrap();
        let proof = candidate.proof.clone();
        let bundle = parts
            .close_scoped(
                &scope,
                bind(&dynamic, candidate.proof, false),
                bind(&dynamic, candidate.component_proposition, true),
                TermScopeLimits::default(),
            )
            .unwrap();
        let result = round_trip(&bundle, &claim).replay(&env, &claim, 2_000_000);
        if false_property {
            let error = result
                .err()
                .expect("a false equality is not a capture premise");
            assert!(
                error.contains("TypeMismatch") && !error.contains("BudgetExhausted"),
                "{error}"
            );
        } else {
            result.unwrap();
            // Preserve the frozen TYPE/claim and every other capture. Changing
            // only the actual root let from succ x to x changes its proof.
            let mut changed = dynamic.clone();
            *changed.last_mut().unwrap() = OwnedProofCapture::Definition {
                local: d,
                value: Arc::new(x.term().clone()),
            };
            let mut corrupt = bundle;
            corrupt.root = scope.close(&bind(&changed, proof, false)).unwrap();
            let error = round_trip(&corrupt, &claim)
                .replay(&env, &claim, 2_000_000)
                .err()
                .expect("a changed defining value must not prove the frozen claim");
            assert!(
                error.contains("TypeMismatch") && !error.contains("BudgetExhausted"),
                "{error}"
            );
        }
    }
}

fn refuse(scope: &mut LocalScope, captures: &[OwnedProofCapture], source: Expr) -> String {
    let env = tests::environment();
    let mut parts = parts(scope);
    let project = identity(scope);
    replay_projected_equality(
        &env,
        scope,
        &[],
        captures,
        n(),
        n(),
        project,
        source,
        Expr::nat_lit(0),
        Level::zero(),
        ImageReplayLimits::default(),
        &mut parts,
    )
    .expect_err("malformed or escaped captures must be refused before proof construction")
}

#[test]
fn dynamic_capture_telescope_refuses_foreign_duplicate_reordered_and_missing_locals() {
    let mut scope = LocalScope::new();
    let x = scope.allocate_local(n()).unwrap();
    let mut foreign_scope = LocalScope::new();
    let foreign = foreign_scope.allocate_local(n()).unwrap();
    assert_eq!(foreign.id(), x.id());
    assert_eq!(foreign.term(), x.term());
    let error = refuse(
        &mut scope,
        &[OwnedProofCapture::Parameter(foreign)],
        Expr::nat_lit(0),
    );
    assert!(error.contains("foreign or duplicate"), "{error}");
    let error = refuse(
        &mut scope,
        &[
            OwnedProofCapture::Parameter(x.clone()),
            OwnedProofCapture::Parameter(x.clone()),
        ],
        Expr::nat_lit(0),
    );
    assert!(error.contains("foreign or duplicate"), "{error}");
    let dependent = scope
        .allocate_local(eq(&Level::zero(), n(), x.term().clone(), x.term().clone()))
        .unwrap();
    let error = refuse(
        &mut scope,
        &[
            OwnedProofCapture::Parameter(dependent),
            OwnedProofCapture::Parameter(x.clone()),
        ],
        Expr::nat_lit(0),
    );
    assert!(error.contains("outside its binder scope"), "{error}");
    let error = refuse(&mut scope, &[], x.term().clone());
    assert!(error.contains("outside its binder scope"), "{error}");
}

#[test]
fn dynamic_let_telescope_refuses_self_forward_and_loose_bound_variables() {
    let mut scope = LocalScope::new();
    let d = scope.allocate_local(n()).unwrap();
    let later = scope.allocate_local(n()).unwrap();
    for (definition, suffix) in [
        (d.term().clone(), vec![]),
        (
            later.term().clone(),
            vec![OwnedProofCapture::Parameter(later)],
        ),
    ] {
        let mut dynamic = vec![OwnedProofCapture::Definition {
            local: d.clone(),
            value: Arc::new(definition),
        }];
        dynamic.extend(suffix);
        // Even an unused declaration must obey its actual preceding prefix.
        let error = refuse(&mut scope, &dynamic, Expr::nat_lit(0));
        assert!(error.contains("outside its binder scope"), "{error}");
    }
    let loose_type = scope.allocate_local(Expr::bvar(0)).unwrap();
    let error = refuse(
        &mut scope,
        &[OwnedProofCapture::Parameter(loose_type)],
        Expr::nat_lit(0),
    );
    assert!(error.contains("loose ordinary bound variables"), "{error}");
    let error = refuse(
        &mut scope,
        &[OwnedProofCapture::Definition {
            local: d,
            value: Arc::new(Expr::bvar(0)),
        }],
        Expr::nat_lit(0),
    );
    assert!(error.contains("loose ordinary bound variables"), "{error}");
}

#[test]
fn temporary_definition_contexts_do_not_extend_base_or_reuse_previous_values() {
    let env = tests::environment();
    let mut scope = LocalScope::new();
    let d = scope.allocate_local(n()).unwrap();
    let mut parts = parts(&scope);
    parts.enable_normalization_reference_reuse(&scope).unwrap();
    let before = parts.counts();
    for value in [0, 1, 0] {
        let dynamic = [OwnedProofCapture::Definition {
            local: d.clone(),
            value: Arc::new(Expr::nat_lit(value)),
        }];
        let (context, locals, work) = parts
            .untrusted_normalization_context_with_captures_profiled(
                &scope,
                std::slice::from_ref(d.term()),
                &dynamic,
            )
            .unwrap();
        assert_eq!(locals.len(), 1);
        assert_eq!(
            TypeChecker::with_context(&env, context).whnf(d.term()),
            Expr::nat_lit(value)
        );
        assert!(work.dependency_visits > 0 && work.inventory_visits > 0);
        let now = parts.counts();
        assert_eq!((now.0, now.1, now.2), (before.0, before.1, before.2));
        assert!(
            now.3 > before.3,
            "temporary scans spend the original owner ledger"
        );
    }
}

#[test]
fn dynamic_capture_initialization_cannot_reset_an_exhausted_owner_budget() {
    let env = tests::environment();
    let mut scope = LocalScope::new();
    let x = scope.allocate_local(n()).unwrap();
    let mut parts = parts(&scope);
    let remaining = parts.context_work_remaining().unwrap();
    parts.spend_context_work(remaining - 8).unwrap();
    let project = identity(&mut scope);
    for attempt in 0..2 {
        let before = parts.context_work_remaining().unwrap();
        let error = replay_projected_equality(
            &env,
            &mut scope,
            &[],
            &[OwnedProofCapture::Parameter(x.clone())],
            n(),
            n(),
            project.clone(),
            x.term().clone(),
            x.term().clone(),
            Level::zero(),
            ImageReplayLimits::default(),
            &mut parts,
        )
        .expect_err("dynamic closure must respect the already spent owner budget");
        assert!(error.contains("admission limit"), "{error}");
        // One admitted dynamic inventory costs five units. Its first
        // construction stays paid when the later closure cannot be admitted;
        // the retry cannot fund another inventory and performs no such work.
        assert_eq!(parts.context_work_remaining().unwrap(), 3);
        assert_eq!(
            before - parts.context_work_remaining().unwrap(),
            if attempt == 0 { 5 } else { 0 }
        );
    }
}

#[test]
fn unused_ill_typed_dynamic_definition_remains_in_complete_replay() {
    let env = tests::environment();
    let mut scope = LocalScope::new();
    let unused = scope.allocate_local(n()).unwrap();
    let dynamic = [OwnedProofCapture::Definition {
        local: unused,
        value: Arc::new(Expr::const_str("Bool.false")),
    }];
    let project = identity(&mut scope);
    let mut parts = parts(&scope);
    let candidate = replay_projected_equality(
        &env,
        &mut scope,
        &[],
        &dynamic,
        n(),
        n(),
        project,
        Expr::nat_lit(0),
        Expr::nat_lit(0),
        Level::zero(),
        ImageReplayLimits::default(),
        &mut parts,
    )
    .unwrap();
    // Scope materialization is not typing evidence. This independently frozen
    // true claim supplies no premise for the malformed unused let in the root.
    let claim = eq(&Level::zero(), n(), Expr::nat_lit(0), Expr::nat_lit(0));
    let _claim_sort = TypeChecker::new(&env).infer_type(&claim).unwrap();
    let bundle = parts
        .close_scoped(
            &scope,
            bind(&dynamic, candidate.proof, false),
            candidate.component_proposition,
            TermScopeLimits::default(),
        )
        .unwrap();
    let error = round_trip(&bundle, &claim)
        .replay(&env, &claim, 2_000_000)
        .err()
        .expect("complete replay must check the unused ill-typed definition");
    assert!(
        error.contains("TypeMismatch") && !error.contains("BudgetExhausted"),
        "{error}"
    );
}
