// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::tests::{BooleanReturnModel, bool_eq, proof, target};
use super::*;
use crate::proof_components::{ScopedProofComponentBundle, ScopedProofDeclaration};
use clean_kernel::{BinderInfo, Name, expr::FVarId};

fn bundle(value: bool) -> ScopedProofComponentBundle {
    let goal = bool_eq(value, value);
    let id = FVarId::new(123);
    ScopedProofComponentBundle {
        declarations: vec![ScopedProofDeclaration {
            id,
            name: Name::from_string("checked_component"),
            binder: BinderInfo::Default.into(),
            non_dep: false,
            type_: goal.clone(),
            value: Some(decode_clean_expr_v1(&proof(value)).unwrap()),
        }],
        outer_count: 0,
        root: Expr::fvar(id),
        goal,
        work: None,
    }
}

#[test]
fn scoped_replay_binds_actual_endpoints_model_and_original_bytes() {
    let checker = TranslationRechecker::<BooleanReturnModel>::new(Default::default()).unwrap();
    for value in [false, true] {
        let source = value;
        let module = target(value);
        let artifact = bundle(value);
        let bytes = artifact.encode_with_claim(&bool_eq(value, value)).unwrap();
        let checked = checker
            .recheck_scoped_components_v1(&source, &module, &bytes)
            .unwrap();
        assert!(std::ptr::eq(checked.source(), &source));
        assert!(std::ptr::eq(checked.target(), &module));
        assert!(std::ptr::eq(checked.checker(), &checker));
        assert_eq!(checked.proof_term().as_ptr(), bytes.as_ptr());
        assert_eq!(
            checked.proof_encoding(),
            TranslationProofEncoding::ScopedComponentsV1
        );
        assert!(
            checker
                .recheck_scoped_components_v1(&!source, &module, &bytes)
                .is_err()
        );
        assert!(
            checker
                .recheck_scoped_components_v1(&source, &target(!value), &bytes)
                .is_err()
        );
    }
}

#[test]
fn transported_claim_and_scoped_assumptions_cannot_supply_authority() {
    let checker = TranslationRechecker::<BooleanReturnModel>::new(Default::default()).unwrap();
    let module = target(true);
    let artifact = bundle(true);
    let false_claim = artifact.encode_with_claim(&bool_eq(false, false)).unwrap();
    let error = checker
        .recheck_scoped_components_v1(&true, &module, &false_claim)
        .unwrap_err();
    assert_eq!(error.stage(), "reconstruct");
    for mutation in 0..3 {
        let mut changed = artifact.clone();
        match mutation {
            0 => changed.declarations[0].value = None,
            1 => changed.declarations[0].value = Some(Expr::const_str("True.intro")),
            _ => changed.root = Expr::fvar(FVarId::new(456)),
        }
        let bytes = changed.encode_with_claim(&bool_eq(true, true)).unwrap();
        let error = checker
            .recheck_scoped_components_v1(&true, &module, &bytes)
            .unwrap_err();
        assert_eq!(error.stage(), "kernel audit");
        assert!(!error.reason().contains("BudgetExhausted"));
    }
}

#[test]
fn scoped_carrier_is_explicit_and_bounded_before_reconstruction() {
    struct MustNotReconstruct;
    impl SourceTranslationModel for MustNotReconstruct {
        type Source = ();
        fn build_environment() -> Result<Environment, String> {
            Ok(Environment::with_prelude())
        }
        fn reconstruct(_: &(), _: &Module) -> Result<Expr, String> {
            panic!("a malformed or wrong carrier reached model reconstruction")
        }
    }
    let checker = TranslationRechecker::<MustNotReconstruct>::new(Default::default()).unwrap();
    let module = target(true);
    let legacy = proof(true);
    let dag =
        trust_ir::proof::encode_clean_expr_dag_v2(&decode_clean_expr_v1(&legacy).unwrap()).unwrap();
    let mut bytes = bundle(true)
        .encode_with_claim(&bool_eq(true, true))
        .unwrap();
    bytes.push(0);
    for wrong in [&legacy, &dag, &bytes] {
        assert_eq!(
            checker
                .recheck_scoped_components_v1(&(), &module, wrong)
                .unwrap_err()
                .stage(),
            "decode"
        );
    }
    let bytes = bundle(true)
        .encode_with_claim(&bool_eq(true, true))
        .unwrap();
    let ordinary = TranslationRechecker::<BooleanReturnModel>::new(Default::default()).unwrap();
    assert!(ordinary.recheck(&true, &module, &bytes).is_err());
    assert!(ordinary.recheck_dag_v2(&true, &module, &bytes).is_err());
}

#[test]
fn scoped_replay_uses_verifier_budget_and_restores_it_after_refusal() {
    let limited = TranslationRechecker::<BooleanReturnModel>::new(TranslationCheckLimits {
        heartbeats: NonZeroU32::new(1).unwrap(),
        ..Default::default()
    })
    .unwrap();
    let module = target(true);
    let bytes = bundle(true)
        .encode_with_claim(&bool_eq(true, true))
        .unwrap();
    assert!(
        limited
            .recheck_scoped_components_v1(&true, &module, &bytes)
            .is_err()
    );
    assert_eq!(clean_kernel::tc::declaration_budget_limit(), 0);
    let ordinary = TranslationRechecker::<BooleanReturnModel>::new(Default::default()).unwrap();
    ordinary
        .recheck_scoped_components_v1(&true, &module, &bytes)
        .unwrap();
}

#[test]
fn scoped_rejection_kind_survives_a_large_work_ledger() {
    let checker = TranslationRechecker::<BooleanReturnModel>::new(Default::default()).unwrap();
    let module = target(true);
    let mut artifact = bundle(true);
    for index in 0..80 {
        artifact.declarations.push(ScopedProofDeclaration {
            id: FVarId::new(200 + index),
            name: Name::from_string("checked_unused_value"),
            binder: BinderInfo::Default.into(),
            non_dep: false,
            type_: Expr::const_str("Bool"),
            value: Some(Expr::const_str("Bool.true")),
        });
    }
    artifact.root = Expr::const_str("True.intro");
    let bytes = artifact.encode_with_claim(&bool_eq(true, true)).unwrap();
    let error = checker
        .recheck_scoped_components_v1(&true, &module, &bytes)
        .unwrap_err();
    assert_eq!(error.stage(), "kernel audit");
    assert!(error.reason().contains("TypeMismatch"), "{error}");
    assert!(!error.reason().contains("BudgetExhausted"), "{error}");
    assert!(error.reason().len() <= 1024 + " (truncated)".len());
}
