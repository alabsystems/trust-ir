// Copyright 2026 Andrew Yates | SPDX-License-Identifier: Apache-2.0
use super::equation_tests::{app, environment, fixture, n};
use super::*;
fn check(failing: bool, bad: bool, cold: bool) {
    let env = environment();
    let (mut scope, mut parts, equation, original, run) = fixture(failing, bad, false);
    if cold {
        parts
            .bind_scoped_owned(&mut scope, &[], n(), Expr::const_str("True.intro"))
            .unwrap();
    }
    let candidate = replay_image_with_structured_call_equations(
        &env,
        &mut scope,
        &[equation.operator.clone(), equation.proof.local.clone()],
        &[],
        ImageTypes {
            state: n(),
            error: n(),
            value: n(),
            answer: n(),
        },
        equation.operator.term().clone(),
        Level::zero(),
        Default::default(),
        &mut parts,
        &[OwnedCpsCallEquation::from(equation)],
    )
    .unwrap();
    assert_eq!(
        candidate
            .construction
            .input
            .lam(candidate.construction.root.observation.clone()),
        candidate.image.run
    );
    let image = candidate.image;
    let claim = scope
        .close(&app(CPS_IMAGE, [n(), n(), n(), n(), run, original]))
        .unwrap();
    let bundle = parts
        .close_scoped(
            &scope,
            image.proof,
            image.component_proposition.unwrap(),
            Default::default(),
        )
        .unwrap();
    let bytes = bundle.encode_with_claim(&claim).unwrap();
    let (decoded, transported) =
        crate::proof_components::ScopedProofComponentBundle::decode_with_claim(&bytes).unwrap();
    assert_eq!(claim, transported);
    assert!(TypeChecker::new(&env).infer_sort(&claim).unwrap().is_zero());
    let result = decoded.replay(&env, &claim, 2_000_000);
    if bad || cold {
        assert!(
            result
                .err()
                .expect("invalid retained original must reject")
                .contains("TypeMismatch")
        );
    } else {
        result.unwrap();
    }
}
#[test]
fn cps_image_replay_structured_actual_normal_and_error() {
    check(false, false, false);
    check(true, false, false);
}
#[test]
fn cps_image_replay_structured_original_equations_and_cold_declarations_must_check() {
    check(false, true, false);
    check(true, true, false);
    check(false, false, true);
}
#[test]
fn cps_image_replay_structured_circular_equation_refuses() {
    let env = environment();
    let (mut scope, mut parts, equation, _, _) = fixture(false, false, true);
    let result = replay_image_with_structured_call_equations(
        &env,
        &mut scope,
        &[equation.operator.clone(), equation.proof.local.clone()],
        &[],
        ImageTypes {
            state: n(),
            error: n(),
            value: n(),
            answer: n(),
        },
        equation.operator.term().clone(),
        Level::zero(),
        Default::default(),
        &mut parts,
        &[OwnedCpsCallEquation::from(equation)],
    );
    assert!(
        result
            .expect_err("invalid retained original must reject")
            .contains("literal TO_CPS")
    );
}

#[test]
fn cps_image_replay_structured_normal_handler_errors_escape_operation_error_handler() {
    for failing_operation in [false, true] {
        let env = environment();
        let (mut scope, mut parts, equation, original, _) =
            fixture(failing_operation, false, false);
        let state = scope.try_local(n()).unwrap();
        let callback_type = Expr::arrow(n(), Expr::arrow(n(), n()));
        let ok = scope.try_local(callback_type.clone()).unwrap();
        let err = scope.try_local(callback_type).unwrap();
        let next = scope.try_local(n()).unwrap();
        let value = scope.try_local(n()).unwrap();
        // A normal return fails downstream; the operation's error handler
        // instead returns normal99. A bind-then-catch implementation is wrong.
        let yes = next.lam(value.lam(Expr::apps(
            err.term().clone(),
            [next.term().clone(), Expr::nat_lit(42)],
        )));
        let no = next.lam(value.lam(Expr::apps(
            ok.term().clone(),
            [next.term().clone(), Expr::nat_lit(99)],
        )));
        let source = state.lam(ok.lam(err.lam(Expr::apps(
            equation.operator.term().clone(),
            [state.term().clone(), yes.clone(), no.clone()],
        ))));
        let original_source =
            state.lam(ok.lam(err.lam(Expr::apps(original, [state.term().clone(), yes, no]))));
        let expected_run = super::equation_tests::run(
            &mut scope,
            !failing_operation,
            if failing_operation { 99 } else { 42 },
        );
        let claim = scope
            .close(&app(
                CPS_IMAGE,
                [n(), n(), n(), n(), expected_run, original_source],
            ))
            .unwrap();
        let candidate = replay_image_with_structured_call_equations(
            &env,
            &mut scope,
            &[equation.operator.clone(), equation.proof.local.clone()],
            &[],
            ImageTypes {
                state: n(),
                error: n(),
                value: n(),
                answer: n(),
            },
            source,
            Level::zero(),
            Default::default(),
            &mut parts,
            &[OwnedCpsCallEquation::from(equation)],
        )
        .unwrap();
        assert_eq!(
            candidate
                .construction
                .input
                .lam(candidate.construction.root.observation.clone()),
            candidate.image.run
        );
        let image = candidate.image;
        let bundle = parts
            .close_scoped(
                &scope,
                image.proof,
                image.component_proposition.unwrap(),
                Default::default(),
            )
            .unwrap();
        let bytes = bundle.encode_with_claim(&claim).unwrap();
        let (decoded, actual_claim) =
            crate::proof_components::ScopedProofComponentBundle::decode_with_claim(&bytes).unwrap();
        assert_eq!(actual_claim, claim);
        assert!(TypeChecker::new(&env).infer_sort(&claim).unwrap().is_zero());
        decoded.replay(&env, &claim, 2_000_000).unwrap();
    }
}

fn opaque_equation_fixture(
    dependent: bool,
) -> (
    crate::scoped_local::LocalScope,
    ProofComponents,
    CpsCallEquation,
    Expr,
    Option<ScopedLocal>,
    Expr,
) {
    use crate::scoped_local::LocalScope;
    let mut scope = LocalScope::new();
    let outcome_type = Expr::apps(
        constant("Except", vec![Level::zero(), Level::zero()]),
        [n(), n()],
    );
    let observed_type = pair_type(&Level::zero(), n(), outcome_type.clone());
    let run_type = Expr::arrow(n(), observed_type);
    let actual = scope.try_local(run_type).unwrap();
    let mut parts = ProofComponents::new("structured.opaque.run", Default::default());
    parts
        .set_base(
            &scope,
            if dependent {
                vec![]
            } else {
                vec![OwnedProofCapture::Parameter(actual.clone())]
            },
        )
        .unwrap();
    let state = scope.try_local(n()).unwrap();
    let callback_type = Expr::arrow(n(), Expr::arrow(n(), n()));
    let yes = scope.try_local(callback_type.clone()).unwrap();
    let no = scope.try_local(callback_type.clone()).unwrap();
    let run = if dependent {
        let run_state = scope.try_local(n()).unwrap();
        let value = Expr::apps(
            yes.term().clone(),
            [run_state.term().clone(), Expr::nat_lit(5)],
        );
        let tag = Expr::apps(
            constant("Except.ok", vec![Level::zero(), Level::zero()]),
            [n(), n(), value],
        );
        run_state.lam(Expr::apps(
            constant("Prod.mk", vec![Level::zero(), Level::zero()]),
            [n(), outcome_type.clone(), run_state.term().clone(), tag],
        ))
    } else {
        actual.term().clone()
    };
    let rhs = app(
        TO_CPS,
        [
            n(),
            n(),
            n(),
            n(),
            run.clone(),
            state.term().clone(),
            yes.term().clone(),
            no.term().clone(),
        ],
    );
    let original = state.lam(yes.lam(no.lam(rhs.clone())));
    let cps_type = Expr::arrow(
        n(),
        Expr::arrow(callback_type.clone(), Expr::arrow(callback_type, n())),
    );
    let operator = parts
        .bind_scoped_owned(&mut scope, &[], cps_type, original.clone())
        .unwrap();
    let args = [state.term().clone(), yes.term().clone(), no.term().clone()];
    let statement = state.pi(yes.pi(no.pi(Expr::apps(
        constant("Eq", vec![Level::succ(Level::zero())]),
        [
            n(),
            Expr::apps(operator.reference.clone(), args),
            rhs.clone(),
        ],
    ))));
    let value = state.lam(yes.lam(no.lam(Expr::apps(
        constant("Eq.refl", vec![Level::succ(Level::zero())]),
        [n(), rhs],
    ))));
    let proof = parts
        .bind_scoped_owned(&mut scope, &[], statement, value)
        .unwrap();
    (
        scope,
        parts,
        CpsCallEquation {
            operator: operator.local,
            replacement: original.clone(),
            proof,
            arity: 3,
        },
        original,
        (!dependent).then_some(actual),
        run,
    )
}
#[test]
fn cps_image_replay_structured_accepts_genuine_opaque_run_with_both_arbitrary_postworlds() {
    let env = environment();
    let (mut scope, mut parts, equation, original, actual, run) = opaque_equation_fixture(false);
    let actual = actual.unwrap();
    let payload = scope.try_local(n()).unwrap();
    let state = scope.try_local(n()).unwrap();
    let outcome_type = Expr::apps(
        constant("Except", vec![Level::zero(), Level::zero()]),
        [n(), n()],
    );
    let handler_state = scope.try_local(n()).unwrap();
    let handler = |tag| {
        payload.lam(handler_state.lam(Expr::apps(
            constant("Prod.mk", vec![Level::zero(), Level::zero()]),
            [
                n(),
                outcome_type.clone(),
                handler_state.term().clone(),
                Expr::apps(
                    constant(tag, vec![Level::zero(), Level::zero()]),
                    [n(), n(), payload.term().clone()],
                ),
            ],
        )))
    };
    let expected = state.lam(app(
        crate::semantic_evaluation::HANDLE,
        [
            n(),
            n(),
            n(),
            n(),
            n(),
            run,
            handler("Except.ok"),
            handler("Except.error"),
            state.term().clone(),
        ],
    ));
    let claim = scope
        .close(&actual.pi(app(CPS_IMAGE, [n(), n(), n(), n(), expected, original])))
        .unwrap();
    let candidate = replay_image_with_structured_call_equations(
        &env,
        &mut scope,
        &[
            actual.clone(),
            equation.operator.clone(),
            equation.proof.local.clone(),
        ],
        &[],
        ImageTypes {
            state: n(),
            error: n(),
            value: n(),
            answer: n(),
        },
        equation.operator.term().clone(),
        Level::zero(),
        Default::default(),
        &mut parts,
        &[OwnedCpsCallEquation::from(equation)],
    )
    .unwrap();
    assert_eq!(
        candidate
            .construction
            .input
            .lam(candidate.construction.root.observation.clone()),
        candidate.image.run
    );
    let image = candidate.image;
    let bundle = parts
        .close_scoped(
            &scope,
            actual.lam(image.proof),
            image.component_proposition.unwrap(),
            Default::default(),
        )
        .unwrap();
    let bytes = bundle.encode_with_claim(&claim).unwrap();
    let (decoded, transported) =
        crate::proof_components::ScopedProofComponentBundle::decode_with_claim(&bytes).unwrap();
    assert_eq!(claim, transported);
    assert!(TypeChecker::new(&env).infer_sort(&claim).unwrap().is_zero());
    decoded.replay(&env, &claim, 2_000_000).unwrap();
}
#[test]
fn cps_image_replay_structured_refuses_callback_dependent_run() {
    let env = environment();
    let (mut scope, mut parts, equation, _, _, _) = opaque_equation_fixture(true);
    let result = replay_image_with_structured_call_equations(
        &env,
        &mut scope,
        &[equation.operator.clone(), equation.proof.local.clone()],
        &[],
        ImageTypes {
            state: n(),
            error: n(),
            value: n(),
            answer: n(),
        },
        equation.operator.term().clone(),
        Level::zero(),
        Default::default(),
        &mut parts,
        &[OwnedCpsCallEquation::from(equation)],
    );
    assert!(
        result
            .unwrap_err()
            .contains("depends on final CPS callbacks")
    );
}

#[test]
fn cps_image_replay_lazy_owned_equations_still_replay_unused_invalid_definition() {
    let env = environment();
    let (mut scope, mut parts, equation, original, run) = fixture(false, false, false);
    let unused_operator = parts
        .bind_scoped_owned(
            &mut scope,
            &[],
            equation.operator.ty().clone(),
            equation.replacement.clone(),
        )
        .unwrap();
    let unused_proof = parts
        .bind_scoped_owned(
            &mut scope,
            &[],
            equation.proof.local.ty().clone(),
            Expr::const_str("True.intro"),
        )
        .unwrap();
    let equations = [
        OwnedCpsCallEquation::from(&equation),
        OwnedCpsCallEquation {
            operator: unused_operator.local.clone(),
            proof: unused_proof.clone(),
            arity: 3,
        },
    ];
    let candidate = replay_image_with_structured_call_equations(
        &env,
        &mut scope,
        &[
            equation.operator.clone(),
            equation.proof.local.clone(),
            unused_operator.local,
            unused_proof.local,
        ],
        &[],
        ImageTypes {
            state: n(),
            error: n(),
            value: n(),
            answer: n(),
        },
        equation.operator.term().clone(),
        Level::zero(),
        Default::default(),
        &mut parts,
        &equations,
    )
    .unwrap();
    let claim = scope
        .close(&app(CPS_IMAGE, [n(), n(), n(), n(), run, original]))
        .unwrap();
    let image = candidate.image;
    let bundle = parts
        .close_scoped(
            &scope,
            image.proof,
            image.component_proposition.unwrap(),
            Default::default(),
        )
        .unwrap();
    let bytes = bundle.encode_with_claim(&claim).unwrap();
    let (decoded, transported) =
        crate::proof_components::ScopedProofComponentBundle::decode_with_claim(&bytes).unwrap();
    assert_eq!(claim, transported);
    assert!(TypeChecker::new(&env).infer_sort(&claim).unwrap().is_zero());
    let error = decoded
        .replay(&env, &claim, 2_000_000)
        .err()
        .expect("unused invalid equation must reject");
    assert!(
        error.contains("TypeMismatch") && !error.contains("BudgetExhausted"),
        "{error}"
    );
}

#[test]
fn cps_image_replay_structured_sibling_continuations_share_callbacks_but_keep_payloads() {
    for failing_operation in [false, true] {
        let env = environment();
        let (mut scope, mut parts, equation, original, _) =
            fixture(failing_operation, false, false);
        let state = scope.try_local(n()).unwrap();
        let callback_type = Expr::arrow(n(), Expr::arrow(n(), n()));
        let ok = scope.try_local(callback_type.clone()).unwrap();
        let err = scope.try_local(callback_type).unwrap();
        let post = scope.try_local(n()).unwrap();
        let payload = scope.try_local(n()).unwrap();
        let mut value = payload.term().clone();
        for _ in 0..64 {
            value = Expr::app(Expr::const_str("Nat.succ"), value);
        }
        // Both original arms are one shared graph. The error payload must
        // reach the success callback too; using the other arm's payload or
        // poststate cannot satisfy this independently frozen original claim.
        let callback =
            post.lam(payload.lam(Expr::apps(ok.term().clone(), [post.term().clone(), value])));
        let args = [state.term().clone(), callback.clone(), callback];
        let source =
            state.lam(ok.lam(err.lam(Expr::apps(equation.operator.term().clone(), args.clone()))));
        let original = state.lam(ok.lam(err.lam(Expr::apps(original, args))));
        let expected =
            super::equation_tests::run(&mut scope, false, if failing_operation { 71 } else { 69 });
        let claim = scope
            .close(&app(CPS_IMAGE, [n(), n(), n(), n(), expected, original]))
            .unwrap();
        let candidate = replay_image_with_structured_call_equations(
            &env,
            &mut scope,
            &[equation.operator.clone(), equation.proof.local.clone()],
            &[],
            ImageTypes {
                state: n(),
                error: n(),
                value: n(),
                answer: n(),
            },
            source,
            Level::zero(),
            Default::default(),
            &mut parts,
            &[OwnedCpsCallEquation::from(equation)],
        )
        .unwrap();
        let bundle = parts
            .close_scoped(
                &scope,
                candidate.image.proof,
                candidate.image.component_proposition.unwrap(),
                Default::default(),
            )
            .unwrap();
        let bytes = bundle.encode_with_claim(&claim).unwrap();
        let (decoded, transported) =
            crate::proof_components::ScopedProofComponentBundle::decode_with_claim(&bytes).unwrap();
        assert_eq!(transported, claim);
        decoded.replay(&env, &claim, 2_000_000).unwrap();
    }
}
