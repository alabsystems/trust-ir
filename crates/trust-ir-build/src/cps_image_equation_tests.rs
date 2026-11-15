// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//! Owned call equations remain untrusted until complete original replay.
use super::*;
use crate::scoped_local::LocalScope;
use crate::semantic_evaluation as eval;
pub(super) fn n() -> Expr {
    Expr::const_str("Nat")
}
pub(super) fn app(name: &str, args: impl IntoIterator<Item = Expr>) -> Expr {
    Expr::apps(constant(name, vec![Level::zero()]), args)
}
fn eq(a: Expr, b: Expr) -> Expr {
    Expr::apps(
        constant("Eq", vec![Level::succ(Level::zero())]),
        [n(), a, b],
    )
}
fn refl(a: Expr) -> Expr {
    Expr::apps(
        constant("Eq.refl", vec![Level::succ(Level::zero())]),
        [n(), a],
    )
}
fn cps() -> Expr {
    let callback = Expr::arrow(n(), Expr::arrow(n(), n()));
    Expr::arrow(
        n(),
        Expr::arrow(callback.clone(), Expr::arrow(callback, n())),
    )
}
pub(super) fn environment() -> Environment {
    let mut e = eval::build_environment().unwrap();
    eval::install_handle_into(&mut e).unwrap();
    eval::install_case_maps_into(&mut e).unwrap();
    e.init_nat().unwrap();
    e.init_eq().unwrap();
    e.init_true_false().unwrap();
    e
}
pub(super) fn run(scope: &mut LocalScope, failing: bool, value: u64) -> Expr {
    let state = scope.try_local(n()).unwrap();
    let outcome = Expr::apps(
        constant(
            if failing { "Except.error" } else { "Except.ok" },
            vec![Level::zero(), Level::zero()],
        ),
        [n(), n(), Expr::nat_lit(value)],
    );
    state.lam(Expr::apps(
        constant("Prod.mk", vec![Level::zero(), Level::zero()]),
        [
            n(),
            Expr::apps(
                constant("Except", vec![Level::zero(), Level::zero()]),
                [n(), n()],
            ),
            Expr::nat_lit(9),
            outcome,
        ],
    ))
}
pub(super) fn fixture(
    failing: bool,
    bad_equation: bool,
    circular: bool,
) -> (LocalScope, ProofComponents, CpsCallEquation, Expr, Expr) {
    let mut scope = LocalScope::new();
    let mut parts = ProofComponents::new("equation.actual.source", Default::default());
    parts.set_base(&scope, vec![]).unwrap();
    let actual_run = run(&mut scope, failing, if failing { 7 } else { 5 });
    let original = app(TO_CPS, [n(), n(), n(), n(), actual_run.clone()]);
    let operator = parts
        .bind_scoped_owned(&mut scope, &[], cps(), original.clone())
        .unwrap();
    let replacement = if circular {
        operator.reference.clone()
    } else if bad_equation {
        let changed = run(&mut scope, failing, 13);
        app(TO_CPS, [n(), n(), n(), n(), changed])
    } else {
        original.clone()
    };
    let state = scope.try_local(n()).unwrap();
    let callback = Expr::arrow(n(), Expr::arrow(n(), n()));
    let yes = scope.try_local(callback.clone()).unwrap();
    let no = scope.try_local(callback).unwrap();
    let args = [state.term().clone(), yes.term().clone(), no.term().clone()];
    let statement = state.pi(yes.pi(no.pi(eq(
        Expr::apps(operator.reference.clone(), args.clone()),
        Expr::apps(replacement.clone(), args.clone()),
    ))));
    let proof_value = state.lam(yes.lam(no.lam(refl(Expr::apps(
        if circular {
            operator.reference.clone()
        } else {
            original.clone()
        },
        args,
    )))));
    let proof = parts
        .bind_scoped_owned(&mut scope, &[], statement, proof_value)
        .unwrap();
    (
        scope,
        parts,
        CpsCallEquation {
            operator: operator.local,
            replacement,
            proof,
            arity: 3,
        },
        original,
        actual_run,
    )
}
fn produce(
    env: &Environment,
    scope: &mut LocalScope,
    parts: &mut ProofComponents,
    equation: CpsCallEquation,
    limits: ImageReplayLimits,
) -> Result<ImageCandidate, String> {
    let globals = [equation.operator.clone(), equation.proof.local.clone()];
    let source = equation.operator.term().clone();
    replay_image_with_call_equations(
        env,
        scope,
        &globals,
        &[],
        ImageTypes {
            state: n(),
            error: n(),
            value: n(),
            answer: n(),
        },
        source,
        Level::zero(),
        limits,
        parts,
        &[equation],
    )
}
fn check(failing: bool, bad_equation: bool, cold_invalid: bool) {
    let env = environment();
    let (mut scope, mut parts, equation, original, actual_run) =
        fixture(failing, bad_equation, false);
    if cold_invalid {
        parts
            .bind_scoped_owned(&mut scope, &[], n(), Expr::const_str("True.intro"))
            .unwrap();
    }
    let image = produce(&env, &mut scope, &mut parts, equation, Default::default()).unwrap();
    let claim = scope
        .close(&app(CPS_IMAGE, [n(), n(), n(), n(), actual_run, original]))
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
    if bad_equation || cold_invalid {
        let error = result
            .err()
            .expect("false or cold-invalid original must reject");
        assert!(
            error.contains("TypeMismatch") && !error.contains("BudgetExhausted"),
            "{error}"
        );
    } else {
        result.unwrap();
    }
}
#[test]
fn cps_image_replay_owned_call_equations_keep_actual_normal_and_error_worlds() {
    check(false, false, false);
    check(true, false, false);
}
#[test]
fn cps_image_replay_owned_call_equations_refuse_false_equations_and_cold_invalid_originals() {
    check(false, true, false);
    check(true, true, false);
    check(false, false, true);
}
#[test]
fn cps_image_replay_owned_call_equations_refuse_foreign_partial_and_parameter_authority() {
    let env = environment();
    let (mut scope, mut parts, equation, _, _) = fixture(false, false, false);
    let mut other = LocalScope::new();
    let foreign = other.try_local(n()).unwrap();
    let mut bad = equation.clone();
    bad.proof.local = foreign;
    assert!(produce(&env, &mut scope, &mut parts, bad, Default::default()).is_err());
    let mut bad = equation.clone();
    bad.proof.reference = Expr::app(bad.proof.reference, n());
    assert!(produce(&env, &mut scope, &mut parts, bad, Default::default()).is_err());
    // A fresh unretained proof handle of the right type is no definition.
    let fresh = scope.try_local(equation.proof.local.ty().clone()).unwrap();
    let mut bad = equation.clone();
    bad.proof.local = fresh.clone();
    bad.proof.reference = fresh.term().clone();
    assert!(
        produce(
            &env,
            &mut scope,
            &mut parts,
            bad.clone(),
            Default::default()
        )
        .is_err()
    );
    parts
        .extend_base(OwnedProofCapture::Parameter(bad.proof.local.clone()))
        .unwrap();
    let error = produce(&env, &mut scope, &mut parts, bad, Default::default())
        .err()
        .unwrap();
    assert!(error.contains("original defining value"), "{error}");
}
#[test]
fn cps_image_replay_owned_call_equations_never_unroll_a_circular_witness() {
    let env = environment();
    let (mut scope, mut parts, equation, _, _) = fixture(false, false, true);
    let mut limits = ImageReplayLimits::default();
    limits.max_depth = 8;
    let error = produce(&env, &mut scope, &mut parts, equation, limits)
        .err()
        .expect("reflexive circular equations do not establish an image");
    assert!(error.contains("depth limit"), "{error}");
}

#[test]
fn cps_image_replay_owned_call_equations_do_not_admit_a_missing_original_global() {
    let env = environment();
    let (mut scope, mut parts, equation, _, _) = fixture(false, false, false);
    let original = scope.try_local(n()).unwrap();
    parts
        .extend_base(OwnedProofCapture::Parameter(original))
        .unwrap();
    let error = produce(&env, &mut scope, &mut parts, equation, Default::default())
        .err()
        .unwrap();
    assert!(
        error.contains("every explicitly admitted original global"),
        "{error}"
    );
}
