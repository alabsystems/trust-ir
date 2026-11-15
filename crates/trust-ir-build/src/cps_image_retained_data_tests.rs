// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//! Ordinary two-call ledger consumer, independent of any source language.
use super::*;
use crate::proof_components::ScopedProofComponentBundle;
use crate::scoped_local::LocalScope;
use crate::semantic_evaluation as eval;

fn n() -> Expr {
    Expr::const_str("Nat")
}
fn b() -> Expr {
    Expr::const_str("Bool")
}
fn app(name: &str, args: impl IntoIterator<Item = Expr>) -> Expr {
    Expr::apps(constant(name, vec![Level::zero()]), args)
}
fn pair_ty(a: Expr, b: Expr) -> Expr {
    Expr::apps(constant("Prod", vec![Level::zero(), Level::zero()]), [a, b])
}
fn pair(a: Expr, b: Expr, left: Expr, right: Expr) -> Expr {
    Expr::apps(
        constant("Prod.mk", vec![Level::zero(), Level::zero()]),
        [a, b, left, right],
    )
}
fn field(a: Expr, b: Expr, value: Expr, second: bool) -> Expr {
    Expr::apps(
        constant(
            if second { "Prod.snd" } else { "Prod.fst" },
            vec![Level::zero(), Level::zero()],
        ),
        [a, b, value],
    )
}
fn state() -> Expr {
    pair_ty(n(), n())
}
fn outcome() -> Expr {
    Expr::apps(
        constant("Except", vec![Level::zero(), Level::zero()]),
        [n(), n()],
    )
}
fn run_ty() -> Expr {
    Expr::arrow(state(), pair_ty(state(), outcome()))
}
fn callback() -> Expr {
    Expr::arrow(state(), Expr::arrow(n(), n()))
}
fn cps_ty() -> Expr {
    Expr::arrow(
        state(),
        Expr::arrow(callback(), Expr::arrow(callback(), n())),
    )
}
fn to_cps(run: Expr) -> Expr {
    app(TO_CPS, [state(), n(), n(), n(), run])
}
fn environment() -> Environment {
    let mut env = eval::build_environment().unwrap();
    eval::install_handle_into(&mut env).unwrap();
    eval::install_case_maps_into(&mut env).unwrap();
    env.init_nat().unwrap();
    env.init_eq().unwrap();
    env.init_bool().unwrap();
    env.init_true_false().unwrap();
    env
}
fn ledger_run(scope: &mut LocalScope, flag: &ScopedLocal, stale_state: bool) -> Expr {
    let s = scope.try_local(state()).unwrap();
    let next = if stale_state {
        s.term().clone()
    } else {
        pair(
            n(),
            n(),
            Expr::app(
                Expr::const_str("Nat.succ"),
                field(n(), n(), s.term().clone(), false),
            ),
            Expr::apps(
                Expr::const_str("Nat.add"),
                [field(n(), n(), s.term().clone(), true), Expr::nat_lit(3)],
            ),
        )
    };
    let ok = pair(
        state(),
        outcome(),
        next.clone(),
        Expr::apps(
            constant("Except.ok", vec![Level::zero(), Level::zero()]),
            [n(), n(), Expr::nat_lit(5)],
        ),
    );
    let error = pair(
        state(),
        outcome(),
        next,
        Expr::apps(
            constant("Except.error", vec![Level::zero(), Level::zero()]),
            [n(), n(), Expr::nat_lit(7)],
        ),
    );
    let flag_arg = scope.try_local(b()).unwrap();
    s.lam(Expr::apps(
        constant("Bool.rec", vec![Level::succ(Level::zero())]),
        [
            flag_arg.lam(pair_ty(state(), outcome())),
            ok,
            error,
            flag.term().clone(),
        ],
    ))
}
fn two_calls(scope: &mut LocalScope, operator: Expr) -> Expr {
    let s = scope.try_local(state()).unwrap();
    let yes = scope.try_local(callback()).unwrap();
    let no = scope.try_local(callback()).unwrap();
    let first = scope.try_local(state()).unwrap();
    let value1 = scope.try_local(n()).unwrap();
    let second = scope.try_local(state()).unwrap();
    let value2 = scope.try_local(n()).unwrap();
    let final_yes = second.lam(value2.lam(Expr::apps(
        yes.term().clone(),
        [
            second.term().clone(),
            Expr::apps(
                Expr::const_str("Nat.add"),
                [value1.term().clone(), value2.term().clone()],
            ),
        ],
    )));
    let first_yes = first.lam(value1.lam(Expr::apps(
        operator.clone(),
        [first.term().clone(), final_yes, no.term().clone()],
    )));
    s.lam(yes.lam(no.lam(Expr::apps(
        operator,
        [s.term().clone(), first_yes, no.term().clone()],
    ))))
}
struct Fixture {
    scope: LocalScope,
    parts: ProofComponents,
    flag: ScopedLocal,
    data: OwnedScopedDefinition,
    equation: CpsCallEquation,
    actual_run: Expr,
    original: Expr,
    source: Expr,
}
fn fixture(stale_data: bool, invalid_data: bool) -> Fixture {
    let mut scope = LocalScope::new();
    let flag = scope.try_local(b()).unwrap();
    let mut parts = ProofComponents::new("ledger.actual", Default::default());
    parts
        .set_base(&scope, vec![OwnedProofCapture::Parameter(flag.clone())])
        .unwrap();
    let actual_run = ledger_run(&mut scope, &flag, false);
    let actual_operator = to_cps(actual_run.clone());
    let operator = parts
        .bind_scoped_owned(&mut scope, &[], cps_ty(), actual_operator.clone())
        .unwrap();
    let stored = if invalid_data {
        Expr::const_str("True.intro")
    } else if stale_data {
        ledger_run(&mut scope, &flag, true)
    } else {
        actual_run.clone()
    };
    let data = parts
        .bind_scoped_owned(&mut scope, &[], run_ty(), stored)
        .unwrap();
    let replacement = to_cps(data.reference.clone());
    let s = scope.try_local(state()).unwrap();
    let yes = scope.try_local(callback()).unwrap();
    let no = scope.try_local(callback()).unwrap();
    let args = [s.term().clone(), yes.term().clone(), no.term().clone()];
    let left = Expr::apps(operator.reference.clone(), args.clone());
    let statement = Expr::apps(
        constant("Eq", vec![Level::succ(Level::zero())]),
        [n(), left.clone(), Expr::apps(replacement.clone(), args)],
    );
    let value = Expr::apps(
        constant("Eq.refl", vec![Level::succ(Level::zero())]),
        [n(), left],
    );
    let proof = parts
        .bind_scoped_owned(
            &mut scope,
            &[],
            s.pi(yes.pi(no.pi(statement))),
            s.lam(yes.lam(no.lam(value))),
        )
        .unwrap();
    let original = two_calls(&mut scope, actual_operator);
    let source = two_calls(&mut scope, operator.reference);
    Fixture {
        scope,
        parts,
        flag,
        data,
        equation: CpsCallEquation {
            operator: operator.local,
            replacement,
            proof,
            arity: 3,
        },
        actual_run,
        original,
        source,
    }
}
fn globals(f: &Fixture) -> Vec<ScopedLocal> {
    vec![
        f.flag.clone(),
        f.equation.operator.clone(),
        f.data.local.clone(),
        f.equation.proof.local.clone(),
    ]
}
fn produce(
    f: &mut Fixture,
    data: &[OwnedScopedDefinition],
    use_old: bool,
) -> Result<ImageCandidate, String> {
    let env = environment();
    let globals = globals(f);
    let types = ImageTypes {
        state: state(),
        error: n(),
        value: n(),
        answer: n(),
    };
    if use_old {
        replay_image_with_call_equations(
            &env,
            &mut f.scope,
            &globals,
            &[],
            types,
            f.source.clone(),
            Level::zero(),
            Default::default(),
            &mut f.parts,
            std::slice::from_ref(&f.equation),
        )
    } else {
        replay_image_with_call_equations_and_retained_data(
            &env,
            &mut f.scope,
            &globals,
            &[],
            types,
            f.source.clone(),
            Level::zero(),
            Default::default(),
            &mut f.parts,
            std::slice::from_ref(&f.equation),
            data,
        )
    }
}
fn checked_consumer(stale_data: bool, invalid_data: bool, use_old: bool, opaque: bool) -> Vec<u8> {
    let env = environment();
    let mut f = fixture(stale_data, invalid_data);
    let data = if opaque { vec![f.data.clone()] } else { vec![] };
    let image = produce(&mut f, &data, use_old).unwrap();
    assert!(image.cases >= 2, "two real result dispatches must remain");
    let globals = globals(&f);
    let run = f
        .parts
        .substitute_scoped_terms(
            &f.scope,
            &globals,
            &[(f.data.local.clone(), f.actual_run)],
            &[image.run],
        )
        .unwrap()
        .remove(0);
    let claim = f
        .scope
        .close(
            &f.flag
                .pi(app(CPS_IMAGE, [state(), n(), n(), n(), run, f.original])),
        )
        .unwrap();
    let bundle = f
        .parts
        .close_scoped(
            &f.scope,
            f.flag.lam(image.proof),
            image.component_proposition.unwrap(),
            Default::default(),
        )
        .unwrap();
    let bytes = bundle.encode_with_claim(&claim).unwrap();
    let (decoded, transported) = ScopedProofComponentBundle::decode_with_claim(&bytes).unwrap();
    assert_eq!(claim, transported);
    let artifact = std::env::var_os("TRUST_IR_RETAINED_DATA_ARTIFACT_DIR").map(|base| {
        let name = if stale_data {
            "stale"
        } else if invalid_data {
            "invalid"
        } else if use_old {
            "old"
        } else if opaque {
            "opaque"
        } else {
            "empty"
        };
        let path = std::path::PathBuf::from(base).join(name);
        std::fs::create_dir_all(&path).unwrap();
        std::fs::write(path.join("scoped.bin"), &bytes).unwrap();
        path
    });
    let result = decoded.replay(&env, &claim, 2_000_000);
    let verdict = if stale_data || invalid_data {
        let error = result.err().expect("retained data cannot certify itself");
        assert!(
            error.contains("TypeMismatch") && !error.contains("BudgetExhausted"),
            "{error}"
        );
        error
    } else {
        let checked = result.unwrap();
        format!(
            "accepted kernel_work={} scope_visits={}",
            checked.kernel_work, checked.scope_visits
        )
    };
    if let Some(path) = artifact {
        std::fs::write(path.join("verdict.txt"), verdict).unwrap();
    }
    bytes
}
#[test]
fn retained_data_keeps_actual_two_call_ledger_state_and_both_outcomes() {
    checked_consumer(false, false, false, true);
}
#[test]
fn retained_data_rejects_shared_stale_poststate_and_invalid_definition() {
    checked_consumer(true, false, false, true);
    checked_consumer(false, true, false, true);
}
#[test]
fn empty_retained_data_preserves_existing_api_bytes() {
    assert_eq!(
        checked_consumer(false, false, true, false),
        checked_consumer(false, false, false, false)
    );
}
#[test]
fn retained_data_refuses_foreign_missing_parameter_and_applied_handles() {
    let mut f = fixture(false, false);
    let mut other = LocalScope::new();
    let foreign = other.try_local(run_ty()).unwrap();
    let bad = OwnedScopedDefinition {
        reference: foreign.term().clone(),
        local: foreign,
    };
    assert!(
        produce(&mut f, &[bad], false)
            .unwrap_err()
            .contains("retained CPS data")
    );
    let missing = f.scope.try_local(run_ty()).unwrap();
    let bad = OwnedScopedDefinition {
        reference: missing.term().clone(),
        local: missing.clone(),
    };
    assert!(
        produce(&mut f, std::slice::from_ref(&bad), false)
            .unwrap_err()
            .contains("retained CPS data")
    );
    let mut applied = f.data.clone();
    applied.reference = Expr::app(applied.reference, Expr::nat_lit(0));
    assert!(
        produce(&mut f, &[applied], false)
            .unwrap_err()
            .contains("retained CPS data")
    );
    let data = f.data.clone();
    assert!(
        produce(&mut f, &[data.clone(), data], false)
            .unwrap_err()
            .contains("retained CPS data")
    );
    f.parts
        .extend_base(OwnedProofCapture::Parameter(missing.clone()))
        .unwrap();
    let env = environment();
    let mut globals = globals(&f);
    globals.push(missing.clone());
    let error = replay_image_with_call_equations_and_retained_data(
        &env,
        &mut f.scope,
        &globals,
        &[],
        ImageTypes {
            state: state(),
            error: n(),
            value: n(),
            answer: n(),
        },
        f.source,
        Level::zero(),
        Default::default(),
        &mut f.parts,
        &[f.equation],
        &[bad],
    )
    .unwrap_err();
    assert!(error.contains("original defining value"), "{error}");
}
#[test]
fn retained_data_never_supplies_an_equation_for_an_opaque_cps_call() {
    let mut f = fixture(false, false);
    let env = environment();
    let globals = globals(&f);
    let data = OwnedScopedDefinition {
        local: f.equation.operator.clone(),
        reference: f.equation.operator.term().clone(),
    };
    let error = replay_image_with_call_equations_and_retained_data(
        &env,
        &mut f.scope,
        &globals,
        &[],
        ImageTypes {
            state: state(),
            error: n(),
            value: n(),
            answer: n(),
        },
        f.source,
        Level::zero(),
        Default::default(),
        &mut f.parts,
        &[],
        &[data],
    )
    .unwrap_err();
    assert!(error.contains("opaque CPS return"), "{error}");
}

#[test]
fn retained_data_refuses_another_component_owner_in_the_same_scope() {
    let mut f = fixture(false, false);
    let env = environment();
    let mut other = ProofComponents::new("ledger.other-owner", Default::default());
    other
        .set_base(&f.scope, vec![OwnedProofCapture::Parameter(f.flag.clone())])
        .unwrap();
    let data = other
        .bind_scoped_owned(&mut f.scope, &[], run_ty(), f.actual_run.clone())
        .unwrap();
    let mut globals = globals(&f);
    globals.push(data.local.clone());
    let error = replay_image_with_call_equations_and_retained_data(
        &env,
        &mut f.scope,
        &globals,
        &[],
        ImageTypes {
            state: state(),
            error: n(),
            value: n(),
            answer: n(),
        },
        f.source,
        Level::zero(),
        Default::default(),
        &mut f.parts,
        &[f.equation],
        &[data],
    )
    .unwrap_err();
    assert!(
        error.contains("charged opaque definition is not retained"),
        "{error}"
    );
}
