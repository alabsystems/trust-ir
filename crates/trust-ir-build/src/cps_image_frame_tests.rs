// Copyright 2026 Andrew Yates | SPDX-License-Identifier: Apache-2.0
//! Actual CPS -> genuine image -> structured Frame controls. No provider axiom.
use super::equation_tests::{app, n};
use super::*;
use crate::scoped_local::LocalScope;
use crate::semantic_evaluation as eval;
fn environment() -> Environment {
    let mut env = super::equation_tests::environment();
    env.init_and().unwrap();
    eval::install_success_framing_into(&mut env).unwrap();
    eval::install_success_handle_related_into(&mut env).unwrap();
    eval::install_success_handle_observer_into(&mut env).unwrap();
    env
}
fn state_type() -> Expr {
    pair_type(&Level::zero(), n(), n())
}
fn outcome_type() -> Expr {
    Expr::apps(
        constant("Except", vec![Level::zero(), Level::zero()]),
        [n(), n()],
    )
}
fn result_type() -> Expr {
    pair_type(&Level::zero(), state_type(), outcome_type())
}
fn state_pair(a: u64, b: u64) -> Expr {
    Expr::apps(
        constant("Prod.mk", vec![Level::zero(), Level::zero()]),
        [n(), n(), Expr::nat_lit(a), Expr::nat_lit(b)],
    )
}
fn result(state: Expr, failing: bool) -> Expr {
    Expr::apps(
        constant("Prod.mk", vec![Level::zero(), Level::zero()]),
        [
            state_type(),
            outcome_type(),
            state,
            Expr::apps(
                constant(
                    if failing { "Except.error" } else { "Except.ok" },
                    vec![Level::zero(), Level::zero()],
                ),
                [n(), n(), Expr::nat_lit(5)],
            ),
        ],
    )
}
fn frame(state: Expr) -> Expr {
    Expr::apps(
        constant("Prod.snd", vec![Level::zero(), Level::zero()]),
        [n(), n(), state],
    )
}
fn frame_claim(scope: &mut LocalScope, run: Expr) -> Expr {
    let input = scope.try_local(state_type()).unwrap();
    let target = frame(input.term().clone());
    input.pi(Expr::apps(
        constant("Eq", vec![Level::succ(Level::zero())]),
        [
            n(),
            app(
                eval::SUCCESS_FRAME_PROJECTION,
                [
                    n(),
                    n(),
                    n(),
                    n(),
                    target.clone(),
                    Expr::app(run, input.term().clone()),
                ],
            ),
            target,
        ],
    ))
}
#[derive(Clone, Copy, PartialEq, Eq)]
enum TraceMutation {
    None,
    NestedReturnLabel,
    NestedObservation,
}
fn mutate_returns(
    node: &mut StructuredObservationConstruction,
    mutation: TraceMutation,
    depth: usize,
) -> usize {
    match &mut node.step {
        StructuredObservationStep::Return { normal, .. } if depth > 0 => {
            match mutation {
                TraceMutation::None => return 0,
                TraceMutation::NestedReturnLabel => *normal = false,
                TraceMutation::NestedObservation => {
                    node.observation = result(state_pair(0, 9), false);
                }
            }
            1
        }
        StructuredObservationStep::Case { branches, .. } => branches
            .iter_mut()
            .map(|(_, child)| mutate_returns(child, mutation, depth + 1))
            .sum(),
        StructuredObservationStep::Handle { yes, no, .. } => {
            mutate_returns(&mut yes.body, mutation, depth + 1)
                + mutate_returns(&mut no.body, mutation, depth + 1)
        }
        _ => 0,
    }
}
fn check(failing: bool, changed: bool, cold: bool, cases: bool) {
    check_mutation(failing, changed, cold, cases, TraceMutation::None);
}
fn check_mutation(failing: bool, changed: bool, cold: bool, cases: bool, mutation: TraceMutation) {
    check_shape(failing, changed, cold, cases, false, mutation);
}
fn check_shape(
    failing: bool,
    changed: bool,
    cold: bool,
    cases: bool,
    nested_cases: bool,
    mutation: TraceMutation,
) {
    check_shape_with_major(failing, changed, cold, cases, nested_cases, mutation, false);
}
fn check_shape_with_major(
    failing: bool,
    changed: bool,
    cold: bool,
    cases: bool,
    nested_cases: bool,
    mutation: TraceMutation,
    computed_major: bool,
) {
    let env = environment();
    let mut scope = LocalScope::new();
    let mut parts = ProofComponents::new("structured.actual.frame", Default::default());
    let flag = scope.try_local(Expr::const_str("Bool")).unwrap();
    parts
        .set_base(
            &scope,
            if cases {
                vec![OwnedProofCapture::Parameter(flag.clone())]
            } else {
                vec![]
            },
        )
        .unwrap();
    if cold {
        parts
            .bind_scoped_owned(&mut scope, &[], n(), Expr::const_str("True.intro"))
            .unwrap();
    }
    let input = scope.try_local(state_type()).unwrap();
    let callback_type = Expr::arrow(state_type(), Expr::arrow(n(), n()));
    let ok = scope.try_local(callback_type.clone()).unwrap();
    let err = scope.try_local(callback_type).unwrap();
    let actual_state = if changed {
        state_pair(0, 9)
    } else {
        input.term().clone()
    };
    let source_body = Expr::apps(
        if failing {
            err.term().clone()
        } else {
            ok.term().clone()
        },
        [actual_state.clone(), Expr::nat_lit(5)],
    );
    let run_body = result(actual_state, failing);
    let (source_body, run_body) = if nested_cases {
        assert!(cases);
        let major = scope.try_local(Expr::const_str("Bool")).unwrap();
        (
            Expr::apps(
                constant("Bool.rec", vec![Level::succ(Level::zero())]),
                [
                    major.lam(n()),
                    source_body.clone(),
                    source_body,
                    flag.term().clone(),
                ],
            ),
            Expr::apps(
                constant("Bool.rec", vec![Level::succ(Level::zero())]),
                [
                    major.lam(result_type()),
                    run_body.clone(),
                    run_body,
                    flag.term().clone(),
                ],
            ),
        )
    } else {
        (source_body, run_body)
    };
    let (source_body, run_body) = if cases {
        let major = scope.try_local(Expr::const_str("Bool")).unwrap();
        let discriminator = if computed_major {
            let inner = scope.try_local(Expr::const_str("Bool")).unwrap();
            Expr::apps(
                constant("Bool.rec", vec![Level::succ(Level::zero())]),
                [
                    inner.lam(Expr::const_str("Bool")),
                    Expr::const_str("Bool.false"),
                    Expr::const_str("Bool.true"),
                    flag.term().clone(),
                ],
            )
        } else {
            flag.term().clone()
        };
        (
            Expr::apps(
                constant("Bool.rec", vec![Level::succ(Level::zero())]),
                [
                    major.lam(n()),
                    source_body.clone(),
                    source_body,
                    discriminator.clone(),
                ],
            ),
            Expr::apps(
                constant("Bool.rec", vec![Level::succ(Level::zero())]),
                [
                    major.lam(result_type()),
                    run_body.clone(),
                    run_body,
                    discriminator,
                ],
            ),
        )
    } else {
        (source_body, run_body)
    };
    let source = input.lam(ok.lam(err.lam(source_body)));
    let run = input.lam(run_body);
    // Freeze complete actual source/image/Frame endpoints before construction.
    let image_claim = app(
        CPS_IMAGE,
        [state_type(), n(), n(), n(), run.clone(), source.clone()],
    );
    let property = frame_claim(&mut scope, run);
    let full = Expr::apps(Expr::const_str("And"), [image_claim, property]);
    let claim = scope
        .close(&if cases { flag.pi(full) } else { full })
        .unwrap();
    let mut candidate = replay_image_with_structured_call_equations(
        &env,
        &mut scope,
        &if cases { vec![flag.clone()] } else { vec![] },
        &[],
        ImageTypes {
            state: state_type(),
            error: n(),
            value: n(),
            answer: n(),
        },
        source,
        Level::zero(),
        Default::default(),
        &mut parts,
        &[],
    )
    .unwrap();
    if computed_major {
        assert_eq!(
            candidate.image.cases, 1,
            "a discriminator-only inner case must not duplicate the structural proof"
        );
    }
    if mutation != TraceMutation::None {
        assert!(mutate_returns(&mut candidate.construction.root, mutation, 0) > 0);
    }
    let mut resolve = |_: &mut LocalScope,
                       _: &mut ProofComponents,
                       _: &[OwnedProofCapture],
                       _: &ScopedLocal,
                       _: &[Expr]|
     -> Result<OperationFrameEvidence, String> {
        panic!("terminal/case source must not invent an operation premise")
    };
    let frame_declarations = parts.counts().0;
    let property = replay_success_frame_from_construction(
        &mut scope,
        &mut parts,
        &candidate.construction,
        FrameReplayTypes {
            base: n(),
            frame: n(),
            error: n(),
            value: n(),
        },
        Level::zero(),
        &mut resolve,
    );
    if changed && !failing && mutation != TraceMutation::NestedReturnLabel {
        assert!(
            property
                .err()
                .expect("changed normal world lacks a reached Frame relation")
                .contains("checked state transport")
        );
        return;
    }
    let property = property.unwrap();
    if nested_cases {
        assert_eq!(
            parts.counts().0,
            frame_declarations + 1,
            "nested typed proof nodes retain only the checked global root"
        );
    }
    let image = candidate.image;
    let image_prop = image.component_proposition.unwrap();
    let goal = Expr::apps(
        Expr::const_str("And"),
        [image_prop.clone(), property.proposition.clone()],
    );
    let proof = Expr::apps(
        Expr::const_str("And.intro"),
        [
            image_prop,
            property.proposition,
            image.proof,
            property.proof,
        ],
    );
    let proof = if cases { flag.lam(proof) } else { proof };
    let bundle = parts
        .close_scoped(&scope, proof, goal, Default::default())
        .unwrap();
    let bytes = bundle.encode_with_claim(&claim).unwrap();
    let (decoded, transported) =
        crate::proof_components::ScopedProofComponentBundle::decode_with_claim(&bytes).unwrap();
    assert_eq!(transported, claim);
    assert!(TypeChecker::new(&env).infer_sort(&claim).unwrap().is_zero());
    let result = decoded.replay(&env, &claim, 2_000_000);
    if cold || mutation != TraceMutation::None {
        assert!(
            result
                .err()
                .expect("cold originals and forged actual observations must still reject")
                .contains("TypeMismatch")
        );
    } else {
        result.unwrap();
    }
}
#[test]
fn cps_image_replay_structured_frame_actual_normal_and_changed_error_worlds() {
    check(false, false, false, false);
    check(true, true, false, false);
}
#[test]
fn cps_image_replay_structured_frame_cases_and_cold_invalid_originals() {
    check(false, false, false, true);
    check(true, true, false, true);
    check(false, false, true, false);
}
#[test]
fn cps_image_replay_structured_frame_refuses_changed_normal_world_without_relation() {
    check(false, true, false, false);
}

#[test]
fn cps_image_replay_structured_frame_nested_return_goal_stays_checked_in_a_true_original() {
    // Original source/image/Frame is true. Only a nested trace observation is
    // forged; dropping its actual typed goal would silently ignore that lie.
    check_mutation(false, false, false, true, TraceMutation::NestedObservation);
}

#[test]
fn cps_image_replay_structured_frame_forged_nested_return_label_cannot_prove_false_frame() {
    // Original source really changes the success frame. A forged error-return
    // label cannot replace the independent actual observation or final claim.
    check_mutation(false, true, false, true, TraceMutation::NestedReturnLabel);
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum HandleInput {
    Plain,
    Rebuilt,
    WrongConstructorType,
    WrongProjectionLevel,
}
#[test]
fn cps_image_replay_structured_frame_handle_requires_actual_operation_preservation() {
    for (failing, wrong_preservation) in [(false, false), (true, false), (false, true)] {
        check_handle_input(failing, wrong_preservation, HandleInput::Plain);
    }
}
fn check_handle_input(failing: bool, wrong_preservation: bool, input_shape: HandleInput) {
    let env = environment();
    let mut scope = LocalScope::new();
    let mut parts = ProofComponents::new("structured.operation.frame", Default::default());
    parts.set_base(&scope, vec![]).unwrap();
    let state = scope.try_local(state_type()).unwrap();
    let run_state = scope.try_local(state_type()).unwrap();
    let actual_state = if failing || wrong_preservation {
        state_pair(0, 9)
    } else {
        run_state.term().clone()
    };
    let run = run_state.lam(result(actual_state, failing));
    let original = app(TO_CPS, [state_type(), n(), n(), n(), run.clone()]);
    let callback_type = Expr::arrow(state_type(), Expr::arrow(n(), n()));
    let cps_type = Expr::arrow(
        state_type(),
        Expr::arrow(
            callback_type.clone(),
            Expr::arrow(callback_type.clone(), n()),
        ),
    );
    let operator = parts
        .bind_scoped_owned(&mut scope, &[], cps_type, original.clone())
        .unwrap();
    let yes = scope.try_local(callback_type.clone()).unwrap();
    let no = scope.try_local(callback_type).unwrap();
    let args = [state.term().clone(), yes.term().clone(), no.term().clone()];
    let rhs = Expr::apps(original.clone(), args.clone());
    let eq = Expr::apps(
        constant("Eq", vec![Level::succ(Level::zero())]),
        [
            n(),
            Expr::apps(operator.reference.clone(), args),
            rhs.clone(),
        ],
    );
    let eq_proof = Expr::apps(
        constant("Eq.refl", vec![Level::succ(Level::zero())]),
        [n(), rhs],
    );
    let equation_proof = parts
        .bind_scoped_owned(
            &mut scope,
            &[],
            state.pi(yes.pi(no.pi(eq))),
            state.lam(yes.lam(no.lam(eq_proof))),
        )
        .unwrap();
    let property = frame_claim(&mut scope, run.clone());
    let proof_value = state.lam(Expr::apps(
        constant("Eq.refl", vec![Level::succ(Level::zero())]),
        [n(), frame(state.term().clone())],
    ));
    let preserves = parts
        .bind_scoped_owned(&mut scope, &[], property.clone(), proof_value)
        .unwrap();
    let rebuilt = Expr::apps(
        constant("Prod.mk", vec![Level::zero(), Level::zero()]),
        [n(), n(), Expr::nat_lit(0), frame(state.term().clone())],
    );
    let root_source = if input_shape == HandleInput::Plain {
        operator.reference.clone()
    } else {
        state.lam(yes.lam(no.lam(Expr::apps(
            operator.reference.clone(),
            [rebuilt.clone(), yes.term().clone(), no.term().clone()],
        ))))
    };
    let root_original = if input_shape == HandleInput::Plain {
        original.clone()
    } else {
        state.lam(yes.lam(no.lam(Expr::apps(
            original.clone(),
            [rebuilt.clone(), yes.term().clone(), no.term().clone()],
        ))))
    };
    let root_run = if input_shape == HandleInput::Plain {
        run
    } else {
        state.lam(Expr::app(run, rebuilt))
    };
    let root_property = frame_claim(&mut scope, root_run.clone());
    // Freeze the genuine rebuilt-input source/image/Frame before any
    // negative mutates only the untrusted construction metadata.
    let claim = scope
        .close(&Expr::apps(
            Expr::const_str("And"),
            [
                app(
                    CPS_IMAGE,
                    [state_type(), n(), n(), n(), root_run, root_original],
                ),
                root_property,
            ],
        ))
        .unwrap();
    let equation = CpsCallEquation {
        operator: operator.local.clone(),
        replacement: original,
        proof: equation_proof,
        arity: 3,
    };
    let mut candidate = replay_image_with_structured_call_equations(
        &env,
        &mut scope,
        &[
            operator.local.clone(),
            equation.proof.local.clone(),
            preserves.local.clone(),
        ],
        &[],
        ImageTypes {
            state: state_type(),
            error: n(),
            value: n(),
            answer: n(),
        },
        root_source,
        Level::zero(),
        Default::default(),
        &mut parts,
        &[OwnedCpsCallEquation::from(equation)],
    )
    .unwrap();
    if matches!(
        input_shape,
        HandleInput::WrongConstructorType | HandleInput::WrongProjectionLevel
    ) {
        let actual_input = candidate.construction.input.term().clone();
        let forged = match input_shape {
            HandleInput::WrongConstructorType => Expr::apps(
                constant("Prod.mk", vec![Level::zero(), Level::zero()]),
                [
                    Expr::const_str("Bool"),
                    n(),
                    Expr::const_str("Bool.false"),
                    frame(actual_input),
                ],
            ),
            HandleInput::WrongProjectionLevel => Expr::apps(
                constant("Prod.mk", vec![Level::zero(), Level::zero()]),
                [
                    n(),
                    n(),
                    Expr::nat_lit(0),
                    Expr::apps(
                        constant("Prod.snd", vec![Level::succ(Level::zero()), Level::zero()]),
                        [n(), n(), actual_input],
                    ),
                ],
            ),
            _ => unreachable!(),
        };
        let StructuredObservationStep::Handle { actual_state, .. } =
            &mut candidate.construction.root.step
        else {
            panic!("genuine source must retain its actual root operation");
        };
        *actual_state = forged;
    }
    let mut resolve = |allocator: &mut LocalScope,
                       _: &mut ProofComponents,
                       _: &[OwnedProofCapture],
                       actual: &ScopedLocal,
                       args: &[Expr]| {
        assert!(allocator.owns(actual));
        assert_eq!(actual.id(), operator.local.id());
        assert_eq!(args.len(), 3);
        Ok(OperationFrameEvidence {
            error: n(),
            value: n(),
            preserves: preserves.reference.clone(),
        })
    };
    let property = replay_success_frame_from_construction(
        &mut scope,
        &mut parts,
        &candidate.construction,
        FrameReplayTypes {
            base: n(),
            frame: n(),
            error: n(),
            value: n(),
        },
        Level::zero(),
        &mut resolve,
    );
    if matches!(
        input_shape,
        HandleInput::WrongConstructorType | HandleInput::WrongProjectionLevel
    ) {
        assert!(
            property
                .err()
                .expect("a forged typed projection must not acquire a relation")
                .contains("no reached-state relation")
        );
        return;
    }
    let property = property.unwrap();
    let image = candidate.image;
    let image_prop = image.component_proposition.unwrap();
    let goal = Expr::apps(
        Expr::const_str("And"),
        [image_prop.clone(), property.proposition.clone()],
    );
    let proof = Expr::apps(
        Expr::const_str("And.intro"),
        [
            image_prop,
            property.proposition,
            image.proof,
            property.proof,
        ],
    );
    let bundle = parts
        .close_scoped(&scope, proof, goal, Default::default())
        .unwrap();
    let bytes = bundle.encode_with_claim(&claim).unwrap();
    let (decoded, transported) =
        crate::proof_components::ScopedProofComponentBundle::decode_with_claim(&bytes).unwrap();
    assert_eq!(transported, claim);
    assert!(TypeChecker::new(&env).infer_sort(&claim).unwrap().is_zero());
    let result = decoded.replay(&env, &claim, 2_000_000);
    if wrong_preservation {
        assert!(
            result
                .err()
                .expect("false operation preservation must reject")
                .contains("TypeMismatch")
        );
    } else {
        result.unwrap();
    }
}

#[test]
fn cps_image_replay_structured_frame_rebuilt_operation_input_reuses_only_the_checked_frame_projection()
 {
    check_handle_input(false, false, HandleInput::Rebuilt);
}
#[test]
fn cps_image_replay_structured_frame_rebuilt_input_keeps_exact_constructor_type_and_projection_universe_guards()
 {
    check_handle_input(false, false, HandleInput::WrongConstructorType);
    check_handle_input(false, false, HandleInput::WrongProjectionLevel);
}

// Append only after the frozen epoch terminates; requires staged constant rule.
fn cleanup_operation(
    scope: &mut LocalScope,
    parts: &mut ProofComponents,
    failing: bool,
) -> (
    CpsCallEquation,
    crate::proof_components::OwnedScopedDefinition,
    Expr,
) {
    let run_state = scope.try_local(state_type()).unwrap();
    let run = run_state.lam(result(
        if failing {
            state_pair(0, 9)
        } else {
            run_state.term().clone()
        },
        failing,
    ));
    let code = app(TO_CPS, [state_type(), n(), n(), n(), run.clone()]);
    let callback_type = Expr::arrow(state_type(), Expr::arrow(n(), n()));
    let cps_type = Expr::arrow(
        state_type(),
        Expr::arrow(
            callback_type.clone(),
            Expr::arrow(callback_type.clone(), n()),
        ),
    );
    let operator = parts
        .bind_scoped_owned(scope, &[], cps_type, code.clone())
        .unwrap();
    let input = scope.try_local(state_type()).unwrap();
    let yes = scope.try_local(callback_type.clone()).unwrap();
    let no = scope.try_local(callback_type).unwrap();
    let args = [input.term().clone(), yes.term().clone(), no.term().clone()];
    let rhs = Expr::apps(code.clone(), args.clone());
    let statement = input.pi(yes.pi(no.pi(Expr::apps(
        constant("Eq", vec![Level::succ(Level::zero())]),
        [
            n(),
            Expr::apps(operator.reference.clone(), args),
            rhs.clone(),
        ],
    ))));
    let proof = input.lam(yes.lam(no.lam(Expr::apps(
        constant("Eq.refl", vec![Level::succ(Level::zero())]),
        [n(), rhs],
    ))));
    let proof = parts
        .bind_scoped_owned(scope, &[], statement, proof)
        .unwrap();
    let property = frame_claim(scope, run);
    let preserves = parts
        .bind_scoped_owned(
            scope,
            &[],
            property,
            input.lam(Expr::apps(
                constant("Eq.refl", vec![Level::succ(Level::zero())]),
                [n(), frame(input.term().clone())],
            )),
        )
        .unwrap();
    (
        CpsCallEquation {
            operator: operator.local,
            replacement: code.clone(),
            proof,
            arity: 3,
        },
        preserves,
        code,
    )
}
#[test]
fn cps_image_replay_structured_frame_arbitrary_error_world_requires_both_strong_handlers() {
    check_arbitrary_error_world(false, false);
    check_arbitrary_error_world(true, false);
}
fn check_arbitrary_error_world(normal_recovers: bool, forge_nested_handle: bool) {
    check_error_world_shape(normal_recovers, forge_nested_handle, false);
}
fn check_error_world_shape(normal_recovers: bool, forge_nested_handle: bool, rebuild_error: bool) {
    let env = environment();
    let mut scope = LocalScope::new();
    let mut parts = ProofComponents::new("actual.arbitrary.error.world", Default::default());
    parts.set_base(&scope, vec![]).unwrap();
    let (first, first_preserves, first_code) = cleanup_operation(&mut scope, &mut parts, true);
    let (second, second_preserves, second_code) = cleanup_operation(&mut scope, &mut parts, false);
    let input = scope.try_local(state_type()).unwrap();
    let callback_type = Expr::arrow(state_type(), Expr::arrow(n(), n()));
    let ok = scope.try_local(callback_type.clone()).unwrap();
    let err = scope.try_local(callback_type).unwrap();
    let post = scope.try_local(state_type()).unwrap();
    let value = scope.try_local(n()).unwrap();
    let failed = scope.try_local(state_type()).unwrap();
    let failure = scope.try_local(n()).unwrap();
    let next = scope.try_local(state_type()).unwrap();
    let result_value = scope.try_local(n()).unwrap();
    let final_yes = next.lam(result_value.lam(Expr::apps(
        if normal_recovers {
            ok.term().clone()
        } else {
            err.term().clone()
        },
        [next.term().clone(), result_value.term().clone()],
    )));
    let final_no = next.lam(result_value.lam(Expr::apps(
        err.term().clone(),
        [next.term().clone(), result_value.term().clone()],
    )));
    let normal = post.lam(value.lam(Expr::apps(
        ok.term().clone(),
        [post.term().clone(), value.term().clone()],
    )));
    let error_input = if rebuild_error {
        Expr::apps(
            constant("Prod.mk", vec![Level::zero(), Level::zero()]),
            [n(), n(), Expr::nat_lit(0), frame(failed.term().clone())],
        )
    } else {
        failed.term().clone()
    };
    let error = failed.lam(failure.lam(Expr::apps(
        second.operator.term().clone(),
        [error_input.clone(), final_yes.clone(), final_no.clone()],
    )));
    let original_error =
        failed.lam(failure.lam(Expr::apps(second_code, [error_input, final_yes, final_no])));
    let source = input.lam(ok.lam(err.lam(Expr::apps(
        first.operator.term().clone(),
        [input.term().clone(), normal.clone(), error],
    ))));
    let original = input.lam(ok.lam(err.lam(Expr::apps(
        first_code,
        [input.term().clone(), normal, original_error],
    ))));
    let expected = input.lam(result(state_pair(0, 9), !normal_recovers));
    let property = frame_claim(&mut scope, expected.clone());
    let claim = scope
        .close(&Expr::apps(
            Expr::const_str("And"),
            [
                app(CPS_IMAGE, [state_type(), n(), n(), n(), expected, original]),
                property,
            ],
        ))
        .unwrap();
    let globals = vec![
        first.operator.clone(),
        first.proof.local.clone(),
        first_preserves.local.clone(),
        second.operator.clone(),
        second.proof.local.clone(),
        second_preserves.local.clone(),
    ];
    let mut candidate = replay_image_with_structured_call_equations(
        &env,
        &mut scope,
        &globals,
        &[],
        ImageTypes {
            state: state_type(),
            error: n(),
            value: n(),
            answer: n(),
        },
        source,
        Level::zero(),
        Default::default(),
        &mut parts,
        &[
            OwnedCpsCallEquation::from(&first),
            OwnedCpsCallEquation::from(&second),
        ],
    )
    .unwrap();
    if forge_nested_handle {
        assert_eq!(mutate_nested_handle(&mut candidate.construction.root, 0), 1);
    }
    let mut resolve = |allocator: &mut LocalScope,
                       _: &mut ProofComponents,
                       _: &[OwnedProofCapture],
                       actual: &ScopedLocal,
                       args: &[Expr]| {
        assert!(allocator.owns(actual));
        assert_eq!(args.len(), 3);
        let proof = if actual.id() == first.operator.id() {
            first_preserves.reference.clone()
        } else {
            assert_eq!(actual.id(), second.operator.id());
            second_preserves.reference.clone()
        };
        Ok(OperationFrameEvidence {
            error: n(),
            value: n(),
            preserves: proof,
        })
    };
    let property = replay_success_frame_from_construction(
        &mut scope,
        &mut parts,
        &candidate.construction,
        FrameReplayTypes {
            base: n(),
            frame: n(),
            error: n(),
            value: n(),
        },
        Level::zero(),
        &mut resolve,
    );
    if normal_recovers {
        assert!(
            property
                .err()
                .expect("normal recovery from unknown error Frame must not acquire a relation")
                .contains("no reached-state relation")
        );
        return;
    }
    let property = property.unwrap();
    let image = candidate.image;
    let image_prop = image.component_proposition.unwrap();
    let goal = Expr::apps(
        Expr::const_str("And"),
        [image_prop.clone(), property.proposition.clone()],
    );
    let proof = Expr::apps(
        Expr::const_str("And.intro"),
        [
            image_prop,
            property.proposition,
            image.proof,
            property.proof,
        ],
    );
    let bundle = parts
        .close_scoped(&scope, proof, goal, Default::default())
        .unwrap();
    let bytes = bundle.encode_with_claim(&claim).unwrap();
    let (decoded, transported) =
        crate::proof_components::ScopedProofComponentBundle::decode_with_claim(&bytes).unwrap();
    assert_eq!(claim, transported);
    assert!(TypeChecker::new(&env).infer_sort(&claim).unwrap().is_zero());
    let result = decoded.replay(&env, &claim, 2_000_000);
    if forge_nested_handle {
        let error = result
            .err()
            .expect("forged actual nested Handle goal must remain checked");
        assert!(
            error.contains("TypeMismatch") && !error.contains("BudgetExhausted"),
            "{error}"
        );
    } else {
        result.unwrap();
    }
}

fn mutate_nested_handle(node: &mut StructuredObservationConstruction, depth: usize) -> usize {
    if depth > 0 && matches!(&node.step, StructuredObservationStep::Handle { .. }) {
        // The original first operation really enters this error handler and
        // the nested Handle observation really is an error. Forge ONLY the
        // actual nested observation to a normal changed-Frame result.
        node.observation = result(state_pair(0, 9), false);
        return 1;
    }
    match &mut node.step {
        StructuredObservationStep::Case { branches, .. } => branches
            .iter_mut()
            .map(|(_, child)| mutate_nested_handle(child, depth + 1))
            .sum(),
        StructuredObservationStep::Handle { yes, no, .. } => {
            mutate_nested_handle(&mut yes.body, depth + 1)
                + mutate_nested_handle(&mut no.body, depth + 1)
        }
        _ => 0,
    }
}

#[test]
fn cps_image_replay_structured_frame_nested_cases_keep_actual_typed_goals_and_one_global_root() {
    check_shape(false, false, false, true, true, TraceMutation::None);
}
#[test]
fn cps_image_replay_structured_frame_nested_handle_goal_stays_checked_in_a_true_original() {
    check_arbitrary_error_world(false, true);
}

#[test]
fn cps_image_replay_structured_frame_rebuilding_an_unknown_error_world_cannot_create_a_reached_relation()
 {
    check_error_world_shape(true, false, true);
}

#[test]
fn cps_image_replay_structured_frame_correlated_case_retains_actual_state_and_outcome() {
    check_correlated_raw_result(false, false, false, false);
}
#[test]
fn cps_image_replay_structured_frame_correlated_case_keeps_changed_normal_world_refused() {
    check_correlated_raw_result(true, false, false, false);
}
#[test]
fn cps_image_replay_structured_frame_correlated_case_checks_frozen_nested_observation() {
    check_correlated_raw_result(false, true, false, false);
}
#[test]
fn cps_image_replay_structured_frame_correlated_except_result_keeps_real_constructor_fields() {
    check_correlated_raw_result(false, false, true, false);
}
#[test]
fn cps_image_replay_structured_frame_correlated_product_result_binds_all_fields_before_closure() {
    check_correlated_raw_result(false, false, false, true);
}
fn check_correlated_raw_result(
    changed_normal: bool,
    forge_observation: bool,
    except_case: bool,
    product_case: bool,
) {
    check_correlated_raw_result_with_major(
        changed_normal,
        forge_observation,
        except_case,
        product_case,
        false,
    );
}
fn check_correlated_raw_result_with_major(
    changed_normal: bool,
    forge_observation: bool,
    except_case: bool,
    product_case: bool,
    computed_status: bool,
) {
    check_correlated_raw_result_with_copies(
        changed_normal,
        forge_observation,
        except_case,
        product_case,
        computed_status,
        false,
        false,
    );
}
fn check_correlated_raw_result_with_copies(
    changed_normal: bool,
    forge_observation: bool,
    except_case: bool,
    product_case: bool,
    computed_status: bool,
    rebuilt_state: bool,
    administrative_state: bool,
) {
    let env = environment();
    let mut scope = LocalScope::new();
    let flag = scope
        .try_local(if computed_status {
            Expr::const_str("Bool")
        } else if product_case {
            state_type()
        } else if except_case {
            outcome_type()
        } else {
            Expr::const_str("Bool")
        })
        .unwrap();
    let mut parts = ProofComponents::new("structured.correlated.raw.result", Default::default());
    parts
        .set_base(&scope, vec![OwnedProofCapture::Parameter(flag.clone())])
        .unwrap();
    let input = scope.try_local(state_type()).unwrap();
    let callback = Expr::arrow(state_type(), Expr::arrow(n(), n()));
    let yes = scope.try_local(callback.clone()).unwrap();
    let no = scope.try_local(callback).unwrap();
    let bool_major = scope.try_local(Expr::const_str("Bool")).unwrap();
    let normal_raw = result(
        if changed_normal {
            state_pair(0, 9)
        } else {
            input.term().clone()
        },
        false,
    );
    let error_raw = result(state_pair(0, 9), true);
    let raw = if product_case {
        let major = scope.try_local(state_type()).unwrap();
        let first = scope.try_local(n()).unwrap();
        let second = scope.try_local(n()).unwrap();
        Expr::apps(
            constant(
                "Prod.rec",
                vec![Level::succ(Level::zero()), Level::zero(), Level::zero()],
            ),
            [
                n(),
                n(),
                major.lam(result_type()),
                first.lam(second.lam(normal_raw)),
                flag.term().clone(),
            ],
        )
    } else if except_case {
        let status_major = if computed_status {
            let b = scope.try_local(Expr::const_str("Bool")).unwrap();
            Expr::apps(
                constant("Bool.rec", vec![Level::succ(Level::zero())]),
                [
                    b.lam(outcome_type()),
                    Expr::apps(
                        constant("Except.error", vec![Level::zero(), Level::zero()]),
                        [n(), n(), Expr::nat_lit(5)],
                    ),
                    Expr::apps(
                        constant("Except.ok", vec![Level::zero(), Level::zero()]),
                        [n(), n(), Expr::nat_lit(5)],
                    ),
                    flag.term().clone(),
                ],
            )
        } else {
            flag.term().clone()
        };
        let major = scope.try_local(outcome_type()).unwrap();
        let failure = scope.try_local(n()).unwrap();
        let payload = scope.try_local(n()).unwrap();
        Expr::apps(
            constant(
                "Except.rec",
                vec![Level::succ(Level::zero()), Level::zero(), Level::zero()],
            ),
            [
                n(),
                n(),
                major.lam(result_type()),
                failure.lam(error_raw),
                payload.lam(normal_raw),
                status_major,
            ],
        )
    } else {
        Expr::apps(
            constant("Bool.rec", vec![Level::succ(Level::zero())]),
            [
                bool_major.lam(result_type()),
                normal_raw,
                error_raw,
                flag.term().clone(),
            ],
        )
    };
    let status = scope.try_local(outcome_type()).unwrap();
    let error = scope.try_local(n()).unwrap();
    let value = scope.try_local(n()).unwrap();
    let state_raw = if rebuilt_state {
        use clean_kernel::expr::ExprFolderOpt;
        struct CopyGraph<'a>(&'a LocalScope);
        impl ExprFolderOpt for CopyGraph<'_> {
            fn fold_expr_opt(&mut self, expression: &Expr) -> Option<Expr> {
                let rebuilt = self
                    .fold_expr_opt_inner(expression)
                    .unwrap_or_else(|| expression.clone());
                Some(self.0.preserve_candidate_binder(expression, rebuilt))
            }
        }
        let copied = CopyGraph(&scope).fold_expr_opt(&raw).unwrap();
        assert!(!crate::proof_assembly::normalize::same_graph(&copied, &raw));
        copied
    } else {
        raw.clone()
    };
    let mut actual_state = Expr::proj(Name::from_string("Prod"), 0, state_raw);
    if administrative_state {
        let ignored = scope.try_local(n()).unwrap();
        let mut unused = Expr::nat_lit(0);
        for _ in 0..280 {
            unused = Expr::app(Expr::const_str("Nat.succ"), unused);
        }
        actual_state = Expr::app(ignored.lam(actual_state), unused);
    }
    let source = input.lam(yes.lam(no.lam(Expr::apps(
        constant(
            "Except.rec",
            vec![Level::succ(Level::zero()), Level::zero(), Level::zero()],
        ),
        [
            n(),
            n(),
            status.lam(n()),
            error.lam(Expr::apps(
                no.term().clone(),
                [actual_state.clone(), error.term().clone()],
            )),
            value.lam(Expr::apps(
                yes.term().clone(),
                [actual_state, value.term().clone()],
            )),
            Expr::proj(Name::from_string("Prod"), 1, raw.clone()),
        ],
    ))));
    let run = input.lam(raw);
    let property = frame_claim(&mut scope, run.clone());
    let claim = scope
        .close(&flag.pi(Expr::apps(
            Expr::const_str("And"),
            [
                app(
                    CPS_IMAGE,
                    [state_type(), n(), n(), n(), run, source.clone()],
                ),
                property,
            ],
        )))
        .unwrap();
    let mut candidate = replay_image_with_structured_call_equations(
        &env,
        &mut scope,
        std::slice::from_ref(&flag),
        &[],
        ImageTypes {
            state: state_type(),
            error: n(),
            value: n(),
            answer: n(),
        },
        source,
        Level::zero(),
        Default::default(),
        &mut parts,
        &[],
    )
    .unwrap();
    if forge_observation {
        assert!(
            mutate_returns(
                &mut candidate.construction.root,
                TraceMutation::NestedObservation,
                0
            ) > 0
        );
    }
    let mut resolve = |_: &mut LocalScope,
                       _: &mut ProofComponents,
                       _: &[OwnedProofCapture],
                       _: &ScopedLocal,
                       _: &[Expr]|
     -> Result<OperationFrameEvidence, String> {
        panic!("correlated scalar case cannot invent an operation premise")
    };
    let property = replay_success_frame_from_construction(
        &mut scope,
        &mut parts,
        &candidate.construction,
        FrameReplayTypes {
            base: n(),
            frame: n(),
            error: n(),
            value: n(),
        },
        Level::zero(),
        &mut resolve,
    );
    if changed_normal {
        assert!(
            property
                .err()
                .expect("changed normal frame must not acquire a relation")
                .contains("checked state transport")
        );
        return;
    }
    let property = property.unwrap();
    let image = candidate.image;
    let image_prop = image.component_proposition.unwrap();
    let goal = Expr::apps(
        Expr::const_str("And"),
        [image_prop.clone(), property.proposition.clone()],
    );
    let proof = flag.lam(Expr::apps(
        Expr::const_str("And.intro"),
        [
            image_prop,
            property.proposition,
            image.proof,
            property.proof,
        ],
    ));
    let bundle = parts
        .close_scoped(&scope, proof, goal, Default::default())
        .unwrap();
    let bytes = bundle.encode_with_claim(&claim).unwrap();
    let (decoded, transported) =
        crate::proof_components::ScopedProofComponentBundle::decode_with_claim(&bytes).unwrap();
    assert_eq!(claim, transported);
    assert!(TypeChecker::new(&env).infer_sort(&claim).unwrap().is_zero());
    let result = decoded.replay(&env, &claim, 2_000_000);
    if forge_observation {
        let error = result
            .err()
            .expect("mutated actual observation must fail strict replay");
        assert!(
            error.contains("TypeMismatch") && !error.contains("BudgetExhausted"),
            "{error}"
        );
    } else {
        result.unwrap();
    }
}

#[test]
fn cps_image_replay_structured_frame_canonical_metadata_normalization_keeps_finite_kernel_budget() {
    let env = environment();
    let mut scope = LocalScope::new();
    let mut parts = ProofComponents::new("structured.frame.state.heartbeat", Default::default());
    parts.set_base(&scope, vec![]).unwrap();
    let input = scope.try_local(state_type()).unwrap();
    let callback = Expr::arrow(state_type(), Expr::arrow(n(), n()));
    let yes = scope.try_local(callback.clone()).unwrap();
    let no = scope.try_local(callback).unwrap();
    let id = scope.try_local(state_type()).unwrap();
    let identity = id.lam(id.term().clone());
    let mut state = input.term().clone();
    for _ in 0..24 {
        state = Expr::app(identity.clone(), state);
    }
    let source =
        input.lam(yes.lam(no.lam(Expr::apps(yes.term().clone(), [state, Expr::nat_lit(5)]))));
    let result = replay_image_with_structured_call_equations(
        &env,
        &mut scope,
        &[],
        &[],
        ImageTypes {
            state: state_type(),
            error: n(),
            value: n(),
            answer: n(),
        },
        source,
        Level::zero(),
        ImageReplayLimits {
            heartbeats: 1,
            ..Default::default()
        },
        &mut parts,
        &[],
    );
    let error =
        result.expect_err("producer must refuse an exhausted finite kernel normalization budget");
    assert!(error.contains("kernel budget"), "{error}");
    assert_eq!(parts.counts().0, 0);
    assert!(parts.counts().3 <= 1_000_000);
}

#[test]
fn cps_image_replay_structured_frame_discriminator_only_case_keeps_actual_structural_run() {
    check_shape_with_major(false, false, false, true, false, TraceMutation::None, true);
}

#[test]
fn cps_image_replay_structured_frame_nearest_raw_receiver_preserves_the_frozen_run_over_computed_status()
 {
    check_correlated_raw_result_with_major(false, false, true, false, true);
}

#[test]
fn cps_image_replay_structured_frame_rebuilt_equal_case_preserves_the_independently_frozen_run() {
    check_correlated_raw_result_with_copies(false, false, true, false, true, true, false);
}

#[test]
fn cps_image_replay_structured_frame_administrative_state_keeps_the_independently_frozen_run() {
    check_correlated_raw_result_with_copies(false, false, true, false, true, false, true);
}

#[test]
fn cps_image_replay_structured_frame_administrative_state_keeps_forged_observation_refused() {
    check_correlated_raw_result_with_copies(false, true, true, false, true, false, true);
}
