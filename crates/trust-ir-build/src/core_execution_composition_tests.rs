// Copyright 2026 Andrew Yates | Licensed under the Apache License, Version 2.0

//! Strict composition of the actual byte-run law. Symbolic leaf executions
//! remain explicit theorem parameters, not source/native execution authority.

use super::*;
use clean_kernel::{BinderInfo, KernelTypeError};
use clean_verify::eval_ir::{EvalIrVocabulary, shared_specification_with_stack};

fn limits() -> Limits {
    Limits {
        max_operations: 1_000,
        max_locals: 100,
        max_list_items: 100,
        max_lookup_candidates: 32,
        lookup_heartbeats: 5_000_000,
        lookup_cache_entries: 100_000,
    }
}

fn replay(scope: &Scope, parameters: &[Local], proof: &PendingEquality, accepted: bool) {
    let term = parameters
        .iter()
        .rev()
        .fold(proof.term().clone(), |body, parameter| parameter.lam(body));
    let claim = parameters
        .iter()
        .rev()
        .fold(proof.proposition(), |body, parameter| parameter.pi(body));
    let term = scope.close(&term).unwrap();
    let claim = scope.close(&claim).unwrap();
    assert!(!term.has_fvar_quick() && !claim.has_fvar_quick());
    let environment = shared_specification_with_stack(EvalIrVocabulary::ByteV1)
        .unwrap()
        .env();
    let mut checker = TypeChecker::new(environment);
    checker.set_allow_unsafe(false);
    checker.set_allow_partial(false);
    checker.set_heartbeat_limit(5_000_000);
    checker.set_max_cache_entries(100_000);
    checker
        .check_type(&claim, &Expr::sort(Level::zero()))
        .unwrap();
    if !accepted {
        let error = checker.check_type(&term, &claim).unwrap_err();
        assert!(
            matches!(error, KernelTypeError::TypeMismatch { .. }),
            "{error:?}"
        );
        assert!(!checker.heartbeat_spent());
        return;
    }
    checker.check_type(&term, &claim).unwrap();
    assert!(
        environment
            .audit_certification(&claim, &term)
            .is_certified()
    );
    let encoded = trust_ir::proof::encode_clean_expr_dag_v2(&term).unwrap();
    let decoded = trust_ir::proof::decode_clean_expr_dag_v2(&encoded).unwrap();
    assert_eq!(decoded, term);
    checker.check_type(&decoded, &claim).unwrap();
    assert!(
        environment
            .audit_certification(&claim, &decoded)
            .is_certified()
    );
}

struct Symbolic {
    scope: Scope,
    parameters: Vec<Local>,
    first: ExactRun,
    second: ExactRun,
}

fn symbolic() -> Symbolic {
    let mut scope = Scope::new();
    let world_type = scope.try_local(Expr::type_()).unwrap();
    let context = scope.try_local(constant("IRByteContextV1")).unwrap();
    let providers = scope
        .try_local(app("IRByteProvidersV1", [world_type.term().clone()]))
        .unwrap();
    let model = MachineModel {
        world_type: world_type.term().clone(),
        context: context.term().clone(),
        providers: providers.term().clone(),
    };
    let a = scope.try_local(constant("Nat")).unwrap();
    let b = scope.try_local(constant("Nat")).unwrap();
    let initial = scope.try_local(model.config_type()).unwrap();
    let middle = scope.try_local(model.config_type()).unwrap();
    let reached = scope.try_local(model.config_type()).unwrap();
    let first_fuel = NatTerm::local(&a).unwrap();
    let second_fuel = NatTerm::local(&b).unwrap();
    let first_left = model.run(&first_fuel, initial.term().clone());
    let second_left = model.run(&second_fuel, middle.term().clone());
    let first_hypothesis = scope
        .try_local(eq(
            &model.config_type(),
            first_left.clone(),
            middle.term().clone(),
        ))
        .unwrap();
    let second_hypothesis = scope
        .try_local(eq(
            &model.config_type(),
            second_left.clone(),
            reached.term().clone(),
        ))
        .unwrap();
    let first = ExactRun::candidate(
        model.clone(),
        initial.term().clone(),
        middle.term().clone(),
        first_fuel,
        PendingEquality::candidate(
            model.config_type(),
            first_left,
            middle.term().clone(),
            first_hypothesis.term().clone(),
        ),
    )
    .unwrap();
    let second = ExactRun::candidate(
        model,
        middle.term().clone(),
        reached.term().clone(),
        second_fuel,
        PendingEquality::candidate(
            first.model.config_type(),
            second_left,
            reached.term().clone(),
            second_hypothesis.term().clone(),
        ),
    )
    .unwrap();
    Symbolic {
        scope,
        parameters: vec![
            world_type,
            context,
            providers,
            a,
            b,
            initial,
            middle,
            reached,
            first_hypothesis,
            second_hypothesis,
        ],
        first,
        second,
    }
}

fn trans_nodes(expression: &Expr) -> usize {
    match expression.kind() {
        ExprKind::Const(name, _) => usize::from(name == &Name::from_string("Eq.trans")),
        ExprKind::App(function, argument) => trans_nodes(function) + trans_nodes(argument),
        _ => 0,
    }
}

#[test]
fn symbolic_exact_run_fusion_keeps_full_endpoints_with_two_trans_nodes_and_four_charges() {
    let Symbolic {
        mut scope,
        parameters,
        first,
        second,
    } = symbolic();
    let model = first.model.clone();
    let claim_left = model.run(
        &NatTerm(app(
            "Nat.add",
            [parameters[4].term().clone(), parameters[3].term().clone()],
        )),
        parameters[5].term().clone(),
    );
    let mut policy = limits();
    policy.max_operations = 4;
    let mut assembler = Assembler::new(&mut scope, policy).unwrap();
    let result = assembler.concatenate(first, second).unwrap();
    assert_eq!(assembler.operations(), 4);
    assert_eq!(
        assembler.operations(),
        4,
        "observing cannot reset/change the ledger"
    );
    assert_eq!(assembler.locals, 0);
    assert_eq!(assembler.local_scope().allocated(), parameters.len());
    assert_eq!(
        trans_nodes(result.equality().term()),
        2,
        "two actual redundant trans nodes were eliminated"
    );
    let independent = PendingEquality::candidate(
        model.config_type(),
        claim_left,
        parameters[7].term().clone(),
        result.equality().term().clone(),
    );
    assert_eq!(result.equality().proposition(), independent.proposition());
    replay(assembler.local_scope(), &parameters, &independent, true);
    for (left, right) in [
        (
            model.run(
                &NatTerm(app(
                    "Nat.add",
                    [parameters[3].term().clone(), parameters[4].term().clone()],
                )),
                parameters[5].term().clone(),
            ),
            parameters[7].term().clone(),
        ),
        (independent.left().clone(), parameters[6].term().clone()),
        (
            model.run(
                &NatTerm(app(
                    "Nat.add",
                    [parameters[4].term().clone(), parameters[3].term().clone()],
                )),
                parameters[6].term().clone(),
            ),
            parameters[7].term().clone(),
        ),
    ] {
        replay(
            assembler.local_scope(),
            &parameters,
            &PendingEquality::candidate(
                model.config_type(),
                left,
                right,
                independent.term().clone(),
            ),
            false,
        );
    }
    assert!(
        assembler
            .conversion(constant("Nat"), nat(0), nat(0))
            .err()
            .unwrap()
            .contains("operation budget")
    );
    assert_eq!(assembler.operations(), 4);
    assert_eq!(assembler.locals, 0);
}

fn empty_context() -> Expr {
    app(
        "IRByteContextV1.mk",
        [
            app("IRModule.mk", [list("IRFunc", &[]), list("IRGlobal", &[])]),
            list("IRByteLayoutV1", &[]),
            list("IRByteSignatureV1", &[]),
            list("IRByteFunctionV1", &[]),
            list("IRByteSiteV1", &[]),
        ],
    )
}

fn providers(world_type: Expr) -> Expr {
    let body = app(
        "IRByteImportResultV1.mk",
        [
            world_type.clone(),
            app("IROutcome.stuck", [constant("IRFault.no_func")]),
            Expr::bvar(1),
            Expr::bvar(0),
        ],
    );
    [
        constant("Nat"),
        app("IRList", [constant("IRScalar")]),
        constant("IRByteMemoryV1"),
        world_type,
    ]
    .into_iter()
    .rev()
    .fold(body, |body, ty| Expr::lam(BinderInfo::Default, ty, body))
}

#[test]
fn closed_zero_and_one_run_fusion_replays_without_execution_hypotheses() {
    for (world_type, host) in [
        (constant("Nat"), nat(37)),
        (constant("Bool"), constant("Bool.false")),
    ] {
        let model = MachineModel {
            world_type: world_type.clone(),
            context: empty_context(),
            providers: providers(world_type.clone()),
        };
        let world = app(
            "IRByteWorldV1.mk",
            [
                world_type.clone(),
                app("ir_byte_memory_empty_v1", [nat(65)]),
                host,
                list("Nat", &[]),
                nat(1),
            ],
        );
        let initial = app(
            "IRByteConfigV1.halted",
            [
                world_type,
                app("IROutcome.ret", [list("IRScalar", &[])]),
                world,
            ],
        );
        let summary = |fuel| {
            ExactRun::candidate(
                model.clone(),
                initial.clone(),
                initial.clone(),
                NatTerm::literal(fuel),
                PendingEquality::candidate(
                    model.config_type(),
                    model.run(&NatTerm::literal(fuel), initial.clone()),
                    initial.clone(),
                    refl(&model.config_type(), initial.clone()),
                ),
            )
            .unwrap()
        };
        for (a, b) in [(0, 0), (0, 1), (1, 0), (1, 1)] {
            let mut scope = Scope::new();
            let mut policy = limits();
            policy.max_operations = 4;
            let mut assembler = Assembler::new(&mut scope, policy).unwrap();
            let result = assembler.concatenate(summary(a), summary(b)).unwrap();
            assert_eq!(assembler.operations(), 4);
            assert_eq!(assembler.locals, 0);
            let independent = PendingEquality::candidate(
                model.config_type(),
                model.run(&NatTerm(app("Nat.add", [nat(b), nat(a)])), initial.clone()),
                initial.clone(),
                result.equality().term().clone(),
            );
            replay(assembler.local_scope(), &[], &independent, true);
        }
    }
}

#[test]
fn strict_fusion_keeps_model_boundary_refusals_and_does_not_certify_poisoned_private_fields() {
    for mutation in 0..10 {
        let Symbolic {
            mut scope,
            parameters,
            mut first,
            mut second,
        } = symbolic();
        match mutation {
            0 => second.model.world_type = constant("Bool"),
            1 => second.model.context = empty_context(),
            2 => second.model.providers = providers(constant("Nat")),
            3 => second.initial = first.initial.clone(),
            4 => first.equality.ty = constant("Nat"),
            5 => first.equality.left = first.initial.clone(),
            6 => first.equality.right = first.initial.clone(),
            7 => second.equality.ty = constant("Nat"),
            8 => second.equality.left = second.initial.clone(),
            _ => second.equality.right = second.initial.clone(),
        }
        let mut assembler = Assembler::new(&mut scope, limits()).unwrap();
        match assembler.concatenate(first, second) {
            Err(error) => assert!(
                !error.contains("budget"),
                "actual candidate mismatch: {error}"
            ),
            Ok(candidate) => {
                // This deliberately poisoned input equality type is outside
                // ExactRun::candidate's public invariant. Existing pending
                // assembly may emit a term; strict replay must still refuse.
                assert_eq!(mutation, 4);
                replay(
                    assembler.local_scope(),
                    &parameters,
                    candidate.equality(),
                    false,
                );
            }
        }
        assert_eq!(
            assembler.operations(),
            if mutation < 4 {
                1
            } else if mutation == 5 {
                3
            } else {
                4
            }
        );
        assert_eq!(assembler.locals, 0);
    }
    let Symbolic {
        mut scope,
        first,
        second,
        ..
    } = symbolic();
    let mut policy = limits();
    policy.max_operations = 3;
    let mut assembler = Assembler::new(&mut scope, policy).unwrap();
    assert!(
        assembler
            .concatenate(first, second)
            .err()
            .unwrap()
            .contains("operation budget")
    );
    assert_eq!(assembler.operations(), 3);
    assert_eq!(assembler.locals, 0);
}

#[test]
fn strict_middle_guard_and_kernel_replay_still_refuse_false_composition() {
    let mut scope = Scope::new();
    let mut assembler = Assembler::new(&mut scope, limits()).unwrap();
    assert!(
        assembler
            .compose(
                PendingEquality::reflexive(constant("Nat"), nat(0)),
                PendingEquality::reflexive(constant("Nat"), nat(1))
            )
            .err()
            .unwrap()
            .contains("middle endpoint")
    );
    assert_eq!(assembler.operations(), 1);
    assert_eq!(assembler.locals, 0);
    for forged_first in [true, false] {
        let Symbolic {
            mut scope,
            parameters,
            mut first,
            mut second,
        } = symbolic();
        if forged_first {
            first.equality.term = refl(&first.model.config_type(), first.reached.clone());
        } else {
            second.equality.term = refl(&second.model.config_type(), second.initial.clone());
        }
        let mut assembler = Assembler::new(&mut scope, limits()).unwrap();
        let result = assembler.concatenate(first, second).unwrap();
        assert_eq!(assembler.operations(), 4);
        // Candidate endpoints match, but false leaf proof terms cannot become
        // facts merely because redundant reflexive bridges were removed.
        replay(
            assembler.local_scope(),
            &parameters,
            result.equality(),
            false,
        );
    }
}
