// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Direct-function candidate assembly and replay against independent claims.
//! Byte composition uses Clean's actual shared vocabulary, not a replacement
//! evaluator. Its two execution premises are explicit theorem parameters;
//! these tests do not claim to execute a particular source or native program.

use super::*;
use crate::term_scope::TermScopeLimits;
use clean_kernel::KernelTypeError;
use clean_verify::eval_ir::{EvalIrVocabulary, shared_specification_with_stack};

fn limits() -> Limits {
    Limits {
        max_operations: 20_000,
        max_locals: 1,
        max_list_items: 100,
        max_lookup_candidates: 100,
        lookup_heartbeats: 1_000_000,
        lookup_cache_entries: 16_384,
    }
}

fn close(scope: &Scope, parameters: &[Local], body: Expr, proof: bool) -> Expr {
    scope
        .close(&parameters.iter().rev().fold(body, |body, local| {
            if proof {
                local.lam(body)
            } else {
                local.pi(body)
            }
        }))
        .unwrap()
}

fn assert_replay(env: &Environment, proof: &Expr, claim: &Expr) {
    let mut checker = TypeChecker::new(env);
    checker.set_allow_unsafe(false);
    checker.set_allow_partial(false);
    checker.set_heartbeat_limit(5_000_000);
    checker.set_max_cache_entries(100_000);
    checker
        .check_type(claim, &Expr::sort(Level::zero()))
        .unwrap();
    checker.check_type(proof, claim).unwrap();
    let audit = env.audit_certification(claim, proof);
    assert!(audit.is_certified(), "{audit:#?}");
    for dependency in &audit.dependencies {
        assert!(env.axiom_deps(dependency).unwrap().is_empty());
        assert!(env.trust_marker_deps(dependency).unwrap().is_empty());
    }
}

fn assert_rejected(env: &Environment, proof: &Expr, claim: &Expr) {
    let mut checker = TypeChecker::new(env);
    checker.set_heartbeat_limit(5_000_000);
    let error = checker.check_type(proof, claim).unwrap_err();
    assert!(
        matches!(error, KernelTypeError::TypeMismatch { .. }),
        "{error:?}"
    );
    assert!(!checker.heartbeat_spent(), "refusal must be semantic");
}

#[test]
fn direct_function_congruence_kernel_checks_without_extra_locals_or_axioms() {
    let mut env = Environment::new();
    env.init_eq().unwrap();
    env.init_nat().unwrap();
    let mut scope = Scope::new();
    let x = scope.try_local(constant("Nat")).unwrap();
    let y = scope.try_local(constant("Nat")).unwrap();
    let h = scope
        .try_local(eq(&constant("Nat"), x.term().clone(), y.term().clone()))
        .unwrap();
    let original = [x, y, h];
    let mut assembler = Assembler::new(&mut scope, limits()).unwrap();
    let mapped = assembler
        .congruence_function(
            PendingEquality::candidate(
                constant("Nat"),
                original[0].term().clone(),
                original[1].term().clone(),
                original[2].term().clone(),
            ),
            constant("Nat"),
            constant("Nat.succ"),
        )
        .unwrap();
    assert_eq!(assembler.operations, 1);
    assert_eq!(assembler.locals, 0);
    assert_eq!(assembler.local_scope().allocated(), original.len());
    let goal = eq(
        &constant("Nat"),
        app("Nat.succ", [original[0].term().clone()]),
        app("Nat.succ", [original[1].term().clone()]),
    );
    let wrong = eq(
        &constant("Nat"),
        app("Nat.succ", [original[0].term().clone()]),
        original[1].term().clone(),
    );
    assert_eq!(mapped.proposition(), goal);
    drop(assembler);
    let proof = close(&scope, &original, mapped.term().clone(), true);
    let claim = close(&scope, &original, goal, false);
    assert_replay(&env, &proof, &claim);
    assert_rejected(&env, &proof, &close(&scope, &original, wrong, false));
}

#[test]
fn direct_function_congruence_preserves_operation_limits_and_old_binder_api() {
    let mut scope = Scope::new();
    let mut policy = limits();
    policy.max_operations = 2;
    let mut assembler = Assembler::new(&mut scope, policy).unwrap();
    assembler.local(constant("Nat")).unwrap();
    let equality = PendingEquality::reflexive(constant("Nat"), nat(4));
    assembler
        .congruence_function(equality.clone(), constant("Nat"), constant("Nat.succ"))
        .unwrap();
    assert_eq!(
        assembler.locals, 1,
        "direct function works at the existing local cap"
    );
    assert_eq!(assembler.operations, 2);
    assert_eq!(assembler.local_scope().allocated(), 1);
    assert!(
        assembler
            .congruence_function(equality.clone(), constant("Nat"), constant("Nat.succ"))
            .err()
            .unwrap()
            .contains("operation budget")
    );
    assert_eq!(assembler.operations, 2);
    assert_eq!(assembler.local_scope().allocated(), 1);

    let mut old_scope = Scope::new();
    let mut old = Assembler::new(&mut old_scope, limits()).unwrap();
    let result = old
        .congruence(equality, constant("Nat"), |value| app("Nat.succ", [value]))
        .unwrap();
    assert_eq!(
        old.locals, 1,
        "old API still allocates the same deferred binder"
    );
    assert_eq!(old.operations, 1);
    let arguments = result.term().get_app_args();
    assert!(matches!(arguments[4].kind(), ExprKind::Lam(_, _, _)));
}

#[test]
fn direct_function_congruence_never_admits_forged_function_type_or_equality() {
    let mut env = Environment::new();
    env.init_eq().unwrap();
    env.init_nat().unwrap();
    env.init_bool().unwrap();
    for (function, output_type, equality) in [
        (
            nat(3),
            constant("Nat"),
            PendingEquality::reflexive(constant("Nat"), nat(4)),
        ),
        (
            constant("Nat.succ"),
            constant("Bool"),
            PendingEquality::reflexive(constant("Nat"), nat(4)),
        ),
        (
            constant("Nat.succ"),
            constant("Nat"),
            PendingEquality::candidate(
                constant("Nat"),
                nat(4),
                nat(5),
                refl(&constant("Nat"), nat(4)),
            ),
        ),
        (
            constant("Nat.succ"),
            constant("Nat"),
            PendingEquality::reflexive(constant("Bool"), constant("Bool.true")),
        ),
    ] {
        let mut scope = Scope::new();
        let mut assembler = Assembler::new(&mut scope, limits()).unwrap();
        let candidate = assembler
            .congruence_function(equality, output_type, function)
            .unwrap();
        assert_eq!(assembler.locals, 0);
        assert_rejected(&env, candidate.term(), &candidate.proposition());
    }
}

struct Composition {
    scope: Scope,
    parameters: Vec<Local>,
    first: ExactRun,
    second: ExactRun,
    claim: Expr,
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

fn unused_provider() -> Expr {
    let body = app(
        "IRByteImportResultV1.mk",
        [
            constant("Nat"),
            app("IROutcome.stuck", [constant("IRFault.no_func")]),
            Expr::bvar(1),
            Expr::bvar(0),
        ],
    );
    [
        constant("Nat"),
        app("IRList", [constant("IRScalar")]),
        constant("IRByteMemoryV1"),
        constant("Nat"),
    ]
    .into_iter()
    .rev()
    .fold(body, |body, ty| {
        Expr::lam(clean_kernel::BinderInfo::Default, ty, body)
    })
}

fn composition() -> Composition {
    let mut scope = Scope::new();
    let context = scope.try_local(constant("IRByteContextV1")).unwrap();
    let providers = scope
        .try_local(app("IRByteProvidersV1", [constant("Nat")]))
        .unwrap();
    let model = MachineModel {
        world_type: constant("Nat"),
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
    let h1 = scope
        .try_local(eq(
            &model.config_type(),
            first_left.clone(),
            middle.term().clone(),
        ))
        .unwrap();
    let h2 = scope
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
            h1.term().clone(),
        ),
    )
    .unwrap();
    let second = ExactRun::candidate(
        model.clone(),
        middle.term().clone(),
        reached.term().clone(),
        second_fuel,
        PendingEquality::candidate(
            model.config_type(),
            second_left,
            reached.term().clone(),
            h2.term().clone(),
        ),
    )
    .unwrap();
    // Independently state the actual byte law's ordered b+a composition.
    let claim = eq(
        &model.config_type(),
        app(
            "ir_byte_run_v1",
            [
                constant("Nat"),
                context.term().clone(),
                providers.term().clone(),
                app("Nat.add", [b.term().clone(), a.term().clone()]),
                initial.term().clone(),
            ],
        ),
        reached.term().clone(),
    );
    Composition {
        scope,
        parameters: vec![context, providers, a, b, initial, middle, reached, h1, h2],
        first,
        second,
        claim,
    }
}

#[test]
fn direct_run_function_composition_replays_actual_byte_law_with_no_new_locals() {
    let fixture = composition();
    let Composition {
        mut scope,
        parameters,
        first,
        second,
        claim,
    } = fixture;
    let run_function = first.model.run_function(&second.fuel);
    assert_eq!(run_function.get_app_fn(), &constant("ir_byte_run_v1"));
    assert_eq!(run_function.get_app_args().len(), 4);
    assert_eq!(
        Expr::app(run_function, second.initial.clone()),
        second.equality.left
    );
    let mut assembler = Assembler::new(&mut scope, limits()).unwrap();
    let result = assembler.concatenate(first, second).unwrap();
    assert_eq!(assembler.locals, 0);
    assert_eq!(
        assembler.operations, 4,
        "composition charges mapping and two strict joins, not identical endpoint bridges"
    );
    assert_eq!(assembler.local_scope().allocated(), parameters.len());
    assert_eq!(result.equality.proposition(), claim);
    drop(assembler);
    let proof = close(&scope, &parameters, result.equality.term, true);
    let claim = close(&scope, &parameters, claim, false);
    let env = shared_specification_with_stack(EvalIrVocabulary::ByteV1)
        .unwrap()
        .env();
    assert_replay(env, &proof, &claim);
    // Typed provider/context/endpoint/fuel changes cannot retarget the proof.
    for lane in [0, 1, 2, 3] {
        let model = &result.model;
        let (context, providers, reached) = match lane {
            0 => (
                empty_context(),
                model.providers.clone(),
                result.reached.clone(),
            ),
            1 => (
                model.context.clone(),
                unused_provider(),
                result.reached.clone(),
            ),
            2 => (
                model.context.clone(),
                model.providers.clone(),
                parameters[5].term().clone(),
            ),
            _ => (
                model.context.clone(),
                model.providers.clone(),
                result.reached.clone(),
            ),
        };
        let fuel = if lane == 3 {
            app("Nat.succ", [result.fuel.term().clone()])
        } else {
            result.fuel.term().clone()
        };
        let wrong = eq(
            &model.config_type(),
            app(
                "ir_byte_run_v1",
                [
                    constant("Nat"),
                    context,
                    providers,
                    fuel,
                    result.initial.clone(),
                ],
            ),
            reached,
        );
        let wrong = close(&scope, &parameters, wrong, false);
        TypeChecker::new(env)
            .check_type(&wrong, &Expr::sort(Level::zero()))
            .unwrap();
        assert_rejected(env, &proof, &wrong);
    }
}

#[test]
fn direct_run_composition_replays_closed_zero_fuel_without_execution_hypotheses() {
    let model = MachineModel {
        world_type: constant("Nat"),
        context: empty_context(),
        providers: unused_provider(),
    };
    let memory = app(
        "IRByteMemoryV1.mk",
        [
            list("IRByteAllocationV1", &[]),
            Expr::lam(
                clean_kernel::BinderInfo::Default,
                constant("Nat"),
                app("IROption.none", [constant("Nat")]),
            ),
            nat(0),
        ],
    );
    let world = app(
        "IRByteWorldV1.mk",
        [constant("Nat"), memory, nat(37), list("Nat", &[]), nat(1)],
    );
    let initial = app(
        "IRByteConfigV1.halted",
        [
            constant("Nat"),
            app("IROutcome.ret", [list("IRScalar", &[])]),
            world,
        ],
    );
    let summary = || {
        ExactRun::candidate(
            model.clone(),
            initial.clone(),
            initial.clone(),
            NatTerm::literal(0),
            PendingEquality::candidate(
                model.config_type(),
                model.run(&NatTerm::literal(0), initial.clone()),
                initial.clone(),
                refl(&model.config_type(), initial.clone()),
            ),
        )
        .unwrap()
    };
    let mut scope = Scope::new();
    let mut assembler = Assembler::new(&mut scope, limits()).unwrap();
    let result = assembler.concatenate(summary(), summary()).unwrap();
    assert_eq!(assembler.locals, 0);
    assert_eq!(assembler.local_scope().allocated(), 0);
    let claim = eq(
        &model.config_type(),
        app(
            "ir_byte_run_v1",
            [
                constant("Nat"),
                empty_context(),
                unused_provider(),
                app("Nat.add", [nat(0), nat(0)]),
                initial.clone(),
            ],
        ),
        initial,
    );
    assert_eq!(result.equality.proposition(), claim);
    assert_replay(
        shared_specification_with_stack(EvalIrVocabulary::ByteV1)
            .unwrap()
            .env(),
        result.equality.term(),
        &claim,
    );
}

#[test]
fn direct_run_composition_preserves_exact_model_fuel_and_boundary_refusals() {
    for mutation in 0..4 {
        let Composition {
            mut scope,
            first,
            mut second,
            ..
        } = composition();
        match mutation {
            0 => second.model.world_type = constant("Bool"),
            1 => second.model.context = constant("changed_context"),
            2 => second.model.providers = constant("changed_providers"),
            _ => second.initial = first.initial.clone(),
        }
        let mut assembler = Assembler::new(&mut scope, limits()).unwrap();
        let error = assembler
            .concatenate(first, second)
            .err()
            .expect("exact mismatch must refuse");
        assert!(
            error.contains(["world type", "reflected context", "providers", "boundary"][mutation]),
            "{error}"
        );
        assert_eq!(assembler.operations, 1);
        assert_eq!(assembler.locals, 0);
    }
    let fixture = composition();
    let error = ExactRun::candidate(
        fixture.first.model,
        fixture.first.initial,
        fixture.first.reached,
        NatTerm::literal(3),
        fixture.first.equality,
    )
    .err()
    .unwrap();
    assert!(error.contains("equality left endpoint"));
}

#[test]
fn repeated_direct_function_maps_keep_closing_depth_and_local_count_constant() {
    let mut scope = Scope::new();
    let x = scope.try_local(constant("Nat")).unwrap();
    let mut assembler = Assembler::new(&mut scope, limits()).unwrap();
    let mut result = PendingEquality::reflexive(constant("Nat"), x.term().clone());
    let mut small = None;
    for count in 1..=128 {
        result = assembler
            .congruence_function(result, constant("Nat"), constant("Nat.succ"))
            .unwrap();
        if count == 64 {
            small = Some(x.lam(result.term().clone()));
        }
    }
    assert_eq!(assembler.locals, 0);
    assert_eq!(assembler.operations, 128);
    assert_eq!(assembler.local_scope().allocated(), 1);
    drop(assembler);
    let small = scope
        .close_with_limits(&small.unwrap(), TermScopeLimits::default())
        .unwrap();
    let large = scope
        .close_with_limits(&x.lam(result.term().clone()), TermScopeLimits::default())
        .unwrap();
    assert_eq!(small.stats.max_binder_depth, 1);
    assert_eq!(large.stats.max_binder_depth, 1);
    assert!(
        large.stats.visits <= 3 * small.stats.visits,
        "{:?} -> {:?}",
        small.stats,
        large.stats
    );
}
