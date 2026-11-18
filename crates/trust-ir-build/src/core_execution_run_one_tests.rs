// Copyright 2026 Andrew Yates | Licensed under the Apache License, Version 2.0

//! Strict replay of the ordinary public one-step producer and its fixed
//! closed recursor. No source semantics, world-validity or native authority.

use super::*;
use clean_kernel::KernelTypeError;
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

fn environment() -> &'static Environment {
    shared_specification_with_stack(EvalIrVocabulary::ByteV1)
        .unwrap()
        .env()
}

fn replay(claim: &Expr, proof: &Expr, accepted: bool) {
    for expression in [claim, proof] {
        assert!(!expression.has_fvar_quick());
        assert!(!expression.has_loose_bvars());
    }
    let env = environment();
    let checker = || {
        let mut kernel = TypeChecker::new(env);
        kernel.set_allow_unsafe(false);
        kernel.set_allow_partial(false);
        kernel.set_heartbeat_limit(5_000_000);
        kernel.set_max_cache_entries(100_000);
        kernel
    };
    checker()
        .check_type(claim, &Expr::sort(Level::zero()))
        .unwrap();
    let bytes = trust_ir::proof::encode_clean_expr_dag_v2(proof).unwrap();
    let decoded = trust_ir::proof::decode_clean_expr_dag_v2(&bytes).unwrap();
    assert_eq!(&decoded, proof);
    for actual in [proof, &decoded] {
        let kernel = checker();
        let result = kernel.check_type(actual, claim);
        assert!(
            !kernel.heartbeat_spent(),
            "resource refusal is not semantic evidence"
        );
        if accepted {
            result.unwrap();
            let audit = env.audit_certification(claim, actual);
            assert!(audit.is_certified(), "{audit:#?}");
            for dependency in &audit.dependencies {
                assert!(env.axiom_deps(dependency).unwrap().is_empty());
                assert!(env.trust_marker_deps(dependency).unwrap().is_empty());
            }
        } else {
            let error = result.unwrap_err();
            assert!(
                matches!(error, KernelTypeError::TypeMismatch { .. }),
                "{error:?}"
            );
        }
    }
}

fn close(scope: &Scope, parameters: &[Local], expression: Expr, proof: bool) -> Expr {
    scope
        .close(&parameters.iter().rev().fold(expression, |body, local| {
            if proof {
                local.lam(body)
            } else {
                local.pi(body)
            }
        }))
        .unwrap()
}

// Independent complete endpoint spelling, not a proposition copied from the
// producer. Its fuel, context, providers and complete reached value all matter.
fn run_claim(model: &MachineModel, initial: Expr, reached: Expr, fuel: u64) -> Expr {
    eq(
        &app("IRByteConfigV1", [model.world_type().clone()]),
        app(
            "ir_byte_run_v1",
            [
                model.world_type().clone(),
                model.context().clone(),
                model.providers().clone(),
                nat(fuel),
                initial,
            ],
        ),
        reached,
    )
}

fn inputs(scope: &mut Scope) -> (MachineModel, Vec<Local>) {
    let world = scope.try_local(Expr::type_()).unwrap();
    let context = scope.try_local(constant("IRByteContextV1")).unwrap();
    let providers = scope
        .try_local(app("IRByteProvidersV1", [world.term().clone()]))
        .unwrap();
    let model = MachineModel::from_terms(
        world.term().clone(),
        context.term().clone(),
        providers.term().clone(),
    );
    (model, vec![world, context, providers])
}

#[test]
fn run_one_closed_recursion_replays_for_neutral_configuration_and_symbolic_world_type() {
    let mut scope = Scope::new();
    let (model, mut parameters) = inputs(&mut scope);
    let configuration = scope.try_local(model.config_type()).unwrap();
    parameters.push(configuration.clone());
    let step = app(
        "ir_byte_step_v1",
        [
            model.world_type().clone(),
            model.context().clone(),
            model.providers().clone(),
            configuration.term().clone(),
        ],
    );
    let claim = close(
        &scope,
        &parameters,
        run_claim(&model, configuration.term().clone(), step.clone(), 1),
        false,
    );
    replay(&claim, &closed_candidate(), true);

    let mut assembler = Assembler::new(&mut scope, limits()).unwrap();
    let before = assembler.local_scope().allocated();
    let run = assembler
        .one_step(
            &model,
            configuration.term().clone(),
            PendingEquality::reflexive(model.config_type(), step),
        )
        .unwrap();
    assert_eq!(assembler.local_scope().allocated(), before);
    assert_eq!(assembler.locals, 0);
    assert_eq!(
        assembler.operations(),
        10,
        "original cold charges are retained"
    );
    let proof = close(
        assembler.local_scope(),
        &parameters,
        run.equality().term().clone(),
        true,
    );
    replay(&claim, &proof, true);
}

#[test]
fn run_one_both_constructor_cases_keep_complete_world_and_reject_changed_fields() {
    let mut scope = Scope::new();
    let (model, mut parameters) = inputs(&mut scope);
    let machine = scope.try_local(constant("IRMachine")).unwrap();
    let outcome = scope.try_local(constant("IROutcome")).unwrap();
    let other_outcome = scope.try_local(constant("IROutcome")).unwrap();
    let memory = scope.try_local(constant("IRByteMemoryV1")).unwrap();
    let other_memory = scope.try_local(constant("IRByteMemoryV1")).unwrap();
    let host = scope.try_local(model.world_type().clone()).unwrap();
    let other_host = scope.try_local(model.world_type().clone()).unwrap();
    let owners = scope.try_local(app("IRList", [constant("Nat")])).unwrap();
    let other_owners = scope.try_local(app("IRList", [constant("Nat")])).unwrap();
    let next = scope.try_local(constant("Nat")).unwrap();
    let other_next = scope.try_local(constant("Nat")).unwrap();
    parameters.extend([
        machine.clone(),
        outcome.clone(),
        other_outcome.clone(),
        memory.clone(),
        other_memory.clone(),
        host.clone(),
        other_host.clone(),
        owners.clone(),
        other_owners.clone(),
        next.clone(),
        other_next.clone(),
    ]);
    let world = |fields: [Expr; 4]| {
        app(
            "IRByteWorldV1.mk",
            std::iter::once(model.world_type().clone()).chain(fields),
        )
    };
    let original_fields = [
        memory.term().clone(),
        host.term().clone(),
        owners.term().clone(),
        next.term().clone(),
    ];
    let original_world = world(original_fields.clone());
    let mut assembler = Assembler::new(&mut scope, limits()).unwrap();
    for (constructor, payload) in [
        ("IRByteConfigV1.running", machine.term()),
        ("IRByteConfigV1.halted", outcome.term()),
    ] {
        let initial = app(
            constructor,
            [
                model.world_type().clone(),
                payload.clone(),
                original_world.clone(),
            ],
        );
        let step = model.step(initial.clone());
        let run = assembler
            .one_step(
                &model,
                initial.clone(),
                PendingEquality::reflexive(model.config_type(), step.clone()),
            )
            .unwrap();
        assert_eq!(run.initial(), &initial);
        assert_eq!(run.reached(), &step);
        assert_eq!(run.fuel().term(), &nat(1));
        let proof = close(
            assembler.local_scope(),
            &parameters,
            run.equality().term().clone(),
            true,
        );
        let claim = close(
            assembler.local_scope(),
            &parameters,
            run_claim(&model, initial, step, 1),
            false,
        );
        replay(&claim, &proof, true);
    }
    let initial = app(
        "IRByteConfigV1.halted",
        [
            model.world_type().clone(),
            outcome.term().clone(),
            original_world.clone(),
        ],
    );
    let run = assembler
        .one_step(
            &model,
            initial.clone(),
            PendingEquality::reflexive(model.config_type(), model.step(initial.clone())),
        )
        .unwrap();
    let proof = close(
        assembler.local_scope(),
        &parameters,
        run.equality().term().clone(),
        true,
    );
    for (index, replacement) in [
        other_memory.term(),
        other_host.term(),
        other_owners.term(),
        other_next.term(),
    ]
    .into_iter()
    .enumerate()
    {
        let mut fields = original_fields.clone();
        fields[index] = replacement.clone();
        let changed = app(
            "IRByteConfigV1.halted",
            [
                model.world_type().clone(),
                outcome.term().clone(),
                world(fields),
            ],
        );
        let claim = close(
            assembler.local_scope(),
            &parameters,
            run_claim(&model, initial.clone(), changed, 1),
            false,
        );
        replay(&claim, &proof, false);
    }
    let changed_outcome = app(
        "IRByteConfigV1.halted",
        [
            model.world_type().clone(),
            other_outcome.term().clone(),
            original_world,
        ],
    );
    let claim = close(
        assembler.local_scope(),
        &parameters,
        run_claim(&model, initial, changed_outcome, 1),
        false,
    );
    replay(&claim, &proof, false);
    assert_eq!(assembler.locals, 0);
}

#[test]
fn run_one_cold_and_warm_do_not_allocate_or_reset_an_exhausted_caller_local_ledger() {
    let mut scope = Scope::new();
    let (model, mut parameters) = inputs(&mut scope);
    let configuration = scope.try_local(model.config_type()).unwrap();
    parameters.push(configuration.clone());
    let mut policy = limits();
    policy.max_locals = 1;
    let mut assembler = Assembler::new(&mut scope, policy).unwrap();
    let used = assembler.local(constant("Nat")).unwrap();
    parameters.push(used);
    let allocated = assembler.local_scope().allocated();
    let step = model.step(configuration.term().clone());
    let mut cached = None;
    for expected_operations in [11, 12] {
        let run = assembler
            .one_step(
                &model,
                configuration.term().clone(),
                PendingEquality::reflexive(model.config_type(), step.clone()),
            )
            .unwrap();
        assert_eq!(assembler.operations(), expected_operations);
        assert_eq!(assembler.locals, 1);
        assert_eq!(assembler.local_scope().allocated(), allocated);
        let helper = assembler.run_one_candidate.as_ref().unwrap();
        assert!(!helper.has_fvar_quick() && !helper.has_loose_bvars());
        if let Some(previous) = &cached {
            assert_eq!(helper, previous);
        }
        cached = Some(helper.clone());
        let claim = close(
            assembler.local_scope(),
            &parameters,
            run_claim(&model, configuration.term().clone(), step.clone(), 1),
            false,
        );
        let proof = close(
            assembler.local_scope(),
            &parameters,
            run.equality().term().clone(),
            true,
        );
        replay(&claim, &proof, true);
    }
    assert_eq!(
        assembler.local(constant("Nat")).err().unwrap(),
        "execution construction local budget exceeded"
    );
    assert_eq!(assembler.locals, 1);
    assert_eq!(assembler.local_scope().allocated(), allocated);
    assert_eq!(assembler.operations(), 13);
    drop(assembler);
    policy.max_locals = 0;
    assert_eq!(
        Assembler::new(&mut scope, policy).err().unwrap(),
        "execution construction limits must be nonzero"
    );
}

#[test]
fn run_one_bad_endpoint_preflight_and_failed_cold_charges_never_publish_a_candidate() {
    let mut scope = Scope::new();
    let (model, _) = inputs(&mut scope);
    let initial = scope.try_local(model.config_type()).unwrap();
    let mut assembler = Assembler::new(&mut scope, limits()).unwrap();
    let error = assembler
        .one_step(
            &model,
            initial.term().clone(),
            PendingEquality::reflexive(model.config_type(), initial.term().clone()),
        )
        .err()
        .unwrap();
    assert_eq!(
        error,
        "equality left endpoint: different candidate terms; supply an explicit equality transport"
    );
    assert_eq!(assembler.operations(), 0);
    assert_eq!(assembler.locals, 0);
    assert!(assembler.run_one_candidate.is_none());
    drop(assembler);
    let mut policy = limits();
    policy.max_operations = 5;
    let mut assembler = Assembler::new(&mut scope, policy).unwrap();
    let allocated = assembler.local_scope().allocated();
    for _ in 0..2 {
        let error = assembler
            .one_step(
                &model,
                initial.term().clone(),
                PendingEquality::reflexive(model.config_type(), model.step(initial.term().clone())),
            )
            .err()
            .unwrap();
        assert_eq!(error, "execution construction operation budget exceeded");
        assert_eq!(assembler.operations(), 5);
        assert_eq!(assembler.locals, 0);
        assert_eq!(assembler.local_scope().allocated(), allocated);
        assert!(assembler.run_one_candidate.is_none());
    }
}

#[test]
fn run_one_does_not_certify_a_forged_supplied_step_or_wrong_fuel() {
    let mut scope = Scope::new();
    let (model, mut parameters) = inputs(&mut scope);
    let initial = scope.try_local(model.config_type()).unwrap();
    let foreign = scope.try_local(model.config_type()).unwrap();
    parameters.extend([initial.clone(), foreign.clone()]);
    let step = model.step(initial.term().clone());
    let mut assembler = Assembler::new(&mut scope, limits()).unwrap();
    let genuine = assembler
        .one_step(
            &model,
            initial.term().clone(),
            PendingEquality::reflexive(model.config_type(), step.clone()),
        )
        .unwrap();
    let wrong_fuel = close(
        assembler.local_scope(),
        &parameters,
        run_claim(&model, initial.term().clone(), step.clone(), 0),
        false,
    );
    let genuine_proof = close(
        assembler.local_scope(),
        &parameters,
        genuine.equality().term().clone(),
        true,
    );
    replay(&wrong_fuel, &genuine_proof, false);
    let forged = assembler
        .one_step(
            &model,
            initial.term().clone(),
            PendingEquality::candidate(
                model.config_type(),
                step.clone(),
                foreign.term().clone(),
                refl(&model.config_type(), step),
            ),
        )
        .unwrap();
    let independent_claim = close(
        assembler.local_scope(),
        &parameters,
        run_claim(&model, initial.term().clone(), foreign.term().clone(), 1),
        false,
    );
    let forged_proof = close(
        assembler.local_scope(),
        &parameters,
        forged.equality().term().clone(),
        true,
    );
    replay(&independent_claim, &forged_proof, false);
}

/// An explicit `running`/`halted` configuration takes the same closed
/// eliminator as a neutral one. Presenting the step proof at the run-one type
/// by kernel conversion instead (trust-ir 2ce4067d, reverted) made strict
/// replay decide `run(1, c) = step(c)` on the ACTUAL configuration, which
/// unfolds `step` until it is a constructor and so evaluates the actual
/// instruction's reference semantics: a full-width U64 shift replay then ran
/// for hours. This pins the term, the cost and both refusals, so that route
/// cannot come back as a construction-cost optimization.
#[test]
fn run_one_explicit_constructors_take_the_closed_eliminator_not_step_conversion() {
    let mut scope = Scope::new();
    let (model, mut parameters) = inputs(&mut scope);
    let machine = scope.try_local(constant("IRMachine")).unwrap();
    let outcome = scope.try_local(constant("IROutcome")).unwrap();
    let world = scope
        .try_local(app("IRByteWorldV1", [model.world_type().clone()]))
        .unwrap();
    let foreign = scope.try_local(model.config_type()).unwrap();
    parameters.extend([
        machine.clone(),
        outcome.clone(),
        world.clone(),
        foreign.clone(),
    ]);
    let mut assembler = Assembler::new(&mut scope, limits()).unwrap();
    for (index, (constructor, payload)) in [
        ("IRByteConfigV1.running", machine.term()),
        ("IRByteConfigV1.halted", outcome.term()),
    ]
    .into_iter()
    .enumerate()
    {
        let initial = app(
            constructor,
            [
                model.world_type().clone(),
                payload.clone(),
                world.term().clone(),
            ],
        );
        let step = model.step(initial.clone());
        let supplied = PendingEquality::reflexive(model.config_type(), step.clone());
        let before = assembler.operations();
        let run = assembler
            .one_step(&model, initial.clone(), supplied.clone())
            .unwrap();
        // Cold: nine factory charges and the composition; warm: composition.
        let paid = if index == 0 { 10 } else { 1 };
        assert_eq!(assembler.operations() - before, paid);
        assert_eq!(assembler.locals, 0);
        let eliminator = assembler.run_one_candidate.clone().unwrap();
        assert_eq!(eliminator, closed_candidate());
        let fuel_one = model.run(&NatTerm::literal(1), initial.clone());
        let expected = trans(
            &model.config_type(),
            fuel_one,
            step.clone(),
            step.clone(),
            Expr::apps(
                eliminator,
                [
                    model.world_type().clone(),
                    model.context().clone(),
                    model.providers().clone(),
                    initial.clone(),
                ],
            ),
            supplied.term().clone(),
        );
        assert_eq!(
            run.equality().term(),
            &expected,
            "the run-one equation is instantiated, never left to conversion"
        );
        let proof = close(
            assembler.local_scope(),
            &parameters,
            run.equality().term().clone(),
            true,
        );
        let claim = close(
            assembler.local_scope(),
            &parameters,
            run_claim(&model, initial.clone(), step.clone(), 1),
            false,
        );
        replay(&claim, &proof, true);
        if constructor == "IRByteConfigV1.running" {
            // A halted configuration is its own run at every fuel and its
            // own step, so fuel 0 is a TRUE claim there; it refuses only here.
            let wrong_fuel = close(
                assembler.local_scope(),
                &parameters,
                run_claim(&model, initial.clone(), step.clone(), 0),
                false,
            );
            replay(&wrong_fuel, &proof, false);
        }
        let forged = assembler
            .one_step(
                &model,
                initial.clone(),
                PendingEquality::candidate(
                    model.config_type(),
                    step.clone(),
                    foreign.term().clone(),
                    refl(&model.config_type(), step),
                ),
            )
            .unwrap();
        let claim = close(
            assembler.local_scope(),
            &parameters,
            run_claim(&model, initial, foreign.term().clone(), 1),
            false,
        );
        let proof = close(
            assembler.local_scope(),
            &parameters,
            forged.equality().term().clone(),
            true,
        );
        replay(&claim, &proof, false);
    }
}
