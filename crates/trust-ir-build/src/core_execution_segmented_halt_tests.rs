// Copyright 2026 Andrew Yates | Licensed under the Apache License, Version 2.0
//! Non-TLA kernel controls over arbitrary source semantics and actual ByteV1
//! Core runs. Premises remain explicit quantified hypotheses of this generic
//! composition lemma, not facts about a particular source or native provider.

use super::*;
use clean_kernel::KernelTypeError;
use clean_verify::eval_ir::{EvalIrVocabulary, shared_specification_with_stack};

fn limits() -> Limits {
    Limits {
        max_operations: 1_000,
        max_locals: 100,
        max_list_items: 100,
        max_lookup_candidates: 100,
        lookup_heartbeats: 1_000_000,
        lookup_cache_entries: 16_384,
    }
}

struct Fixture {
    scope: Scope,
    parameters: Vec<Local>,
    model: MachineModel,
    simulation: SegmentedPrefixSimulation,
    terminal: SegmentedHaltProjection,
    fuel: NatTerm,
    source: Expr,
    core: Expr,
    initial: PendingProof,
    source_halted: PendingProof,
}

fn fixture() -> Fixture {
    let mut scope = Scope::new();
    let mut parameters = Vec::new();
    let mut local = |ty| {
        let value = scope.try_local(ty).unwrap();
        parameters.push(value.clone());
        value
    };
    let context = local(constant("IRByteContextV1"));
    let providers = local(app("IRByteProvidersV1", [constant("Nat")]));
    let model = MachineModel::from_terms(
        constant("Nat"),
        context.term().clone(),
        providers.term().clone(),
    );
    let source_type = local(Expr::type_());
    let halted = local(Expr::arrow(source_type.term().clone(), constant("Bool")));
    let step = local(Expr::arrow(
        source_type.term().clone(),
        source_type.term().clone(),
    ));
    let cost = local(Expr::arrow(source_type.term().clone(), constant("Nat")));
    let relation = local(Expr::arrow(
        source_type.term().clone(),
        Expr::arrow(model.config_type(), Expr::sort(Level::zero())),
    ));
    let mut simulation = SegmentedPrefixSimulation {
        source_type: source_type.term().clone(),
        source_halted: halted.term().clone(),
        source_step: step.term().clone(),
        core_steps: cost.term().clone(),
        relation: relation.term().clone(),
        step_preserves: PendingProof::candidate(constant("False"), constant("False")),
    };
    let premise = simulation.step_preservation_proposition(&model);
    let proof = local(premise.clone());
    simulation.step_preserves = PendingProof::candidate(premise, proof.term().clone());
    let fuel = local(constant("Nat"));
    let source = local(source_type.term().clone());
    let core = local(model.config_type());
    let initial_prop = Expr::apps(
        relation.term().clone(),
        [source.term().clone(), core.term().clone()],
    );
    let initial = local(initial_prop.clone());
    let binary = |result| {
        Expr::arrow(
            source_type.term().clone(),
            Expr::arrow(model.config_type(), result),
        )
    };
    let terminal_cost = local(binary(constant("Nat")));
    let outcome = local(binary(constant("IROutcome")));
    let world = local(binary(app("IRByteWorldV1", [constant("Nat")])));
    let mut terminal = SegmentedHaltProjection {
        core_steps: terminal_cost.term().clone(),
        outcome: outcome.term().clone(),
        world: world.term().clone(),
        reaches_halt: PendingProof::candidate(constant("False"), constant("False")),
    };
    let premise = terminal.halt_proposition(&model, &simulation);
    let proof = local(premise.clone());
    terminal.reaches_halt = PendingProof::candidate(premise, proof.term().clone());
    let fuel = NatTerm::local(&fuel).unwrap();
    let source_halted = simulation.halted_after_proposition(&fuel, source.term().clone());
    let halt = local(source_halted.clone());
    drop(local);
    Fixture {
        scope,
        parameters,
        model,
        simulation,
        terminal,
        fuel,
        source: source.term().clone(),
        core: core.term().clone(),
        initial: PendingProof::candidate(initial_prop, initial.term().clone()),
        source_halted: PendingProof::candidate(source_halted, halt.term().clone()),
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

fn replay(f: &Fixture, proof: Expr, claim: Expr, accepted: bool) {
    let proof = close(&f.scope, &f.parameters, proof, true);
    let claim = close(&f.scope, &f.parameters, claim, false);
    assert!(!proof.has_fvar_quick() && !claim.has_fvar_quick());
    assert!(!proof.has_loose_bvars() && !claim.has_loose_bvars());
    let env = shared_specification_with_stack(EvalIrVocabulary::ByteV1)
        .unwrap()
        .env();
    let mut checker = TypeChecker::new(env);
    checker.set_allow_unsafe(false);
    checker.set_allow_partial(false);
    checker.set_heartbeat_limit(5_000_000);
    checker.set_max_cache_entries(100_000);
    checker
        .check_type(&claim, &Expr::sort(Level::zero()))
        .unwrap();
    if accepted {
        checker.check_type(&proof, &claim).unwrap();
        let audit = env.audit_certification(&claim, &proof);
        assert!(audit.is_certified(), "{audit:#?}");
        for name in &audit.dependencies {
            assert!(env.axiom_deps(name).unwrap().is_empty());
            assert!(env.trust_marker_deps(name).unwrap().is_empty());
        }
    } else {
        let error = checker.check_type(&proof, &claim).unwrap_err();
        assert!(
            matches!(error, KernelTypeError::TypeMismatch { .. }),
            "{error:?}"
        );
        assert!(!checker.heartbeat_spent());
    }
}

fn compose(f: &mut Fixture) -> Result<SimulatedHalt> {
    Assembler::new(&mut f.scope, limits())?.simulate_segmented_halt(
        &f.model,
        &f.simulation,
        &f.terminal,
        &f.fuel,
        f.source.clone(),
        f.core.clone(),
        f.initial.clone(),
        f.source_halted.clone(),
    )
}

#[test]
fn segmented_halt_replays_actual_full_run_and_retains_source_obligations() {
    let mut f = fixture();
    let result = compose(&mut f).unwrap();
    assert_eq!(result.run.initial(), &f.core);
    assert_eq!(
        result.run.reached(),
        &app(
            "IRByteConfigV1.halted",
            [
                f.model.world_type().clone(),
                result.outcome.clone(),
                result.world.clone(),
            ]
        ),
    );
    assert_eq!(
        result.prefix_relation.proposition(),
        &Expr::apps(
            f.simulation.relation.clone(),
            [
                result.source_final.clone(),
                result.prefix_configuration.clone(),
            ]
        ),
    );
    assert_eq!(
        result.source_halted.proposition(),
        f.source_halted.proposition()
    );
    let cost = result.run.fuel().term();
    let fields = cost.get_app_args();
    assert_eq!(cost.get_app_fn(), &constant("Nat.add"));
    assert_eq!(fields.len(), 2);
    assert_eq!(
        *fields[0],
        Expr::apps(
            f.terminal.core_steps.clone(),
            [result.source_final, result.prefix_configuration.clone(),]
        ),
    );
    assert_eq!(
        result.prefix_configuration,
        f.model.run(&NatTerm((*fields[1]).clone()), f.core.clone()),
    );
    replay(
        &f,
        result.run.equality().term().clone(),
        result.run.equality().proposition(),
        true,
    );
}

#[test]
fn segmented_halt_does_not_mint_source_halt_or_terminal_equations() {
    for corrupt_terminal in [false, true] {
        let mut f = fixture();
        if corrupt_terminal {
            // Preserve the theorem's full function telescope. Its final proof
            // is about the initial relation instead of the required run/halt
            // equation, so rejection must be a real result-type mismatch.
            let source = f.scope.try_local(f.simulation.source_type.clone()).unwrap();
            let core = f.scope.try_local(f.model.config_type()).unwrap();
            let related = f
                .scope
                .try_local(Expr::apps(
                    f.simulation.relation.clone(),
                    [source.term().clone(), core.term().clone()],
                ))
                .unwrap();
            let halted = f
                .scope
                .try_local(eq(
                    &constant("Bool"),
                    Expr::app(f.simulation.source_halted.clone(), source.term().clone()),
                    constant("Bool.true"),
                ))
                .unwrap();
            let wrong = source.lam(core.lam(related.lam(halted.lam(f.initial.term().clone()))));
            f.terminal.reaches_halt =
                PendingProof::candidate(f.terminal.reaches_halt.proposition().clone(), wrong);
        } else {
            f.source_halted = PendingProof::candidate(
                f.source_halted.proposition().clone(),
                f.initial.term().clone(),
            );
        }
        let result = compose(&mut f).unwrap();
        replay(
            &f,
            result.run.equality().term().clone(),
            result.run.equality().proposition(),
            false,
        );
    }
}

#[test]
fn segmented_halt_rejects_changed_final_world_and_exact_fuel_at_replay() {
    let mut f = fixture();
    let wrong_world = f
        .scope
        .try_local(app("IRByteWorldV1", [constant("Nat")]))
        .unwrap();
    f.parameters.push(wrong_world.clone());
    let result = compose(&mut f).unwrap();
    let wrong = eq(
        &f.model.config_type(),
        result.run.equality().left().clone(),
        app(
            "IRByteConfigV1.halted",
            [
                f.model.world_type().clone(),
                result.outcome,
                wrong_world.term().clone(),
            ],
        ),
    );
    replay(&f, result.run.equality().term().clone(), wrong, false);
    let wrong = eq(
        &f.model.config_type(),
        f.model.run(
            &NatTerm(app("Nat.succ", [result.run.fuel().term().clone()])),
            f.core.clone(),
        ),
        result.run.reached().clone(),
    );
    replay(&f, result.run.equality().term().clone(), wrong, false);
}

#[test]
fn segmented_halt_checks_complete_source_and_terminal_boundaries_before_prefix() {
    let mut f = fixture();
    let bad_halt = f.initial.clone();
    let mut assembler = Assembler::new(&mut f.scope, limits()).unwrap();
    assert!(
        assembler
            .simulate_segmented_halt(
                &f.model,
                &f.simulation,
                &f.terminal,
                &f.fuel,
                f.source.clone(),
                f.core.clone(),
                f.initial.clone(),
                bad_halt,
            )
            .is_err()
    );
    assert_eq!(assembler.operations, 1);
    let mut f = fixture();
    f.terminal.core_steps = f.terminal.world.clone();
    let mut assembler = Assembler::new(&mut f.scope, limits()).unwrap();
    assert!(
        assembler
            .simulate_segmented_halt(
                &f.model,
                &f.simulation,
                &f.terminal,
                &f.fuel,
                f.source.clone(),
                f.core.clone(),
                f.initial.clone(),
                f.source_halted.clone(),
            )
            .is_err()
    );
    assert_eq!(assembler.operations, 1);
}

#[test]
fn segmented_halt_retains_the_original_assembler_construction_cap() {
    let mut f = fixture();
    let mut budget = limits();
    budget.max_operations = 1;
    let mut assembler = Assembler::new(&mut f.scope, budget).unwrap();
    assert!(
        assembler
            .simulate_segmented_halt(
                &f.model,
                &f.simulation,
                &f.terminal,
                &f.fuel,
                f.source,
                f.core,
                f.initial,
                f.source_halted,
            )
            .is_err()
    );
}
