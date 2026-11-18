// Copyright 2026 Andrew Yates | Licensed under the Apache License, Version 2.0
//! Kernel replay with arbitrary source semantics, variable costs, actual Core
//! providers and explicit simulation premises. No new semantics or axiom.
use super::*;
use clean_verify::eval_ir::{EvalIrVocabulary, shared_specification_with_stack};

fn limits() -> Limits {
    Limits {
        max_operations: 1000,
        max_locals: 100,
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
struct Fixture {
    scope: Scope,
    parameters: Vec<Local>,
    model: MachineModel,
    simulation: SegmentedPrefixSimulation,
    fuel: NatTerm,
    source: Expr,
    core: Expr,
    initial: PendingProof,
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
    let step_proof = local(premise.clone());
    simulation.step_preserves = PendingProof::candidate(premise, step_proof.term().clone());
    let fuel = local(constant("Nat"));
    let source = local(source_type.term().clone());
    let core = local(model.config_type());
    let initial_prop = Expr::apps(
        relation.term().clone(),
        [source.term().clone(), core.term().clone()],
    );
    let initial = local(initial_prop.clone());
    drop(local);
    Fixture {
        scope,
        parameters,
        model,
        simulation,
        fuel: NatTerm::local(&fuel).unwrap(),
        source: source.term().clone(),
        core: core.term().clone(),
        initial: PendingProof::candidate(initial_prop, initial.term().clone()),
    }
}
fn replay(scope: &Scope, parameters: &[Local], proof: &Expr, claim: Expr) {
    let proof = close(scope, parameters, proof.clone(), true);
    let claim = close(scope, parameters, claim, false);
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
    checker.check_type(&proof, &claim).unwrap();
    let audit = env.audit_certification(&claim, &proof);
    assert!(audit.is_certified(), "{audit:#?}");
    for name in &audit.dependencies {
        assert!(env.axiom_deps(name).unwrap().is_empty());
        assert!(env.trust_marker_deps(name).unwrap().is_empty());
    }
}
#[test]
fn variable_segments_replay_for_arbitrary_source_cost_and_actual_core() {
    let mut f = fixture();
    let result = Assembler::new(&mut f.scope, limits())
        .unwrap()
        .simulate_segmented_prefix(
            &f.model,
            &f.simulation,
            &f.fuel,
            f.source.clone(),
            f.core.clone(),
            f.initial.clone(),
        )
        .unwrap();
    let claim = f.simulation.related(
        f.simulation
            .source_run(f.fuel.term().clone(), f.source.clone()),
        f.model.run(&result.core_fuel, f.core.clone()),
    );
    assert_eq!(result.proof.proposition(), &claim);
    replay(&f.scope, &f.parameters, result.proof.term(), claim);
}
#[test]
fn segment_candidates_do_not_authorize_forged_premises_or_extra_core_steps() {
    let mut f = fixture();
    let result = Assembler::new(&mut f.scope, limits())
        .unwrap()
        .simulate_segmented_prefix(
            &f.model,
            &f.simulation,
            &f.fuel,
            f.source.clone(),
            f.core.clone(),
            f.initial.clone(),
        )
        .unwrap();
    let env = shared_specification_with_stack(EvalIrVocabulary::ByteV1)
        .unwrap()
        .env();
    let proof = close(&f.scope, &f.parameters, result.proof.term().clone(), true);
    let wrong_cost = NatTerm(app("Nat.succ", [result.core_fuel.term().clone()]));
    let wrong = f.simulation.related(
        f.simulation
            .source_run(f.fuel.term().clone(), f.source.clone()),
        f.model.run(&wrong_cost, f.core.clone()),
    );
    let wrong = close(&f.scope, &f.parameters, wrong, false);
    let mut checker = TypeChecker::new(env);
    checker.set_heartbeat_limit(5_000_000);
    assert!(checker.check_type(&proof, &wrong).is_err());
    assert!(!checker.heartbeat_spent());
    let mut forged = f.simulation.clone();
    forged.step_preserves = PendingProof::candidate(
        forged.step_preserves.proposition().clone(),
        f.initial.term().clone(),
    );
    let forged = Assembler::new(&mut f.scope, limits())
        .unwrap()
        .simulate_segmented_prefix(
            &f.model,
            &forged,
            &f.fuel,
            f.source.clone(),
            f.core.clone(),
            f.initial.clone(),
        )
        .unwrap();
    let proof = close(&f.scope, &f.parameters, forged.proof.term().clone(), true);
    let claim = close(
        &f.scope,
        &f.parameters,
        forged.proof.proposition().clone(),
        false,
    );
    assert!(checker.check_type(&proof, &claim).is_err());
}
#[test]
fn segment_boundaries_and_binder_limits_remain_fail_closed() {
    let mut f = fixture();
    let mut changed = f.simulation.clone();
    changed.core_steps = Expr::lam(
        BinderInfo::Default,
        f.simulation.source_type.clone(),
        nat(0),
    );
    let mut assembler = Assembler::new(&mut f.scope, limits()).unwrap();
    assert!(
        assembler
            .simulate_segmented_prefix(
                &f.model,
                &changed,
                &f.fuel,
                f.source.clone(),
                f.core.clone(),
                f.initial.clone()
            )
            .is_err()
    );
    assert_eq!(assembler.operations, 1);
    let mut budget = limits();
    budget.max_locals = 1;
    let mut assembler = Assembler::new(&mut f.scope, budget).unwrap();
    assert!(
        assembler
            .simulate_segmented_prefix(
                &f.model,
                &f.simulation,
                &f.fuel,
                f.source.clone(),
                f.core.clone(),
                f.initial.clone()
            )
            .is_err()
    );
    assert_eq!(assembler.locals, 1);
    assert!(assembler.operations > 1);
}

#[test]
fn halted_source_adds_no_core_steps_without_claiming_a_halted_core() {
    let mut f = fixture();
    f.simulation.source_halted = Expr::lam(
        BinderInfo::Default,
        f.simulation.source_type.clone(),
        constant("Bool.true"),
    );
    let premise = f.simulation.step_preservation_proposition(&f.model);
    let witness = f.scope.try_local(premise.clone()).unwrap();
    f.parameters.push(witness.clone());
    f.simulation.step_preserves = PendingProof::candidate(premise, witness.term().clone());
    let result = Assembler::new(&mut f.scope, limits())
        .unwrap()
        .simulate_segmented_prefix(
            &f.model,
            &f.simulation,
            &NatTerm::literal(5),
            f.source.clone(),
            f.core.clone(),
            f.initial.clone(),
        )
        .unwrap();
    replay(
        &f.scope,
        &f.parameters,
        result.proof.term(),
        f.initial.proposition().clone(),
    );
    let fuel_zero = eq(&constant("Nat"), result.core_fuel.term().clone(), nat(0));
    replay(
        &f.scope,
        &f.parameters,
        &refl(&constant("Nat"), nat(0)),
        fuel_zero,
    );
}
