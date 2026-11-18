// Copyright 2026 Andrew Yates | Licensed under the Apache License, Version 2.0

//! Arbitrary typed pulses and fuel: no concrete terminating source substitutes
//! for the general bridge. Every positive candidate is independently replayed.

use super::*;
use clean_verify::eval_ir::{EvalIrVocabulary, shared_specification_with_stack};

fn limits() -> Limits {
    // Existing segmented-simulation test limits, unchanged.
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

fn environment() -> Environment {
    let specification = shared_specification_with_stack(EvalIrVocabulary::ByteV1).unwrap();
    let mut env = specification.env().clone();
    crate::semantic_evaluation::install_loop_into(&mut env).unwrap();
    env
}

fn check(env: &Environment, claim: &Expr, proof: &Expr, accepted: bool) {
    assert!(!claim.has_fvar_quick() && !claim.has_loose_bvars());
    assert!(!proof.has_fvar_quick() && !proof.has_loose_bvars());
    let mut checker = TypeChecker::new(env);
    checker.set_allow_unsafe(false);
    checker.set_allow_partial(false);
    checker.set_heartbeat_limit(5_000_000);
    checker.set_max_cache_entries(100_000);
    checker
        .check_type(claim, &Expr::sort(Level::zero()))
        .unwrap();
    let result = checker.check_type(proof, claim);
    assert!(!checker.heartbeat_spent());
    if accepted {
        result.unwrap();
        drop(checker);
        let audit = env.audit_certification(claim, proof);
        assert!(audit.is_certified(), "{audit:?}");
        for name in audit.dependencies {
            assert!(env.axiom_deps(&name).unwrap().is_empty());
            assert!(env.trust_marker_deps(&name).unwrap().is_empty());
        }
    } else {
        assert!(
            matches!(
                result,
                Err(clean_kernel::KernelTypeError::TypeMismatch { .. })
            ),
            "{result:?}"
        );
    }
}

#[test]
fn pulse_prefix_drive_replays_for_every_fuel_and_rejects_extra_source_steps() {
    let mut scope = Scope::new();
    let state_type = scope.try_local(Expr::type_()).unwrap();
    let done_type = scope.try_local(Expr::type_()).unwrap();
    let source_type = Expr::apps(
        Expr::const_(Name::from_string("Sum"), vec![Level::zero(), Level::zero()]),
        [state_type.term().clone(), done_type.term().clone()],
    );
    let pulse = scope
        .try_local(Expr::arrow(state_type.term().clone(), source_type))
        .unwrap();
    let fuel = scope.try_local(constant("Nat")).unwrap();
    let initial = scope.try_local(state_type.term().clone()).unwrap();
    let done = scope.try_local(done_type.term().clone()).unwrap();
    let parameters = [
        state_type.clone(),
        done_type.clone(),
        pulse.clone(),
        fuel.clone(),
        initial.clone(),
        done.clone(),
    ];
    let mut assembler = Assembler::new(&mut scope, limits()).unwrap();
    let drive = assembler
        .pulse_drive(
            state_type.term().clone(),
            done_type.term().clone(),
            pulse.term().clone(),
        )
        .unwrap();
    let fuel = NatTerm::local(&fuel).unwrap();
    let equality = assembler
        .pulse_prefix_equality(&drive, &fuel, initial.term().clone())
        .unwrap();
    let zero = assembler
        .pulse_prefix_equality(&drive, &NatTerm(nat(0)), initial.term().clone())
        .unwrap();
    assert_eq!(
        equality.left(),
        &drive.run(&fuel, drive.initial(initial.term().clone()))
    );
    assert_eq!(
        equality.right(),
        &drive.prefix(&fuel, initial.term().clone())
    );
    let proof = close(&scope, &parameters, equality.term().clone(), true);
    let claim = close(&scope, &parameters, equality.proposition(), false);
    let env = environment();
    check(&env, &claim, &proof, true);
    let extra = NatTerm(app("Nat.succ", [fuel.term().clone()]));
    let wrong = close(
        &scope,
        &parameters,
        eq(
            drive.source_type(),
            equality.left().clone(),
            drive.prefix(&extra, initial.term().clone()),
        ),
        false,
    );
    check(&env, &wrong, &proof, false);

    // Zero remains suspended. The bridge cannot turn a prefix into an
    // arbitrary completed result, even though both are the same Sum type.
    let proof = close(&scope, &parameters, zero.term().clone(), true);
    let wrong = close(
        &scope,
        &parameters,
        eq(
            drive.source_type(),
            zero.left().clone(),
            drive.terminal(done.term().clone()),
        ),
        false,
    );
    check(&env, &wrong, &proof, false);
}

#[test]
fn pulse_terminal_drive_keeps_the_exact_done_payload_for_every_fuel() {
    let mut scope = Scope::new();
    let state_type = scope.try_local(Expr::type_()).unwrap();
    let done_type = scope.try_local(Expr::type_()).unwrap();
    let source_type = Expr::apps(
        Expr::const_(Name::from_string("Sum"), vec![Level::zero(), Level::zero()]),
        [state_type.term().clone(), done_type.term().clone()],
    );
    let pulse = scope
        .try_local(Expr::arrow(state_type.term().clone(), source_type))
        .unwrap();
    let fuel = scope.try_local(constant("Nat")).unwrap();
    let done = scope.try_local(done_type.term().clone()).unwrap();
    let foreign = scope.try_local(done_type.term().clone()).unwrap();
    let parameters = [
        state_type.clone(),
        done_type.clone(),
        pulse.clone(),
        fuel.clone(),
        done.clone(),
        foreign.clone(),
    ];
    let mut assembler = Assembler::new(&mut scope, limits()).unwrap();
    let drive = assembler
        .pulse_drive(
            state_type.term().clone(),
            done_type.term().clone(),
            pulse.term().clone(),
        )
        .unwrap();
    let equality = assembler
        .pulse_terminal_equality(&drive, &NatTerm::local(&fuel).unwrap(), done.term().clone())
        .unwrap();
    let proof = close(&scope, &parameters, equality.term().clone(), true);
    let claim = close(&scope, &parameters, equality.proposition(), false);
    let env = environment();
    check(&env, &claim, &proof, true);
    let wrong = close(
        &scope,
        &parameters,
        eq(
            drive.source_type(),
            equality.left().clone(),
            drive.terminal(foreign.term().clone()),
        ),
        false,
    );
    check(&env, &wrong, &proof, false);
}

#[test]
fn pulse_construction_uses_the_existing_budget_without_reset_or_refund() {
    let mut scope = Scope::new();
    let mut tiny = limits();
    tiny.max_operations = 1;
    let mut assembler = Assembler::new(&mut scope, tiny).unwrap();
    assert!(
        assembler
            .pulse_drive(constant("Nat"), constant("Nat"), constant("False"))
            .is_err()
    );
    assert_eq!(assembler.operations(), 1);
    assert!(
        assembler
            .pulse_drive(constant("Nat"), constant("Nat"), constant("False"))
            .is_err()
    );
    assert_eq!(assembler.operations(), 1);
}
