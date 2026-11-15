// Copyright 2026 Andrew Yates | Licensed under the Apache License, Version 2.0

//! Strict replay of the actual internal-call owner mapper, not call admission.
//! Independently stated endpoints retain the complete world and configuration.

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

fn model(world_type: Expr) -> MachineModel {
    MachineModel {
        world_type,
        context: constant("owner_mapper_unused_context"),
        providers: constant("owner_mapper_unused_providers"),
    }
}

fn direct(world_type: Expr, config: Expr, world: Expr) -> Expr {
    app(
        "ir_byte_lift_v1",
        [
            world_type.clone(),
            app("ir_byte_push_owner_v1", [world_type, world]),
            config,
        ],
    )
}

fn independent(
    model: &MachineModel,
    config: Expr,
    left: Expr,
    right: Expr,
    term: Expr,
) -> PendingEquality {
    PendingEquality::candidate(
        model.config_type(),
        direct(model.world_type.clone(), config.clone(), left),
        direct(model.world_type.clone(), config, right),
        term,
    )
}

fn check_closed(term: Expr, claim: Expr, accepted: bool) {
    assert!(!term.has_fvar_quick() && !claim.has_fvar_quick());
    assert!(!term.has_loose_bvars_quick() && !claim.has_loose_bvars_quick());
    let environment = shared_specification_with_stack(EvalIrVocabulary::ByteV1)
        .unwrap()
        .env();
    let term_bytes = trust_ir::proof::encode_clean_expr_dag_v2(&term).unwrap();
    let claim_bytes = trust_ir::proof::encode_clean_expr_dag_v2(&claim).unwrap();
    let decoded_term = trust_ir::proof::decode_clean_expr_dag_v2(&term_bytes).unwrap();
    let decoded_claim = trust_ir::proof::decode_clean_expr_dag_v2(&claim_bytes).unwrap();
    assert_eq!(decoded_term, term);
    assert_eq!(decoded_claim, claim);
    for (term, claim) in [(term, claim), (decoded_term, decoded_claim)] {
        let mut checker = TypeChecker::new(environment);
        checker.set_allow_unsafe(false);
        checker.set_allow_partial(false);
        checker.set_heartbeat_limit(5_000_000);
        checker.set_max_cache_entries(100_000);
        checker
            .check_type(&claim, &Expr::sort(Level::zero()))
            .unwrap();
        let checked = checker.check_type(&term, &claim);
        if accepted {
            checked.unwrap();
            let audit = environment.audit_certification(&claim, &term);
            assert!(audit.is_certified(), "{audit:?}");
            for name in &audit.dependencies {
                assert!(environment.axiom_deps(name).unwrap().is_empty(), "{name}");
                assert!(
                    environment.trust_marker_deps(name).unwrap().is_empty(),
                    "{name}"
                );
            }
        } else {
            let error = checked.unwrap_err();
            assert!(
                matches!(error, KernelTypeError::TypeMismatch { .. }),
                "semantic type mismatch, not a resource refusal: {error:?}"
            );
        }
        assert!(!checker.heartbeat_spent());
    }
}

fn replay(scope: &Scope, parameters: &[Local], proof: &PendingEquality, accepted: bool) {
    let term = parameters
        .iter()
        .rev()
        .fold(proof.term().clone(), |body, local| local.lam(body));
    let claim = parameters
        .iter()
        .rev()
        .fold(proof.proposition(), |body, local| local.pi(body));
    check_closed(
        scope.close(&term).unwrap(),
        scope.close(&claim).unwrap(),
        accepted,
    );
}

struct Fixture {
    model: MachineModel,
    config: Local,
    other_config: Local,
    world: Local,
    other_world: Local,
    bool_world: Local,
    machine: Local,
    parameters: Vec<Local>,
}

fn fixture(scope: &mut Scope) -> Fixture {
    let world_type = scope.try_local(Expr::type_()).unwrap();
    let config = scope.try_local(constant("IRConfig")).unwrap();
    let other_config = scope.try_local(constant("IRConfig")).unwrap();
    let world = scope
        .try_local(app("IRByteWorldV1", [world_type.term().clone()]))
        .unwrap();
    let other_world = scope.try_local(world.ty().clone()).unwrap();
    let bool_world = scope
        .try_local(app("IRByteWorldV1", [constant("Bool")]))
        .unwrap();
    let machine = scope.try_local(constant("IRMachine")).unwrap();
    let parameters = vec![
        world_type.clone(),
        config.clone(),
        other_config.clone(),
        world.clone(),
        other_world.clone(),
        bool_world.clone(),
        machine.clone(),
    ];
    Fixture {
        model: model(world_type.term().clone()),
        config,
        other_config,
        world,
        other_world,
        bool_world,
        machine,
        parameters,
    }
}

#[test]
fn closed_call_owner_mapper_replays_opaque_polymorphic_endpoints_without_hot_locals() {
    let mut scope = Scope::new();
    let f = fixture(&mut scope);
    let mut assembler = Assembler::new(&mut scope, limits()).unwrap();
    let eta = world_eta(&mut assembler, &f.model, f.world.term().clone()).unwrap();
    assert_eq!(assembler.locals, 7);
    assert_eq!(assembler.operations(), 8);
    let function = push_world_mapper(&f.model.world_type, f.config.term().clone());
    for iteration in 0..32 {
        let mapped = assembler
            .congruence_function(eta.clone(), f.model.config_type(), function.clone())
            .unwrap();
        assert_eq!(assembler.locals, 7);
        assert_eq!(assembler.operations(), 9 + iteration);
        assert_eq!(*mapped.term().get_app_args()[4], function);
        if iteration == 0 || iteration == 31 {
            let claim = independent(
                &f.model,
                f.config.term().clone(),
                f.world.term().clone(),
                eta.right().clone(),
                mapped.term().clone(),
            );
            replay(assembler.local_scope(), &f.parameters, &claim, true);
        }
    }
}

#[test]
fn closed_call_owner_mapper_rejects_forged_eta_and_changed_config_world_type_endpoints() {
    let mut scope = Scope::new();
    let f = fixture(&mut scope);
    let mut assembler = Assembler::new(&mut scope, limits()).unwrap();
    let eta = world_eta(&mut assembler, &f.model, f.world.term().clone()).unwrap();
    let function = push_world_mapper(&f.model.world_type, f.config.term().clone());
    let mapped = assembler
        .congruence_function(eta.clone(), f.model.config_type(), function)
        .unwrap();
    let genuine = independent(
        &f.model,
        f.config.term().clone(),
        f.world.term().clone(),
        eta.right().clone(),
        mapped.term().clone(),
    );
    replay(assembler.local_scope(), &f.parameters, &genuine, true);
    let changed = [
        direct(
            f.model.world_type.clone(),
            f.other_config.term().clone(),
            eta.right().clone(),
        ),
        direct(
            f.model.world_type.clone(),
            f.config.term().clone(),
            f.other_world.term().clone(),
        ),
        // Omitting the owner push is not definitional world eta.
        app(
            "ir_byte_lift_v1",
            [
                f.model.world_type.clone(),
                eta.right().clone(),
                f.config.term().clone(),
            ],
        ),
    ];
    for right in changed {
        let forged = PendingEquality::candidate(
            f.model.config_type(),
            genuine.left().clone(),
            right,
            mapped.term().clone(),
        );
        replay(assembler.local_scope(), &f.parameters, &forged, false);
    }
    let bool_model = model(constant("Bool"));
    let wrong_type = independent(
        &bool_model,
        f.config.term().clone(),
        f.bool_world.term().clone(),
        f.bool_world.term().clone(),
        mapped.term().clone(),
    );
    replay(assembler.local_scope(), &f.parameters, &wrong_type, false);
    for corrupt in [
        PendingEquality::candidate(
            eta.ty.clone(),
            eta.left().clone(),
            eta.right().clone(),
            constant("True.intro"),
        ),
        PendingEquality::candidate(
            eta.ty.clone(),
            eta.left().clone(),
            f.other_world.term().clone(),
            eta.term().clone(),
        ),
    ] {
        let proof = assembler
            .congruence_function(
                corrupt.clone(),
                f.model.config_type(),
                push_world_mapper(&f.model.world_type, f.config.term().clone()),
            )
            .unwrap();
        let claim = independent(
            &f.model,
            f.config.term().clone(),
            corrupt.left().clone(),
            corrupt.right().clone(),
            proof.term().clone(),
        );
        replay(assembler.local_scope(), &f.parameters, &claim, false);
    }
    for function in [
        push_world_mapper(&constant("Bool"), f.config.term().clone()),
        push_world_mapper(&f.model.world_type, f.world.term().clone()),
    ] {
        let proof = assembler
            .congruence_function(eta.clone(), f.model.config_type(), function)
            .unwrap();
        let claim = PendingEquality::candidate(
            f.model.config_type(),
            genuine.left().clone(),
            genuine.right().clone(),
            proof.term().clone(),
        );
        replay(assembler.local_scope(), &f.parameters, &claim, false);
    }
}

#[test]
fn closed_call_owner_mapper_does_not_capture_independent_external_type_config_world_bvars() {
    let mut scope = Scope::new();
    let mut assembler = Assembler::new(&mut scope, limits()).unwrap();
    // Invoke production before adding ANY ordinary binder. The five external
    // operands below are independently bound U/config/other_config/world/other_world.
    let model = model(Expr::bvar(4));
    let config = Expr::bvar(3);
    let world = Expr::bvar(1);
    let eta = world_eta(&mut assembler, &model, world.clone()).unwrap();
    let function = push_world_mapper(&model.world_type, config.clone());
    let proof = assembler
        .congruence_function(eta.clone(), model.config_type(), function)
        .unwrap();
    assert_eq!(assembler.locals, 7);
    assert_eq!(assembler.operations(), 9);
    let domains = [
        Expr::type_(),
        constant("IRConfig"),
        constant("IRConfig"),
        app("IRByteWorldV1", [Expr::bvar(2)]),
        app("IRByteWorldV1", [Expr::bvar(3)]),
    ];
    for (right, accepted) in [
        (
            direct(
                model.world_type.clone(),
                config.clone(),
                eta.right().clone(),
            ),
            true,
        ),
        (
            direct(model.world_type.clone(), Expr::bvar(2), eta.right().clone()),
            false,
        ),
        (
            direct(model.world_type.clone(), config.clone(), Expr::bvar(0)),
            false,
        ),
    ] {
        let claim = PendingEquality::candidate(
            model.config_type(),
            direct(model.world_type.clone(), config.clone(), world.clone()),
            right,
            proof.term().clone(),
        );
        let term = domains.iter().rev().fold(claim.term().clone(), |body, ty| {
            Expr::lam(BinderInfo::Default, ty.clone(), body)
        });
        let proposition = domains.iter().rev().fold(claim.proposition(), |body, ty| {
            Expr::pi(BinderInfo::Default, ty.clone(), body)
        });
        check_closed(
            assembler.local_scope().close(&term).unwrap(),
            assembler.local_scope().close(&proposition).unwrap(),
            accepted,
        );
    }
}

#[test]
fn closed_call_owner_mapper_preserves_single_charge_and_exhausted_local_operation_caps() {
    for cap in [1, 2, 3] {
        let mut scope = Scope::new();
        let config = scope.try_local(constant("IRConfig")).unwrap();
        let world = scope
            .try_local(app("IRByteWorldV1", [constant("Nat")]))
            .unwrap();
        let parameters = [config.clone(), world.clone()];
        let mut assembler = Assembler::new(
            &mut scope,
            Limits {
                max_operations: cap,
                max_locals: 1,
                ..limits()
            },
        )
        .unwrap();
        // Occupy the entire admitted local allowance before mapping. Zero
        // limits are still refused by the ordinary Limits admission policy.
        let _occupied = assembler.local(constant("Nat")).unwrap();
        let equality = PendingEquality::candidate(
            world.ty().clone(),
            world.term().clone(),
            world.term().clone(),
            refl(world.ty(), world.term().clone()),
        );
        for iteration in 0..cap {
            let proof = assembler.congruence_function(
                equality.clone(),
                app("IRByteConfigV1", [constant("Nat")]),
                push_world_mapper(&constant("Nat"), config.term().clone()),
            );
            if iteration + 1 == cap {
                assert_eq!(
                    proof.err().unwrap(),
                    "execution construction operation budget exceeded"
                );
            } else {
                let proof = proof.unwrap();
                let claim = independent(
                    &model(constant("Nat")),
                    config.term().clone(),
                    world.term().clone(),
                    world.term().clone(),
                    proof.term().clone(),
                );
                replay(assembler.local_scope(), &parameters, &claim, true);
            }
            assert_eq!(assembler.locals, 1);
            assert_eq!(assembler.local_scope().allocated(), 3);
            assert_eq!(assembler.operations(), (iteration + 2).min(cap));
        }
    }
}

#[test]
fn closed_call_owner_mapper_does_not_supply_world_validity_or_escape_source_world() {
    let mut scope = Scope::new();
    let f = fixture(&mut scope);
    let mut assembler = Assembler::new(&mut scope, limits()).unwrap();
    let eta = world_eta(&mut assembler, &f.model, f.world.term().clone()).unwrap();
    let proof = assembler
        .congruence_function(
            eta,
            f.model.config_type(),
            push_world_mapper(&f.model.world_type, f.config.term().clone()),
        )
        .unwrap();
    let validity = app(
        "ir_byte_world_valid_v1",
        [
            f.model.world_type.clone(),
            f.machine.term().clone(),
            f.world.term().clone(),
        ],
    );
    let forged = PendingEquality::candidate(
        constant("Bool"),
        validity,
        constant("Bool.true"),
        proof.term().clone(),
    );
    replay(assembler.local_scope(), &f.parameters, &forged, false);
    let mut escaped = f.parameters.clone();
    escaped.retain(|parameter| parameter.term() != f.world.term());
    let term = escaped
        .iter()
        .rev()
        .fold(proof.term().clone(), |body, local| local.lam(body));
    assert!(matches!(
        assembler.local_scope().close(&term),
        Err(crate::scoped_local::LocalScopeError::Closure(
            crate::term_scope::TermScopeError::OutOfScope(id)
        )) if id == f.world.id()
    ));
}
