// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Independent kernel replay of exact with_memory normalization. These claims
//! grant neither memory access nor validity of the reconstructed world.

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
    MachineModel::from_terms(
        world_type.clone(),
        constant("memory_normalization_unused_context"),
        constant("memory_normalization_unused_providers"),
    )
}

fn explicit(world_type: Expr, memory: Expr, host: Expr, owners: Expr, next: Expr) -> Expr {
    app("IRByteWorldV1.mk", [world_type, memory, host, owners, next])
}

fn memory(byte: Option<u64>, cursor: u64) -> Expr {
    app(
        "IRByteMemoryV1.mk",
        [
            list("IRByteAllocationV1", &[]),
            Expr::lam(
                BinderInfo::Default,
                constant("Nat"),
                match byte {
                    Some(byte) => some("Nat", nat(byte)),
                    None => app("IROption.none", [constant("Nat")]),
                },
            ),
            nat(cursor),
        ],
    )
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
    if accepted {
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
    } else {
        let error = checker.check_type(&term, &claim).unwrap_err();
        assert!(
            matches!(error, KernelTypeError::TypeMismatch { .. }),
            "actual mismatch, not a resource refusal: {error:?}"
        );
    }
}

#[test]
fn constructor_memory_normalization_symbolic_fields_uses_no_helper_locals() {
    let mut scope = Scope::new();
    let mut assembler = Assembler::new(&mut scope, limits()).unwrap();
    let world_type = assembler.local(Expr::type_()).unwrap();
    let old_memory = assembler.local(constant("IRByteMemoryV1")).unwrap();
    let host = assembler.local(world_type.term().clone()).unwrap();
    let owners = assembler.local(app("IRList", [constant("Nat")])).unwrap();
    let next = assembler.local(constant("Nat")).unwrap();
    let returned = assembler.local(constant("IRByteMemoryV1")).unwrap();
    let world = explicit(
        world_type.term().clone(),
        old_memory.term().clone(),
        host.term().clone(),
        owners.term().clone(),
        next.term().clone(),
    );
    let locals = assembler.locals;
    let operations = assembler.operations;
    let proof = normalize_memory_world(
        &mut assembler,
        &model(world_type.term().clone()),
        &world,
        returned.term().clone(),
    )
    .unwrap();
    assert_eq!(assembler.locals, locals);
    assert_eq!(assembler.operations, operations + 1);
    assert!(assembler.world_eta_candidate.is_none());
    // Independently spell the result using the original opaque fields, not
    // the helper's projections or a memory/world-validity assumption.
    let expected = explicit(
        world_type.term().clone(),
        returned.term().clone(),
        host.term().clone(),
        owners.term().clone(),
        next.term().clone(),
    );
    let independent = PendingEquality::candidate(
        app("IRByteWorldV1", [world_type.term().clone()]),
        app(
            "ir_byte_with_memory_v1",
            [world_type.term().clone(), world, returned.term().clone()],
        ),
        expected,
        proof.term().clone(),
    );
    let parameters = [world_type, old_memory, host, owners, next, returned];
    replay(assembler.local_scope(), &parameters, &proof, true);
    replay(assembler.local_scope(), &parameters, &independent, true);
}

#[test]
fn constructor_memory_normalization_retains_nat_bool_fields_and_refutes_changes() {
    for (world_type, host, wrong_host) in [
        (constant("Nat"), nat(37), nat(38)),
        (
            constant("Bool"),
            constant("Bool.false"),
            constant("Bool.true"),
        ),
    ] {
        let mut scope = Scope::new();
        let mut assembler = Assembler::new(&mut scope, limits()).unwrap();
        let old = memory(Some(173), 12);
        let returned = memory(None, 42);
        let owners = list("Nat", &[nat(8), nat(7)]);
        let world = explicit(
            world_type.clone(),
            old.clone(),
            host.clone(),
            owners.clone(),
            nat(19),
        );
        let proof = normalize_memory_world(
            &mut assembler,
            &model(world_type.clone()),
            &world,
            returned.clone(),
        )
        .unwrap();
        assert_eq!(assembler.locals, 0);
        assert_eq!(assembler.operations, 1);
        let expected = explicit(
            world_type.clone(),
            returned.clone(),
            host.clone(),
            owners.clone(),
            nat(19),
        );
        let independent = PendingEquality::candidate(
            proof.ty.clone(),
            proof.left().clone(),
            expected,
            proof.term().clone(),
        );
        replay(assembler.local_scope(), &[], &independent, true);
        for changed in [
            explicit(
                world_type.clone(),
                old,
                host.clone(),
                owners.clone(),
                nat(19),
            ),
            explicit(
                world_type.clone(),
                memory(None, 43),
                host.clone(),
                owners.clone(),
                nat(19),
            ),
            explicit(
                world_type.clone(),
                returned.clone(),
                wrong_host,
                owners.clone(),
                nat(19),
            ),
            explicit(
                world_type.clone(),
                returned.clone(),
                host.clone(),
                list("Nat", &[nat(7), nat(8)]),
                nat(19),
            ),
            explicit(
                world_type.clone(),
                returned.clone(),
                host.clone(),
                owners.clone(),
                nat(20),
            ),
        ] {
            let forged = PendingEquality::candidate(
                proof.ty.clone(),
                proof.left().clone(),
                changed,
                proof.term().clone(),
            );
            replay(assembler.local_scope(), &[], &forged, false);
        }
    }
}

// Preserve the old seven-local factory evidence independently of production.
#[test]
fn opaque_memory_normalization_original_oracle_keeps_inductive_fallback_and_closed_cache() {
    let mut scope = Scope::new();
    let mut assembler = Assembler::new(&mut scope, limits()).unwrap();
    let world_type = assembler.local(Expr::type_()).unwrap();
    let world = assembler
        .local(app("IRByteWorldV1", [world_type.term().clone()]))
        .unwrap();
    let returned = assembler.local(constant("IRByteMemoryV1")).unwrap();
    let model = model(world_type.term().clone());
    let locals = assembler.locals;
    let first = world_mapper_tests::original_normalize_memory_world(
        &mut assembler,
        &model,
        world.term(),
        returned.term().clone(),
    )
    .unwrap();
    assert_eq!(
        assembler.locals - locals,
        7,
        "seven inductive factory locals; closed with_memory mapping adds none"
    );
    assert!(
        !assembler
            .world_eta_candidate
            .as_ref()
            .unwrap()
            .has_fvar_quick()
    );
    let locals = assembler.locals;
    let second = world_mapper_tests::original_normalize_memory_world(
        &mut assembler,
        &model,
        world.term(),
        returned.term().clone(),
    )
    .unwrap();
    assert_eq!(
        assembler.locals - locals,
        0,
        "opaque application reuses the factory without caller mapper locals"
    );
    let parameters = [world_type, world, returned];
    replay(assembler.local_scope(), &parameters, &first, true);
    replay(assembler.local_scope(), &parameters, &second, true);
}

#[test]
fn constructor_memory_normalization_charges_operations_not_unused_locals() {
    let mut scope = Scope::new();
    let mut assembler = Assembler::new(
        &mut scope,
        Limits {
            max_operations: 1,
            max_locals: 1,
            ..limits()
        },
    )
    .unwrap();
    // Deliberately invalid ownership is still a well-typed world. This
    // normalization grants no memory-access or world-validity proposition.
    let world = explicit(
        constant("Nat"),
        memory(None, 0),
        nat(0),
        list("Nat", &[nat(8), nat(8)]),
        nat(0),
    );
    let proof = normalize_memory_world(
        &mut assembler,
        &model(constant("Nat")),
        &world,
        memory(Some(7), 1),
    )
    .unwrap();
    assert_eq!(assembler.operations, 1);
    assert_eq!(assembler.locals, 0);
    assert!(assembler.world_eta_candidate.is_none());
    replay(assembler.local_scope(), &[], &proof, true);
    let error = match normalize_memory_world(
        &mut assembler,
        &model(constant("Nat")),
        &world,
        memory(None, 2),
    ) {
        Ok(_) => panic!("constructor normalization must charge the operation cap"),
        Err(error) => error,
    };
    assert_eq!(error, "execution construction operation budget exceeded");
    assert_eq!(assembler.operations, 1);
    assert_eq!(assembler.locals, 0);
}
