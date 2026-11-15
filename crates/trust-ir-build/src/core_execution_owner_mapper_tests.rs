// Copyright 2026 Andrew Yates | Licensed under the Apache License, Version 2.0

//! Strict replay of the real allocation-only owner transport. These conditional
//! component proofs do not grant access, initialized bytes or native authority.

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

fn check_closed(term: Expr, claim: Expr, accepted: bool) {
    let environment = shared_specification_with_stack(EvalIrVocabulary::ByteV1)
        .unwrap()
        .env();
    let mut checker = TypeChecker::new(environment);
    checker.set_allow_unsafe(false);
    checker.set_allow_partial(false);
    checker.set_heartbeat_limit(5_000_000);
    checker.set_max_cache_entries(100_000);
    assert!(!term.has_fvar_quick() && !claim.has_fvar_quick());
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

fn replay(scope: &Scope, parameters: &[Local], proof: &PendingEquality, accepted: bool) {
    let term = parameters
        .iter()
        .rev()
        .fold(proof.term().clone(), |body, p| p.lam(body));
    let claim = parameters
        .iter()
        .rev()
        .fold(proof.proposition(), |body, p| p.pi(body));
    check_closed(
        scope.close(&term).unwrap(),
        scope.close(&claim).unwrap(),
        accepted,
    );
}

fn rows(owner: u64) -> Expr {
    list(
        "IRByteAllocationV1",
        &[app(
            "IRByteAllocationV1.mk",
            [nat(16), nat(8), nat(owner), constant("Bool.true")],
        )],
    )
}

fn memory(rows: Expr, byte: u64, cursor: u64) -> Expr {
    app(
        "IRByteMemoryV1.mk",
        [
            rows,
            Expr::lam(BinderInfo::Default, constant("Nat"), some("Nat", nat(byte))),
            nat(cursor),
        ],
    )
}

fn fixture(world_type: Expr, host: Expr) -> (MachineModel, Current) {
    let model = MachineModel {
        world_type: world_type.clone(),
        context: constant("owner_mapper_unused_context"),
        providers: constant("owner_mapper_unused_providers"),
    };
    let current = Current {
        frame: app(
            "IRFrame.mk",
            [
                nat(41),
                nat(17),
                nat(9),
                list("IRBinding", &[]),
                list("Nat", &[]),
            ],
        ),
        tail: list("IRFrame", &[]),
        legacy_memory: list("IRMemSlot", &[]),
        legacy_cursor: nat(0),
        world: app(
            "IRByteWorldV1.mk",
            [
                world_type,
                memory(rows(7), 11, 65),
                host,
                list("Nat", &[nat(7)]),
                nat(8),
            ],
        ),
    };
    (model, current)
}

#[test]
fn allocation_owner_mapper_does_not_capture_external_bound_operands() {
    let mut scope = Scope::new();
    let mut assembler = Assembler::new(&mut scope, limits()).unwrap();
    // The actual operands deliberately contain open bvars. Their four
    // independently constructed external binders are added only after mapping.
    let memory = Expr::bvar(3);
    let owners = Expr::bvar(2);
    let next = Expr::bvar(1);
    let allocations = Expr::bvar(0);
    let left = Expr::app(
        allocation_owner_mapper(memory.clone(), owners.clone(), next.clone()),
        allocations.clone(),
    );
    let right = app(
        "ir_byte_memory_owners_v1",
        [
            app(
                "IRByteMemoryV1.mk",
                [
                    allocations,
                    app("ir_byte_mem_bytes_v1", [memory.clone()]),
                    app("ir_byte_mem_next_v1", [memory]),
                ],
            ),
            owners,
            next,
        ],
    );
    let proof = assembler.conversion(constant("Bool"), left, right).unwrap();
    assert_eq!(assembler.locals, 0);
    assert_eq!(assembler.operations, 1);
    let types = [
        constant("IRByteMemoryV1"),
        app("IRList", [constant("Nat")]),
        constant("Nat"),
        app("IRList", [constant("IRByteAllocationV1")]),
    ];
    let term = types.iter().rev().fold(proof.term().clone(), |body, ty| {
        Expr::lam(BinderInfo::Default, ty.clone(), body)
    });
    let claim = types.iter().rev().fold(proof.proposition(), |body, ty| {
        Expr::pi(BinderInfo::Default, ty.clone(), body)
    });
    check_closed(term, claim, true);
}

#[test]
fn repeated_returned_owner_transports_use_no_locals_at_exact_budget() {
    for (world_type, host) in [
        (constant("Nat"), nat(37)),
        (constant("Bool"), constant("Bool.false")),
    ] {
        let (model, current) = fixture(world_type, host);
        let before = PendingEquality::candidate(
            constant("Bool"),
            current.valid(&model),
            constant("Bool.true"),
            refl(&constant("Bool"), constant("Bool.true")),
        );
        let mut scope = Scope::new();
        let mut policy = limits();
        policy.max_locals = 1;
        policy.max_operations = 10;
        let mut assembler = Assembler::new(&mut scope, policy).unwrap();
        let existing = assembler.local(constant("Nat")).unwrap();
        for (index, byte) in [22, 33, 44].into_iter().enumerate() {
            let returned = memory(rows(7), byte, 101 + index as u64);
            let same_allocations = PendingEquality::candidate(
                app("IRList", [constant("IRByteAllocationV1")]),
                allocations(returned.clone()),
                allocations(projection(&model, &current.world, "memory")),
                refl(&app("IRList", [constant("IRByteAllocationV1")]), rows(7)),
            );
            let proof = returned_memory_owners(
                &mut assembler,
                &model,
                &current,
                &returned,
                same_allocations,
                &before,
            )
            .unwrap();
            assert_eq!(assembler.locals, 1);
            assert_eq!(assembler.local_scope().allocated(), 1);
            assert_eq!(assembler.operations, 1 + (index + 1) * 3);
            let independent = PendingEquality::candidate(
                constant("Bool"),
                app(
                    "ir_byte_memory_owners_v1",
                    [returned.clone(), list("Nat", &[nat(7)]), nat(8)],
                ),
                constant("Bool.true"),
                proof.term().clone(),
            );
            replay(
                assembler.local_scope(),
                std::slice::from_ref(&existing),
                &independent,
                true,
            );
            for wrong in [
                app(
                    "ir_byte_memory_owners_v1",
                    [memory(rows(9), byte, 101), list("Nat", &[nat(7)]), nat(8)],
                ),
                app(
                    "ir_byte_memory_owners_v1",
                    [returned.clone(), list("Nat", &[]), nat(8)],
                ),
                app(
                    "ir_byte_memory_owners_v1",
                    [returned.clone(), list("Nat", &[nat(7)]), nat(7)],
                ),
            ] {
                replay(
                    assembler.local_scope(),
                    std::slice::from_ref(&existing),
                    &PendingEquality::candidate(
                        constant("Bool"),
                        wrong,
                        constant("Bool.true"),
                        proof.term().clone(),
                    ),
                    false,
                );
            }
        }
        let returned = memory(rows(7), 55, 999);
        let same_allocations = PendingEquality::reflexive(
            app("IRList", [constant("IRByteAllocationV1")]),
            allocations(returned.clone()),
        );
        assert!(
            returned_memory_owners(
                &mut assembler,
                &model,
                &current,
                &returned,
                same_allocations,
                &before
            )
            .err()
            .unwrap()
            .contains("operation budget")
        );
        assert_eq!(assembler.operations, 10);
        assert_eq!(assembler.locals, 1);
    }
}

#[test]
fn opaque_world_and_returned_memory_preserve_explicit_allocation_premises() {
    let mut scope = Scope::new();
    let world_type = scope.try_local(Expr::type_()).unwrap();
    let world = scope
        .try_local(app("IRByteWorldV1", [world_type.term().clone()]))
        .unwrap();
    let returned = scope.try_local(constant("IRByteMemoryV1")).unwrap();
    let (mut model, mut current) = fixture(constant("Nat"), nat(37));
    model.world_type = world_type.term().clone();
    current.world = world.term().clone();
    let old_memory = projection(&model, &current.world, "memory");
    let left = allocations(returned.term().clone());
    let right = allocations(old_memory);
    let same = scope
        .try_local(eq(
            &app("IRList", [constant("IRByteAllocationV1")]),
            left.clone(),
            right.clone(),
        ))
        .unwrap();
    let valid = scope
        .try_local(eq(
            &constant("Bool"),
            current.valid(&model),
            constant("Bool.true"),
        ))
        .unwrap();
    let parameters = [world_type, world, returned, same, valid];
    let before = PendingEquality::candidate(
        constant("Bool"),
        current.valid(&model),
        constant("Bool.true"),
        parameters[4].term().clone(),
    );
    let same_allocations = PendingEquality::candidate(
        app("IRList", [constant("IRByteAllocationV1")]),
        left,
        right,
        parameters[3].term().clone(),
    );
    let mut assembler = Assembler::new(&mut scope, limits()).unwrap();
    let proof = returned_memory_owners(
        &mut assembler,
        &model,
        &current,
        parameters[2].term(),
        same_allocations,
        &before,
    )
    .unwrap();
    assert_eq!(assembler.locals, 0);
    assert_eq!(assembler.operations, 3);
    replay(assembler.local_scope(), &parameters, &proof, true);
    let forged = PendingEquality::candidate(
        constant("Bool"),
        app(
            "ir_byte_memory_owners_v1",
            [memory(rows(9), 11, 65), list("Nat", &[nat(7)]), nat(8)],
        ),
        constant("Bool.true"),
        proof.term().clone(),
    );
    replay(assembler.local_scope(), &parameters, &forged, false);
}
