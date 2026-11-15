// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Kernel-replayed constructor reconstruction, not world validity, allocation
//! permission, native execution, or a proof of a consuming whole program.

use super::*;
use clean_kernel::{BinderInfo, KernelTypeError};
use clean_verify::eval_ir::{EvalIrVocabulary, shared_specification_with_stack};

fn environment() -> &'static Environment {
    shared_specification_with_stack(EvalIrVocabulary::ByteV1)
        .unwrap()
        .env()
}

fn checker() -> TypeChecker<'static> {
    let mut checker = TypeChecker::new(environment());
    checker.set_allow_unsafe(false);
    checker.set_allow_partial(false);
    checker.set_heartbeat_limit(5_000_000);
    checker.set_max_cache_entries(100_000);
    checker
}

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
    // This isolated helper reads only the host-world type. Neither unused
    // expression is introduced into its claim or its closed proof candidate.
    MachineModel {
        world_type,
        context: constant("world_eta_unused_context"),
        providers: constant("world_eta_unused_providers"),
    }
}

fn close(scope: &Scope, parameters: &[Local], proof: &PendingEquality) -> (Expr, Expr) {
    let term = parameters
        .iter()
        .rev()
        .fold(proof.term().clone(), |body, local| local.lam(body));
    let claim = parameters
        .iter()
        .rev()
        .fold(proof.proposition(), |body, local| local.pi(body));
    (scope.close(&term).unwrap(), scope.close(&claim).unwrap())
}

fn replay(scope: &Scope, parameters: &[Local], proof: &PendingEquality, accepted: bool) {
    let (term, claim) = close(scope, parameters, proof);
    assert!(!term.has_fvar_quick() && !claim.has_fvar_quick());
    let checker = checker();
    checker
        .check_type(&claim, &Expr::sort(Level::zero()))
        .expect("the candidate has a real well-typed proposition");
    if accepted {
        checker.check_type(&term, &claim).unwrap();
        assert!(
            environment()
                .audit_certification(&claim, &term)
                .is_certified()
        );
        let encoded = trust_ir::proof::encode_clean_expr_dag_v2(&term).unwrap();
        let decoded = trust_ir::proof::decode_clean_expr_dag_v2(&encoded).unwrap();
        assert_eq!(decoded, term);
        assert!(!decoded.has_fvar_quick());
        checker.check_type(&decoded, &claim).unwrap();
        assert!(
            environment()
                .audit_certification(&claim, &decoded)
                .is_certified()
        );
    } else {
        let error = checker.check_type(&term, &claim).unwrap_err();
        assert!(
            matches!(error, KernelTypeError::TypeMismatch { .. }),
            "semantic mismatch, not a heartbeat/resource refusal: {error:?}"
        );
    }
}

fn reconstructed(world_type: Expr, world: Expr) -> Expr {
    // Independently spell the public constructor and its exact four fields.
    app(
        "IRByteWorldV1.mk",
        [
            world_type.clone(),
            app(
                "ir_byte_world_memory_v1",
                [world_type.clone(), world.clone()],
            ),
            app("ir_byte_world_host_v1", [world_type.clone(), world.clone()]),
            app(
                "ir_byte_world_owners_v1",
                [world_type.clone(), world.clone()],
            ),
            app("ir_byte_world_next_v1", [world_type, world]),
        ],
    )
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
                    Some(byte) => app("IROption.some", [constant("Nat"), nat(byte)]),
                    None => app("IROption.none", [constant("Nat")]),
                },
            ),
            nat(cursor),
        ],
    )
}

fn world(world_type: Expr, memory: Expr, host: Expr, owners: &[u64], next: u64) -> Expr {
    app(
        "IRByteWorldV1.mk",
        [
            world_type,
            memory,
            host,
            list("Nat", &owners.iter().copied().map(nat).collect::<Vec<_>>()),
            nat(next),
        ],
    )
}

fn same_cached_graph(left: &Expr, right: &Expr) {
    match (left.kind(), right.kind()) {
        (ExprKind::Lam(_, left_ty, left_body), ExprKind::Lam(_, right_ty, right_body)) => {
            assert!(std::sync::Arc::ptr_eq(left_ty, right_ty));
            assert!(std::sync::Arc::ptr_eq(left_body, right_body));
        }
        _ => panic!("the closed cached helper quantifies its world type"),
    }
}

#[test]
fn world_eta_symbolic_type_and_opaque_world_replays_kernel_dag_v2() {
    let mut scope = Scope::new();
    let mut assembler = Assembler::new(&mut scope, limits()).unwrap();
    let unrelated = assembler.local(constant("Nat")).unwrap();
    let world_type = assembler.local(Expr::type_()).unwrap();
    let opaque = assembler
        .local(app("IRByteWorldV1", [world_type.term().clone()]))
        .unwrap();
    let before = assembler.locals;
    let proof = world_eta(
        &mut assembler,
        &model(world_type.term().clone()),
        opaque.term().clone(),
    )
    .unwrap();
    assert_eq!(assembler.locals - before, 7);
    assert_eq!(proof.left(), opaque.term());
    assert_eq!(
        proof.right(),
        &reconstructed(world_type.term().clone(), opaque.term().clone())
    );
    assert!(
        !assembler
            .world_eta_candidate
            .as_ref()
            .unwrap()
            .has_fvar_quick()
    );
    replay(
        assembler.local_scope(),
        &[unrelated, world_type, opaque],
        &proof,
        true,
    );
}

#[test]
fn world_eta_closed_cache_reuses_nat_bool_and_changed_worlds() {
    let mut scope = Scope::new();
    let mut assembler = Assembler::new(&mut scope, limits()).unwrap();
    let nat_world = assembler
        .local(app("IRByteWorldV1", [constant("Nat")]))
        .unwrap();
    let bool_world = assembler
        .local(app("IRByteWorldV1", [constant("Bool")]))
        .unwrap();
    let first = world_eta(
        &mut assembler,
        &model(constant("Nat")),
        nat_world.term().clone(),
    )
    .unwrap();
    let saved = assembler.world_eta_candidate.clone().unwrap();
    let locals = assembler.locals;
    let operations = assembler.operations;
    let second = world_eta(
        &mut assembler,
        &model(constant("Bool")),
        bool_world.term().clone(),
    )
    .unwrap();
    let third = world_eta(
        &mut assembler,
        &model(constant("Bool")),
        world(
            constant("Bool"),
            memory(Some(173), 12),
            constant("Bool.false"),
            &[8, 7],
            19,
        ),
    )
    .unwrap();
    assert_eq!(assembler.locals, locals);
    assert_eq!(assembler.operations, operations + 2);
    same_cached_graph(&saved, assembler.world_eta_candidate.as_ref().unwrap());
    replay(assembler.local_scope(), &[nat_world], &first, true);
    replay(assembler.local_scope(), &[bool_world], &second, true);
    replay(assembler.local_scope(), &[], &third, true);
}

#[test]
fn world_eta_repeated_calls_fit_the_unchanged_one_hundred_local_limit() {
    let mut scope = Scope::new();
    let mut assembler = Assembler::new(&mut scope, limits()).unwrap();
    let world_type = assembler.local(Expr::type_()).unwrap();
    let opaque = assembler
        .local(app("IRByteWorldV1", [world_type.term().clone()]))
        .unwrap();
    let model = model(world_type.term().clone());
    let first = world_eta(&mut assembler, &model, opaque.term().clone()).unwrap();
    let saved = assembler.world_eta_candidate.clone().unwrap();
    let locals = assembler.locals;
    let operations = assembler.operations;
    let mut last = first.clone();
    for _ in 0..32 {
        last = world_eta(&mut assembler, &model, opaque.term().clone()).unwrap();
        assert_eq!(assembler.locals, locals, "cache hits allocate no locals");
    }
    assert_eq!(
        locals, 9,
        "two actual inputs plus seven closed-template locals"
    );
    assert_eq!(assembler.operations, operations + 32);
    assert_eq!(assembler.limits.max_locals, 100);
    same_cached_graph(&saved, assembler.world_eta_candidate.as_ref().unwrap());
    assert_eq!(first.left(), last.left());
    assert_eq!(first.right(), last.right());
    let parameters = [world_type, opaque];
    replay(assembler.local_scope(), &parameters, &first, true);
    replay(assembler.local_scope(), &parameters, &last, true);
}

#[test]
fn world_eta_rejects_changed_memory_host_owner_order_and_cursor() {
    let mut scope = Scope::new();
    let mut assembler = Assembler::new(&mut scope, limits()).unwrap();
    let original = world(constant("Nat"), memory(Some(173), 12), nat(37), &[8, 7], 9);
    let proof = world_eta(&mut assembler, &model(constant("Nat")), original).unwrap();
    assert_eq!(assembler.locals, 0);
    assert_eq!(assembler.operations, 1);
    assert!(assembler.world_eta_candidate.is_none());
    replay(assembler.local_scope(), &[], &proof, true);
    for changed in [
        world(constant("Nat"), memory(None, 12), nat(37), &[8, 7], 9),
        world(constant("Nat"), memory(Some(173), 13), nat(37), &[8, 7], 9),
        world(constant("Nat"), memory(Some(173), 12), nat(38), &[8, 7], 9),
        world(constant("Nat"), memory(Some(173), 12), nat(37), &[7, 8], 9),
        world(constant("Nat"), memory(Some(173), 12), nat(37), &[8, 7], 10),
    ] {
        let forged = PendingEquality::candidate(
            app("IRByteWorldV1", [constant("Nat")]),
            proof.left().clone(),
            changed,
            proof.term().clone(),
        );
        replay(assembler.local_scope(), &[], &forged, false);
    }
    let wrong_type = PendingEquality::candidate(
        app("IRByteWorldV1", [constant("Bool")]),
        proof.left().clone(),
        proof.right().clone(),
        proof.term().clone(),
    );
    let (_, claim) = close(assembler.local_scope(), &[], &wrong_type);
    assert!(
        checker()
            .check_type(&claim, &Expr::sort(Level::zero()))
            .is_err()
    );
}

#[test]
fn world_eta_does_not_grant_world_validity_or_memory_permission() {
    let mut scope = Scope::new();
    let mut assembler = Assembler::new(&mut scope, limits()).unwrap();
    let no_allocations = memory(None, 0);
    let proof = world_eta(
        &mut assembler,
        &model(constant("Nat")),
        world(constant("Nat"), no_allocations, nat(0), &[8, 8], 0),
    )
    .unwrap();
    replay(assembler.local_scope(), &[], &proof, true);
    let accessible = app(
        "ir_byte_accessible_v1",
        [list("IRByteAllocationV1", &[]), nat(80), nat(8), nat(8)],
    );
    let unavailable = PendingEquality::candidate(
        constant("Bool"),
        accessible.clone(),
        constant("Bool.false"),
        refl(&constant("Bool"), constant("Bool.false")),
    );
    replay(assembler.local_scope(), &[], &unavailable, true);
    let fake_permission = PendingEquality::candidate(
        constant("Bool"),
        accessible,
        constant("Bool.true"),
        proof.term().clone(),
    );
    replay(assembler.local_scope(), &[], &fake_permission, false);
}

#[test]
fn world_eta_keeps_first_construction_and_cache_hit_budget_refusals() {
    // A well-typed but not directly spelled constructor must still take the
    // recursor path, even though this particular function application reduces.
    let actual_world = app(
        "ir_byte_with_memory_v1",
        [
            constant("Nat"),
            world(constant("Nat"), memory(None, 0), nat(0), &[], 0),
            memory(None, 0),
        ],
    );
    for small in [
        Limits {
            max_operations: 1,
            ..limits()
        },
        Limits {
            max_locals: 1,
            ..limits()
        },
    ] {
        let mut scope = Scope::new();
        let mut assembler = Assembler::new(&mut scope, small).unwrap();
        let error = match world_eta(
            &mut assembler,
            &model(constant("Nat")),
            actual_world.clone(),
        ) {
            Ok(_) => panic!("a closed template must not bypass construction limits"),
            Err(error) => error,
        };
        assert!(error.contains("execution construction"));
        assert!(assembler.world_eta_candidate.is_none());
    }
    let mut scope = Scope::new();
    let mut assembler = Assembler::new(&mut scope, limits()).unwrap();
    let model = model(constant("Nat"));
    world_eta(&mut assembler, &model, actual_world.clone()).unwrap();
    let locals = assembler.locals;
    let cached = assembler.world_eta_candidate.clone().unwrap();
    while assembler.operations < assembler.limits.max_operations {
        world_eta(&mut assembler, &model, actual_world.clone()).unwrap();
        assert_eq!(assembler.locals, locals);
    }
    let error = match world_eta(&mut assembler, &model, actual_world) {
        Ok(_) => panic!("cache hits must still charge the actual operation budget"),
        Err(error) => error,
    };
    assert_eq!(error, "execution construction operation budget exceeded");
    assert_eq!(assembler.operations, 1_000);
    assert_eq!(assembler.locals, locals);
    same_cached_graph(&cached, assembler.world_eta_candidate.as_ref().unwrap());
}

#[test]
fn world_eta_explicit_nat_and_bool_keep_exact_fields_without_a_factory() {
    let mut scope = Scope::new();
    let mut assembler = Assembler::new(&mut scope, limits()).unwrap();
    for (world_type, actual) in [
        (
            constant("Nat"),
            world(constant("Nat"), memory(Some(173), 12), nat(37), &[8, 7], 9),
        ),
        (
            constant("Bool"),
            world(
                constant("Bool"),
                memory(None, 99),
                constant("Bool.false"),
                &[7, 8],
                0,
            ),
        ),
    ] {
        let before = assembler.operations;
        let actual_model = model(world_type.clone());
        assert!(is_explicit_world(&actual_model, &actual));
        let proof = world_eta(&mut assembler, &actual_model, actual.clone()).unwrap();
        assert_eq!(proof.left(), &actual);
        assert_eq!(proof.right(), &reconstructed(world_type, actual));
        assert_eq!(assembler.operations, before + 1);
        assert_eq!(assembler.locals, 0);
        assert!(assembler.world_eta_candidate.is_none());
        replay(assembler.local_scope(), &[], &proof, true);
    }
}

#[test]
fn world_eta_explicit_symbolic_type_and_opaque_fields_replay_without_locals() {
    let mut scope = Scope::new();
    let mut assembler = Assembler::new(&mut scope, limits()).unwrap();
    let world_type = assembler.local(Expr::type_()).unwrap();
    let memory = assembler.local(constant("IRByteMemoryV1")).unwrap();
    let host = assembler.local(world_type.term().clone()).unwrap();
    let owners = assembler.local(app("IRList", [constant("Nat")])).unwrap();
    let next = assembler.local(constant("Nat")).unwrap();
    let actual = app(
        "IRByteWorldV1.mk",
        [
            world_type.term().clone(),
            memory.term().clone(),
            host.term().clone(),
            owners.term().clone(),
            next.term().clone(),
        ],
    );
    let before = (assembler.locals, assembler.operations);
    let proof = world_eta(
        &mut assembler,
        &model(world_type.term().clone()),
        actual.clone(),
    )
    .unwrap();
    assert_eq!(assembler.locals, before.0);
    assert_eq!(assembler.operations, before.1 + 1);
    assert!(assembler.world_eta_candidate.is_none());
    assert_eq!(proof.left(), &actual);
    assert_eq!(
        proof.right(),
        &reconstructed(world_type.term().clone(), actual)
    );
    replay(
        assembler.local_scope(),
        &[world_type, memory, host, owners, next],
        &proof,
        true,
    );
}

#[test]
fn world_eta_explicit_then_opaque_preserves_closed_cache_custody() {
    let mut scope = Scope::new();
    let mut assembler = Assembler::new(&mut scope, limits()).unwrap();
    let first = world_eta(
        &mut assembler,
        &model(constant("Nat")),
        world(constant("Nat"), memory(Some(173), 12), nat(37), &[8, 7], 9),
    )
    .unwrap();
    assert_eq!(assembler.locals, 0);
    assert!(assembler.world_eta_candidate.is_none());
    let opaque = assembler
        .local(app("IRByteWorldV1", [constant("Bool")]))
        .unwrap();
    let before = (assembler.locals, assembler.operations);
    let fallback = world_eta(
        &mut assembler,
        &model(constant("Bool")),
        opaque.term().clone(),
    )
    .unwrap();
    assert_eq!(assembler.locals, before.0 + 7);
    assert_eq!(assembler.operations, before.1 + 8);
    let cached = assembler.world_eta_candidate.clone().unwrap();
    assert!(!cached.has_fvar_quick());
    let before = (assembler.locals, assembler.operations);
    let changed = world_eta(
        &mut assembler,
        &model(constant("Bool")),
        world(
            constant("Bool"),
            memory(None, 0),
            constant("Bool.false"),
            &[8, 8],
            0,
        ),
    )
    .unwrap();
    assert_eq!(assembler.locals, before.0);
    assert_eq!(assembler.operations, before.1 + 1);
    same_cached_graph(&cached, assembler.world_eta_candidate.as_ref().unwrap());
    replay(assembler.local_scope(), &[], &first, true);
    replay(assembler.local_scope(), &[opaque], &fallback, true);
    replay(assembler.local_scope(), &[], &changed, true);
}

#[test]
fn world_eta_constructor_selector_checks_exact_head_arity_type_and_levels() {
    let actual_model = model(constant("Nat"));
    let fields = [
        constant("Nat"),
        memory(None, 0),
        nat(0),
        list("Nat", &[]),
        nat(0),
    ];
    let actual = app("IRByteWorldV1.mk", fields.clone());
    assert!(is_explicit_world(&actual_model, &actual));
    for changed in [
        app("IRByteWorldV1.mk", fields[..4].iter().cloned()),
        Expr::app(actual.clone(), nat(0)),
        app("not_a_world_constructor", fields.clone()),
        world(
            constant("Bool"),
            memory(None, 0),
            constant("Bool.true"),
            &[],
            0,
        ),
        Expr::apps(
            Expr::const_(Name::from_string("IRByteWorldV1.mk"), vec![Level::zero()]),
            fields,
        ),
    ] {
        assert!(!is_explicit_world(&actual_model, &changed));
    }
    let mut scope = Scope::new();
    let mut assembler = Assembler::new(&mut scope, limits()).unwrap();
    let wrong_host_type = world(
        constant("Bool"),
        memory(None, 0),
        constant("Bool.true"),
        &[],
        0,
    );
    let candidate = world_eta(&mut assembler, &actual_model, wrong_host_type).unwrap();
    assert_eq!(
        assembler.locals, 7,
        "type mismatch does not select conversion"
    );
    assert!(assembler.world_eta_candidate.is_some());
    let (_, claim) = close(assembler.local_scope(), &[], &candidate);
    assert!(
        checker()
            .check_type(&claim, &Expr::sort(Level::zero()))
            .is_err()
    );
}

#[test]
fn world_eta_explicit_application_retains_exact_operation_and_local_caps() {
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
    let actual_model = model(constant("Nat"));
    let actual = world(constant("Nat"), memory(None, 0), nat(0), &[], 0);
    let proof = world_eta(&mut assembler, &actual_model, actual.clone()).unwrap();
    assert_eq!(assembler.operations, 1);
    assert_eq!(assembler.locals, 0);
    assert!(assembler.world_eta_candidate.is_none());
    replay(assembler.local_scope(), &[], &proof, true);
    let error = world_eta(&mut assembler, &actual_model, actual.clone())
        .err()
        .expect("the second application exceeds the unchanged one-operation cap");
    assert_eq!(error, "execution construction operation budget exceeded");
    assert_eq!(assembler.operations, 1);

    let mut full_scope = Scope::new();
    let mut full = Assembler::new(&mut full_scope, limits()).unwrap();
    for _ in 0..100 {
        full.local(constant("Nat")).unwrap();
    }
    let proof = world_eta(&mut full, &actual_model, actual.clone()).unwrap();
    assert_eq!(
        full.locals, 100,
        "conversion adds no locals at the actual cap"
    );
    assert_eq!(full.operations, 101);
    assert_eq!(full.limits.max_locals, 100);
    assert_eq!(full.limits.max_operations, 1_000);
    replay(full.local_scope(), &[], &proof, true);
    let opaque_application = app(
        "ir_byte_with_memory_v1",
        [constant("Nat"), actual, memory(None, 0)],
    );
    let error = world_eta(&mut full, &actual_model, opaque_application)
        .err()
        .expect("the opaque-world factory still cannot allocate beyond the actual cap");
    assert_eq!(error, "execution construction local budget exceeded");
    assert_eq!(full.locals, 100);
    assert!(full.world_eta_candidate.is_none());
}
