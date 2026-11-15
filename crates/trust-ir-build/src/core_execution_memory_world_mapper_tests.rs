// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Independent strict replay of actual opaque-world normalization and the
//! literal old eta/mapper oracle. Old caps remain recorded, not production
//! claims. Local savings grant no validity, initialization or memory access.

use super::*;
use clean_kernel::{BinderInfo, KernelTypeError};
use clean_verify::eval_ir::{EvalIrVocabulary, shared_specification_with_stack};

// Literal old producer retained only as an independent test oracle and old
// construction-cap evidence. Production never selects this proof composer.
pub(super) fn original_normalize_memory_world(
    assembler: &mut Assembler<'_>,
    model: &MachineModel,
    world: &Expr,
    memory: Expr,
) -> Result<PendingEquality> {
    let ty = app("IRByteWorldV1", [model.world_type.clone()]);
    let expected = app(
        "IRByteWorldV1.mk",
        [
            model.world_type.clone(),
            memory.clone(),
            projection(model, world, "host"),
            projection(model, world, "owners"),
            projection(model, world, "next"),
        ],
    );
    if calling::is_explicit_world(model, world) {
        return assembler.conversion(
            ty,
            app(
                "ir_byte_with_memory_v1",
                [model.world_type.clone(), world.clone(), memory],
            ),
            expected,
        );
    }
    let eta = calling::world_eta(assembler, model, world.clone())?;
    let changed = world_mapper::replace_memory(assembler, &model.world_type, eta, memory)?;
    let normalized = assembler.conversion(ty, changed.right.clone(), expected)?;
    assembler.compose(changed, normalized)
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
    MachineModel {
        world_type,
        context: constant("memory_mapper_unused_context"),
        providers: constant("memory_mapper_unused_providers"),
    }
}

fn expected(model: &MachineModel, world: &Expr, memory: Expr) -> Expr {
    app(
        "IRByteWorldV1.mk",
        [
            model.world_type.clone(),
            memory,
            projection(model, world, "host"),
            projection(model, world, "owners"),
            projection(model, world, "next"),
        ],
    )
}

fn independent(
    model: &MachineModel,
    world: &Expr,
    memory: Expr,
    right: Expr,
    term: Expr,
) -> PendingEquality {
    PendingEquality::candidate(
        app("IRByteWorldV1", [model.world_type.clone()]),
        app(
            "ir_byte_with_memory_v1",
            [model.world_type.clone(), world.clone(), memory],
        ),
        right,
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
            assert!(audit.is_certified(), "{audit:#?}");
            for dependency in &audit.dependencies {
                assert!(environment.axiom_deps(dependency).unwrap().is_empty());
                assert!(
                    environment
                        .foundational_axiom_deps(dependency)
                        .unwrap()
                        .is_empty()
                );
                assert!(
                    environment
                        .trust_marker_deps(dependency)
                        .unwrap()
                        .is_empty()
                );
            }
        } else {
            let error = checked.unwrap_err();
            assert!(
                matches!(error, KernelTypeError::TypeMismatch { .. }),
                "real type mismatch, not a resource refusal: {error:?}"
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

#[test]
fn opaque_memory_mapper_original_oracle_repeated_symbolic_normalization_keeps_one_hundred_local_cap()
 {
    let mut scope = Scope::new();
    let mut assembler = Assembler::new(&mut scope, limits()).unwrap();
    let world_type = assembler.local(Expr::type_()).unwrap();
    let world = assembler
        .local(app("IRByteWorldV1", [world_type.term().clone()]))
        .unwrap();
    let memory = assembler.local(constant("IRByteMemoryV1")).unwrap();
    let model = model(world_type.term().clone());
    let mut first = None;
    let mut last = None;
    for iteration in 0..100 {
        let locals = assembler.locals;
        let operations = assembler.operations;
        let proof = original_normalize_memory_world(
            &mut assembler,
            &model,
            world.term(),
            memory.term().clone(),
        )
        .unwrap();
        assert_eq!(
            assembler.locals - locals,
            if iteration == 0 { 7 } else { 0 }
        );
        assert_eq!(
            assembler.operations - operations,
            if iteration == 0 { 12 } else { 5 }
        );
        let independently_spelled = independent(
            &model,
            world.term(),
            memory.term().clone(),
            expected(&model, world.term(), memory.term().clone()),
            proof.term().clone(),
        );
        if iteration == 0 {
            first = Some(independently_spelled.clone());
        }
        last = Some(independently_spelled);
    }
    assert_eq!(assembler.locals, 10);
    assert_eq!(assembler.local_scope().allocated(), 10);
    assert_eq!(assembler.operations, 510);
    assert!(
        !assembler
            .world_eta_candidate
            .as_ref()
            .unwrap()
            .has_fvar_quick()
    );
    let parameters = [world_type, world, memory];
    replay(assembler.local_scope(), &parameters, &first.unwrap(), true);
    replay(assembler.local_scope(), &parameters, &last.unwrap(), true);
}

#[test]
fn opaque_memory_mapper_retains_all_fields_and_refuses_forged_proof() {
    let mut scope = Scope::new();
    let mut assembler = Assembler::new(&mut scope, limits()).unwrap();
    let world_type = assembler.local(Expr::type_()).unwrap();
    let world = assembler
        .local(app("IRByteWorldV1", [world_type.term().clone()]))
        .unwrap();
    let memory = assembler.local(constant("IRByteMemoryV1")).unwrap();
    let wrong_memory = assembler.local(constant("IRByteMemoryV1")).unwrap();
    let wrong_host = assembler.local(world_type.term().clone()).unwrap();
    let wrong_owners = assembler.local(app("IRList", [constant("Nat")])).unwrap();
    let wrong_next = assembler.local(constant("Nat")).unwrap();
    let model = model(world_type.term().clone());
    let proof = normalize_memory_world(&mut assembler, &model, world.term(), memory.term().clone())
        .unwrap();
    let fields = [
        memory.term().clone(),
        projection(&model, world.term(), "host"),
        projection(&model, world.term(), "owners"),
        projection(&model, world.term(), "next"),
    ];
    let parameters = [
        world_type,
        world.clone(),
        memory.clone(),
        wrong_memory.clone(),
        wrong_host.clone(),
        wrong_owners.clone(),
        wrong_next.clone(),
    ];
    let genuine = independent(
        &model,
        world.term(),
        memory.term().clone(),
        expected(&model, world.term(), memory.term().clone()),
        proof.term().clone(),
    );
    replay(assembler.local_scope(), &parameters, &genuine, true);
    for (field, replacement) in [
        (0, wrong_memory.term().clone()),
        (0, projection(&model, world.term(), "memory")),
        (1, wrong_host.term().clone()),
        (2, wrong_owners.term().clone()),
        (3, wrong_next.term().clone()),
    ] {
        let mut changed = fields.clone();
        changed[field] = replacement;
        let right = app(
            "IRByteWorldV1.mk",
            std::iter::once(model.world_type.clone()).chain(changed),
        );
        let false_endpoint = independent(
            &model,
            world.term(),
            memory.term().clone(),
            right,
            proof.term().clone(),
        );
        replay(assembler.local_scope(), &parameters, &false_endpoint, false);
    }
    let forged = independent(
        &model,
        world.term(),
        memory.term().clone(),
        genuine.right().clone(),
        constant("True.intro"),
    );
    replay(assembler.local_scope(), &parameters, &forged, false);
}

#[test]
fn opaque_memory_mapper_original_oracle_does_not_capture_external_type_memory_or_world_bvars() {
    let mut scope = Scope::new();
    let mut assembler = Assembler::new(&mut scope, limits()).unwrap();
    // Add ordinary binders only AFTER the actual production helper runs.
    // The external U / memory / world are #2 / #1 / #0 in its inputs.
    let model = model(Expr::bvar(2));
    let world = Expr::bvar(0);
    let memory = Expr::bvar(1);
    let proof =
        original_normalize_memory_world(&mut assembler, &model, &world, memory.clone()).unwrap();
    assert_eq!(assembler.locals, 7);
    assert_eq!(assembler.operations, 12);
    let domains = [
        Expr::type_(),
        constant("IRByteMemoryV1"),
        app("IRByteWorldV1", [Expr::bvar(1)]),
    ];
    for (right, accepted) in [
        (expected(&model, &world, memory.clone()), true),
        (
            expected(&model, &world, projection(&model, &world, "memory")),
            false,
        ),
    ] {
        let claim = independent(&model, &world, memory.clone(), right, proof.term().clone());
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

fn opaque_ground_world() -> Expr {
    let empty_memory = app(
        "IRByteMemoryV1.mk",
        [
            list("IRByteAllocationV1", &[]),
            Expr::lam(
                BinderInfo::Default,
                constant("Nat"),
                app("IROption.none", [constant("Nat")]),
            ),
            nat(0),
        ],
    );
    let explicit = app(
        "IRByteWorldV1.mk",
        [
            constant("Nat"),
            empty_memory,
            nat(37),
            list("Nat", &[nat(8), nat(8)]),
            nat(0),
        ],
    );
    Expr::app(
        Expr::lam(
            BinderInfo::Default,
            app("IRByteWorldV1", [constant("Nat")]),
            Expr::bvar(0),
        ),
        explicit,
    )
}

#[test]
fn opaque_memory_mapper_original_oracle_preserves_cold_and_cumulative_construction_caps() {
    let model = model(constant("Nat"));
    let world = opaque_ground_world();
    let memory = projection(&model, &world, "memory");
    for (operation_cap, local_cap, expected_error, spent_operations, spent_locals) in [
        (
            11,
            100,
            "execution construction operation budget exceeded",
            11,
            7,
        ),
        (
            1_000,
            6,
            "execution construction local budget exceeded",
            8,
            6,
        ),
    ] {
        let mut scope = Scope::new();
        let mut assembler = Assembler::new(
            &mut scope,
            Limits {
                max_operations: operation_cap,
                max_locals: local_cap,
                ..limits()
            },
        )
        .unwrap();
        let error =
            match original_normalize_memory_world(&mut assembler, &model, &world, memory.clone()) {
                Ok(_) => panic!("literal old oracle must retain its construction caps"),
                Err(error) => error,
            };
        assert_eq!(error, expected_error);
        assert_eq!(assembler.operations, spent_operations);
        assert_eq!(assembler.locals, spent_locals);
        assert_eq!(assembler.local_scope().allocated(), spent_locals);
        assert_eq!(assembler.world_eta_candidate.is_some(), operation_cap == 11);
    }
    for (operation_cap, accepted) in [(16, false), (17, true)] {
        let mut scope = Scope::new();
        let mut assembler = Assembler::new(
            &mut scope,
            Limits {
                max_operations: operation_cap,
                max_locals: 7,
                ..limits()
            },
        )
        .unwrap();
        let first = original_normalize_memory_world(&mut assembler, &model, &world, memory.clone())
            .unwrap();
        assert_eq!(assembler.operations, 12);
        assert_eq!(assembler.locals, 7);
        let second =
            original_normalize_memory_world(&mut assembler, &model, &world, memory.clone());
        if accepted {
            replay(assembler.local_scope(), &[], &second.unwrap(), true);
        } else {
            assert_eq!(
                second.err().unwrap(),
                "execution construction operation budget exceeded"
            );
        }
        assert_eq!(assembler.operations, operation_cap);
        assert_eq!(assembler.locals, 7);
        replay(assembler.local_scope(), &[], &first, true);
    }
}

#[test]
fn opaque_memory_mapper_does_not_grant_memory_access() {
    let mut scope = Scope::new();
    let mut assembler = Assembler::new(&mut scope, limits()).unwrap();
    let model = model(constant("Nat"));
    let world = opaque_ground_world();
    let memory = projection(&model, &world, "memory");
    let proof = normalize_memory_world(&mut assembler, &model, &world, memory).unwrap();
    replay(assembler.local_scope(), &[], &proof, true);
    let accessible = app(
        "ir_byte_accessible_v1",
        [list("IRByteAllocationV1", &[]), nat(80), nat(8), nat(8)],
    );
    let denied = PendingEquality::candidate(
        constant("Bool"),
        accessible.clone(),
        constant("Bool.false"),
        refl(&constant("Bool"), constant("Bool.false")),
    );
    replay(assembler.local_scope(), &[], &denied, true);
    let forged = PendingEquality::candidate(
        constant("Bool"),
        accessible,
        constant("Bool.true"),
        proof.term().clone(),
    );
    replay(assembler.local_scope(), &[], &forged, false);
}

#[test]
fn closed_memory_presentation_repeated_symbolic_normalization_keeps_one_hundred_local_cap() {
    let mut scope = Scope::new();
    let mut assembler = Assembler::new(&mut scope, limits()).unwrap();
    let world_type = assembler.local(Expr::type_()).unwrap();
    let world = assembler
        .local(app("IRByteWorldV1", [world_type.term().clone()]))
        .unwrap();
    let memory = assembler.local(constant("IRByteMemoryV1")).unwrap();
    let model = model(world_type.term().clone());
    let mut first = None;
    let mut last = None;
    for iteration in 0..100 {
        let locals = assembler.locals;
        let operations = assembler.operations;
        let proof =
            normalize_memory_world(&mut assembler, &model, world.term(), memory.term().clone())
                .unwrap();
        assert_eq!(assembler.locals - locals, 0);
        assert_eq!(
            assembler.operations - operations,
            if iteration == 0 { 10 } else { 1 }
        );
        let independently_spelled = independent(
            &model,
            world.term(),
            memory.term().clone(),
            expected(&model, world.term(), memory.term().clone()),
            proof.term().clone(),
        );
        if iteration == 0 {
            first = Some(independently_spelled.clone());
        }
        last = Some(independently_spelled);
    }
    assert_eq!(assembler.locals, 3);
    assert_eq!(assembler.local_scope().allocated(), 3);
    assert_eq!(assembler.operations, 112);
    assert!(
        !assembler
            .memory_world_presentation_candidate
            .as_ref()
            .unwrap()
            .has_fvar_quick()
    );
    let parameters = [world_type, world, memory];
    replay(assembler.local_scope(), &parameters, &first.unwrap(), true);
    replay(assembler.local_scope(), &parameters, &last.unwrap(), true);
}

#[test]
fn closed_memory_presentation_does_not_capture_external_type_memory_or_world_bvars() {
    let mut scope = Scope::new();
    let mut assembler = Assembler::new(&mut scope, limits()).unwrap();
    // Add ordinary binders only AFTER the actual production helper runs.
    // The external U / memory / world are #2 / #1 / #0 in its inputs.
    let model = model(Expr::bvar(2));
    let world = Expr::bvar(0);
    let memory = Expr::bvar(1);
    let proof = normalize_memory_world(&mut assembler, &model, &world, memory.clone()).unwrap();
    assert_eq!(assembler.locals, 0);
    assert_eq!(assembler.operations, 10);
    let domains = [
        Expr::type_(),
        constant("IRByteMemoryV1"),
        app("IRByteWorldV1", [Expr::bvar(1)]),
    ];
    for (right, accepted) in [
        (expected(&model, &world, memory.clone()), true),
        (
            expected(&model, &world, projection(&model, &world, "memory")),
            false,
        ),
    ] {
        let claim = independent(&model, &world, memory.clone(), right, proof.term().clone());
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
fn closed_memory_presentation_keeps_explicit_fastpath_and_reuses_polymorphic_template() {
    let mut scope = Scope::new();
    let nat_world = scope
        .try_local(app("IRByteWorldV1", [constant("Nat")]))
        .unwrap();
    let bool_world = scope
        .try_local(app("IRByteWorldV1", [constant("Bool")]))
        .unwrap();
    let memory = scope.try_local(constant("IRByteMemoryV1")).unwrap();
    let mut assembler = Assembler::new(&mut scope, limits()).unwrap();
    let wrapped = opaque_ground_world();
    let explicit = (*wrapped.get_app_args()[0]).clone();
    let explicit_model = model(constant("Nat"));
    let explicit_memory = projection(&explicit_model, &explicit, "memory");
    let fast = normalize_memory_world(&mut assembler, &explicit_model, &explicit, explicit_memory)
        .unwrap();
    assert_eq!(assembler.operations, 1);
    assert_eq!(assembler.locals, 0);
    assert!(assembler.memory_world_presentation_candidate.is_none());
    replay(assembler.local_scope(), &[], &fast, true);

    let parameters = [nat_world.clone(), bool_world.clone(), memory.clone()];
    let mut saved: Option<Expr> = None;
    for (index, (host_type, world)) in [
        (constant("Nat"), nat_world.term()),
        (constant("Bool"), bool_world.term()),
        (constant("Nat"), nat_world.term()),
    ]
    .into_iter()
    .enumerate()
    {
        let operations = assembler.operations;
        let m = model(host_type);
        let proof =
            normalize_memory_world(&mut assembler, &m, world, memory.term().clone()).unwrap();
        assert_eq!(
            assembler.operations - operations,
            if index == 0 { 10 } else { 1 }
        );
        assert_eq!(assembler.locals, 0);
        assert!(assembler.world_eta_candidate.is_none());
        let cached = assembler
            .memory_world_presentation_candidate
            .as_ref()
            .unwrap();
        if let Some(previous) = &saved {
            match (previous.kind(), cached.kind()) {
                (ExprKind::Lam(_, old_ty, old_body), ExprKind::Lam(_, ty, body)) => {
                    assert!(std::sync::Arc::ptr_eq(old_ty, ty));
                    assert!(std::sync::Arc::ptr_eq(old_body, body));
                }
                _ => panic!("the closed candidate quantifies its actual host type"),
            }
        } else {
            assert!(!cached.has_fvar_quick() && !cached.has_loose_bvars_quick());
            saved = Some(cached.clone());
        }
        let genuine = independent(
            &m,
            world,
            memory.term().clone(),
            expected(&m, world, memory.term().clone()),
            proof.term().clone(),
        );
        replay(assembler.local_scope(), &parameters, &genuine, true);
    }
    assert_eq!(assembler.local_scope().allocated(), 3);
}

#[test]
fn closed_memory_presentation_partial_work_never_publishes_or_refunds_cache() {
    let m = model(constant("Nat"));
    let world = opaque_ground_world();
    let memory = projection(&m, &world, "memory");
    for cap in 1..10 {
        let mut scope = Scope::new();
        let mut assembler = Assembler::new(
            &mut scope,
            Limits {
                max_operations: cap,
                max_locals: 1,
                ..limits()
            },
        )
        .unwrap();
        for _ in 0..2 {
            let error = normalize_memory_world(&mut assembler, &m, &world, memory.clone())
                .err()
                .unwrap();
            assert_eq!(error, "execution construction operation budget exceeded");
            assert_eq!(assembler.operations, cap);
            assert_eq!(assembler.locals, 0);
            assert_eq!(assembler.local_scope().allocated(), 0);
            assert!(assembler.memory_world_presentation_candidate.is_none());
            assert!(assembler.world_eta_candidate.is_none());
        }
    }
    for (cap, second_accepted) in [(10, false), (11, true)] {
        let mut scope = Scope::new();
        let mut assembler = Assembler::new(
            &mut scope,
            Limits {
                max_operations: cap,
                max_locals: 1,
                ..limits()
            },
        )
        .unwrap();
        let first = normalize_memory_world(&mut assembler, &m, &world, memory.clone()).unwrap();
        assert_eq!(assembler.operations, 10);
        assert!(assembler.memory_world_presentation_candidate.is_some());
        let second = normalize_memory_world(&mut assembler, &m, &world, memory.clone());
        if second_accepted {
            replay(assembler.local_scope(), &[], &second.unwrap(), true);
        } else {
            assert_eq!(
                second.err().unwrap(),
                "execution construction operation budget exceeded"
            );
        }
        assert_eq!(assembler.operations, cap);
        assert_eq!(assembler.locals, 0);
        replay(assembler.local_scope(), &[], &first, true);
    }
}

#[test]
fn closed_memory_presentation_uses_exhausted_caller_locals_without_new_authority() {
    let m = model(constant("Nat"));
    let world = opaque_ground_world();
    let memory = projection(&m, &world, "memory");
    let mut scope = Scope::new();
    let mut assembler = Assembler::new(
        &mut scope,
        Limits {
            max_locals: 1,
            ..limits()
        },
    )
    .unwrap();
    let held = assembler.local(constant("Nat")).unwrap();
    let first = normalize_memory_world(&mut assembler, &m, &world, memory.clone()).unwrap();
    assert_eq!(assembler.operations, 11);
    assert_eq!(assembler.locals, 1);
    let operations = assembler.operations;
    assert_eq!(
        assembler.local(constant("Nat")).err().unwrap(),
        "execution construction local budget exceeded"
    );
    assert_eq!(
        assembler.operations,
        operations + 1,
        "failed work remains spent"
    );
    assert!(assembler.local_scope().owns(&held));
    let warm = normalize_memory_world(&mut assembler, &m, &world, memory).unwrap();
    assert_eq!(assembler.operations, operations + 2);
    assert_eq!(assembler.locals, 1);
    replay(assembler.local_scope(), &[], &first, true);
    replay(assembler.local_scope(), &[], &warm, true);

    // A cached Expr is still untrusted. This closed, well-typed function proves
    // only world=world, not the consumer's exact memory-replacement equality.
    let mut forged_scope = Scope::new();
    let opaque = forged_scope
        .try_local(app("IRByteWorldV1", [constant("Nat")]))
        .unwrap();
    let replacement = forged_scope.try_local(constant("IRByteMemoryV1")).unwrap();
    let mut forged = Assembler::new(&mut forged_scope, limits()).unwrap();
    forged.memory_world_presentation_candidate = Some(
        [
            Expr::type_(),
            app("IRByteWorldV1", [Expr::bvar(0)]),
            constant("IRByteMemoryV1"),
        ]
        .into_iter()
        .rev()
        .fold(
            refl(&app("IRByteWorldV1", [Expr::bvar(2)]), Expr::bvar(1)),
            |body, ty| Expr::lam(BinderInfo::Default, ty, body),
        ),
    );
    let wrong =
        normalize_memory_world(&mut forged, &m, opaque.term(), replacement.term().clone()).unwrap();
    assert_eq!(forged.operations, 1);
    let claim = independent(
        &m,
        opaque.term(),
        replacement.term().clone(),
        expected(&m, opaque.term(), replacement.term().clone()),
        wrong.term().clone(),
    );
    replay(forged.local_scope(), &[opaque, replacement], &claim, false);
}
