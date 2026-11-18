// Copyright 2026 Andrew Yates | Licensed under the Apache License, Version 2.0

use super::*;
use crate::proof_assembly::ProofLimits;
use crate::proof_components::{OwnedProofCapture, ProofComponents, ScopedProofDeclaration};
use crate::term_scope::{TermScope, TermScopeLimits};
use clean_kernel::{KernelTypeError, expr::FVarId};
use clean_verify::eval_ir::{EvalIrVocabulary, shared_specification_with_stack};
use std::sync::Arc;

// Independently keep the original public-field construction as the oracle.
fn original_machine(current: &Current) -> Expr {
    app(
        "IRMachine.mk",
        [
            app(
                "IRList.cons",
                [
                    constant("IRFrame"),
                    current.frame.clone(),
                    current.tail.clone(),
                ],
            ),
            current.legacy_memory.clone(),
            current.legacy_cursor.clone(),
        ],
    )
}

#[test]
fn shared_current_borrow_preserves_actual_fields_and_refreshes_after_every_mutation() {
    let mut current = Current {
        frame: Expr::bvar(0),
        tail: Expr::bvar(1),
        legacy_memory: Expr::bvar(2),
        legacy_cursor: Expr::bvar(3),
        world: Expr::bvar(4),
    };
    for field in 0..5 {
        let previous = {
            let shared = current.shared_machine();
            let first = shared.machine();
            let second = shared.machine();
            let (ExprKind::App(first, _), ExprKind::App(second, _)) = (first.kind(), second.kind())
            else {
                panic!("actual machine applications");
            };
            assert!(
                Arc::ptr_eq(first, second),
                "same borrowed constructor spine"
            );
            shared.machine()
        };
        let fresh = Expr::bvar(20 + field);
        match field {
            0 => current.frame = fresh,
            1 => current.tail = fresh,
            2 => current.legacy_memory = fresh,
            3 => current.legacy_cursor = fresh,
            4 => current.world = fresh,
            _ => unreachable!(),
        }
        let shared = current.shared_machine();
        assert_eq!(shared.machine(), original_machine(&current));
        assert_eq!(shared.machine() == previous, field == 4);
        for [world_type, context, providers] in [
            [constant("Nat"), constant("context"), constant("providers")],
            [
                constant("Bool"),
                constant("foreign_context"),
                constant("foreign_providers"),
            ],
            [Expr::bvar(40), Expr::bvar(41), Expr::bvar(42)],
        ] {
            let model =
                MachineModel::from_terms(world_type.clone(), context.clone(), providers.clone());
            let running = app(
                "IRByteConfigV1.running",
                [
                    world_type.clone(),
                    original_machine(&current),
                    current.world.clone(),
                ],
            );
            assert_eq!(shared.running(&model), running);
            assert_eq!(
                shared.valid(&model),
                app(
                    "ir_byte_world_valid_v1",
                    [
                        world_type.clone(),
                        original_machine(&current),
                        current.world.clone()
                    ]
                )
            );
            for fuel in [0, 1, 2048] {
                let fuel = NatTerm::literal(fuel);
                assert_eq!(
                    model.run(&fuel, shared.running(&model)),
                    app(
                        "ir_byte_run_v1",
                        [
                            world_type.clone(),
                            context.clone(),
                            providers.clone(),
                            fuel.term().clone(),
                            running.clone()
                        ]
                    )
                );
            }
        }
    }
}

#[test]
fn shared_current_borrow_reduces_charged_spine_work_without_changing_the_forest() {
    let current = Current {
        frame: Expr::bvar(0),
        tail: Expr::bvar(1),
        legacy_memory: Expr::bvar(2),
        legacy_cursor: Expr::bvar(3),
        world: Expr::bvar(4),
    };
    let model = MachineModel::from_terms(constant("Nat"), Expr::bvar(5), Expr::bvar(6));
    let shared = current.shared_machine();
    let mut actual = Vec::new();
    let mut original = Vec::new();
    for _ in 0..64 {
        actual.extend([
            shared.machine(),
            shared.running(&model),
            shared.valid(&model),
        ]);
        original.extend([
            original_machine(&current),
            current.running(&model),
            current.valid(&model),
        ]);
    }
    assert_eq!(actual, original);
    let limits = TermScopeLimits::default();
    assert_eq!(limits.max_visits, 1_000_000);
    assert_eq!(limits.max_depth, 16_384);
    let shared = TermScope::new()
        .intern_forest_with_limits(&actual, limits)
        .unwrap();
    let original = TermScope::new()
        .intern_forest_with_limits(&original, limits)
        .unwrap();
    assert_eq!(shared.terms, original.terms);
    assert_eq!(shared.stats.canonical, original.stats.canonical);
    assert!(shared.stats.visits < original.stats.visits);
    assert!(shared.stats.examined < original.stats.examined);
    eprintln!(
        "CURRENT_MACHINE_INTERN shared={:?} original={:?}",
        shared.stats, original.stats
    );
}

#[test]
fn shared_current_replays_original_run_and_rejects_foreign_state_world_fuel_and_unused_data() {
    let mut scope = Scope::new();
    let world_type = scope.try_local(Expr::type_()).unwrap();
    let context = scope.try_local(constant("IRByteContextV1")).unwrap();
    let providers_type = app("IRByteProvidersV1", [world_type.term().clone()]);
    let providers = scope.try_local(providers_type.clone()).unwrap();
    let frame = scope.try_local(constant("IRFrame")).unwrap();
    let tail = scope
        .try_local(app("IRList", [constant("IRFrame")]))
        .unwrap();
    let memory = scope
        .try_local(app("IRList", [constant("IRMemSlot")]))
        .unwrap();
    let cursor = scope.try_local(constant("Nat")).unwrap();
    let world_term_type = app("IRByteWorldV1", [world_type.term().clone()]);
    let world = scope.try_local(world_term_type.clone()).unwrap();
    let fuel = scope.try_local(constant("Nat")).unwrap();
    let foreign_frame = scope.try_local(constant("IRFrame")).unwrap();
    let foreign_world = scope.try_local(world_term_type).unwrap();
    let foreign_fuel = scope.try_local(constant("Nat")).unwrap();
    let foreign_context = scope.try_local(constant("IRByteContextV1")).unwrap();
    let foreign_providers = scope.try_local(providers_type).unwrap();
    let current = Current {
        frame: frame.term().clone(),
        tail: tail.term().clone(),
        legacy_memory: memory.term().clone(),
        legacy_cursor: cursor.term().clone(),
        world: world.term().clone(),
    };
    let model = MachineModel::from_terms(
        world_type.term().clone(),
        context.term().clone(),
        providers.term().clone(),
    );
    let configuration_type = app("IRByteConfigV1", [world_type.term().clone()]);
    let original = app(
        "ir_byte_run_v1",
        [
            world_type.term().clone(),
            context.term().clone(),
            providers.term().clone(),
            fuel.term().clone(),
            app(
                "IRByteConfigV1.running",
                [
                    world_type.term().clone(),
                    original_machine(&current),
                    world.term().clone(),
                ],
            ),
        ],
    );
    let parameters = [
        world_type.clone(),
        context,
        providers,
        frame,
        tail,
        memory,
        cursor,
        world,
        fuel.clone(),
        foreign_frame.clone(),
        foreign_world.clone(),
        foreign_fuel.clone(),
        foreign_context.clone(),
        foreign_providers.clone(),
    ];
    let frozen = scope
        .close(&parameters.iter().rev().fold(
            eq(&configuration_type, original.clone(), original.clone()),
            |body, parameter| parameter.pi(body),
        ))
        .unwrap();
    let mut parts = ProofComponents::new("current.machine.borrow", ProofLimits::default());
    parts
        .set_base(
            &scope,
            parameters
                .iter()
                .cloned()
                .map(OwnedProofCapture::Parameter)
                .collect(),
        )
        .unwrap();
    let shared = current.shared_machine();
    let retained = parts
        .bind_scoped_owned(
            &mut scope,
            &[],
            configuration_type.clone(),
            model.run(&NatTerm::local(&fuel).unwrap(), shared.running(&model)),
        )
        .unwrap();
    let goal = eq(&configuration_type, retained.reference.clone(), original);
    let root = parameters.iter().rev().fold(
        refl(&configuration_type, retained.reference),
        |body, parameter| parameter.lam(body),
    );
    let bundle = parts
        .close_scoped(&scope, root, goal, TermScopeLimits::default())
        .unwrap();
    let binding = bundle.outer_count;
    assert_eq!(binding, parameters.len());
    assert_eq!(bundle.declarations.len(), binding + 1);
    assert!(
        bundle.declarations[..binding]
            .iter()
            .all(|d| d.value.is_none())
    );
    assert!(bundle.declarations[binding].value.is_some());
    let exported = bundle
        .clone()
        .into_closed_terms(TermScopeLimits::default())
        .unwrap();
    let specification = shared_specification_with_stack(EvalIrVocabulary::ByteV1).unwrap();
    bundle
        .replay(specification.env(), &frozen, 5_000_000)
        .unwrap();
    let mut checker = TypeChecker::new(specification.env());
    checker.set_allow_unsafe(false);
    checker.set_allow_partial(false);
    checker.set_heartbeat_limit(5_000_000);
    checker.set_max_cache_entries(100_000);
    checker
        .check_type(&frozen, &Expr::sort(Level::zero()))
        .unwrap();
    checker.check_type(&exported.root, &frozen).unwrap();
    let wire = trust_ir::proof::encode_clean_expr_dag_v2(&exported.root).unwrap();
    let decoded = trust_ir::proof::decode_clean_expr_dag_v2(&wire).unwrap();
    checker.check_type(&decoded, &frozen).unwrap();
    assert!(
        specification
            .env()
            .audit_certification(&frozen, &decoded)
            .is_certified()
    );
    for mutation in 0..5 {
        let mut wrong = current.clone();
        let mut wrong_model = model.clone();
        let mut wrong_fuel = NatTerm::local(&fuel).unwrap();
        match mutation {
            0 => wrong.frame = foreign_frame.term().clone(),
            1 => wrong.world = foreign_world.term().clone(),
            2 => wrong_fuel = NatTerm::local(&foreign_fuel).unwrap(),
            3 => {
                wrong_model = MachineModel::from_terms(
                    world_type.term().clone(),
                    foreign_context.term().clone(),
                    model.providers().clone(),
                )
            }
            4 => {
                wrong_model = MachineModel::from_terms(
                    world_type.term().clone(),
                    model.context().clone(),
                    foreign_providers.term().clone(),
                )
            }
            _ => unreachable!(),
        }
        let mut invalid = bundle.clone();
        invalid.declarations[binding].value =
            Some(wrong_model.run(&wrong_fuel, wrong.shared_machine().running(&wrong_model)));
        assert_eq!(invalid.root, bundle.root);
        assert_eq!(invalid.goal, bundle.goal);
        let error = invalid
            .replay(specification.env(), &frozen, 5_000_000)
            .err()
            .expect("the original scoped claim must reject each changed actual operand");
        assert!(
            error.contains("scoped goal differs from the complete original external claim"),
            "mutation{mutation}: {error}"
        );
        assert!(!error.contains("BudgetExhausted") && !error.contains("HeartbeatExceeded"));
        let exported = invalid
            .into_closed_terms(TermScopeLimits::default())
            .unwrap();
        let error = checker.check_type(&exported.root, &frozen).unwrap_err();
        assert!(
            matches!(error, KernelTypeError::TypeMismatch { .. }),
            "mutation{mutation}: {error:?}"
        );
        assert!(!checker.heartbeat_spent());
    }
    let mut invalid = bundle.clone();
    let id = FVarId::new(
        invalid
            .declarations
            .iter()
            .map(|declaration| declaration.id.as_u64())
            .max()
            .unwrap()
            .checked_add(1)
            .filter(|id| *id < 1u64 << 63)
            .unwrap(),
    );
    for declaration in &invalid.declarations {
        assert_ne!(declaration.id, id);
        assert_eq!(
            declaration.type_.subst_fvar(id, &constant("Nat")),
            declaration.type_
        );
        if let Some(value) = &declaration.value {
            assert_eq!(value.subst_fvar(id, &constant("Nat")), *value);
        }
    }
    assert_eq!(invalid.root.subst_fvar(id, &constant("Nat")), invalid.root);
    assert_eq!(invalid.goal.subst_fvar(id, &constant("Nat")), invalid.goal);
    invalid.declarations.push(ScopedProofDeclaration {
        id,
        name: Name::from_string("unused.invalid.current.machine"),
        binder: clean_kernel::BinderInfo::Default.into(),
        non_dep: false,
        type_: constant("Nat"),
        value: Some(constant("True.intro")),
    });
    assert_eq!(invalid.declarations.len(), bundle.declarations.len() + 1);
    assert_eq!(invalid.outer_count, bundle.outer_count);
    assert_eq!(invalid.root, bundle.root);
    assert_eq!(invalid.goal, bundle.goal);
    let error = invalid
        .replay(specification.env(), &frozen, 5_000_000)
        .err()
        .expect("unused invalid value must be audited in the original scoped forest");
    assert!(error.contains("TypeMismatch"), "{error}");
    assert!(!error.contains("BudgetExhausted") && !error.contains("HeartbeatExceeded"));
    let exported = invalid
        .into_closed_terms(TermScopeLimits::default())
        .unwrap();
    let error = checker.check_type(&exported.root, &frozen).unwrap_err();
    assert!(
        matches!(error, KernelTypeError::TypeMismatch { .. }),
        "{error:?}"
    );
    assert!(!checker.heartbeat_spent());
}
