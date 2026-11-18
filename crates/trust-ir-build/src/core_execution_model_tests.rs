// Copyright 2026 Andrew Yates | Licensed under the Apache License, Version 2.0

use super::*;
use crate::proof_assembly::ProofLimits;
use crate::proof_components::{OwnedProofCapture, ProofComponents, ScopedProofDeclaration};
use crate::term_scope::{TermScope, TermScopeLimits};
use clean_kernel::{KernelTypeError, expr::FVarId};
use clean_verify::eval_ir::{EvalIrVocabulary, shared_specification_with_stack};

#[test]
fn immutable_model_prefixes_preserve_original_terms_and_fresh_dynamic_operands() {
    for [world_type, context, providers] in [
        [constant("Nat"), constant("context"), constant("providers")],
        [constant("Bool"), constant("context"), constant("providers")],
        [
            constant("Nat"),
            constant("foreign_context"),
            constant("providers"),
        ],
        [
            constant("Nat"),
            constant("context"),
            constant("foreign_providers"),
        ],
        [Expr::bvar(11), Expr::bvar(10), Expr::bvar(9)],
    ] {
        let model =
            MachineModel::from_terms(world_type.clone(), context.clone(), providers.clone());
        assert_eq!(
            model.config_type(),
            app("IRByteConfigV1", [world_type.clone()])
        );
        for offset in [0, 20] {
            let dynamic = |i| Expr::bvar(offset + i);
            let current = Current {
                frame: dynamic(0),
                tail: dynamic(1),
                legacy_memory: dynamic(2),
                legacy_cursor: dynamic(3),
                world: dynamic(4),
            };
            let fuel = NatTerm::literal(u64::from(offset) + 7);
            let config = dynamic(5);
            assert_eq!(
                model.run_function(&fuel),
                app(
                    "ir_byte_run_v1",
                    [
                        world_type.clone(),
                        context.clone(),
                        providers.clone(),
                        fuel.term().clone()
                    ]
                )
            );
            assert_eq!(
                model.run(&fuel, config.clone()),
                app(
                    "ir_byte_run_v1",
                    [
                        world_type.clone(),
                        context.clone(),
                        providers.clone(),
                        fuel.term().clone(),
                        config.clone()
                    ]
                )
            );
            assert_eq!(
                model.step(config.clone()),
                app(
                    "ir_byte_step_v1",
                    [
                        world_type.clone(),
                        context.clone(),
                        providers.clone(),
                        config
                    ]
                )
            );
            assert_eq!(
                current.running(&model),
                app(
                    "IRByteConfigV1.running",
                    [world_type.clone(), current.machine(), current.world.clone()]
                )
            );
            assert_eq!(
                current.valid(&model),
                app(
                    "ir_byte_world_valid_v1",
                    [world_type.clone(), current.machine(), current.world.clone()]
                )
            );
            assert_eq!(
                model.dispatch(&current, dynamic(6), dynamic(7), dynamic(8)),
                app(
                    "ir_byte_exec_v1",
                    [
                        world_type.clone(),
                        context.clone(),
                        providers.clone(),
                        current.machine(),
                        current.world.clone(),
                        dynamic(6),
                        dynamic(7),
                        dynamic(8)
                    ]
                )
            );
            let arguments: [Expr; 16] = std::array::from_fn(|i| dynamic(i as u32));
            let original = Expr::apps(
                constant("ir_byte_step_fetched_v1"),
                [world_type.clone(), context.clone(), providers.clone()]
                    .into_iter()
                    .chain(arguments.clone()),
            );
            assert_eq!(model.fetched_step(arguments), original);
        }
    }
}

#[test]
fn immutable_model_prefixes_reduce_charged_duplicate_construction_work() {
    let world = constant("Nat");
    let context = constant("actual_context");
    let providers = constant("actual_providers");
    let model = MachineModel::from_terms(world.clone(), context.clone(), providers.clone());
    let mut shared = Vec::new();
    let mut original = Vec::new();
    for i in 0..64 {
        let fuel = NatTerm::literal(i);
        let config = Expr::bvar(i as u32);
        shared.push(model.config_type());
        original.push(app("IRByteConfigV1", [world.clone()]));
        shared.push(model.run(&fuel, config.clone()));
        original.push(app(
            "ir_byte_run_v1",
            [
                world.clone(),
                context.clone(),
                providers.clone(),
                fuel.term().clone(),
                config.clone(),
            ],
        ));
        shared.push(model.step(config.clone()));
        original.push(app(
            "ir_byte_step_v1",
            [world.clone(), context.clone(), providers.clone(), config],
        ));
    }
    assert_eq!(shared, original);
    let limits = TermScopeLimits::default();
    assert_eq!(limits.max_visits, 1_000_000);
    assert_eq!(limits.max_depth, 16_384);
    let shared = TermScope::new()
        .intern_forest_with_limits(&shared, limits)
        .unwrap();
    let original = TermScope::new()
        .intern_forest_with_limits(&original, limits)
        .unwrap();
    assert_eq!(shared.terms, original.terms);
    assert!(shared.stats.visits < original.stats.visits);
    assert!(shared.stats.examined < original.stats.examined);
    eprintln!(
        "MODEL_PREFIX_INTERN shared={:?} original={:?}",
        shared.stats, original.stats
    );
}

#[test]
fn immutable_model_prefixes_replay_original_claim_and_reject_unused_invalid_definition() {
    let mut scope = Scope::new();
    let world = scope.try_local(Expr::type_()).unwrap();
    let context = scope.try_local(constant("IRByteContextV1")).unwrap();
    let providers = scope
        .try_local(app("IRByteProvidersV1", [world.term().clone()]))
        .unwrap();
    let fuel = scope.try_local(constant("Nat")).unwrap();
    let configuration_type = app("IRByteConfigV1", [world.term().clone()]);
    let initial = scope.try_local(configuration_type.clone()).unwrap();
    let model = MachineModel::from_terms(
        world.term().clone(),
        context.term().clone(),
        providers.term().clone(),
    );
    let original_run = app(
        "ir_byte_run_v1",
        [
            world.term().clone(),
            context.term().clone(),
            providers.term().clone(),
            fuel.term().clone(),
            initial.term().clone(),
        ],
    );
    let parameters = [world, context, providers, fuel.clone(), initial.clone()];
    let frozen = scope
        .close(&parameters.iter().rev().fold(
            eq(
                &configuration_type,
                original_run.clone(),
                original_run.clone(),
            ),
            |body, parameter| parameter.pi(body),
        ))
        .unwrap();
    let mut parts = ProofComponents::new("model.prefix", ProofLimits::default());
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
    let retained = parts
        .bind_scoped_owned(
            &mut scope,
            &[],
            configuration_type.clone(),
            model.run(&NatTerm::local(&fuel).unwrap(), initial.term().clone()),
        )
        .unwrap();
    let goal = eq(
        &configuration_type,
        retained.reference,
        original_run.clone(),
    );
    let root = parameters.iter().rev().fold(
        refl(&configuration_type, original_run),
        |body, parameter| parameter.lam(body),
    );
    let bundle = parts
        .close_scoped(&scope, root, goal, TermScopeLimits::default())
        .unwrap();
    let exported = bundle
        .clone()
        .into_closed_terms(TermScopeLimits::default())
        .unwrap();
    let specification = shared_specification_with_stack(EvalIrVocabulary::ByteV1).unwrap();
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

    let mut invalid = bundle.clone();
    let id = invalid
        .declarations
        .iter()
        .map(|d| d.id.as_u64())
        .max()
        .unwrap()
        .checked_add(1)
        .filter(|id| *id < 1u64 << 63)
        .unwrap();
    let id = FVarId::new(id);
    for declaration in &invalid.declarations {
        assert_eq!(
            declaration.type_.subst_fvar(id, &constant("Nat")),
            declaration.type_
        );
        let value = declaration.value.as_ref();
        if let Some(value) = value {
            assert_eq!(value.subst_fvar(id, &constant("Nat")), *value);
        }
    }
    assert_eq!(invalid.root.subst_fvar(id, &constant("Nat")), invalid.root);
    assert_eq!(invalid.goal.subst_fvar(id, &constant("Nat")), invalid.goal);
    invalid.declarations.push(ScopedProofDeclaration {
        id,
        name: Name::from_string("unused.invalid.model.prefix"),
        binder: clean_kernel::BinderInfo::Default.into(),
        non_dep: false,
        type_: constant("Nat"),
        value: Some(constant("True.intro")),
    });
    assert_eq!(invalid.declarations.len(), bundle.declarations.len() + 1);
    assert_eq!(invalid.root, bundle.root);
    assert_eq!(invalid.goal, bundle.goal);
    assert_eq!(invalid.outer_count, bundle.outer_count);
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
