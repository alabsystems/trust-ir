// Copyright 2026 Andrew Yates | Licensed under the Apache License, Version 2.0

//! Strict replay of the existing ByteV1 CondBr eliminator and actual reflected
//! branch transfers. A closed mapper is a construction optimization, not a new
//! semantics declaration, caller admission, or native execution authority.

use super::*;
use crate::{ModuleBuilder, core_reflection::reflect_core_module_v1};
use clean_kernel::{BinderInfo, KernelTypeError};
use clean_verify::eval_ir::{EvalIrVocabulary, shared_specification_with_stack};
use trust_ir::{Endianness, StructPassingPolicy, TargetInfo, Ty, ValueId};

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

fn environment() -> &'static Environment {
    shared_specification_with_stack(EvalIrVocabulary::ByteV1)
        .unwrap()
        .env()
}

fn check_closed(term: Expr, claim: Expr, accepted: bool) {
    let mut checker = TypeChecker::new(environment());
    checker.set_allow_unsafe(false);
    checker.set_allow_partial(false);
    checker.set_heartbeat_limit(5_000_000);
    checker.set_max_cache_entries(100_000);
    assert!(!term.has_fvar_quick() && !claim.has_fvar_quick());
    checker
        .check_type(&claim, &Expr::sort(Level::zero()))
        .expect("the original claim has a well-typed proposition");
    if !accepted {
        let error = checker.check_type(&term, &claim).unwrap_err();
        assert!(
            matches!(error, KernelTypeError::TypeMismatch { .. }),
            "a semantic mismatch, not a resource refusal: {error:?}"
        );
        assert!(!checker.heartbeat_spent());
        return;
    }
    checker.check_type(&term, &claim).unwrap();
    assert!(
        environment()
            .audit_certification(&claim, &term)
            .is_certified()
    );
    let encoded = trust_ir::proof::encode_clean_expr_dag_v2(&term).unwrap();
    let decoded = trust_ir::proof::decode_clean_expr_dag_v2(&encoded).unwrap();
    assert_eq!(decoded, term);
    checker.check_type(&decoded, &claim).unwrap();
    assert!(
        environment()
            .audit_certification(&claim, &decoded)
            .is_certified()
    );
}

fn replay(scope: &Scope, parameters: &[Local], proof: &PendingEquality, accepted: bool) {
    let term = parameters
        .iter()
        .rev()
        .fold(proof.term().clone(), |body, parameter| parameter.lam(body));
    let claim = parameters
        .iter()
        .rev()
        .fold(proof.proposition(), |body, parameter| parameter.pi(body));
    check_closed(
        scope.close(&term).unwrap(),
        scope.close(&claim).unwrap(),
        accepted,
    );
}

fn boolean(value: bool) -> Expr {
    app(
        "IRScalar.bool_",
        [constant(if value { "Bool.true" } else { "Bool.false" })],
    )
}

#[test]
fn condition_eliminator_all_constructors_preserve_symbolic_type_and_opaque_arms() {
    let mut scope = Scope::new();
    let world_type = scope.try_local(Expr::type_()).unwrap();
    let config_type = app("IRByteConfigV1", [world_type.term().clone()]);
    let yes = scope.try_local(config_type.clone()).unwrap();
    let no = scope.try_local(config_type.clone()).unwrap();
    let failure = scope.try_local(config_type.clone()).unwrap();
    let first_word = scope.try_local(constant("Nat")).unwrap();
    let second_word = scope.try_local(constant("Nat")).unwrap();
    let first_field = scope.try_local(constant("IRScalar")).unwrap();
    let second_field = scope.try_local(constant("IRScalar")).unwrap();
    let mapper = condition_mapper(
        world_type.term().clone(),
        yes.term().clone(),
        no.term().clone(),
        failure.term().clone(),
    );
    // Every actual IRScalar constructor, in consumed ByteV1 order. Recursive
    // fields remain arbitrary: the mapper must not inspect them or mistake
    // either induction hypothesis for an outer arm.
    let cases = [
        (constant("IRScalar.undef_"), failure.term().clone()),
        (boolean(false), no.term().clone()),
        (boolean(true), yes.term().clone()),
        (
            app("IRScalar.int_", [first_word.term().clone()]),
            failure.term().clone(),
        ),
        (
            app("IRScalar.float_", [first_word.term().clone()]),
            failure.term().clone(),
        ),
        (constant("IRScalar.unit_"), failure.term().clone()),
        (
            app("IRScalar.ptr_", [first_word.term().clone()]),
            failure.term().clone(),
        ),
        (constant("IRScalar.nullptr_"), failure.term().clone()),
        (
            app(
                "IRScalar.fat_",
                [first_word.term().clone(), second_word.term().clone()],
            ),
            failure.term().clone(),
        ),
        (
            app("IRScalar.fnptr_", [first_word.term().clone()]),
            failure.term().clone(),
        ),
        (
            app("IRScalar.aggv", [first_field.term().clone()]),
            failure.term().clone(),
        ),
        (constant("IRScalar.vnil"), failure.term().clone()),
        (
            app(
                "IRScalar.vcons",
                [first_field.term().clone(), second_field.term().clone()],
            ),
            failure.term().clone(),
        ),
    ];
    let parameters = [
        world_type,
        yes,
        no,
        failure,
        first_word,
        second_word,
        first_field,
        second_field,
    ];
    let allocated = scope.allocated();
    let mut assembler = Assembler::new(&mut scope, limits()).unwrap();
    assert!(!mapper.get_app_fn().has_fvar_quick());
    for (index, (carrier, expected)) in cases.into_iter().enumerate() {
        let proof = assembler
            .conversion(
                config_type.clone(),
                Expr::app(mapper.clone(), carrier),
                expected,
            )
            .unwrap();
        replay(assembler.local_scope(), &parameters, &proof, true);
        assert_eq!(assembler.operations, index + 1);
        assert_eq!(assembler.locals, 0);
        assert_eq!(assembler.local_scope().allocated(), allocated);
    }
}

#[test]
fn condition_eliminator_nat_and_bool_worlds_reject_swapped_arms_and_failure() {
    for world_type in [constant("Nat"), constant("Bool")] {
        let mut scope = Scope::new();
        let config_type = app("IRByteConfigV1", [world_type.clone()]);
        let yes = scope.try_local(config_type.clone()).unwrap();
        let no = scope.try_local(config_type.clone()).unwrap();
        let failure = scope.try_local(config_type.clone()).unwrap();
        let mapper = condition_mapper(
            world_type.clone(),
            yes.term().clone(),
            no.term().clone(),
            failure.term().clone(),
        );
        let swapped = condition_mapper(
            world_type,
            no.term().clone(),
            yes.term().clone(),
            yes.term().clone(),
        );
        let parameters = [yes, no, failure];
        for (carrier, expected) in [
            (boolean(true), parameters[0].term().clone()),
            (boolean(false), parameters[1].term().clone()),
            (constant("IRScalar.nullptr_"), parameters[2].term().clone()),
            (
                app("IRScalar.aggv", [constant("IRScalar.vnil")]),
                parameters[2].term().clone(),
            ),
        ] {
            let original = PendingEquality::candidate(
                config_type.clone(),
                Expr::app(mapper.clone(), carrier.clone()),
                expected.clone(),
                refl(&config_type, expected.clone()),
            );
            replay(&scope, &parameters, &original, true);
            let mutant = PendingEquality::candidate(
                config_type.clone(),
                Expr::app(swapped.clone(), carrier),
                expected,
                original.term().clone(),
            );
            replay(&scope, &parameters, &mutant, false);
        }
    }
}

#[test]
fn condition_eliminator_does_not_capture_external_dependent_bvars() {
    let mut scope = Scope::new();
    let mut assembler = Assembler::new(&mut scope, limits()).unwrap();
    // These are already inside W, yes, no and failure binders. The mapper
    // applies all four actual expressions OUTSIDE its own closed binders.
    let world_type = Expr::bvar(3);
    let config_type = app("IRByteConfigV1", [world_type.clone()]);
    for (carrier, expected) in [
        (boolean(true), Expr::bvar(2)),
        (boolean(false), Expr::bvar(1)),
        (constant("IRScalar.vnil"), Expr::bvar(0)),
    ] {
        let proof = assembler
            .conversion(
                config_type.clone(),
                Expr::app(
                    condition_mapper(
                        world_type.clone(),
                        Expr::bvar(2),
                        Expr::bvar(1),
                        Expr::bvar(0),
                    ),
                    carrier,
                ),
                expected,
            )
            .unwrap();
        let term = Expr::lam(
            BinderInfo::Default,
            Expr::type_(),
            Expr::lam(
                BinderInfo::Default,
                app("IRByteConfigV1", [Expr::bvar(0)]),
                Expr::lam(
                    BinderInfo::Default,
                    app("IRByteConfigV1", [Expr::bvar(1)]),
                    Expr::lam(
                        BinderInfo::Default,
                        app("IRByteConfigV1", [Expr::bvar(2)]),
                        proof.term().clone(),
                    ),
                ),
            ),
        );
        let claim = Expr::pi(
            BinderInfo::Default,
            Expr::type_(),
            Expr::pi(
                BinderInfo::Default,
                app("IRByteConfigV1", [Expr::bvar(0)]),
                Expr::pi(
                    BinderInfo::Default,
                    app("IRByteConfigV1", [Expr::bvar(1)]),
                    Expr::pi(
                        BinderInfo::Default,
                        app("IRByteConfigV1", [Expr::bvar(2)]),
                        proof.proposition(),
                    ),
                ),
            ),
        );
        check_closed(term, claim, true);
    }
    assert_eq!(assembler.operations, 3);
    assert_eq!(assembler.locals, 0);
    assert_eq!(assembler.local_scope().allocated(), 0);
}

fn branch_module() -> (trust_ir::Module, FuncId, [BlockId; 3], ValueId) {
    let mut builder = ModuleBuilder::new_with_target_info(
        "ordinary_conditional_branch",
        TargetInfo {
            triple: "aarch64-apple-darwin".into(),
            pointer_size: 8,
            endianness: Endianness::Little,
            abi: Some("aapcs64".into()),
            struct_passing: StructPassingPolicy::NativeC,
        },
    );
    let signature = builder.add_func_type(vec![Ty::Bool], vec![Ty::U64]);
    let function = builder.declare_function("conditional_branch", signature);
    let mut body = builder.define_function(function).unwrap();
    let blocks = std::array::from_fn(|_| body.create_block());
    let condition = body.add_block_param(blocks[0], Ty::Bool);
    body.switch_to_block(blocks[0]);
    body.condbr(condition, blocks[1], vec![], blocks[2], vec![]);
    for (block, returned) in [(blocks[1], 17), (blocks[2], 23)] {
        body.switch_to_block(block);
        let value = body.uconst(Ty::U64, returned);
        body.ret(vec![value]);
    }
    body.build();
    let module = builder.build().expect("ModuleBuilder::build: test fixture");
    assert!(crate::validate_module(&module).is_empty());
    (module, function, blocks, condition)
}

fn frame(function: FuncId, block: BlockId, pc: u64, bindings: Expr) -> Expr {
    app(
        "IRFrame.mk",
        [
            nat(u64::from(function.index())),
            nat(u64::from(block.index())),
            nat(pc),
            bindings,
            list("Nat", &[]),
        ],
    )
}

fn model_current(
    scope: &mut Scope,
    reflected: &crate::core_reflection::ReflectedCoreModuleV1<'_>,
    function: FuncId,
    block: BlockId,
    condition: ValueId,
    value: Expr,
) -> (MachineModel, Current, Vec<Local>) {
    let providers = scope
        .try_local(app("IRByteProvidersV1", [constant("Nat")]))
        .unwrap();
    let host = scope.try_local(constant("Nat")).unwrap();
    let bytes = scope
        .try_local(Expr::arrow(
            constant("Nat"),
            app("IROption", [constant("Nat")]),
        ))
        .unwrap();
    let model = MachineModel::new(constant("Nat"), reflected, providers.term().clone());
    let world = app(
        "IRByteWorldV1.mk",
        [
            constant("Nat"),
            app(
                "IRByteMemoryV1.mk",
                [
                    list("IRByteAllocationV1", &[]),
                    bytes.term().clone(),
                    nat(65),
                ],
            ),
            host.term().clone(),
            list("Nat", &[nat(1)]),
            nat(2),
        ],
    );
    let current = Current {
        frame: frame(
            function,
            block,
            0,
            list(
                "IRBinding",
                &[app(
                    "IRBinding.mk",
                    [nat(u64::from(condition.index())), value],
                )],
            ),
        ),
        tail: list("IRFrame", &[]),
        legacy_memory: list("IRMemSlot", &[]),
        legacy_cursor: nat(0),
        world,
    };
    (model, current, vec![providers, host, bytes])
}

fn branch_premises(
    assembler: &mut Assembler<'_>,
    site: &FetchedSite,
    model: &MachineModel,
    current: &Current,
    target: &BranchTarget,
    taken: bool,
) -> BranchPremises {
    let checks = site
        .branch_checks(model, current, target, Some(taken))
        .unwrap();
    BranchPremises {
        condition: Some(PendingEquality::candidate(
            constant("IRScalar"),
            checks.condition.unwrap(),
            boolean(taken),
            refl(&constant("IRScalar"), boolean(taken)),
        )),
        resolved: assembler
            .conversion(
                app("IRList", [constant("IRScalar")]),
                app("ir_resolve", [current.machine(), checks.arguments]),
                list("IRScalar", &[]),
            )
            .unwrap(),
        arity: assembler
            .conversion(constant("Bool"), checks.arity, constant("Bool.true"))
            .unwrap(),
        before: assembler
            .conversion(
                constant("Bool"),
                current.valid(model),
                constant("Bool.true"),
            )
            .unwrap(),
    }
}

#[test]
fn condition_eliminator_actual_reflected_condbr_replays_both_complete_world_arms() {
    let (module, function, blocks, condition) = branch_module();
    let original = format!("{module:?}");
    let reflected = reflect_core_module_v1(&module, &[(function, 4096)]).unwrap();
    for taken in [false, true] {
        let mut scope = Scope::new();
        let (model, current, parameters) = model_current(
            &mut scope,
            &reflected,
            function,
            blocks[0],
            condition,
            boolean(taken),
        );
        let mut catalog = Catalog::new(environment(), &reflected, limits()).unwrap();
        let site = catalog
            .fetch(Coordinate {
                function,
                block: blocks[0],
                instruction: 0,
            })
            .unwrap();
        let target = catalog
            .branch_target(function, blocks[if taken { 1 } else { 2 }])
            .unwrap();
        let mut assembler = Assembler::new(&mut scope, limits()).unwrap();
        let premises = branch_premises(&mut assembler, &site, &model, &current, &target, taken);
        let transfer = site
            .branch_to(
                &mut assembler,
                &model,
                &current,
                &target,
                Some(taken),
                premises,
            )
            .unwrap();
        let bindings = app("ir_frame_locals", [current.frame.clone()]);
        let expected = Current {
            frame: frame(function, target.block_id(), 0, bindings.clone()),
            ..current.clone()
        };
        let step = PendingEquality::candidate(
            model.config_type(),
            model.step(current.running(&model)),
            expected.running(&model),
            transfer.step().term().clone(),
        );
        replay(assembler.local_scope(), &parameters, &step, true);
        let run = PendingEquality::candidate(
            model.config_type(),
            model.run(&NatTerm::literal(1), current.running(&model)),
            expected.running(&model),
            transfer.run().equality().term().clone(),
        );
        replay(assembler.local_scope(), &parameters, &run, true);
        replay(assembler.local_scope(), &parameters, transfer.valid(), true);
        assert_eq!(transfer.current().world, current.world);
        assert_eq!(transfer.current().tail, current.tail);
        assert_eq!(transfer.current().legacy_memory, current.legacy_memory);
        assert_eq!(transfer.current().legacy_cursor, current.legacy_cursor);
        for wrong in [
            Current {
                frame: frame(function, target.block_id(), 1, bindings.clone()),
                ..expected.clone()
            },
            Current {
                frame: frame(function, blocks[if taken { 2 } else { 1 }], 0, bindings),
                ..expected.clone()
            },
            Current {
                world: app(
                    "IRByteWorldV1.mk",
                    [
                        constant("Nat"),
                        app(
                            "ir_byte_world_memory_v1",
                            [constant("Nat"), current.world.clone()],
                        ),
                        app("Nat.succ", [parameters[1].term().clone()]),
                        list("Nat", &[nat(1)]),
                        nat(2),
                    ],
                ),
                ..expected.clone()
            },
        ] {
            let mutant = PendingEquality::candidate(
                model.config_type(),
                step.left().clone(),
                wrong.running(&model),
                step.term().clone(),
            );
            replay(assembler.local_scope(), &parameters, &mutant, false);
        }
    }
    assert_eq!(format!("{module:?}"), original);
}

#[test]
fn condition_eliminator_actual_condbr_requires_all_original_condition_and_guard_proofs() {
    let (module, function, blocks, condition) = branch_module();
    let reflected = reflect_core_module_v1(&module, &[(function, 4096)]).unwrap();
    let mut catalog = Catalog::new(environment(), &reflected, limits()).unwrap();
    let site = catalog
        .fetch(Coordinate {
            function,
            block: blocks[0],
            instruction: 0,
        })
        .unwrap();
    let target = catalog.branch_target(function, blocks[1]).unwrap();
    for mutation in 0..5 {
        let mut scope = Scope::new();
        let (model, current, parameters) = model_current(
            &mut scope,
            &reflected,
            function,
            blocks[0],
            condition,
            if mutation == 4 {
                app("IRScalar.int_", [nat(1)])
            } else {
                boolean(true)
            },
        );
        let mut assembler = Assembler::new(&mut scope, limits()).unwrap();
        let mut premises = branch_premises(&mut assembler, &site, &model, &current, &target, true);
        match mutation {
            0 => {
                premises.condition.as_mut().unwrap().term =
                    refl(&constant("IRScalar"), boolean(false));
            }
            1 => premises.before.term = refl(&constant("Bool"), constant("Bool.false")),
            2 => premises.arity.term = refl(&constant("Bool"), constant("Bool.false")),
            3 => {
                premises.resolved.term = refl(
                    &app("IRList", [constant("IRScalar")]),
                    list("IRScalar", &[constant("IRScalar.unit_")]),
                );
            }
            4 => {}
            _ => unreachable!(),
        }
        let transfer = site
            .branch_to(
                &mut assembler,
                &model,
                &current,
                &target,
                Some(true),
                premises,
            )
            .unwrap();
        replay(assembler.local_scope(), &parameters, transfer.step(), false);
    }
}

#[test]
fn condition_eliminator_actual_lookup_and_target_identity_are_not_authorized_by_mapper() {
    let (module, function, blocks, condition) = branch_module();
    let reflected = reflect_core_module_v1(&module, &[(function, 4096)]).unwrap();
    let mut scope = Scope::new();
    let (model, current, parameters) = model_current(
        &mut scope,
        &reflected,
        function,
        blocks[0],
        condition,
        boolean(true),
    );
    let mut catalog = Catalog::new(environment(), &reflected, limits()).unwrap();
    let site = catalog
        .fetch(Coordinate {
            function,
            block: blocks[0],
            instruction: 0,
        })
        .unwrap();
    let target = catalog.branch_target(function, blocks[1]).unwrap();
    let other_arm = catalog.branch_target(function, blocks[2]).unwrap();
    assert!(
        site.branch_checks(&model, &current, &other_arm, Some(true))
            .err()
            .unwrap()
            .contains("actual selected branch target")
    );
    let mut foreign = target.clone();
    foreign.function = FuncId::new(99);
    assert!(
        site.branch_checks(&model, &current, &foreign, Some(true))
            .err()
            .unwrap()
            .contains("different function")
    );
    let mut changed = site;
    // Same nominal destination and empty argument shape, but a different
    // retained original instruction. Its proof cannot replace the fetched node.
    changed.instruction = app(
        "IRInst.condbr",
        [
            nat(u64::from(condition.index())),
            nat(u64::from(blocks[2].index())),
            list("Nat", &[]),
            nat(u64::from(blocks[1].index())),
            list("Nat", &[]),
        ],
    );
    let mut assembler = Assembler::new(&mut scope, limits()).unwrap();
    let premises = branch_premises(&mut assembler, &changed, &model, &current, &other_arm, true);
    let transfer = changed
        .branch_to(
            &mut assembler,
            &model,
            &current,
            &other_arm,
            Some(true),
            premises,
        )
        .unwrap();
    replay(assembler.local_scope(), &parameters, transfer.step(), false);
}

#[test]
fn condition_eliminator_repeated_factory_is_one_operation_zero_locals_and_budgeted() {
    let (module, function, blocks, condition) = branch_module();
    let reflected = reflect_core_module_v1(&module, &[(function, 4096)]).unwrap();
    let mut scope = Scope::new();
    let (model, current, _parameters) = model_current(
        &mut scope,
        &reflected,
        function,
        blocks[0],
        condition,
        boolean(true),
    );
    let mut catalog = Catalog::new(environment(), &reflected, limits()).unwrap();
    let site = catalog
        .fetch(Coordinate {
            function,
            block: blocks[0],
            instruction: 0,
        })
        .unwrap();
    let allocated = scope.allocated();
    let mut policy = limits();
    policy.max_operations = 2;
    policy.max_locals = 1;
    let mut assembler = Assembler::new(&mut scope, policy).unwrap();
    let first = site
        .condition_eliminator(&mut assembler, &model, &current)
        .unwrap();
    assert_eq!(assembler.operations, 1);
    assert_eq!(assembler.locals, 0);
    let second = site
        .condition_eliminator(&mut assembler, &model, &current)
        .unwrap();
    assert_eq!(first, second);
    assert_eq!(assembler.operations, 2);
    assert_eq!(assembler.locals, 0);
    assert_eq!(assembler.local_scope().allocated(), allocated);
    assert!(
        site.condition_eliminator(&mut assembler, &model, &current)
            .unwrap_err()
            .contains("operation budget")
    );
    assert_eq!(assembler.operations, 2);
    assert_eq!(assembler.locals, 0);
    assert_eq!(assembler.local_scope().allocated(), allocated);
}

#[test]
fn condition_eliminator_keeps_the_actual_hundred_local_cap_without_using_fresh_slots() {
    let (module, function, blocks, condition) = branch_module();
    let reflected = reflect_core_module_v1(&module, &[(function, 4096)]).unwrap();
    let mut scope = Scope::new();
    let (model, current, _parameters) = model_current(
        &mut scope,
        &reflected,
        function,
        blocks[0],
        condition,
        boolean(false),
    );
    let mut catalog = Catalog::new(environment(), &reflected, limits()).unwrap();
    let site = catalog
        .fetch(Coordinate {
            function,
            block: blocks[0],
            instruction: 0,
        })
        .unwrap();
    let mut assembler = Assembler::new(&mut scope, limits()).unwrap();
    for _ in 0..100 {
        assembler.local(constant("Nat")).unwrap();
    }
    let allocated = assembler.local_scope().allocated();
    let mapper = site
        .condition_eliminator(&mut assembler, &model, &current)
        .unwrap();
    assert!(!mapper.get_app_fn().has_fvar_quick());
    assert_eq!(assembler.locals, 100);
    assert_eq!(assembler.operations, 101);
    assert_eq!(assembler.local_scope().allocated(), allocated);
    assert!(
        assembler
            .local(constant("Nat"))
            .err()
            .unwrap()
            .contains("local budget")
    );
    assert_eq!(assembler.locals, 100);
    assert_eq!(assembler.local_scope().allocated(), allocated);
    assert_eq!(assembler.limits.max_locals, 100);
    assert_eq!(assembler.limits.max_operations, 1_000);
}
