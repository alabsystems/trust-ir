// Copyright 2026 Andrew Yates | Licensed under the Apache License, Version 2.0

//! Real reflected Br execution plus strict conditional fallback transports.
//! Neither recognition nor assembly authenticates a native execution route.

use super::*;
use crate::{ModuleBuilder, core_reflection::reflect_core_module_v1};
use clean_kernel::{BinderInfo, KernelTypeError};
use clean_verify::eval_ir::{EvalIrVocabulary, shared_specification_with_stack};
use trust_ir::{Endianness, StructPassingPolicy, TargetInfo, Ty};

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

#[test]
fn empty_branch_mapper_does_not_capture_external_dependent_binders() {
    let mut scope = Scope::new();
    let mut assembler = Assembler::new(&mut scope, limits()).unwrap();
    let world_type = Expr::bvar(1);
    let reached = Expr::bvar(0);
    let proof = assembler
        .conversion(
            app("IRByteConfigV1", [world_type.clone()]),
            Expr::app(
                empty_branch_mapper(world_type, reached.clone()),
                list("IRScalar", &[]),
            ),
            reached,
        )
        .unwrap();
    let term = Expr::lam(
        BinderInfo::Default,
        Expr::type_(),
        Expr::lam(
            BinderInfo::Default,
            app("IRByteConfigV1", [Expr::bvar(0)]),
            proof.term().clone(),
        ),
    );
    let claim = Expr::pi(
        BinderInfo::Default,
        Expr::type_(),
        Expr::pi(
            BinderInfo::Default,
            app("IRByteConfigV1", [Expr::bvar(0)]),
            proof.proposition(),
        ),
    );
    assert_eq!(assembler.locals, 0);
    assert_eq!(assembler.operations, 1);
    check_closed(term, claim, true);
}

fn branch_chain() -> (trust_ir::Module, FuncId, [BlockId; 5]) {
    let mut builder = ModuleBuilder::new_with_target_info(
        "empty_branch_chain",
        TargetInfo {
            triple: "aarch64-apple-darwin".into(),
            pointer_size: 8,
            endianness: Endianness::Little,
            abi: Some("aapcs64".into()),
            struct_passing: StructPassingPolicy::NativeC,
        },
    );
    let signature = builder.add_func_type(vec![], vec![Ty::U64]);
    let function = builder.declare_function("branch_chain", signature);
    let mut body = builder.define_function(function).unwrap();
    let blocks = std::array::from_fn(|_| body.create_block());
    for index in 0..4 {
        body.switch_to_block(blocks[index]);
        body.br(blocks[index + 1], vec![]);
    }
    body.switch_to_block(blocks[4]);
    let result = body.uconst(Ty::U64, 17);
    body.ret(vec![result]);
    body.build();
    let module = builder.build().expect("ModuleBuilder::build: test fixture");
    assert!(crate::validate_module(&module).is_empty());
    (module, function, blocks)
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

#[test]
fn actual_repeated_empty_branches_keep_exact_run_budget_and_refuse_changed_currents() {
    let (module, function, blocks) = branch_chain();
    let reflected = reflect_core_module_v1(&module, &[(function, 4096)]).unwrap();
    let mut scope = Scope::new();
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
    let model = MachineModel::new(constant("Nat"), &reflected, providers.term().clone());
    let parameters = [providers, host, bytes];
    let world = app(
        "IRByteWorldV1.mk",
        [
            constant("Nat"),
            app(
                "IRByteMemoryV1.mk",
                [
                    list("IRByteAllocationV1", &[]),
                    parameters[2].term().clone(),
                    nat(65),
                ],
            ),
            parameters[1].term().clone(),
            list("Nat", &[nat(1)]),
            nat(2),
        ],
    );
    let mut current = Current {
        frame: frame(function, blocks[0], 0, list("IRBinding", &[])),
        tail: list("IRFrame", &[]),
        legacy_memory: list("IRMemSlot", &[]),
        legacy_cursor: nat(0),
        world,
    };
    let mut catalog = Catalog::new(environment(), &reflected, limits()).unwrap();
    let mut policy = limits();
    // The existing run-one factory uses nine locals once. Empty branch
    // transports must add none. Direct endpoint conversion removes four
    // redundant wrapper constructions per branch: 12 operations, not 16.
    policy.max_locals = 9;
    policy.max_operations = 57;
    let mut assembler = Assembler::new(&mut scope, policy).unwrap();
    for index in 0..4 {
        let site = catalog
            .fetch(Coordinate {
                function,
                block: blocks[index],
                instruction: 0,
            })
            .unwrap();
        let target = catalog.branch_target(function, blocks[index + 1]).unwrap();
        assert!(target.has_explicit_empty_parameters());
        let checks = site.branch_checks(&model, &current, &target, None).unwrap();
        let transfer = site
            .branch_to(
                &mut assembler,
                &model,
                &current,
                &target,
                None,
                BranchPremises {
                    condition: None,
                    resolved: PendingEquality::candidate(
                        app("IRList", [constant("IRScalar")]),
                        app("ir_resolve", [current.machine(), checks.arguments]),
                        list("IRScalar", &[]),
                        refl(
                            &app("IRList", [constant("IRScalar")]),
                            list("IRScalar", &[]),
                        ),
                    ),
                    arity: PendingEquality::candidate(
                        constant("Bool"),
                        checks.arity,
                        constant("Bool.true"),
                        refl(&constant("Bool"), constant("Bool.true")),
                    ),
                    before: PendingEquality::candidate(
                        constant("Bool"),
                        current.valid(&model),
                        constant("Bool.true"),
                        refl(&constant("Bool"), constant("Bool.true")),
                    ),
                },
            )
            .unwrap();
        let expected = Current {
            frame: frame(function, blocks[index + 1], 0, list("IRBinding", &[])),
            ..current.clone()
        };
        let independent = PendingEquality::candidate(
            model.config_type(),
            model.step(current.running(&model)),
            expected.running(&model),
            transfer.step().term().clone(),
        );
        replay(assembler.local_scope(), &parameters, &independent, true);
        let run = PendingEquality::candidate(
            model.config_type(),
            model.run(&NatTerm::literal(1), current.running(&model)),
            expected.running(&model),
            transfer.run().equality().term().clone(),
        );
        replay(assembler.local_scope(), &parameters, &run, true);
        replay(assembler.local_scope(), &parameters, transfer.valid(), true);
        for wrong in [
            Current {
                frame: frame(function, blocks[index + 1], 1, list("IRBinding", &[])),
                ..expected.clone()
            },
            Current {
                frame: frame(
                    function,
                    blocks[index + 1],
                    0,
                    list(
                        "IRBinding",
                        &[app("IRBinding.mk", [nat(93), constant("IRScalar.unit_")])],
                    ),
                ),
                ..expected.clone()
            },
            Current {
                world: app(
                    "IRByteWorldV1.mk",
                    [
                        constant("Nat"),
                        app(
                            "ir_byte_world_memory_v1",
                            [constant("Nat"), expected.world.clone()],
                        ),
                        app("Nat.succ", [parameters[1].term().clone()]),
                        list("Nat", &[nat(1)]),
                        nat(2),
                    ],
                ),
                ..expected.clone()
            },
        ] {
            replay(
                assembler.local_scope(),
                &parameters,
                &PendingEquality::candidate(
                    model.config_type(),
                    independent.left().clone(),
                    wrong.running(&model),
                    independent.term().clone(),
                ),
                false,
            );
        }
        assert_eq!(assembler.locals, 0);
        assert_eq!(assembler.limits.max_locals, 9);
        assert_eq!(assembler.local_scope().allocated(), parameters.len());
        assert_eq!(assembler.operations, 9 + (index + 1) * 12);
        current = transfer.current().clone();
    }
    assert_eq!(assembler.operations, 57);
    assert!(
        assembler
            .conversion(constant("Nat"), nat(0), nat(0))
            .err()
            .unwrap()
            .contains("operation budget")
    );
    assert_eq!(assembler.operations, 57);
}

#[test]
fn parameterized_and_opaque_targets_keep_the_binder_transport() {
    for opaque in [false, true] {
        let mut scope = Scope::new();
        let values_left = scope
            .try_local(app("IRList", [constant("IRScalar")]))
            .unwrap();
        let values_right = scope
            .try_local(app("IRList", [constant("IRScalar")]))
            .unwrap();
        let equality = scope
            .try_local(eq(
                &app("IRList", [constant("IRScalar")]),
                values_left.term().clone(),
                values_right.term().clone(),
            ))
            .unwrap();
        let locals = scope
            .try_local(app("IRList", [constant("IRBinding")]))
            .unwrap();
        let opaque_block = scope.try_local(constant("IRBlock")).unwrap();
        let parameters = [values_left, values_right, equality, locals, opaque_block];
        let model = MachineModel::from_terms(
            constant("Nat"),
            constant("branch_mapper_unused_context"),
            constant("branch_mapper_unused_providers"),
        );
        let target = BranchTarget {
            context: model.context().clone(),
            function: FuncId(41),
            block_id: BlockId(53),
            block: if opaque {
                parameters[4].term().clone()
            } else {
                app(
                    "IRBlock.mk",
                    [nat(53), list("Nat", &[nat(601)]), list("IRNode", &[])],
                )
            },
        };
        assert!(!target.has_explicit_empty_parameters());
        let current = Current {
            frame: frame(FuncId(41), BlockId(17), 9, parameters[3].term().clone()),
            tail: list("IRFrame", &[]),
            legacy_memory: list("IRMemSlot", &[]),
            legacy_cursor: nat(0),
            world: app(
                "IRByteWorldV1.mk",
                [
                    constant("Nat"),
                    app("ir_byte_memory_empty_v1", [nat(65)]),
                    nat(37),
                    list("Nat", &[nat(1)]),
                    nat(2),
                ],
            ),
        };
        let map = |values| {
            replace_frame(
                &current,
                app(
                    "ir_frame_goto",
                    [
                        current.frame.clone(),
                        nat(53),
                        app(
                            "ir_bind_params",
                            [target.parameters(), values, parameters[3].term().clone()],
                        ),
                    ],
                ),
            )
            .running(&model)
        };
        let mut policy = limits();
        policy.max_locals = 3;
        policy.max_operations = 6;
        let mut assembler = Assembler::new(&mut scope, policy).unwrap();
        for index in 0..3 {
            let proof = branch_argument_transport(
                &mut assembler,
                &model,
                &target,
                PendingEquality::candidate(
                    app("IRList", [constant("IRScalar")]),
                    parameters[0].term().clone(),
                    parameters[1].term().clone(),
                    parameters[2].term().clone(),
                ),
                map,
            )
            .unwrap();
            assert_eq!(assembler.locals, index + 1);
            assert_eq!(assembler.operations, (index + 1) * 2);
            let independent = PendingEquality::candidate(
                model.config_type(),
                map(parameters[0].term().clone()),
                map(parameters[1].term().clone()),
                proof.term().clone(),
            );
            replay(assembler.local_scope(), &parameters, &independent, true);
        }
        assert!(
            assembler
                .local(constant("Nat"))
                .err()
                .unwrap()
                .contains("operation budget")
        );
    }
}

#[test]
fn empty_branch_recognition_does_not_normalize_opaque_or_malformed_candidates() {
    let good = app(
        "IRBlock.mk",
        [nat(53), list("Nat", &[]), list("IRNode", &[])],
    );
    let mut target = BranchTarget {
        context: constant("unused_context"),
        function: FuncId(41),
        block_id: BlockId(53),
        block: good.clone(),
    };
    assert!(target.has_explicit_empty_parameters());
    for bad in [
        constant("opaque_block"),
        app(
            "IRBlock.mk",
            [nat(53), list("Nat", &[nat(601)]), list("IRNode", &[])],
        ),
        app(
            "IRBlock.mk",
            [nat(53), constant("opaque_parameters"), list("IRNode", &[])],
        ),
        app(
            "IRBlock.mk",
            [nat(53), list("Bool", &[]), list("IRNode", &[])],
        ),
        app("IRBlock.mk", [nat(53), list("Nat", &[])]),
        Expr::app(good, nat(0)),
        Expr::apps(
            Expr::const_(Name::from_string("IRBlock.mk"), vec![Level::zero()]),
            [nat(53), list("Nat", &[]), list("IRNode", &[])],
        ),
    ] {
        target.block = bad;
        assert!(!target.has_explicit_empty_parameters());
    }
}
