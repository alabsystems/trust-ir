// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Structural candidate-construction regressions only. Placeholder constants
//! below are not installed as vocabulary or accepted as kernel evidence. The
//! frontend's actual reflected-byte replay is the consuming semantic gate.

use super::*;

fn limits() -> Limits {
    Limits {
        max_operations: 10_000,
        max_locals: 1_000,
        max_list_items: 1_000,
        max_lookup_candidates: 100,
        lookup_heartbeats: 1_000_000,
        lookup_cache_entries: 16_384,
    }
}

struct Fixture {
    model: MachineModel,
    current: Current,
    site: FetchedSite,
    parameters: Vec<Local>,
}

fn local(scope: &mut Scope, parameters: &mut Vec<Local>, ty: Expr) -> Expr {
    let parameter = scope.try_local(ty).unwrap();
    let term = parameter.term().clone();
    parameters.push(parameter);
    term
}

fn premise(
    scope: &mut Scope,
    parameters: &mut Vec<Local>,
    ty: Expr,
    left: Expr,
    right: Expr,
) -> PendingEquality {
    let proof = local(scope, parameters, eq(&ty, left.clone(), right.clone()));
    PendingEquality::candidate(ty, left, right, proof)
}

fn fixture(scope: &mut Scope, instruction: Expr, results: Expr) -> Fixture {
    let mut parameters = Vec::new();
    let model = MachineModel {
        world_type: constant("Nat"),
        context: constant("test_context"),
        providers: constant("test_providers"),
    };
    let current = Current {
        frame: app(
            "IRFrame.mk",
            [
                nat(41),
                nat(17),
                nat(9),
                local(
                    scope,
                    &mut parameters,
                    app("IRList", [constant("IRBinding")]),
                ),
                list("Nat", &[nat(300)]),
            ],
        ),
        tail: local(scope, &mut parameters, app("IRList", [constant("IRFrame")])),
        legacy_memory: local(
            scope,
            &mut parameters,
            app("IRList", [constant("IRMemSlot")]),
        ),
        legacy_cursor: local(scope, &mut parameters, constant("Nat")),
        world: local(
            scope,
            &mut parameters,
            app("IRByteWorldV1", [constant("Nat")]),
        ),
    };
    let site = FetchedSite {
        context: model.context.clone(),
        coordinate: Coordinate {
            function: FuncId::new(41),
            block: BlockId::new(17),
            instruction: 9,
        },
        function: constant("test_function"),
        block: constant("test_block"),
        node: app("IRNode.mk", [instruction.clone(), results.clone()]),
        instruction,
        results,
        site: constant("test_site"),
    };
    Fixture {
        model,
        current,
        site,
        parameters,
    }
}

fn scalar_premises(scope: &mut Scope, f: &mut Fixture, value: &Expr) -> ScalarPremises {
    let checks = f
        .site
        .scalar_checks(&f.model, &f.current, value.clone())
        .unwrap();
    ScalarPremises {
        evaluated: premise(
            scope,
            &mut f.parameters,
            constant("IRStepResult"),
            checks.evaluation,
            app("IRStepResult.value", [value.clone()]),
        ),
        operands: premise(
            scope,
            &mut f.parameters,
            constant("Bool"),
            checks.operands,
            constant("Bool.true"),
        ),
        result: premise(
            scope,
            &mut f.parameters,
            constant("Bool"),
            checks.result,
            constant("Bool.true"),
        ),
        before: premise(
            scope,
            &mut f.parameters,
            constant("Bool"),
            f.current.valid(&f.model),
            constant("Bool.true"),
        ),
    }
}

fn scalar_instructions() -> Vec<Expr> {
    let ty = app("IRTy.uint_", [nat(64)]);
    vec![
        app("IRInst.const_", [ty.clone(), app("IRConst.int_", [nat(7)])]),
        app(
            "IRInst.extractfield",
            [app("IRTy.struct_", [nat(23)]), nat(29), nat(1)],
        ),
        app(
            "IRInst.icmp",
            [constant("IRICmpOp.eq_"), ty.clone(), nat(31), nat(41)],
        ),
        app(
            "IRInst.binop",
            [constant("IRBinOp.add"), ty.clone(), nat(31), nat(41)],
        ),
        app(
            "IRInst.binop",
            [constant("IRBinOp.sub"), ty.clone(), nat(41), nat(31)],
        ),
        app(
            "IRInst.binop",
            [constant("IRBinOp.udiv"), ty.clone(), nat(41), nat(31)],
        ),
        app("IRInst.select", [ty, nat(13), nat(31), nat(41)]),
    ]
}

fn reflected_list_items(term: &Expr) -> Vec<Expr> {
    let mut cursor = term;
    let mut items = Vec::new();
    while *cursor.get_app_fn() == constant("IRList.cons") {
        let args = cursor.get_app_args();
        assert_eq!(args.len(), 3);
        items.push(args[1].clone());
        cursor = args[2];
    }
    assert_eq!(*cursor.get_app_fn(), constant("IRList.nil"));
    items
}

#[test]
fn icmp_candidates_use_actual_byte_evaluator_without_erasing_nominal_types() {
    for ty in [app("IRTy.usize_", [nat(64)]), app("IRTy.uint_", [nat(64)])] {
        let mut scope = Scope::new();
        let f = fixture(
            &mut scope,
            app(
                "IRInst.icmp",
                [constant("IRICmpOp.ugt"), ty.clone(), nat(31), nat(41)],
            ),
            list("Nat", &[nat(197)]),
        );
        let value = app("IRScalar.bool_", [constant("Bool.true")]);
        let checks = f.site.scalar_checks(&f.model, &f.current, value).unwrap();
        let read = |id| app("ir_getd", [f.current.machine(), nat(id)]);
        assert_eq!(
            checks.evaluation,
            app(
                "ir_byte_icmp_eval_v1",
                [constant("IRICmpOp.ugt"), ty.clone(), read(31), read(41),]
            )
        );
        assert_eq!(
            checks.operands,
            app(
                "Bool.and",
                [31, 41].map(|id| {
                    app(
                        "ir_byte_value_matches_v1",
                        [f.model.context.clone(), ty.clone(), read(id)],
                    )
                })
            )
        );
        // This structural test grants no semantic authority; the integration
        // replay below must establish these candidates against real vocabulary.
        assert_eq!(*checks.result.get_app_fn(), constant("Bool.and"));
    }
}

#[test]
fn pointer_parts_keep_nominal_type_metadata_sort_and_both_live_operands() {
    for (ty, metadata_ty) in [
        (constant("IRTy.fatstr_"), app("IRTy.uint_", [nat(64)])),
        (
            app("IRTy.fatslice_", [app("IRTy.uint_", [nat(8)])]),
            app("IRTy.uint_", [nat(64)]),
        ),
        (app("IRTy.fatdyn_", [nat(91)]), constant("IRTy.ptr_")),
        (constant("IRTy.containerlen_"), app("IRTy.uint_", [nat(64)])),
        (constant("IRTy.containervtable_"), constant("IRTy.ptr_")),
    ] {
        for (instruction, evaluator, typed, operands) in [
            (
                app("IRInst.ptrdata", [ty.clone(), nat(31)]),
                "ir_byte_ptrdata_eval_v1",
                vec![ty.clone()],
                vec![31],
            ),
            (
                app(
                    "IRInst.ptrmetadata",
                    [ty.clone(), metadata_ty.clone(), nat(41)],
                ),
                "ir_byte_ptrmetadata_eval_v1",
                vec![ty.clone(), metadata_ty.clone()],
                vec![41],
            ),
            (
                app(
                    "IRInst.ptrfromparts",
                    [ty.clone(), metadata_ty.clone(), nat(31), nat(41)],
                ),
                "ir_byte_ptrfromparts_eval_v1",
                vec![ty.clone(), metadata_ty.clone()],
                vec![31, 41],
            ),
        ] {
            let mut scope = Scope::new();
            let f = fixture(&mut scope, instruction, list("Nat", &[nat(197)]));
            let checks = f
                .site
                .scalar_checks(&f.model, &f.current, constant("test_value"))
                .unwrap();
            let mut expected = vec![f.model.context.clone()];
            expected.extend(typed);
            expected.extend(
                operands
                    .into_iter()
                    .map(|id| app("ir_getd", [f.current.machine(), nat(id)])),
            );
            assert_eq!(checks.evaluation, app(evaluator, expected));
            assert_eq!(checks.operands, constant("Bool.true"));
            assert_eq!(*checks.result.get_app_fn(), constant("Bool.and"));
        }
    }
}

#[test]
fn actual_reflected_nullptr_uses_existing_scalar_transfer_structurally() {
    use crate::{ModuleBuilder, core_reflection::reflect_core_module_v1};
    use trust_ir::{Endianness, Inst, StructPassingPolicy, TargetInfo, Ty};

    // Exercise the real producer and complete reflection, including a nonzero
    // instruction PC. NullPtr is not a new IRInst constructor: its meaning is
    // the already published typed constant, not a numeric pointer at address 0.
    let mut builder = ModuleBuilder::new_with_target_info(
        "null_scalar",
        TargetInfo {
            triple: "aarch64-apple-darwin".into(),
            pointer_size: 8,
            endianness: Endianness::Little,
            abi: Some("aapcs64".into()),
            struct_passing: StructPassingPolicy::NativeC,
        },
    );
    let signature = builder.add_func_type(vec![], vec![Ty::Ptr]);
    let function_id = builder.declare_function("null_result", signature);
    let block_id;
    let result_id;
    {
        let mut function = builder.define_function(function_id).unwrap();
        block_id = function.create_block();
        function.switch_to_block(block_id);
        function.uconst(Ty::U64, 7);
        result_id = function.null_ptr();
        function.ret(vec![result_id]);
        function.build();
    }
    let module = builder.build().expect("ModuleBuilder::build: test fixture");
    let reflected = reflect_core_module_v1(&module, &[(function_id, 4096)]).unwrap();
    assert!(matches!(
        reflected.node(function_id, block_id, 1).unwrap().inst,
        Inst::NullPtr
    ));
    let context = reflected.context_term();
    let context_fields = context.get_app_args();
    let module_fields = context_fields[0].get_app_args();
    let functions = reflected_list_items(module_fields[0]);
    let function = &functions[0];
    let blocks = reflected_list_items(function.get_app_args()[3]);
    let block = &blocks[0];
    let nodes = reflected_list_items(block.get_app_args()[2]);
    let node = &nodes[1];
    let sites = reflected_list_items(context_fields[4]);
    let instruction = node.get_app_args()[0].clone();
    let results = node.get_app_args()[1].clone();
    assert_eq!(
        instruction,
        app(
            "IRInst.const_",
            [constant("IRTy.ptr_"), constant("IRConst.null_")]
        )
    );
    assert_eq!(results, list("Nat", &[nat(u64::from(result_id.index()))]));

    let mut scope = Scope::new();
    let mut f = fixture(&mut scope, instruction.clone(), results.clone());
    f.model.context = context.clone();
    f.site = FetchedSite {
        context: context.clone(),
        coordinate: Coordinate {
            function: function_id,
            block: block_id,
            instruction: 1,
        },
        function: function.clone(),
        block: block.clone(),
        node: node.clone(),
        instruction,
        results: results.clone(),
        site: sites[1].clone(),
    };
    let frame = {
        let old_frame_fields = f.current.frame.get_app_args();
        app(
            "IRFrame.mk",
            [
                nat(u64::from(function_id.index())),
                nat(u64::from(block_id.index())),
                nat(1),
                old_frame_fields[3].clone(),
                old_frame_fields[4].clone(),
            ],
        )
    };
    f.current.frame = frame;
    let value = constant("IRScalar.nullptr_");
    let checks = f
        .site
        .scalar_checks(&f.model, &f.current, value.clone())
        .unwrap();
    assert_eq!(
        checks.evaluation,
        app(
            "ir_byte_const_eval_v1",
            [constant("IRTy.ptr_"), constant("IRConst.null_")]
        )
    );
    assert_eq!(checks.operands, constant("Bool.true"));
    // These are typed candidate premises, not kernel-checked byte facts. The
    // actual byte environment is deliberately not replaced with test aliases.
    let premises = scalar_premises(&mut scope, &mut f, &value);
    let transfer = f
        .site
        .scalar_value(
            &mut Assembler::new(&mut scope, limits()).unwrap(),
            &f.model,
            &f.current,
            value.clone(),
            premises.clone(),
        )
        .unwrap();
    let expected_frame = app(
        "ir_frame_advance",
        [app(
            "ir_frame_set_many",
            [f.current.frame.clone(), results, list("IRScalar", &[value])],
        )],
    );
    let expected = Current {
        frame: expected_frame,
        ..f.current.clone()
    };
    assert_eq!(transfer.current().frame, expected.frame);
    assert_eq!(transfer.current().world, f.current.world);
    assert_eq!(transfer.run().initial(), &f.current.running(&f.model));
    assert_eq!(transfer.run().reached(), &expected.running(&f.model));
    assert_eq!(transfer.run().fuel().term(), &nat(1));
    assert_eq!(transfer.step().right(), &expected.running(&f.model));
    assert_eq!(transfer.valid().left(), &expected.valid(&f.model));
    for proof in [
        transfer.step().term(),
        transfer.run().equality().term(),
        transfer.valid().term(),
    ] {
        let closed = f
            .parameters
            .iter()
            .rev()
            .fold(proof.clone(), |body, p| p.lam(body));
        assert!(!scope.close(&closed).unwrap().has_fvar_quick());
    }
    // Exact candidate endpoint refusals, not kernel TypeMismatch evidence:
    // numeric ptr(0), undef and another SSA destination cannot reuse this proof.
    for wrong_value in [app("IRScalar.ptr_", [nat(0)]), constant("IRScalar.undef_")] {
        assert!(
            f.site
                .scalar_value(
                    &mut Assembler::new(&mut scope, limits()).unwrap(),
                    &f.model,
                    &f.current,
                    wrong_value,
                    premises.clone(),
                )
                .is_err()
        );
    }
    let mut wrong_site = f.site.clone();
    wrong_site.results = list("Nat", &[nat(197)]);
    assert!(
        wrong_site
            .scalar_value(
                &mut Assembler::new(&mut scope, limits()).unwrap(),
                &f.model,
                &f.current,
                constant("IRScalar.nullptr_"),
                premises,
            )
            .is_err()
    );
}

#[test]
fn scalar_transfers_bind_once_advance_once_and_preserve_entire_world() {
    for instruction in scalar_instructions() {
        let mut scope = Scope::new();
        let mut f = fixture(&mut scope, instruction, list("Nat", &[nat(197)]));
        let value = local(&mut scope, &mut f.parameters, constant("IRScalar"));
        let premises = scalar_premises(&mut scope, &mut f, &value);
        let before = premises.before.term.clone();
        let transfer = f
            .site
            .scalar_value(
                &mut Assembler::new(&mut scope, limits()).unwrap(),
                &f.model,
                &f.current,
                value.clone(),
                premises,
            )
            .unwrap();
        let expected_frame = app(
            "ir_frame_advance",
            [app(
                "ir_frame_set_many",
                [
                    f.current.frame.clone(),
                    list("Nat", &[nat(197)]),
                    list("IRScalar", &[value]),
                ],
            )],
        );
        assert_eq!(transfer.current().frame, expected_frame);
        assert_eq!(transfer.current().world, f.current.world);
        assert_eq!(transfer.current().tail, f.current.tail);
        assert_eq!(transfer.current().legacy_memory, f.current.legacy_memory);
        assert_eq!(transfer.current().legacy_cursor, f.current.legacy_cursor);
        assert_eq!(transfer.run().initial(), &f.current.running(&f.model));
        assert_eq!(
            transfer.run().reached(),
            &transfer.current().running(&f.model)
        );
        assert_eq!(transfer.run().fuel().term(), &nat(1));
        assert_eq!(transfer.valid().left(), &transfer.current().valid(&f.model));
        assert_eq!(transfer.valid().right(), &constant("Bool.true"));
        assert_ne!(transfer.valid().left(), &f.current.valid(&f.model));
        assert_eq!(
            transfer.valid().term(),
            &before,
            "post-validity conversion reuses the pre-proof, not the pre-claim"
        );
        for proof in [transfer.run().equality().term(), transfer.valid().term()] {
            let closed = f
                .parameters
                .iter()
                .rev()
                .fold(proof.clone(), |body, p| p.lam(body));
            assert!(!scope.close(&closed).unwrap().has_fvar_quick());
        }
    }
}

#[test]
fn scalar_checks_keep_actual_operand_carriers_and_site_result_types() {
    for (index, instruction) in scalar_instructions().into_iter().enumerate() {
        let mut scope = Scope::new();
        let f = fixture(&mut scope, instruction, list("Nat", &[nat(197)]));
        let value = constant("test_value");
        let checks = f
            .site
            .scalar_checks(&f.model, &f.current, value.clone())
            .unwrap();
        if index == 1 {
            // Clean `ee4dff170`: the dispatcher's nominal field evaluator over
            // the fetched site's operand catalog, never the untyped `ir_ef_at`.
            assert_eq!(
                checks.evaluation,
                app(
                    "ir_byte_extract_field_v1",
                    [
                        f.model.context.clone(),
                        f.site.site.clone(),
                        app("IRTy.struct_", [nat(23)]),
                        nat(29),
                        app("ir_getd", [f.current.machine(), nat(29)]),
                        nat(1),
                    ],
                )
            );
        }
        if index < 2 {
            assert_eq!(checks.operands, constant("Bool.true"));
        } else {
            let ty = app("IRTy.uint_", [nat(64)]);
            let fit = |id| {
                app(
                    "ir_byte_value_matches_v1",
                    [
                        f.model.context.clone(),
                        ty.clone(),
                        app("ir_getd", [f.current.machine(), nat(id)]),
                    ],
                )
            };
            let (left, right) = if matches!(index, 4 | 5) {
                (41, 31)
            } else {
                (31, 41)
            };
            assert_eq!(checks.operands, app("Bool.and", [fit(left), fit(right)]));
        }
        assert_eq!(
            checks.result,
            app(
                "Bool.and",
                [
                    app(
                        "ir_nat_eqb",
                        [
                            app(
                                "ir_byte_length_v1",
                                [constant("Nat"), f.site.results.clone()]
                            ),
                            app(
                                "ir_byte_length_v1",
                                [
                                    constant("IRScalar"),
                                    list("IRScalar", std::slice::from_ref(&value))
                                ]
                            )
                        ]
                    ),
                    app(
                        "ir_byte_values_match_v1",
                        [
                            f.model.context.clone(),
                            app("ir_byte_site_results_v1", [f.site.site.clone()]),
                            list("IRScalar", &[value])
                        ]
                    )
                ]
            )
        );
    }
}

#[test]
fn binary_scalar_candidates_are_bound_to_exact_operator_and_ordered_operands() {
    for op in [
        "add", "sub", "mul", "udiv", "sdiv", "urem", "srem", "and_", "or_", "xor_", "shl", "lshr",
        "ashr",
    ] {
        let mut scope = Scope::new();
        let ty = app("IRTy.uint_", [nat(64)]);
        let instruction = app(
            "IRInst.binop",
            [
                constant(&format!("IRBinOp.{op}")),
                ty.clone(),
                nat(41),
                nat(31),
            ],
        );
        let mut f = fixture(&mut scope, instruction, list("Nat", &[nat(197)]));
        let value = constant("test_value");
        let checks = f
            .site
            .scalar_checks(&f.model, &f.current, value.clone())
            .unwrap();
        assert_eq!(
            checks.evaluation,
            app(
                "ir_binop_eval",
                [
                    constant(&format!("IRBinOp.{op}")),
                    ty.clone(),
                    app("ir_getd", [f.current.machine(), nat(41)]),
                    app("ir_getd", [f.current.machine(), nat(31)]),
                ]
            )
        );
        let premises = scalar_premises(&mut scope, &mut f, &value);
        for (wrong_op, wrong_ty, a, b) in [
            (if op == "sub" { "add" } else { "sub" }, ty.clone(), 41, 31),
            (op, app("IRTy.int_", [nat(64)]), 41, 31),
            (op, ty.clone(), 31, 41),
            (op, ty.clone(), 41, 41),
        ] {
            let mut wrong_site = f.site.clone();
            wrong_site.instruction = app(
                "IRInst.binop",
                [
                    constant(&format!("IRBinOp.{wrong_op}")),
                    wrong_ty,
                    nat(a),
                    nat(b),
                ],
            );
            assert!(
                wrong_site
                    .scalar_value(
                        &mut Assembler::new(&mut scope, limits()).unwrap(),
                        &f.model,
                        &f.current,
                        value.clone(),
                        premises.clone(),
                    )
                    .is_err()
            );
        }
    }
}

#[test]
fn scalar_refuses_wrong_evaluation_guard_context_and_unsupported_instruction() {
    let mut scope = Scope::new();
    let mut f = fixture(
        &mut scope,
        scalar_instructions().remove(2),
        list("Nat", &[nat(197)]),
    );
    let value = constant("test_value");
    let p = scalar_premises(&mut scope, &mut f, &value);
    for mutation in 0..4 {
        let mut wrong = p.clone();
        match mutation {
            0 => wrong.evaluated.right = app("IRStepResult.value", [constant("wrong_value")]),
            1 => wrong.operands.left = constant("Bool.true"),
            2 => wrong.result.left = constant("Bool.true"),
            _ => wrong.before.left = constant("Bool.true"),
        }
        assert!(
            f.site
                .scalar_value(
                    &mut Assembler::new(&mut scope, limits()).unwrap(),
                    &f.model,
                    &f.current,
                    value.clone(),
                    wrong
                )
                .is_err()
        );
    }
    let mut wrong_site = f.site.clone();
    wrong_site.context = constant("other_context");
    assert!(
        wrong_site
            .scalar_checks(&f.model, &f.current, value.clone())
            .is_err()
    );
    for instruction in [
        app(
            "IRInst.load",
            [constant("IRTy.ptr_"), nat(31), constant("Bool.false")],
        ),
        app("IRInst.const_", [constant("IRTy.ptr_")]),
        app("IRInst.ret", [list("Nat", &[])]),
    ] {
        wrong_site = f.site.clone();
        wrong_site.instruction = instruction;
        assert!(
            wrong_site
                .scalar_checks(&f.model, &f.current, value.clone())
                .is_err()
        );
    }
}

fn branch_fixture(scope: &mut Scope, taken: Option<bool>) -> (Fixture, BranchTarget) {
    let arguments = list("Nat", &[nat(103), nat(19)]);
    let instruction = match taken {
        None => app("IRInst.br", [nat(53), arguments.clone()]),
        Some(_) => app(
            "IRInst.condbr",
            [
                nat(7),
                nat(53),
                arguments,
                nat(71),
                list("Nat", &[nat(19), nat(103)]),
            ],
        ),
    };
    let f = fixture(scope, instruction, list("Nat", &[]));
    let block_id = BlockId::new(if taken == Some(false) { 71 } else { 53 });
    let target = BranchTarget {
        context: f.model.context.clone(),
        function: FuncId::new(41),
        block_id,
        block: app(
            "IRBlock.mk",
            [
                nat(u64::from(block_id.index())),
                list("Nat", &[nat(601), nat(809)]),
                list("IRNode", &[]),
            ],
        ),
    };
    (f, target)
}

fn branch_premises(
    scope: &mut Scope,
    f: &mut Fixture,
    target: &BranchTarget,
    taken: Option<bool>,
    values: Expr,
) -> BranchPremises {
    let checks = f
        .site
        .branch_checks(&f.model, &f.current, target, taken)
        .unwrap();
    let condition = checks.condition.map(|actual| {
        premise(
            scope,
            &mut f.parameters,
            constant("IRScalar"),
            actual,
            app(
                "IRScalar.bool_",
                [constant(if taken.unwrap() {
                    "Bool.true"
                } else {
                    "Bool.false"
                })],
            ),
        )
    });
    BranchPremises {
        condition,
        resolved: premise(
            scope,
            &mut f.parameters,
            app("IRList", [constant("IRScalar")]),
            app("ir_resolve", [f.current.machine(), checks.arguments]),
            values,
        ),
        arity: premise(
            scope,
            &mut f.parameters,
            constant("Bool"),
            checks.arity,
            constant("Bool.true"),
        ),
        before: premise(
            scope,
            &mut f.parameters,
            constant("Bool"),
            f.current.valid(&f.model),
            constant("Bool.true"),
        ),
    }
}

#[test]
fn branch_transfers_use_selected_arguments_real_parameters_and_goto_not_advance() {
    for taken in [None, Some(false), Some(true)] {
        let mut scope = Scope::new();
        let (mut f, target) = branch_fixture(&mut scope, taken);
        let values = local(
            &mut scope,
            &mut f.parameters,
            app("IRList", [constant("IRScalar")]),
        );
        let premises = branch_premises(&mut scope, &mut f, &target, taken, values.clone());
        let transfer = f
            .site
            .branch_to(
                &mut Assembler::new(&mut scope, limits()).unwrap(),
                &f.model,
                &f.current,
                &target,
                taken,
                premises,
            )
            .unwrap();
        assert_eq!(
            transfer.current().frame,
            app(
                "ir_frame_goto",
                [
                    f.current.frame.clone(),
                    nat(u64::from(target.block_id.index())),
                    app(
                        "ir_bind_params",
                        [
                            target.parameters(),
                            values,
                            app("ir_frame_locals", [f.current.frame.clone()])
                        ]
                    )
                ]
            )
        );
        assert_eq!(transfer.current().world, f.current.world);
        assert_eq!(transfer.current().tail, f.current.tail);
        assert_eq!(transfer.current().legacy_memory, f.current.legacy_memory);
        assert_eq!(transfer.current().legacy_cursor, f.current.legacy_cursor);
        assert_eq!(transfer.run().fuel().term(), &nat(1));
        assert_eq!(transfer.run().initial(), &f.current.running(&f.model));
        assert_eq!(
            transfer.run().reached(),
            &transfer.current().running(&f.model)
        );
        assert_eq!(transfer.valid().left(), &transfer.current().valid(&f.model));
        for proof in [transfer.run().equality().term(), transfer.valid().term()] {
            let closed = f
                .parameters
                .iter()
                .rev()
                .fold(proof.clone(), |body, p| p.lam(body));
            assert!(!scope.close(&closed).unwrap().has_fvar_quick());
        }
    }
}

#[test]
fn branch_refuses_wrong_arm_function_context_condition_and_resolution() {
    let mut scope = Scope::new();
    let (mut f, target) = branch_fixture(&mut scope, Some(true));
    let values = list(
        "IRScalar",
        &[
            app("IRScalar.int_", [nat(11)]),
            app("IRScalar.int_", [nat(13)]),
        ],
    );
    let p = branch_premises(&mut scope, &mut f, &target, Some(true), values);
    for mutation in 0..6 {
        let mut wrong = p.clone();
        match mutation {
            0 => wrong.condition = None,
            1 => {
                wrong.condition.as_mut().unwrap().right =
                    app("IRScalar.bool_", [constant("Bool.false")])
            }
            2 => wrong.condition.as_mut().unwrap().right = app("IRScalar.int_", [nat(1)]),
            3 => {
                wrong.resolved.left = app(
                    "ir_resolve",
                    [f.current.machine(), list("Nat", &[nat(19), nat(103)])],
                )
            }
            4 => wrong.arity.left = constant("Bool.true"),
            _ => wrong.before.left = constant("Bool.true"),
        }
        assert!(
            f.site
                .branch_to(
                    &mut Assembler::new(&mut scope, limits()).unwrap(),
                    &f.model,
                    &f.current,
                    &target,
                    Some(true),
                    wrong
                )
                .is_err()
        );
    }
    for mutation in 0..3 {
        let mut wrong = target.clone();
        match mutation {
            0 => wrong.block_id = BlockId::new(71),
            1 => wrong.function = FuncId::new(99),
            _ => wrong.context = constant("other_context"),
        }
        assert!(
            f.site
                .branch_checks(&f.model, &f.current, &wrong, Some(true))
                .is_err()
        );
    }
    assert!(
        f.site
            .branch_checks(&f.model, &f.current, &target, None)
            .is_err()
    );
    let mut wrong = f.site.clone();
    wrong.results = list("Nat", &[nat(99)]);
    assert!(
        wrong
            .branch_checks(&f.model, &f.current, &target, Some(true))
            .is_err()
    );
}

#[test]
fn scalar_and_branch_candidates_respect_existing_assembler_budgets() {
    let mut scope = Scope::new();
    let mut f = fixture(
        &mut scope,
        scalar_instructions().remove(0),
        list("Nat", &[nat(197)]),
    );
    let value = constant("test_value");
    let p = scalar_premises(&mut scope, &mut f, &value);
    let mut small = limits();
    small.max_operations = 1;
    assert!(
        f.site
            .scalar_value(
                &mut Assembler::new(&mut scope, small).unwrap(),
                &f.model,
                &f.current,
                value,
                p
            )
            .is_err()
    );
    let (mut f, target) = branch_fixture(&mut scope, Some(true));
    let p = branch_premises(
        &mut scope,
        &mut f,
        &target,
        Some(true),
        list("IRScalar", &[]),
    );
    small = limits();
    small.max_locals = 1;
    let mut assembler = Assembler::new(&mut scope, small).unwrap();
    // This parameterized branch retains its one real argument-transport
    // binder, but the closed run-one helper no longer consumes nine more.
    f.site
        .branch_to(
            &mut assembler,
            &f.model,
            &f.current,
            &target,
            Some(true),
            p.clone(),
        )
        .unwrap();
    assert_eq!(assembler.locals, 1);
    assert_eq!(assembler.limits.max_locals, 1);
    let operations = assembler.operations;
    assert!(
        assembler
            .local(constant("Nat"))
            .err()
            .unwrap()
            .contains("local budget")
    );
    assert_eq!(assembler.locals, 1);
    assert_eq!(assembler.operations, operations + 1);
    drop(assembler);
    // The original operation limit still refuses the same branch's real
    // construction, including all nine unchanged cold helper charges.
    small.max_operations = 1;
    assert!(
        f.site
            .branch_to(
                &mut Assembler::new(&mut scope, small).unwrap(),
                &f.model,
                &f.current,
                &target,
                Some(true),
                p
            )
            .is_err()
    );
}
