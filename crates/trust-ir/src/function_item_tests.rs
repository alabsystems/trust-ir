// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

use crate::interpret::{
    ArrayValue, InterpretErrorCode, InterpretValue, InterpretValueKind as K, Interpreter,
};
use crate::*;

fn v(id: u32) -> ValueId {
    ValueId::new(id)
}
fn node(inst: Inst, result: u32) -> InstrNode {
    InstrNode::new(inst).with_result(v(result))
}

fn function(id: u32, signature: FuncTyId, value: i128) -> Function {
    let mut function = Function::new(
        FuncId::new(id),
        format!("pick_{value}"),
        signature,
        BlockId::new(0),
    );
    let mut block = Block::new(BlockId::new(0));
    block.body.push(node(
        Inst::Const {
            ty: Ty::I32,
            value: Constant::Int(value),
        },
        0,
    ));
    block
        .body
        .push(InstrNode::new(Inst::Return { values: vec![v(0)] }));
    function.blocks.push(block);
    function
}

fn module() -> Module {
    let mut module = Module::new("nominal-items");
    let signature = module
        .add_func_type(FuncTy::unrecorded(vec![], vec![Ty::I32], false))
        .unwrap();
    module.functions = vec![function(7, signature, 1), function(42, signature, 2)];
    module
}

fn entry(module: &mut Module, params: Vec<Ty>, returns: Vec<Ty>, instructions: Vec<InstrNode>) {
    let signature = module
        .add_func_type(FuncTy::unrecorded(params.clone(), returns, false))
        .unwrap();
    let mut function = Function::new(FuncId::new(0), "entry", signature, BlockId::new(0));
    let mut block = Block::new(BlockId::new(0));
    block.params = params
        .into_iter()
        .enumerate()
        .map(|(i, ty)| (v(i as u32), ty))
        .collect();
    block.body = instructions;
    function.blocks.push(block);
    module.functions.push(function);
}

fn item_value(id: u32) -> InterpretValue {
    InterpretValue {
        ty: Ty::FnItem(FuncId::new(id)),
        kind: K::FnItem(FuncId::new(id)),
    }
}

fn unit_value() -> InterpretValue {
    InterpretValue {
        ty: Ty::Unit,
        kind: K::Unit,
    }
}

fn identity_entry(module: &mut Module, ty: &Ty) {
    entry(
        module,
        vec![ty.clone()],
        vec![ty.clone()],
        vec![InstrNode::new(Inst::Return { values: vec![v(0)] })],
    );
}

#[test]
fn fn_item_headers_are_sparse_unique_and_signature_checked() {
    let mut module = module();
    assert_eq!(
        module.function_item(FuncId::new(42)).unwrap().0.id,
        FuncId::new(42)
    );
    assert_ne!(Ty::FnItem(FuncId::new(7)), Ty::FnItem(FuncId::new(42)));
    assert_ne!(
        Constant::FnItem(FuncId::new(7)),
        Constant::FnItem(FuncId::new(42))
    );
    assert!(!Ty::FnItem(FuncId::new(7)).is_pointer_like());
    let layout = module.ty_layout_shape(&Ty::FnItem(FuncId::new(7))).unwrap();
    assert_eq!((layout.size_bits, layout.align_bits), (0, Some(8)));
    assert!(
        module
            .ty_layout_shape(&Ty::FnItem(FuncId::new(99)))
            .is_err()
    );
    module.functions.push(module.functions[0].clone());
    assert!(module.function_item(FuncId::new(7)).is_err());
    assert!(module.ty_layout_shape(&Ty::FnItem(FuncId::new(7))).is_err());
    module.functions.pop();
    module.functions[0].ty = FuncTyId::new(99);
    assert!(matches!(
        module.function_item(FuncId::new(7)),
        Err(FunctionItemError::MissingSignature { .. })
    ));
}

#[test]
fn fn_item_layout_memo_does_not_reuse_changed_or_ambiguous_headers() {
    let mut module = module();
    module.types.push(Ty::FnItem(FuncId::new(7)));
    let array = Ty::Array(TyId::new(0), 2);
    let layouts = module.layout_table();
    assert_eq!(layouts.ty_layout_shape(&array).unwrap().size_bits, 0);
    let memo = layouts.into_memo();
    let cached = LayoutTable::with_memo(&module, memo);
    assert_eq!(cached.ty_layout_shape(&array).unwrap().size_bits, 0);
    let memo = cached.into_memo();
    module.functions[0].id = FuncId::new(42); // same row count, now ambiguous
    assert!(
        LayoutTable::with_memo(&module, memo)
            .ty_layout_shape(&array)
            .is_err()
    );
}

#[test]
fn fn_item_header_dependency_does_not_invalidate_legacy_layout_only_memos() {
    fn shorten<'short, 'long: 'short>(table: LayoutTable<'long>) -> LayoutTable<'short> {
        table
    }
    let mut module = module();
    module.types.push(Ty::U8);
    let array = Ty::Array(TyId::new(0), 4);
    let layouts = module.layout_table();
    assert_eq!(layouts.ty_layout_shape(&array).unwrap().size_bits, 32);
    let memo = layouts.into_memo();
    let before = memo.stats();
    module
        .func_types
        .push(FuncTy::unrecorded(vec![], vec![], false));
    let next = shorten(LayoutTable::with_memo(&module, memo));
    assert_eq!(next.stats().nodes, before.nodes);
    assert_eq!(next.stats().steps, before.steps);
    assert_eq!(next.ty_layout_shape(&array).unwrap().size_bits, 32);
}

#[test]
fn fn_item_calls_preserve_distinct_same_signature_targets() {
    let mut module = module();
    let item = |id| Ty::FnItem(FuncId::new(id));
    entry(
        &mut module,
        vec![],
        vec![Ty::I32, Ty::I32],
        vec![
            node(
                Inst::Const {
                    ty: item(7),
                    value: Constant::FnItem(FuncId::new(7)),
                },
                0,
            ),
            node(
                Inst::Const {
                    ty: item(42),
                    value: Constant::FnItem(FuncId::new(42)),
                },
                1,
            ),
            node(
                Inst::CallIndirect {
                    callee: v(0),
                    sig: FuncTyId::new(0),
                    args: vec![],
                    calling_conv: CallingConv::C,
                },
                2,
            ),
            node(
                Inst::CallIndirect {
                    callee: v(1),
                    sig: FuncTyId::new(0),
                    args: vec![],
                    calling_conv: CallingConv::C,
                },
                3,
            ),
            InstrNode::new(Inst::Return {
                values: vec![v(2), v(3)],
            }),
        ],
    );
    let result = Interpreter::with_module(&module)
        .execute_func(FuncId::new(0), [])
        .unwrap();
    assert_eq!(
        result.returns[0].as_int().map(|value| value.as_signed()),
        Some(1)
    );
    assert_eq!(
        result.returns[1].as_int().map(|value| value.as_signed()),
        Some(2)
    );
    assert_eq!(result.host_calls, 0);
}

#[test]
fn fn_item_zero_byte_memory_and_explicit_casts_reconstruct_destination_identity() {
    let mut module = module();
    let one = Ty::FnItem(FuncId::new(7));
    let two = Ty::FnItem(FuncId::new(42));
    module.types.push(one.clone());
    let huge = Ty::Array(TyId::new(0), u64::MAX);
    entry(
        &mut module,
        vec![],
        vec![one.clone(), two.clone(), huge.clone()],
        vec![
            node(
                Inst::Const {
                    ty: one.clone(),
                    value: Constant::FnItem(FuncId::new(7)),
                },
                0,
            ),
            node(
                Inst::Alloca {
                    ty: one.clone(),
                    count: None,
                    align: None,
                },
                1,
            ),
            InstrNode::new(Inst::Store {
                ty: one.clone(),
                ptr: v(1),
                value: v(0),
                volatile: false,
                align: None,
            }),
            node(
                Inst::Load {
                    ty: one.clone(),
                    ptr: v(1),
                    volatile: false,
                    align: None,
                },
                2,
            ),
            node(
                Inst::Cast {
                    op: CastOp::Transmute,
                    src_ty: one.clone(),
                    dst_ty: Ty::Unit,
                    operand: v(2),
                },
                3,
            ),
            node(
                Inst::Cast {
                    op: CastOp::Transmute,
                    src_ty: Ty::Unit,
                    dst_ty: two.clone(),
                    operand: v(3),
                },
                4,
            ),
            node(
                Inst::Alloca {
                    ty: huge.clone(),
                    count: None,
                    align: None,
                },
                5,
            ),
            node(
                Inst::Load {
                    ty: huge,
                    ptr: v(5),
                    volatile: false,
                    align: None,
                },
                6,
            ),
            InstrNode::new(Inst::Return {
                values: vec![v(2), v(4), v(6)],
            }),
        ],
    );
    let result = Interpreter::with_module(&module)
        .execute_func(FuncId::new(0), [])
        .unwrap();
    assert_eq!(result.returns[0].kind, K::FnItem(FuncId::new(7)));
    assert_eq!(result.returns[1].kind, K::FnItem(FuncId::new(42)));
    let K::Array(values) = &result.returns[2].kind else {
        panic!("array")
    };
    assert_eq!(values.len(), u64::MAX);
    assert_eq!(
        values.get(u64::MAX - 1).unwrap().kind,
        K::FnItem(FuncId::new(7))
    );
    let mut stored = 0;
    let _: core::ops::ControlFlow<()> = values.try_for_each_stored(|_| {
        stored += 1;
        core::ops::ControlFlow::Continue(())
    });
    assert_eq!(
        stored, 1,
        "logical zero-byte length must not allocate per element"
    );
}

#[test]
fn fn_item_runtime_rejects_forged_payloads_and_wrong_constant_ids() {
    let mut module = module();
    let item = Ty::FnItem(FuncId::new(7));
    entry(
        &mut module,
        vec![item.clone()],
        vec![item.clone()],
        vec![InstrNode::new(Inst::Return { values: vec![v(0)] })],
    );
    for kind in [
        K::FnItem(FuncId::new(42)),
        K::Unit,
        K::FnDef(FuncId::new(7)),
    ] {
        let error = Interpreter::with_module(&module)
            .execute_func(
                FuncId::new(0),
                [InterpretValue {
                    ty: item.clone(),
                    kind,
                }],
            )
            .unwrap_err();
        assert_eq!(error.code, InterpretErrorCode::TypeError);
    }
    module.functions.pop();
    entry(
        &mut module,
        vec![],
        vec![item.clone()],
        vec![
            node(
                Inst::Const {
                    ty: item,
                    value: Constant::FnItem(FuncId::new(42)),
                },
                0,
            ),
            InstrNode::new(Inst::Return { values: vec![v(0)] }),
        ],
    );
    assert_eq!(
        Interpreter::with_module(&module)
            .execute_func(FuncId::new(0), [])
            .unwrap_err()
            .code,
        InterpretErrorCode::TypeError
    );
}

#[test]
fn fn_item_reification_preserves_exact_target_and_pointer_representation() {
    let mut module = module();
    let item = Ty::FnItem(FuncId::new(42));
    let pointer = Ty::Func(FuncTyId::new(0));
    entry(
        &mut module,
        vec![],
        vec![Ty::I32],
        vec![
            node(
                Inst::Const {
                    ty: item.clone(),
                    value: Constant::FnItem(FuncId::new(42)),
                },
                0,
            ),
            node(
                Inst::Cast {
                    op: CastOp::ReifyFnPointer,
                    src_ty: item,
                    dst_ty: pointer,
                    operand: v(0),
                },
                1,
            ),
            node(
                Inst::CallIndirect {
                    callee: v(1),
                    sig: FuncTyId::new(0),
                    args: vec![],
                    calling_conv: CallingConv::C,
                },
                2,
            ),
            InstrNode::new(Inst::Return { values: vec![v(2)] }),
        ],
    );
    assert_eq!(
        Interpreter::with_module(&module)
            .execute_func(FuncId::new(0), [])
            .unwrap()
            .returns[0]
            .as_int()
            .map(|value| value.as_signed()),
        Some(2)
    );
}

#[test]
fn fn_item_nested_boundaries_check_source_fields_and_preserve_unwritten_lanes() {
    let mut module = module();
    let item = Ty::FnItem(FuncId::new(7));
    let tuple = Ty::Tuple(vec![item.clone()]);
    entry(
        &mut module,
        vec![tuple.clone()],
        vec![tuple.clone()],
        vec![InstrNode::new(Inst::Return { values: vec![v(0)] })],
    );
    for child in [
        InterpretValue {
            ty: Ty::Unit,
            kind: K::Unit,
        },
        InterpretValue {
            ty: item.clone(),
            kind: K::FnItem(FuncId::new(42)),
        },
    ] {
        let forged = InterpretValue {
            ty: tuple.clone(),
            kind: K::Aggregate(vec![child]),
        };
        assert_eq!(
            Interpreter::with_module(&module)
                .execute_func(FuncId::new(0), [forged])
                .unwrap_err()
                .code,
            InterpretErrorCode::TypeError
        );
    }
    let unwritten = InterpretValue {
        ty: tuple,
        kind: K::Aggregate(vec![InterpretValue {
            ty: item,
            kind: K::Uninit,
        }]),
    };
    let result = Interpreter::with_module(&module)
        .execute_func(FuncId::new(0), [unwritten.clone()])
        .unwrap();
    assert_eq!(result.returns, vec![unwritten]);
}

#[test]
fn fn_item_record_boundaries_require_exact_names_and_preserve_unwritten_lanes() {
    let mut module = module();
    let item = Ty::FnItem(FuncId::new(7));
    let record = Ty::Record(RecordId::new(0));
    module.records.push(RecordDef {
        id: RecordId::new(0),
        name: "StoredItem".into(),
        fields: vec![
            FieldDef {
                name: "held".into(),
                ty: item.clone(),
                offset: None,
            },
            FieldDef {
                name: "plain".into(),
                ty: Ty::Unit,
                offset: None,
            },
        ],
    });
    identity_entry(&mut module, &record);
    let argument = |fields| InterpretValue {
        ty: record.clone(),
        kind: K::Record(fields),
    };
    let named = argument(vec![
        ("held".into(), item_value(7)),
        ("plain".into(), unit_value()),
    ]);
    assert_eq!(
        Interpreter::with_module(&module)
            .execute_func(FuncId::new(0), [named.clone()])
            .unwrap()
            .returns,
        vec![named]
    );
    for fields in [
        // A missing field and a same-count duplicated label are different
        // malformed arguments to the same otherwise valid source module.
        vec![("plain".into(), unit_value())],
        vec![
            ("plain".into(), unit_value()),
            ("plain".into(), unit_value()),
        ],
        vec![
            ("held".into(), item_value(7)),
            ("unknown".into(), unit_value()),
        ],
        vec![
            ("held".into(), unit_value()),
            ("plain".into(), unit_value()),
        ],
        vec![
            ("held".into(), item_value(42)),
            ("plain".into(), unit_value()),
        ],
        vec![
            ("held".into(), item_value(7)),
            (
                "unknown".into(),
                InterpretValue {
                    ty: Ty::Unit,
                    kind: K::Uninit,
                },
            ),
        ],
    ] {
        assert_eq!(
            Interpreter::with_module(&module)
                .execute_func(FuncId::new(0), [argument(fields)])
                .unwrap_err()
                .code,
            InterpretErrorCode::TypeError
        );
    }
    let unwritten = argument(vec![
        (
            "held".into(),
            InterpretValue {
                ty: item.clone(),
                kind: K::Uninit,
            },
        ),
        ("plain".into(), unit_value()),
    ]);
    assert_eq!(
        Interpreter::with_module(&module)
            .execute_func(FuncId::new(0), [unwritten.clone()])
            .unwrap()
            .returns,
        vec![unwritten.clone()]
    );
    module.functions.pop();
    entry(
        &mut module,
        vec![record.clone()],
        vec![item.clone()],
        vec![
            node(
                Inst::ExtractField {
                    ty: item,
                    aggregate: v(0),
                    field: 0,
                },
                1,
            ),
            InstrNode::new(Inst::Return { values: vec![v(1)] }),
        ],
    );
    assert_eq!(
        Interpreter::with_module(&module)
            .execute_func(FuncId::new(0), [unwritten])
            .unwrap_err()
            .code,
        InterpretErrorCode::UndefinedBehavior
    );
}

#[test]
fn fn_item_record_boundary_refuses_duplicate_declared_labels() {
    // This declaration is intentionally malformed. Genuine item headers are
    // still present; an ambiguous source label cannot be hidden by the first
    // matching Unit field or blamed on a missing item declaration.
    let mut module = module();
    let record = Ty::Record(RecordId::new(0));
    module.records.push(RecordDef {
        id: RecordId::new(0),
        name: "AmbiguousItemField".into(),
        fields: vec![
            FieldDef {
                name: "same".into(),
                ty: Ty::Unit,
                offset: None,
            },
            FieldDef {
                name: "same".into(),
                ty: Ty::FnItem(FuncId::new(7)),
                offset: None,
            },
        ],
    });
    identity_entry(&mut module, &record);
    let argument = InterpretValue {
        ty: record,
        kind: K::Record(vec![
            ("same".into(), unit_value()),
            ("same".into(), unit_value()),
        ]),
    };
    let error = Interpreter::with_module(&module)
        .execute_func(FuncId::new(0), [argument])
        .unwrap_err();
    assert_eq!(error.code, InterpretErrorCode::TypeError);
    assert!(error.message.contains("declaration has duplicate"));
}

#[test]
fn fn_item_collection_boundaries_require_matching_kinds_and_array_counts() {
    let roots = [
        Ty::Array(TyId::new(0), 1),
        Ty::Sequence(TyId::new(0)),
        Ty::Set(TyId::new(0), SetRepr::Boxed),
    ];
    for (expected, ty) in roots.into_iter().enumerate() {
        let mut module = module();
        module.types.push(Ty::FnItem(FuncId::new(7)));
        identity_entry(&mut module, &ty);
        for actual in 0..3 {
            let values = ArrayValue::from_vec(vec![item_value(7)]);
            let kind = match actual {
                0 => K::Array(values),
                1 => K::Sequence(values),
                2 => K::Set(values),
                _ => unreachable!(),
            };
            let argument = InterpretValue {
                ty: ty.clone(),
                kind,
            };
            let result =
                Interpreter::with_module(&module).execute_func(FuncId::new(0), [argument.clone()]);
            if actual == expected {
                assert_eq!(result.unwrap().returns, vec![argument]);
            } else {
                assert_eq!(result.unwrap_err().code, InterpretErrorCode::TypeError);
            }
        }
        if expected == 0 {
            for count in [0, 2, u64::MAX] {
                let argument = InterpretValue {
                    ty: ty.clone(),
                    kind: K::Array(ArrayValue::splat(item_value(7), count)),
                };
                assert_eq!(
                    Interpreter::with_module(&module)
                        .execute_func(FuncId::new(0), [argument])
                        .unwrap_err()
                        .code,
                    InterpretErrorCode::TypeError
                );
            }
        }
    }
}

#[test]
fn fn_item_collection_boundary_keeps_huge_zero_byte_arrays_compact() {
    let mut module = module();
    module.types.push(Ty::FnItem(FuncId::new(7)));
    let ty = Ty::Array(TyId::new(0), u64::MAX);
    identity_entry(&mut module, &ty);
    let argument = InterpretValue {
        ty,
        kind: K::Array(ArrayValue::splat(item_value(7), u64::MAX)),
    };
    let result = Interpreter::with_module(&module)
        .execute_func(FuncId::new(0), [argument.clone()])
        .unwrap();
    assert_eq!(result.returns, vec![argument]);
    let K::Array(values) = &result.returns[0].kind else {
        panic!("array")
    };
    assert_eq!(values.len(), u64::MAX);
    let mut stored = 0;
    let _: core::ops::ControlFlow<()> = values.try_for_each_stored(|_| {
        stored += 1;
        core::ops::ControlFlow::Continue(())
    });
    assert_eq!(stored, 1);
}

#[test]
fn fn_item_vector_boundary_checks_raw_schema_logical_lane_counts() {
    // The validator already excludes FnItem SIMD lanes. These cases exercise
    // only defense at the public interpreter's raw-schema boundary; they do
    // not admit a new vector family or change the validator's scalar lanes.
    let mut module = module();
    let ty = Ty::Vector(Box::new(Ty::FnItem(FuncId::new(7))), 2);
    identity_entry(&mut module, &ty);
    for count in [0, 1, 3, u64::MAX] {
        let argument = InterpretValue {
            ty: ty.clone(),
            kind: K::Vector(ArrayValue::splat(item_value(7), count)),
        };
        assert_eq!(
            Interpreter::with_module(&module)
                .execute_func(FuncId::new(0), [argument])
                .unwrap_err()
                .code,
            InterpretErrorCode::TypeError
        );
    }
}

#[test]
fn fn_item_census_preserves_non_item_legacy_container_behavior() {
    // This new nominal-only guard is not a replacement for general module
    // validation. Keep the old non-item raw-value behavior unchanged.
    let mut module = module();
    module.types.push(Ty::U8);
    let array = Ty::Array(TyId::new(0), 1);
    identity_entry(&mut module, &array);
    let values = ArrayValue::splat(InterpretValue::int(Ty::U8, 5).unwrap(), 2);
    for kind in [K::Array(values.clone()), K::Sequence(values)] {
        let argument = InterpretValue {
            ty: array.clone(),
            kind,
        };
        assert_eq!(
            Interpreter::with_module(&module)
                .execute_func(FuncId::new(0), [argument.clone()])
                .unwrap()
                .returns,
            vec![argument]
        );
    }
    module.functions.pop();
    let record = Ty::Record(RecordId::new(0));
    module.records.push(RecordDef {
        id: RecordId::new(0),
        name: "NoItems".into(),
        fields: vec![
            FieldDef {
                name: "first".into(),
                ty: Ty::Unit,
                offset: None,
            },
            FieldDef {
                name: "second".into(),
                ty: Ty::Unit,
                offset: None,
            },
        ],
    });
    identity_entry(&mut module, &record);
    let argument = InterpretValue {
        ty: record,
        kind: K::Record(vec![
            ("second".into(), unit_value()),
            ("second".into(), unit_value()),
        ]),
    };
    assert_eq!(
        Interpreter::with_module(&module)
            .execute_func(FuncId::new(0), [argument.clone()])
            .unwrap()
            .returns,
        vec![argument]
    );
}

#[test]
fn fn_item_invoke_uses_the_normal_call_result_path() {
    let mut module = module();
    let mut function = Function::new(
        FuncId::new(0),
        "invoke_item",
        FuncTyId::new(0),
        BlockId::new(0),
    );
    let mut start = Block::new(BlockId::new(0));
    start.body.push(node(
        Inst::Const {
            ty: Ty::FnItem(FuncId::new(42)),
            value: Constant::FnItem(FuncId::new(42)),
        },
        0,
    ));
    start.body.push(node(
        Inst::InvokeIndirect {
            callee: v(0),
            sig: FuncTyId::new(0),
            args: vec![],
            calling_conv: CallingConv::C,
            normal_dest: BlockId::new(1),
            normal_args: vec![v(1)],
            unwind_dest: BlockId::new(2),
        },
        1,
    ));
    let mut normal = Block::new(BlockId::new(1));
    normal.params.push((v(2), Ty::I32));
    normal
        .body
        .push(InstrNode::new(Inst::Return { values: vec![v(2)] }));
    let mut unwind = Block::new(BlockId::new(2));
    unwind.body.push(InstrNode::new(Inst::Unreachable));
    function.blocks = vec![start, normal, unwind];
    module.functions.push(function);
    assert_eq!(
        Interpreter::with_module(&module)
            .execute_func(FuncId::new(0), [])
            .unwrap()
            .returns[0]
            .as_int()
            .map(|value| value.as_signed()),
        Some(2)
    );
}

#[test]
fn fn_item_generic_level_maps_and_cross_module_comparison_keep_identity() {
    let item = Ty::Tuple(vec![Ty::FnItem(FuncId::new(7))]);
    let embedded: crate::ty::TyG<()> = item.embed();
    assert!(
        matches!(embedded, crate::ty::TyG::Tuple(ref fields) if matches!(fields.as_slice(), [crate::ty::TyG::FnItem(id)] if *id == FuncId::new(7)))
    );
    let constant: crate::constant::ConstantG<()> = Constant::FnItem(FuncId::new(42)).embed();
    assert!(matches!(constant, crate::constant::ConstantG::FnItem(id) if id == FuncId::new(42)));
    let a = module();
    let mut b = module();
    b.functions[0].id = FuncId::new(99);
    assert!(crate::imports::ty_structurally_eq_across(
        &a,
        &Ty::FnItem(FuncId::new(7)),
        &b,
        &Ty::FnItem(FuncId::new(99))
    ));
    assert!(!crate::imports::ty_structurally_eq_across(
        &a,
        &Ty::FnItem(FuncId::new(7)),
        &b,
        &Ty::FnItem(FuncId::new(42))
    ));
    b.functions.push(b.functions[0].clone());
    assert!(!crate::imports::ty_structurally_eq_across(
        &a,
        &Ty::FnItem(FuncId::new(7)),
        &b,
        &Ty::FnItem(FuncId::new(99))
    ));
}

#[test]
fn fn_item_nominal_reachability_uses_exact_ssa_type_and_rejects_ambiguous_or_early_uses() {
    use crate::function_dependencies::{
        DependencyNode, DependencyRefusalKind, inspect_function_dependencies,
    };
    let mut module = module();
    entry(
        &mut module,
        vec![Ty::FnItem(FuncId::new(7))],
        vec![Ty::I32],
        vec![
            node(
                Inst::CallIndirect {
                    callee: v(0),
                    sig: FuncTyId::new(0),
                    args: vec![],
                    calling_conv: CallingConv::C,
                },
                1,
            ),
            InstrNode::new(Inst::Return { values: vec![v(1)] }),
        ],
    );
    let census = inspect_function_dependencies(&module, FuncId::new(0));
    assert!(census.refusals().is_empty(), "{:?}", census.refusals());
    assert!(
        census
            .edges()
            .iter()
            .any(|edge| edge.target == DependencyNode::Function(FuncId::new(7)))
    );
    let duplicate = node(
        Inst::Const {
            ty: Ty::FnItem(FuncId::new(42)),
            value: Constant::FnItem(FuncId::new(42)),
        },
        0,
    );
    module.functions.last_mut().unwrap().blocks[0]
        .body
        .insert(0, duplicate);
    assert!(
        inspect_function_dependencies(&module, FuncId::new(0))
            .refusals()
            .iter()
            .any(|refusal| refusal.kind == DependencyRefusalKind::IndirectCall)
    );
    module.functions.last_mut().unwrap().blocks[0]
        .params
        .clear();
    module.functions.last_mut().unwrap().blocks[0]
        .body
        .swap(0, 1);
    assert!(
        inspect_function_dependencies(&module, FuncId::new(0))
            .refusals()
            .iter()
            .any(|refusal| refusal.kind == DependencyRefusalKind::IndirectCall)
    );
}

#[test]
fn fn_item_handoff_keys_keep_nominal_identity_separate_from_pointer_shapes() {
    use crate::analysis::{CarriedKey, FnShape, IndirectCallUniverse, PoolKey};
    let module = module();
    let one = PoolKey::FnItem(FuncId::new(7));
    let two = PoolKey::FnItem(FuncId::new(42));
    let keys = crate::analysis::carried_keys(
        &ModuleFunctionCatalog::new(&module),
        &mut crate::reach::DefIndex::default(),
        &Ty::Tuple(vec![
            Ty::FnItem(FuncId::new(7)),
            Ty::FnItem(FuncId::new(42)),
        ]),
    );
    assert!(keys.contains(&CarriedKey::Key(one.clone())));
    assert!(keys.contains(&CarriedKey::Key(two.clone())));
    assert!(!keys.contains(&CarriedKey::AnyFn));
    let pools = IndirectCallUniverse::default().close(false);
    assert!(pools.admits(&CarriedKey::Key(one.clone()), &one));
    assert!(!pools.admits(&CarriedKey::Key(one.clone()), &two));
    assert!(!pools.admits(&CarriedKey::Key(one), &PoolKey::Fn(FnShape::unclassified())));
    assert!(pools.admits(&CarriedKey::AnyFn, &two));
}

#[test]
fn fn_item_carrier_catalogs_preserve_nested_identity_and_header_refusals() {
    use crate::analysis::{CarriedKey, PoolKey};
    let mut source = module();
    source.types.push(Ty::FnItem(FuncId::new(7)));
    let ty = Ty::Tuple(vec![
        Ty::Array(TyId::new(0), 1 << 40),
        Ty::FnItem(FuncId::new(42)),
    ]);
    source.types.push(ty.clone());
    let check = |source: &Module, opaque: bool| {
        let catalog = ModuleFunctionCatalog::new(source);
        let carriers = catalog.callable_carriers(&ty);
        assert_eq!(carriers, source.callable_carriers(&ty));
        assert_eq!(carriers.opaque, opaque);
        assert_eq!(carriers.fn_items, [FuncId::new(7), FuncId::new(42)].into());
        assert!(catalog.callable_carriers(&Ty::U64).is_empty());
        let keys =
            crate::analysis::carried_keys(&catalog, &mut crate::reach::DefIndex::default(), &ty);
        if opaque {
            assert_eq!(keys, vec![CarriedKey::Any]);
        } else {
            assert_eq!(
                keys,
                vec![
                    CarriedKey::Key(PoolKey::FnItem(FuncId::new(7))),
                    CarriedKey::Key(PoolKey::FnItem(FuncId::new(42))),
                ]
            );
        }
    };
    check(&source, false);
    source.functions.push(source.functions[0].clone());
    check(&source, true);
    source.functions.pop();
    source.functions[0].ty = FuncTyId::new(99);
    check(&source, true);
    source.functions.remove(0);
    check(&source, true);
    // Identical type spellings in another source do not borrow these headers.
    let mut other = Module::new("other");
    other.types = source.types.clone();
    check(&other, true);
}

#[test]
fn fn_item_transparent_argument_shapes_use_the_actual_catalog_headers() {
    use crate::analysis::{ArgClass, fn_pool_shape};
    let mut source = module();
    source.structs.push(StructDef {
        id: StructId::new(90),
        name: "payload_and_item".into(),
        fields: vec![
            FieldDef {
                name: "value".into(),
                ty: Ty::U64,
                offset: None,
            },
            FieldDef {
                name: "item".into(),
                ty: Ty::FnItem(FuncId::new(7)),
                offset: None,
            },
        ],
        size: None,
        align: None,
        repr: StructRepr::Transparent,
        origin: None,
    });
    let signature = source
        .add_func_type(FuncTy::unrecorded(
            vec![Ty::Struct(StructId::new(90))],
            vec![],
            false,
        ))
        .unwrap();
    let params = |source: &Module| {
        fn_pool_shape(&ModuleFunctionCatalog::new(source), signature)
            .params
            .unwrap()
    };
    assert_eq!(params(&source), vec![ArgClass::Int(64)]);
    source.functions.push(source.functions[0].clone());
    assert_eq!(params(&source), vec![ArgClass::Unclassified]);
    source.functions.pop();
    source.functions[0].ty = FuncTyId::new(99);
    assert_eq!(params(&source), vec![ArgClass::Unclassified]);
}
