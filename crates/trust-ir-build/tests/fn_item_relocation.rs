// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! Function-item identity follows function relocation, rather than signature
//! interning. Exercise the public merge and checked template entry points.

use trust_ir::template::{
    HoleAnswer, HoleDef, HoleKind, HostKey, InstArg, InstanceHeader, LinkAnswer, ScriptedAnswer,
    ScriptedHost, TEMPLATE_BODY_NAME, Template, TemplateArg, TemplateHeader, TemplateParam,
    hole_row_name,
};
use trust_ir::{
    Block, BlockG, BlockId, BodyGate, CallingConv, Constant, ConstantG, FieldDef, FieldDefG,
    FuncId, FuncTy, FuncTyG, Function, FunctionG, HoleId, Inst, InstG, InstrNode, InstrNodeG,
    InterpretValue, InterpretValueKind, Interpreter, Linkage, Module, ModuleG, StructDef,
    StructDefG, StructId, StructRepr, TargetInfo, TemplateRef, Ty, TyG, ValueId, Visibility,
};
use trust_ir_build::template::{InstantiateError, instantiate};
use trust_ir_build::{MergeError, MergePolicy, merge_into, validate_module};

fn target() -> TargetInfo {
    TargetInfo {
        triple: "aarch64-apple-darwin".into(),
        pointer_size: 8,
        endianness: trust_ir::Endianness::Little,
        abi: None,
        struct_passing: Default::default(),
    }
}

fn value(id: u32) -> ValueId {
    ValueId::new(id)
}

fn source() -> Module {
    let mut module = Module::new("items-to-relocate");
    module.target_info = Some(target());
    let signature = module
        .add_func_type(FuncTy::unrecorded(vec![], vec![Ty::U32], false))
        .unwrap();
    for id in [7, 19] {
        let mut function = Function::new(
            FuncId::new(id),
            format!("target_{id}"),
            signature,
            BlockId::new(0),
        );
        function.blocks.push(Block {
            id: BlockId::new(0),
            params: vec![],
            body: vec![
                InstrNode::new(Inst::Const {
                    ty: Ty::U32,
                    value: Constant::Int(i128::from(id)),
                })
                .with_result(value(0)),
                InstrNode::new(Inst::Return {
                    values: vec![value(0)],
                }),
            ],
        });
        module.try_add_function(function).unwrap();
    }
    // Stored types must relocate even when no instruction queries their layout.
    module.types.push(Ty::Tuple(vec![
        Ty::FnItem(FuncId::new(7)),
        Ty::Ref(Box::new(Ty::FnItem(FuncId::new(19)))),
        Ty::Func(signature),
    ]));
    module.structs.push(StructDef {
        id: StructId::new(3),
        name: "ItemHolder".into(),
        fields: vec![FieldDef {
            name: "item".into(),
            ty: Ty::FnItem(FuncId::new(19)),
            offset: None,
        }],
        size: None,
        align: None,
        repr: StructRepr::Rust,
        origin: None,
    });
    let entry_signature = module
        .add_func_type(FuncTy::unrecorded(vec![], vec![Ty::U32, Ty::U32], false))
        .unwrap();
    let mut entry = Function::new(
        FuncId::new(41),
        "call_both_items",
        entry_signature,
        BlockId::new(0),
    );
    entry.blocks.push(Block {
        id: BlockId::new(0),
        params: vec![],
        body: vec![
            InstrNode::new(Inst::Const {
                ty: Ty::FnItem(FuncId::new(7)),
                value: Constant::FnItem(FuncId::new(7)),
            })
            .with_result(value(0)),
            InstrNode::new(Inst::Const {
                ty: Ty::FnItem(FuncId::new(19)),
                value: Constant::FnItem(FuncId::new(19)),
            })
            .with_result(value(1)),
            InstrNode::new(Inst::CallIndirect {
                callee: value(0),
                sig: signature,
                args: vec![],
                calling_conv: CallingConv::C,
            })
            .with_result(value(2)),
            InstrNode::new(Inst::CallIndirect {
                callee: value(1),
                sig: signature,
                args: vec![],
                calling_conv: CallingConv::C,
            })
            .with_result(value(3)),
            InstrNode::new(Inst::Return {
                values: vec![value(2), value(3)],
            }),
        ],
    });
    module.try_add_function(entry).unwrap();
    module
}

#[test]
fn fn_item_merge_relocates_stored_types_constants_and_actual_call_targets() {
    let source = source();
    assert_eq!(validate_module(&source), vec![]);
    let mut destination = Module::new("destination");
    destination.target_info = Some(target());
    let signature = destination
        .add_func_type(FuncTy::unrecorded(vec![], vec![Ty::U32], false))
        .unwrap();
    let mut occupied = Function::new(
        FuncId::new(7),
        "unrelated_existing_item",
        signature,
        BlockId::new(0),
    );
    occupied.linkage = Linkage::External;
    destination.try_add_function(occupied).unwrap();
    destination.types.push(Ty::FnItem(FuncId::new(7)));

    let remap = merge_into(&mut destination, &source, &MergePolicy::EXECUTION_IMAGE).unwrap();
    let first = remap.func(FuncId::new(7)).unwrap();
    let second = remap.func(FuncId::new(19)).unwrap();
    assert_ne!(first, FuncId::new(7), "the colliding source id must move");
    assert_ne!(
        first, second,
        "equal signatures are not equal item identities"
    );
    assert_eq!(destination.types[0], Ty::FnItem(FuncId::new(7)));
    assert_eq!(
        destination.types[remap.ty(trust_ir::TyId::new(0)).unwrap().as_usize()],
        Ty::Tuple(vec![
            Ty::FnItem(first),
            Ty::Ref(Box::new(Ty::FnItem(second))),
            Ty::Func(remap.func_ty(trust_ir::FuncTyId::new(0)).unwrap()),
        ])
    );
    let holder = destination
        .structs
        .iter()
        .find(|s| s.id == remap.struct_(StructId::new(3)).unwrap())
        .unwrap();
    assert_eq!(holder.fields[0].ty, Ty::FnItem(second));
    let entry_id = remap.func(FuncId::new(41)).unwrap();
    let entry = destination.function_by_id(entry_id).unwrap();
    for (node, target) in entry.blocks[0].body.iter().zip([first, second]) {
        assert_eq!(
            node.inst,
            Inst::Const {
                ty: Ty::FnItem(target),
                value: Constant::FnItem(target)
            }
        );
    }
    assert_eq!(validate_module(&destination), vec![]);
    let outcome = Interpreter::with_module(&destination)
        .execute_func(entry_id, vec![])
        .unwrap();
    assert_eq!(
        outcome.returns,
        vec![
            InterpretValue::int(Ty::U32, 7).unwrap(),
            InterpretValue::int(Ty::U32, 19).unwrap()
        ]
    );
}

#[test]
fn fn_item_merge_refuses_dangling_identity_without_mutating_destination() {
    for constant_only in [false, true] {
        let mut source = source();
        if constant_only {
            source.functions[2].blocks[0].body[0].inst = Inst::Const {
                ty: Ty::FnItem(FuncId::new(7)),
                value: Constant::FnItem(FuncId::new(999)),
            };
        } else {
            source.types.push(Ty::FnItem(FuncId::new(999)));
        }
        let mut destination = Module::new("unchanged");
        let before = destination.clone();
        assert!(matches!(
            merge_into(&mut destination, &source, &MergePolicy::EXECUTION_IMAGE),
            Err(MergeError::Dangling {
                table: "functions",
                id: 999
            })
        ));
        assert_eq!(destination, before);
    }
}

fn coalescing_template() -> (Template, ScriptedHost) {
    let mut module: ModuleG<TemplateRef> = ModuleG::new("item-template");
    module.target_info = Some(target());
    let callee_signature = module
        .add_func_type(FuncTyG {
            abi: None,
            params: vec![],
            returns: vec![TyG::U32],
            is_vararg: false,
        })
        .unwrap();
    let body_signature = module
        .add_func_type(FuncTyG {
            abi: None,
            params: vec![],
            returns: vec![
                TyG::FnItem(FuncId::new(19)),
                TyG::Func(callee_signature),
                TyG::FnItem(FuncId::new(29)),
            ],
            is_vararg: false,
        })
        .unwrap();
    let mut body = FunctionG::new(
        FuncId::new(0),
        TEMPLATE_BODY_NAME,
        body_signature,
        BlockId::new(0),
    );
    body.blocks.push(BlockG {
        id: BlockId::new(0),
        params: vec![],
        body: vec![
            InstrNodeG::new(InstG::Const {
                ty: TyG::FnItem(FuncId::new(19)),
                value: ConstantG::FnItem(FuncId::new(19)),
            })
            .with_result(value(0)),
            InstrNodeG::new(InstG::Const {
                ty: TyG::Func(callee_signature),
                value: ConstantG::FnDef(FuncId::new(19)),
            })
            .with_result(value(1)),
            InstrNodeG::new(InstG::Const {
                ty: TyG::FnItem(FuncId::new(29)),
                value: ConstantG::FnItem(FuncId::new(29)),
            })
            .with_result(value(2)),
            InstrNodeG::new(InstG::Return {
                values: vec![value(0), value(1), value(2)],
            }),
        ],
    });
    module.functions.push(body);
    for (id, name) in [
        (7, hole_row_name(HoleId::new(0))),
        (19, "target".into()),
        (29, "other_target".into()),
    ] {
        let mut declaration =
            FunctionG::new(FuncId::new(id), name, callee_signature, BlockId::new(0));
        declaration.linkage = Linkage::External;
        if id != 7 {
            declaration.calling_conv = CallingConv::Rust;
        }
        module.functions.push(declaration);
    }
    module.types.push(TyG::Tuple(vec![
        TyG::FnItem(FuncId::new(19)),
        TyG::Ref(Box::new(TyG::FnItem(FuncId::new(29)))),
    ]));
    module.structs.push(StructDefG {
        id: StructId::new(3),
        name: "StoredItem".into(),
        fields: vec![FieldDefG {
            name: "item".into(),
            ty: TyG::FnItem(FuncId::new(19)),
            offset: None,
        }],
        size: None,
        align: None,
        repr: StructRepr::Rust,
        origin: None,
    });
    let template = Template {
        header: TemplateHeader {
            identity: "fn-item-symbol-coalescing".into(),
            params: vec![TemplateParam::Type],
            holes: vec![HoleDef {
                kind: HoleKind::Callee {
                    decl: FuncId::new(7),
                },
                key: HostKey::new("rust", b"target".to_vec()),
                args: vec![TemplateArg::Type(TyG::Ext(TemplateRef::Param(
                    trust_ir::ParamId::new(0),
                )))],
            }],
        },
        module,
    };
    let host = ScriptedHost {
        arguments: vec![InstArg::Type(Ty::U32)],
        holes: vec![ScriptedAnswer::Answer(HoleAnswer::Callee(
            LinkAnswer::rust("target"),
        ))],
        header: Some(InstanceHeader {
            symbol: "return_items".into(),
            linkage: Linkage::Internal,
            visibility: Visibility::Default,
            calling_conv: CallingConv::Rust,
            attrs: Default::default(),
            display_path: None,
            body_gate: BodyGate::Ungated,
        }),
        ..ScriptedHost::default()
    };
    (template, host)
}

#[test]
fn fn_item_template_coalescing_rewrites_type_and_value_identity_but_keeps_pointer_kind() {
    let (template, mut host) = coalescing_template();
    let output = instantiate(&template, &mut host).unwrap().module;
    assert_eq!(validate_module(&output), vec![]);
    assert_eq!(output.functions.len(), 3);
    assert!(output.function_by_id(FuncId::new(19)).is_none());
    let target = output
        .functions
        .iter()
        .find(|f| f.name == "target")
        .unwrap()
        .id;
    assert_eq!(target, FuncId::new(7));
    assert_eq!(
        output.types[0],
        Ty::Tuple(vec![
            Ty::FnItem(target),
            Ty::Ref(Box::new(Ty::FnItem(FuncId::new(29))))
        ])
    );
    assert_eq!(output.structs[0].fields[0].ty, Ty::FnItem(target));
    let body = output.function_by_id(FuncId::new(0)).unwrap();
    let signature = &output.func_types[body.ty.as_usize()];
    assert_eq!(signature.returns[0], Ty::FnItem(target));
    let pointer_ty = Ty::Func(output.function_by_id(target).unwrap().ty);
    assert_eq!(signature.returns[1], pointer_ty);
    assert_eq!(
        body.blocks[0].body[0].inst,
        Inst::Const {
            ty: Ty::FnItem(target),
            value: Constant::FnItem(target)
        }
    );
    assert_eq!(
        body.blocks[0].body[1].inst,
        Inst::Const {
            ty: pointer_ty,
            value: Constant::FnDef(target)
        }
    );
    assert_eq!(
        body.blocks[0].body[2].inst,
        Inst::Const {
            ty: Ty::FnItem(FuncId::new(29)),
            value: Constant::FnItem(FuncId::new(29))
        }
    );
    let values = Interpreter::with_module(&output)
        .execute_func(body.id, vec![])
        .unwrap()
        .returns;
    assert_eq!(
        values[0],
        InterpretValue {
            ty: Ty::FnItem(target),
            kind: InterpretValueKind::FnItem(target)
        }
    );
    assert_eq!(
        values[2],
        InterpretValue {
            ty: Ty::FnItem(FuncId::new(29)),
            kind: InterpretValueKind::FnItem(FuncId::new(29))
        }
    );
}

#[test]
fn fn_item_template_coalescing_still_refuses_conflicting_target_signatures() {
    let (mut template, mut host) = coalescing_template();
    let incompatible = template
        .module
        .add_func_type(FuncTyG {
            abi: None,
            params: vec![TyG::U8],
            returns: vec![TyG::U32],
            is_vararg: false,
        })
        .unwrap();
    template
        .module
        .functions
        .iter_mut()
        .find(|f| f.id == FuncId::new(19))
        .unwrap()
        .ty = incompatible;
    // Keep the template individually well typed: refusal must come from the
    // two resolved declarations, rather than a stale pointer constant in T6.
    let body_signature = template.module.functions[0].ty;
    template.module.func_types[body_signature.as_usize()].returns[1] = TyG::Func(incompatible);
    if let InstG::Const { ty, .. } = &mut template.module.functions[0].blocks[0].body[1].inst {
        *ty = TyG::Func(incompatible);
    } else {
        panic!("fixture's legacy pointer constant moved");
    }
    assert!(matches!(
        instantiate(&template, &mut host),
        Err(InstantiateError::AnswerConflict { .. })
    ));
}

// Native structural/call-boundary controls; no compiler-proof claim.
mod zero_array_identity {
    use trust_ir::interpret::{
        ArrayValue, InterpretErrorCode, InterpretValue, InterpretValueKind as K, Interpreter,
    };
    use trust_ir::{
        Block, BlockId, Constant, FuncId, FuncTy, Function, Inst, InstrNode, Module, Ty, ValueId,
    };

    fn source(len: u64) -> (Module, Ty, Ty) {
        let mut module = Module::new("fnitem_zero_array_raw_identity");
        let signature = module
            .add_func_type(FuncTy::unrecorded(vec![], vec![Ty::U32], false))
            .unwrap();
        for target in [7, 42] {
            let mut f = Function::new(
                FuncId::new(target),
                format!("item_{target}"),
                signature,
                BlockId::new(0),
            );
            let mut b = Block::new(BlockId::new(0));
            b.body.push(
                InstrNode::new(Inst::Const {
                    ty: Ty::U32,
                    value: Constant::Int(i128::from(target)),
                })
                .with_result(ValueId::new(0)),
            );
            b.body.push(InstrNode::new(Inst::Return {
                values: vec![ValueId::new(0)],
            }));
            f.blocks.push(b);
            module.try_add_function(f).unwrap();
        }
        let first = module.add_type(Ty::FnItem(FuncId::new(7))).unwrap();
        let second = module.add_type(Ty::FnItem(FuncId::new(7))).unwrap();
        assert_ne!(first, second);
        assert_eq!(
            module.types[first.0 as usize],
            module.types[second.0 as usize]
        );
        let left = Ty::Array(first, len);
        let right = Ty::Array(second, len);
        assert_ne!(left, right);
        let signature = module
            .add_func_type(FuncTy::unrecorded(
                vec![left.clone()],
                vec![left.clone()],
                false,
            ))
            .unwrap();
        let mut entry = Function::new(FuncId::new(0), "array_identity", signature, BlockId::new(0));
        let mut block = Block::new(BlockId::new(0));
        block.params.push((ValueId::new(0), left.clone()));
        block.body.push(InstrNode::new(Inst::Return {
            values: vec![ValueId::new(0)],
        }));
        entry.blocks.push(block);
        module.try_add_function(entry).unwrap();
        (module, left, right)
    }
    fn item(id: u32) -> InterpretValue {
        InterpretValue {
            ty: Ty::FnItem(FuncId::new(id)),
            kind: K::FnItem(FuncId::new(id)),
        }
    }
    fn array(ty: &Ty, len: u64, value: InterpretValue) -> InterpretValue {
        InterpretValue {
            ty: ty.clone(),
            kind: K::Array(ArrayValue::splat(value, len)),
        }
    }
    #[test]
    fn structurally_valid_equal_rows_keep_distinct_array_types_and_exact_elements() {
        for len in [0, 1, u64::MAX] {
            let (module, left, right) = source(len);
            // Structural/default validation only: no codegen, certificate or proof grade.
            let errors = trust_ir_build::validate_module(&module);
            assert!(errors.is_empty(), "{errors:#?}");
            for ty in [&left, &right] {
                let layout = module.ty_layout_shape(ty).unwrap();
                assert_eq!((layout.size_bits, layout.align_bits), (0, Some(8)));
            }
            let good = Interpreter::with_module(&module)
                .execute_func(FuncId::new(0), [array(&left, len, item(7))])
                .unwrap();
            assert_eq!(good.host_calls, 0);
            assert_eq!(good.returns[0].ty, left);
            let K::Array(values) = &good.returns[0].kind else {
                panic!("array carrier")
            };
            assert_eq!(values.len(), len);
            if len > 0 {
                assert_eq!(values.get(len - 1).unwrap().kind, K::FnItem(FuncId::new(7)));
            }
            let alias = Interpreter::with_module(&module)
                .execute_func(FuncId::new(0), [array(&right, len, item(7))])
                .unwrap_err();
            assert_eq!(alias.code, InterpretErrorCode::SignatureMismatch);
            // The second raw array type is also structurally valid at its own
            // declared boundary. Equal element rows do not equate the raw TyIds.
            let mut alias_module = module.clone();
            let signature = alias_module.function_by_id(FuncId::new(0)).unwrap().ty;
            alias_module.func_types[signature.0 as usize].params[0] = right.clone();
            alias_module.func_types[signature.0 as usize].returns[0] = right.clone();
            alias_module
                .functions
                .iter_mut()
                .find(|f| f.id == FuncId::new(0))
                .unwrap()
                .blocks[0]
                .params[0]
                .1 = right.clone();
            assert!(trust_ir_build::validate_module(&alias_module).is_empty());
            let own_alias = Interpreter::with_module(&alias_module)
                .execute_func(FuncId::new(0), [array(&right, len, item(7))])
                .unwrap();
            assert_eq!(own_alias.host_calls, 0);
            assert_eq!(own_alias.returns[0].ty, right);
            if len == 0 {
                // A zero-count splat has no held leaf. Its unused constructor
                // argument must not be inspected as an element of the empty value.
                for seed in [
                    item(42),
                    item(99),
                    InterpretValue {
                        ty: Ty::FnItem(FuncId::new(7)),
                        kind: K::FnItem(FuncId::new(42)),
                    },
                ] {
                    let empty = array(&left, 0, seed);
                    let K::Array(values) = &empty.kind else {
                        panic!("empty array")
                    };
                    assert!(values.get(0).is_none());
                    let result = Interpreter::with_module(&module)
                        .execute_func(FuncId::new(0), [empty])
                        .unwrap();
                    let K::Array(values) = &result.returns[0].kind else {
                        panic!("empty array")
                    };
                    assert_eq!(values.len(), 0);
                    assert_eq!(result.host_calls, 0);
                }
            } else {
                // Recursive item validation precedes the outer function signature:
                // a bad held element wins even when the raw array alias also differs.
                let nested_before_alias = Interpreter::with_module(&module)
                    .execute_func(FuncId::new(0), [array(&right, len, item(42))])
                    .unwrap_err();
                assert_eq!(nested_before_alias.code, InterpretErrorCode::TypeError);
                let wrong = Interpreter::with_module(&module)
                    .execute_func(FuncId::new(0), [array(&left, len, item(42))])
                    .unwrap_err();
                assert_eq!(wrong.code, InterpretErrorCode::TypeError);
                let forged = InterpretValue {
                    ty: Ty::FnItem(FuncId::new(7)),
                    kind: K::FnItem(FuncId::new(42)),
                };
                let wrong = Interpreter::with_module(&module)
                    .execute_func(FuncId::new(0), [array(&left, len, forged)])
                    .unwrap_err();
                assert_eq!(wrong.code, InterpretErrorCode::TypeError);
            }
        }
    }
}
