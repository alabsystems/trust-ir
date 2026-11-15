// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Data-reflection admission controls, not source/native/atomic safety proofs.

use super::*;
use trust_ir::{
    ArgExt, Endianness, FieldDef, FuncTy, ParamAttrs, PassMode, StructDef, StructId,
    StructPassingPolicy, StructRepr, TargetInfo, TyId,
};

fn leaf(ty: Ty) -> Module {
    let mut module = Module::new("unclassified_leaf");
    module.target_info = Some(TargetInfo {
        triple: "arm64-apple-macosx".into(),
        pointer_size: 8,
        endianness: Endianness::Little,
        abi: None,
        struct_passing: StructPassingPolicy::Unclassified,
    });
    let signature = module
        .add_func_type(FuncTy {
            params: vec![ty.clone()],
            returns: vec![ty.clone()],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut function = Function::new(FuncId(0), "leaf", signature, BlockId(0));
    let mut block = Block::new(BlockId(0));
    block.params.push((ValueId(0), ty));
    block.body.push(InstrNode::new(Inst::Return {
        values: vec![ValueId(0)],
    }));
    function.blocks.push(block);
    module.functions.push(function);
    module
}

fn add_nominal_layouts(module: &mut Module) {
    // Sparse nominal IDs deliberately differ from positions in the table.
    // These mirror the measured Align8 / UnsafeCell / Atomic layout shape;
    // names themselves confer no recognition or authority.
    for (id, name, field, ty, repr) in [
        (17, "carrier", "0", Ty::U64, StructRepr::C),
        (
            31,
            "cell",
            "value",
            Ty::Struct(StructId(17)),
            StructRepr::Transparent,
        ),
        (49, "outer", "v", Ty::Struct(StructId(31)), StructRepr::C),
    ] {
        module.structs.push(StructDef {
            id: StructId(id),
            name: name.into(),
            fields: vec![FieldDef {
                name: field.into(),
                ty,
                offset: Some(0),
            }],
            size: Some(8),
            align: Some(8),
            repr,
            origin: None,
        });
    }
}

fn gep_leaf() -> Module {
    let mut module = leaf(Ty::Ptr);
    add_nominal_layouts(&mut module);
    let block = &mut module.functions[0].blocks[0];
    block.body = vec![
        InstrNode::new(Inst::Const {
            ty: Ty::I64,
            value: Constant::Int(0),
        })
        .with_result(ValueId(1)),
        InstrNode::new(Inst::GEP {
            pointee_ty: Ty::Struct(StructId(31)),
            base: ValueId(0),
            indices: vec![ValueId(1)],
            inbounds: false,
        })
        .with_result(ValueId(2)),
        InstrNode::new(Inst::Return {
            values: vec![ValueId(2)],
        }),
    ];
    module
}

fn reflect(module: &Module) -> Result<ReflectedCoreModuleV1<'_>> {
    let addresses = module
        .functions
        .iter()
        .map(|function| (function.id, 4096 + u64::from(function.id.index()) * 16))
        .collect::<Vec<_>>();
    reflect_core_module_v1(module, &addresses)
}

fn elements(term: &Expr) -> Vec<&Expr> {
    let mut cursor = term;
    let mut result = Vec::new();
    while *cursor.get_app_fn() == c("IRList.cons") {
        let args = cursor.get_app_args();
        result.push(args[1]);
        cursor = args[2];
    }
    assert_eq!(*cursor.get_app_fn(), c("IRList.nil"));
    result
}

#[test]
fn unclassified_scalar_and_thin_pointer_leaves_keep_exact_module_identity() {
    for ty in [
        Ty::Bool,
        Ty::I8,
        Ty::I16,
        Ty::I32,
        Ty::I64,
        Ty::I128,
        Ty::U8,
        Ty::U16,
        Ty::U32,
        Ty::U64,
        Ty::U128,
        Ty::Usize,
        Ty::Unit,
        Ty::Ptr,
        Ty::Ref(Box::new(Ty::Struct(StructId(31)))),
        Ty::RefMut(Box::new(Ty::Struct(StructId(31)))),
        Ty::PtrConst(Box::new(Ty::Struct(StructId(31)))),
        Ty::PtrMut(Box::new(Ty::Struct(StructId(31)))),
    ] {
        let mut module = leaf(ty.clone());
        add_nominal_layouts(&mut module);
        let before = module.clone();
        assert!(crate::validate_module(&module).is_empty(), "{ty:?}");
        let reflected = reflect(&module).expect("scalar/thin-pointer leaf");
        assert!(std::ptr::eq(reflected.module(), &module));
        assert_eq!(module, before);
        assert_eq!(reflected.module().func_types[0].params, [ty]);
        assert_eq!(
            reflected
                .module()
                .target_info
                .as_ref()
                .unwrap()
                .struct_passing,
            StructPassingPolicy::Unclassified
        );
        assert!(
            reflected
                .module()
                .target_info
                .as_ref()
                .unwrap()
                .abi
                .is_none()
        );
    }
}

#[test]
fn transparent_gep_reflects_nominal_ids_and_checked_layout_without_flattening() {
    let module = gep_leaf();
    assert!(crate::validate_module(&module).is_empty());
    let reflected = reflect(&module).unwrap();
    let ctx = reflected.context_term().get_app_args();
    let layouts = elements(ctx[1]);
    for (id, field) in [
        (17, app("IRTy.uint_", [nat(64)])),
        (31, app("IRTy.struct_", [nat(17)])),
        (49, app("IRTy.struct_", [nat(31)])),
    ] {
        assert!(layouts.contains(&&app(
            "IRByteLayoutV1.mk",
            [
                app("IRTy.struct_", [nat(id)]),
                nat(8),
                nat(8),
                list("IRTy", [field]),
                list("Nat", [nat(0)]),
            ]
        )));
    }
    let functions = elements(ctx[0].get_app_args()[0]);
    let blocks = elements(functions[0].get_app_args()[3]);
    let nodes = elements(blocks[0].get_app_args()[2]);
    assert_eq!(
        nodes[1],
        &app(
            "IRNode.mk",
            [
                app(
                    "IRInst.gep",
                    [
                        app("IRTy.struct_", [nat(31)]),
                        nat(0),
                        list("Nat", [nat(1)]),
                        boolean(false)
                    ]
                ),
                list("Nat", [nat(2)]),
            ]
        )
    );
    // Classification does not alter this leaf's data model. The original
    // borrowed module nevertheless retains its original, distinct policy.
    let mut native = module.clone();
    native.target_info.as_mut().unwrap().struct_passing = StructPassingPolicy::NativeC;
    assert_eq!(
        reflected.context_term(),
        reflect(&native).unwrap().context_term()
    );
    assert_ne!(reflected.module(), &native);
}

#[test]
fn unused_aggregate_and_variadic_signatures_cannot_bypass_leaf_check() {
    for aggregate in [
        Ty::Struct(StructId(31)),
        Ty::Tuple(vec![Ty::U64]),
        Ty::Array(TyId(0), 1),
    ] {
        for in_return in [false, true] {
            let mut module = gep_leaf();
            module.types.push(Ty::U64);
            module.func_types.push(FuncTy {
                params: if in_return {
                    vec![]
                } else {
                    vec![aggregate.clone()]
                },
                returns: if in_return {
                    vec![aggregate.clone()]
                } else {
                    vec![]
                },
                abi: None,
                is_vararg: false,
            });
            let error = reflect(&module).unwrap_err();
            assert!(
                error
                    .to_string()
                    .contains("nonvariadic scalar/thin-pointer"),
                "{error}"
            );
        }
    }
    let mut module = gep_leaf();
    module.func_types.push(FuncTy {
        params: vec![],
        returns: vec![],
        abi: None,
        is_vararg: true,
    });
    assert!(
        reflect(&module)
            .unwrap_err()
            .to_string()
            .contains("nonvariadic scalar/thin-pointer")
    );
}

#[test]
fn function_pointer_signature_cannot_hide_aggregate_signature() {
    let mut module = gep_leaf();
    let signature = module
        .add_func_type(FuncTy {
            params: vec![Ty::U64],
            returns: vec![Ty::U64],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    module.func_types.push(FuncTy {
        params: vec![Ty::Func(signature)],
        returns: vec![],
        abi: None,
        is_vararg: false,
    });
    assert!(
        reflect(&module).is_ok(),
        "unused thin function pointer is explicit data"
    );
    module.func_types[signature.index() as usize].params = vec![Ty::Struct(StructId(31))];
    assert!(
        reflect(&module)
            .unwrap_err()
            .to_string()
            .contains("nonvariadic scalar/thin-pointer")
    );
}

#[test]
fn direct_indirect_calls_and_unused_declarations_still_require_classification() {
    for indirect in [false, true] {
        let mut module = leaf(Ty::Ptr);
        let signature = module.functions[0].ty;
        let body = &mut module.functions[0].blocks[0].body;
        let call = if indirect {
            body.insert(
                0,
                InstrNode::new(Inst::Const {
                    ty: Ty::Func(signature),
                    value: Constant::FnDef(FuncId(0)),
                })
                .with_result(ValueId(1)),
            );
            Inst::CallIndirect {
                callee: ValueId(1),
                sig: signature,
                args: vec![ValueId(0)],
                calling_conv: CallingConv::C,
            }
        } else {
            Inst::Call {
                callee: FuncId(0),
                args: vec![ValueId(0)],
            }
        };
        body.insert(body.len() - 1, InstrNode::new(call).with_result(ValueId(2)));
        assert!(crate::validate_module(&module).is_empty());
        assert!(
            reflect(&module)
                .unwrap_err()
                .to_string()
                .contains("cannot contain calls")
        );
        module.target_info.as_mut().unwrap().struct_passing = StructPassingPolicy::NativeC;
        assert!(
            reflect(&module).is_ok(),
            "existing NativeC call lane retained"
        );
    }
    let mut module = leaf(Ty::Ptr);
    module.functions.push(Function::new(
        FuncId(3),
        "unused_import",
        module.functions[0].ty,
        BlockId(0),
    ));
    assert!(crate::validate_module(&module).is_empty());
    assert!(
        reflect(&module)
            .unwrap_err()
            .to_string()
            .contains("cannot contain declarations")
    );
    module.target_info.as_mut().unwrap().struct_passing = StructPassingPolicy::NativeC;
    assert!(
        reflect(&module).is_ok(),
        "existing NativeC declaration lane retained"
    );

    let mut module = leaf(Ty::Ptr);
    let mut unused = module.functions[0].clone();
    unused.id = FuncId(3);
    unused.name = "unused_calling_body".into();
    unused.blocks[0].body.insert(
        0,
        InstrNode::new(Inst::Call {
            callee: FuncId(0),
            args: vec![ValueId(0)],
        })
        .with_result(ValueId(1)),
    );
    module.functions.push(unused);
    assert!(crate::validate_module(&module).is_empty());
    assert!(
        reflect(&module)
            .unwrap_err()
            .to_string()
            .contains("cannot contain calls"),
        "an uncalled function still belongs to the complete module"
    );
}

#[test]
fn unclassified_leaf_refuses_opaque_assembly_and_unused_imports() {
    let baseline = leaf(Ty::Ptr);
    assert!(reflect(&baseline).is_ok());
    let mut assembly = baseline.clone();
    assembly
        .global_asm
        .push("opaque external implementation".into());
    assert!(
        reflect(&assembly)
            .unwrap_err()
            .to_string()
            .contains("assembly or imports")
    );
    let mut imported = baseline.clone();
    imported.imports.push(trust_ir::ModuleImport::new(
        "unused_dependency",
        trust_ir::proof::ProofDigest::sha256([7; 32]),
    ));
    assert!(
        reflect(&imported)
            .unwrap_err()
            .to_string()
            .contains("assembly or imports")
    );
}

#[test]
fn unclassified_leaf_does_not_erase_abi_or_proof_annotations() {
    for attrs in [
        ParamAttrs {
            byval: true,
            ..Default::default()
        },
        ParamAttrs {
            sret: true,
            ..Default::default()
        },
        ParamAttrs {
            pass: Some(PassMode::Direct),
            ..Default::default()
        },
        ParamAttrs {
            ext: ArgExt::ZeroExt,
            ..Default::default()
        },
    ] {
        let mut module = leaf(Ty::Ptr);
        module.functions[0].attrs.params.push(attrs.clone());
        assert!(
            reflect(&module)
                .unwrap_err()
                .to_string()
                .contains("function claims")
        );
        module.functions[0].attrs.params.clear();
        module.functions[0].attrs.ret = attrs;
        assert!(
            reflect(&module)
                .unwrap_err()
                .to_string()
                .contains("function claims")
        );
    }
    let mut module = leaf(Ty::Ptr);
    module.functions[0]
        .proofs
        .push(trust_ir::ProofAnnotation::Pure);
    assert!(
        reflect(&module)
            .unwrap_err()
            .to_string()
            .contains("function claims")
    );
    module.functions[0].proofs.clear();
    module.functions[0].blocks[0].body[0]
        .proofs
        .push(trust_ir::ProofAnnotation::Pure);
    assert!(
        reflect(&module)
            .unwrap_err()
            .to_string()
            .contains("instruction annotation")
    );
}

#[test]
fn unclassified_leaf_retains_target_and_unsupported_type_refusals() {
    for mutate in [
        |m: &mut Module| m.target_info = None,
        |m: &mut Module| m.target_info.as_mut().unwrap().pointer_size = 4,
        |m: &mut Module| m.target_info.as_mut().unwrap().endianness = Endianness::Big,
        |m: &mut Module| m.target_info.as_mut().unwrap().triple = "mystery-target".into(),
        |m: &mut Module| {
            m.target_info.as_mut().unwrap().struct_passing = StructPassingPolicy::AlwaysMemory
        },
    ] {
        let mut module = leaf(Ty::Ptr);
        mutate(&mut module);
        assert!(reflect(&module).is_err());
    }
    for ty in [Ty::Isize, Ty::F64] {
        let mut module = gep_leaf();
        module.types.push(ty);
        assert!(
            reflect(&module)
                .unwrap_err()
                .to_string()
                .contains("unsupported byte-profile type")
        );
    }
}

#[test]
fn malformed_transparent_and_unmodeled_struct_representations_stay_refused() {
    for mutate in [
        |m: &mut Module| m.structs[1].size = Some(16),
        |m: &mut Module| {
            m.structs[1].align = Some(16);
            m.structs[1].size = Some(16);
        },
        |m: &mut Module| {
            m.structs[1].fields[0].offset = Some(8);
            m.structs[1].size = Some(16);
        },
        |m: &mut Module| m.structs[1].fields[0].offset = None,
        |m: &mut Module| {
            m.structs[1].fields.push(FieldDef {
                name: "second".into(),
                ty: Ty::U64,
                offset: Some(8),
            });
            m.structs[1].size = Some(16);
        },
    ] {
        let mut module = gep_leaf();
        mutate(&mut module);
        assert!(module.ty_layout_shape(&Ty::Struct(StructId(31))).is_err());
        assert!(reflect(&module).is_err());
    }
    for (repr, admitted) in [
        (StructRepr::Rust, true),
        (StructRepr::Packed(1), false),
        (StructRepr::Packed(8), false),
    ] {
        let mut module = gep_leaf();
        module.structs[1].repr = repr;
        assert_eq!(reflect(&module).is_ok(), admitted, "{repr:?}");
    }
}
