// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use trust_ir::{
    CastOp, Endianness, FuncTy, StructPassingPolicy, TargetInfo, TupleLayoutDescriptor, TyId,
};

fn module(source: Ty) -> Module {
    let mut module = Module::new("typed_pointer");
    module.target_info = Some(TargetInfo {
        triple: "aarch64-unknown-linux-gnu".into(),
        pointer_size: 8,
        endianness: Endianness::Little,
        abi: Some("aapcs64".into()),
        struct_passing: StructPassingPolicy::NativeC,
    });
    let signature = module
        .add_func_type(FuncTy {
            params: vec![source.clone()],
            returns: vec![Ty::Ptr],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut function = Function::new(FuncId::new(13), "address", signature, BlockId::new(21));
    let mut block = Block::new(function.entry);
    block.params.push((ValueId::new(17), source.clone()));
    block.body.push(
        InstrNode::new(Inst::Copy {
            ty: source.clone(),
            operand: ValueId::new(17),
        })
        .with_result(ValueId::new(91)),
    );
    block.body.push(
        InstrNode::new(Inst::Cast {
            op: CastOp::PtrToPtr,
            src_ty: source,
            dst_ty: Ty::Ptr,
            operand: ValueId::new(91),
        })
        .with_result(ValueId::new(103)),
    );
    block.body.push(InstrNode::new(Inst::Return {
        values: vec![ValueId::new(103)],
    }));
    function.blocks.push(block);
    module
        .try_add_function(function)
        .expect("Module::try_add_function: test fixture");
    module
}

fn reflect(module: &Module) -> Result<ReflectedCoreModuleV1<'_>> {
    reflect_core_module_v1(module, &[(FuncId::new(13), 4096)])
}

fn elements(term: &Expr) -> Vec<&Expr> {
    let mut cursor = term;
    let mut values = Vec::new();
    while *cursor.get_app_fn() == c("IRList.cons") {
        let args = cursor.get_app_args();
        values.push(args[1]);
        cursor = args[2];
    }
    assert_eq!(*cursor.get_app_fn(), c("IRList.nil"));
    values
}

fn tuple_module() -> Module {
    let tuple = Ty::Tuple(vec![Ty::U8, Ty::U64]);
    let mut module = module(Ty::RefMut(Box::new(tuple.clone())));
    module.types = vec![Ty::Unit; 5];
    module.types.push(tuple);
    module.tuple_layouts.push(TupleLayoutDescriptor {
        tuple_type: TyId::new(5),
        size: 16,
        align: 8,
        // Physical order differs from logical field order. Never infer it.
        field_offsets: vec![8, 0],
    });
    module
}

#[test]
fn four_thin_pointer_types_preserve_copy_cast_signature_and_layout() {
    for (source, constructor) in [
        (Ty::Ref(Box::new(Ty::U64)), "IRTy.ref_"),
        (Ty::RefMut(Box::new(Ty::U64)), "IRTy.refmut_"),
        (Ty::PtrConst(Box::new(Ty::U64)), "IRTy.rawconst_"),
        (Ty::PtrMut(Box::new(Ty::U64)), "IRTy.rawmut_"),
    ] {
        let module = module(source);
        assert!(crate::validate_module(&module).is_empty());
        let reflected = reflect(&module).unwrap();
        assert!(std::ptr::eq(reflected.module(), &module));
        let ctx = reflected.context_term().get_app_args();
        let ty = app(constructor, [app("IRTy.uint_", [nat(64)])]);
        let signature = elements(ctx[2])[0].get_app_args();
        assert_eq!(elements(signature[1]), [&ty]);
        let functions = elements(ctx[0].get_app_args()[0]);
        let blocks = elements(functions[0].get_app_args()[3]);
        let nodes = elements(blocks[0].get_app_args()[2]);
        assert_eq!(
            nodes[0],
            &app(
                "IRNode.mk",
                [
                    app("IRInst.copy", [ty.clone(), nat(17)]),
                    list("Nat", [nat(91)])
                ]
            )
        );
        assert_eq!(
            nodes[1],
            &app(
                "IRNode.mk",
                [
                    app(
                        "IRInst.cast",
                        [c("IRCastOp.ptrtoptr"), ty.clone(), c("IRTy.ptr_"), nat(91)]
                    ),
                    list("Nat", [nat(103)])
                ]
            )
        );
        assert!(elements(ctx[1]).contains(&&app(
            "IRByteLayoutV1.mk",
            [ty, nat(8), nat(8), list("IRTy", []), list("Nat", [])]
        )));
    }
}

#[test]
fn tuple_pointee_preserves_nominal_descriptor_fields_and_physical_offsets() {
    let module = tuple_module();
    assert!(crate::validate_module(&module).is_empty());
    let reflected = reflect(&module).unwrap();
    let ctx = reflected.context_term().get_app_args();
    let tuple = app("IRTy.tuple_", [nat(5)]);
    let expected = app(
        "IRByteLayoutV1.mk",
        [
            tuple.clone(),
            nat(16),
            nat(8),
            list(
                "IRTy",
                [app("IRTy.uint_", [nat(8)]), app("IRTy.uint_", [nat(64)])],
            ),
            list("Nat", [nat(8), nat(0)]),
        ],
    );
    assert!(elements(ctx[1]).contains(&&expected));
    let signature = elements(ctx[2])[0].get_app_args();
    assert_eq!(elements(signature[1]), [&app("IRTy.refmut_", [tuple])]);
    let mut changed = module.clone();
    changed.tuple_layouts[0].field_offsets = vec![0, 8];
    assert!(crate::validate_module(&changed).is_empty());
    assert_ne!(
        reflected.context_term(),
        reflect(&changed).unwrap().context_term()
    );
}

#[test]
fn tuple_reflection_refuses_missing_ambiguous_and_incoherent_layouts() {
    for mutate in [
        |m: &mut Module| m.tuple_layouts.clear(),
        |m: &mut Module| m.tuple_layouts[0].field_offsets = vec![0, 0],
        |m: &mut Module| m.tuple_layouts[0].field_offsets = vec![0, 1],
        |m: &mut Module| m.tuple_layouts[0].field_offsets = vec![8, 16],
        |m: &mut Module| m.tuple_layouts[0].tuple_type = TyId::new(0),
        |m: &mut Module| m.tuple_layouts.push(m.tuple_layouts[0].clone()),
        |m: &mut Module| m.target_info = None,
        |m: &mut Module| m.target_info.as_mut().unwrap().pointer_size = 4,
    ] {
        let mut module = tuple_module();
        mutate(&mut module);
        assert!(reflect(&module).is_err());
    }
    let mut value = tuple_module();
    let tuple = value.types[5].clone();
    value.func_types[0].params[0] = tuple.clone();
    value.functions[0].blocks[0].params[0].1 = tuple.clone();
    value.functions[0].blocks[0].body = vec![InstrNode::new(Inst::Return {
        values: vec![ValueId::new(17)],
    })];
    value.func_types[0].returns = vec![tuple];
    assert!(crate::validate_module(&value).is_empty());
    assert!(
        reflect(&value)
            .unwrap_err()
            .to_string()
            .contains("not SSA value semantics")
    );
}

#[test]
fn inline_type_preflight_bounds_depth_size_and_resets_between_roots() {
    let mut module = tuple_module();
    let mut ty = Ty::U64;
    for _ in 0..63 {
        ty = Ty::Ref(Box::new(ty));
    }
    module.types = vec![ty.clone(), Ty::U64, ty];
    assert!(type_profile::check(&module, 1024).is_ok());
    module.types[0] = Ty::Ref(Box::new(module.types[0].clone()));
    assert!(
        type_profile::check(&module, 1024)
            .unwrap_err()
            .to_string()
            .contains("depth limit")
    );
    // The full reflection must stop before the validator hashes or clones the
    // over-depth type, even though this module's tuple descriptor is invalid.
    assert!(
        reflect(&module)
            .unwrap_err()
            .to_string()
            .contains("depth limit")
    );
    module.types = vec![Ty::Tuple(vec![Ty::U64; 64])];
    assert!(type_profile::check(&module, 65).is_err());
    assert!(type_profile::check(&module, 1024).is_ok());
    module.types = vec![Ty::Ref(Box::new(Ty::F64))];
    assert!(
        reflect(&module)
            .unwrap_err()
            .to_string()
            .contains("unsupported byte-profile type")
    );
}
