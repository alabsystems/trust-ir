// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Exact authored layout-data controls, not rustc provenance or Rust ABI proof.

use super::*;
use trust_ir::{
    Endianness, FieldDef, FuncTy, StructDef, StructId, StructPassingPolicy, StructRepr, TargetInfo,
};

const EMPTY: StructId = StructId(17);
const NESTED: StructId = StructId(31);
const ARC_SHAPE: StructId = StructId(149);
const REORDERED: StructId = StructId(97);

fn field(ty: Ty, offset: u64) -> FieldDef {
    FieldDef {
        name: "ordinary_field".into(),
        ty,
        offset: Some(offset),
    }
}

fn fixture(ty: Ty) -> Module {
    let mut module = Module::new("authored_rust_layout_data");
    module.target_info = Some(TargetInfo {
        triple: "aarch64-apple-darwin".into(),
        pointer_size: 8,
        endianness: Endianness::Little,
        abi: None,
        struct_passing: StructPassingPolicy::Unclassified,
    });
    // Neither names nor positions are authority; sparse IDs are nominal.
    for (id, size, align, fields) in [
        (
            ARC_SHAPE,
            8,
            8,
            vec![
                field(Ty::Ptr, 0),
                field(Ty::Struct(NESTED), 8),
                field(Ty::Struct(EMPTY), 8),
            ],
        ),
        (
            REORDERED,
            16,
            8,
            vec![
                field(Ty::U8, 8),
                field(Ty::U64, 0),
                field(Ty::Struct(NESTED), 9),
            ],
        ),
        (EMPTY, 0, 1, vec![]),
        (NESTED, 0, 1, vec![field(Ty::Struct(EMPTY), 0)]),
    ] {
        module.structs.push(StructDef {
            id,
            name: format!("nominal_{}", id.index()),
            fields,
            size: Some(size),
            align: Some(align),
            repr: StructRepr::Rust,
            origin: None,
        });
    }
    let signature = module
        .add_func_type(FuncTy {
            params: vec![ty.clone()],
            returns: vec![ty.clone()],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut function = Function::new(FuncId(4001), "thin_leaf", signature, BlockId(29));
    let mut block = Block::new(BlockId(29));
    block.params.push((ValueId(0), ty));
    block.body.push(InstrNode::new(Inst::Return {
        values: vec![ValueId(0)],
    }));
    function.blocks.push(block);
    module.functions.push(function);
    module
}

fn reflect(module: &Module) -> Result<ReflectedCoreModuleV1<'_>> {
    reflect_core_module_v1(module, &[(FuncId(4001), 4096)])
}
fn elements(term: &Expr) -> Vec<Expr> {
    let mut cursor = term;
    let mut result = Vec::new();
    while *cursor.get_app_fn() == c("IRList.cons") {
        let args = cursor.get_app_args();
        result.push(args[1].clone());
        cursor = args[2];
    }
    assert_eq!(*cursor.get_app_fn(), c("IRList.nil"));
    result
}
fn nominal(id: StructId) -> Expr {
    app("IRTy.struct_", [nat(u64::from(id.index()))])
}
fn row(id: StructId, size: u64, align: u64, fields: Vec<Expr>, offsets: &[u64]) -> Expr {
    app(
        "IRByteLayoutV1.mk",
        [
            nominal(id),
            nat(size),
            nat(align),
            list("IRTy", fields),
            list("Nat", offsets.iter().copied().map(nat)),
        ],
    )
}
fn refused_unchanged(module: &Module) -> CoreReflectionError {
    let original = module.clone();
    let error = reflect(module).unwrap_err();
    assert_eq!(module, &original);
    error
}

#[test]
fn explicit_rust_layouts_keep_sparse_ids_ordered_fields_and_zst_positions() {
    let module = fixture(Ty::PtrConst(Box::new(Ty::Struct(ARC_SHAPE))));
    let original = module.clone();
    assert!(crate::validate_module(&module).is_empty());
    let reflected = reflect(&module).unwrap();
    assert!(std::ptr::eq(reflected.module(), &module));
    let layouts = elements(reflected.context_term().get_app_args()[1]);
    for expected in [
        row(EMPTY, 0, 1, vec![], &[]),
        row(NESTED, 0, 1, vec![nominal(EMPTY)], &[0]),
        row(
            ARC_SHAPE,
            8,
            8,
            vec![c("IRTy.ptr_"), nominal(NESTED), nominal(EMPTY)],
            &[0, 8, 8],
        ),
        row(
            REORDERED,
            16,
            8,
            vec![
                app("IRTy.uint_", [nat(8)]),
                app("IRTy.uint_", [nat(64)]),
                nominal(NESTED),
            ],
            &[8, 0, 9],
        ),
    ] {
        assert!(
            layouts.contains(&expected),
            "missing exact descriptor {expected:?}"
        );
    }
    assert_eq!(module, original);
    assert!(module.structs.iter().all(|s| s.repr == StructRepr::Rust));
    assert_eq!(
        module.target_info.as_ref().unwrap().struct_passing,
        StructPassingPolicy::Unclassified
    );
    assert!(module.target_info.as_ref().unwrap().abi.is_none());
    let mut renamed = module.clone();
    for definition in &mut renamed.structs {
        definition.name = "Arc_PhantomData_Global_is_not_authority".into();
    }
    assert_eq!(
        reflect(&renamed).unwrap().context_term(),
        reflected.context_term()
    );
    let mut shifted = module.clone();
    shifted.structs[1].fields[2].offset = Some(16);
    assert_ne!(
        reflect(&shifted).unwrap().context_term(),
        reflected.context_term(),
        "even legal ZST placement remains data"
    );
}

#[test]
fn every_rust_descriptor_requires_size_align_and_all_offsets_even_unused_zsts() {
    let baseline = fixture(Ty::Ptr);
    for index in 0..baseline.structs.len() {
        for size in [false, true] {
            let mut module = baseline.clone();
            if size {
                module.structs[index].size = None;
            } else {
                module.structs[index].align = None;
            }
            refused_unchanged(&module);
        }
        for field in 0..baseline.structs[index].fields.len() {
            let mut module = baseline.clone();
            let ty = module.structs[index].fields[field].ty.clone();
            module.structs[index].fields[field].offset = None;
            let error = refused_unchanged(&module);
            if module.ty_layout_shape(&ty).unwrap().size_bits == 0 {
                // The common helper deliberately canonicalizes absent ZST
                // offsets to zero. This stricter profile must reject first.
                assert!(
                    module
                        .ty_layout_shape(&Ty::Struct(module.structs[index].id))
                        .is_ok()
                );
                assert!(error.to_string().contains("every field offset"), "{error}");
            }
        }
    }
}

#[test]
fn rust_shape_checks_still_reject_overlap_bad_alignment_bounds_and_overflow() {
    let baseline = fixture(Ty::Ptr);
    for mutate in [
        |m: &mut Module| m.structs[1].fields[0].offset = Some(0), // overlap U64
        |m: &mut Module| m.structs[1].fields[1].offset = Some(1), // misaligned
        |m: &mut Module| m.structs[1].align = Some(3),
        |m: &mut Module| m.structs[1].align = Some(4), // below field alignment
        |m: &mut Module| m.structs[0].size = Some(4),
        |m: &mut Module| m.structs[0].fields[1].offset = Some(9), // ZST out of bounds
        |m: &mut Module| m.structs[2].size = Some(u64::MAX),
        |m: &mut Module| m.structs[2].align = Some(1 << 63),
    ] {
        let mut changed = baseline.clone();
        mutate(&mut changed);
        refused_unchanged(&changed);
    }
}

#[test]
fn rust_layout_admission_does_not_admit_packed_cycles_enums_or_unresolved_fields() {
    let baseline = fixture(Ty::Ptr);
    let mut packed = baseline.clone();
    packed.structs[2].repr = StructRepr::Packed(1);
    assert!(packed.ty_layout_shape(&Ty::Struct(EMPTY)).is_ok());
    assert!(
        refused_unchanged(&packed)
            .to_string()
            .contains("packed nominal")
    );
    for ty in [
        Ty::Struct(ARC_SHAPE),
        Ty::F64,
        Ty::FatPtr(trust_ir::FatPtrKind::Slice(trust_ir::TyId(999))),
        Ty::Enum(trust_ir::EnumId(71)),
    ] {
        let mut changed = baseline.clone();
        changed.structs[0].fields[0].ty = ty;
        refused_unchanged(&changed);
    }
    let mut indirect_cycle = baseline;
    indirect_cycle.structs[2]
        .fields
        .push(field(Ty::Struct(NESTED), 0));
    refused_unchanged(&indirect_cycle);
}

#[test]
fn rust_typed_thin_leaves_do_not_gain_by_value_abi_or_aggregate_memory_admission() {
    for ty in [
        Ty::Ptr,
        Ty::Ref(Box::new(Ty::Struct(ARC_SHAPE))),
        Ty::RefMut(Box::new(Ty::Struct(ARC_SHAPE))),
        Ty::PtrConst(Box::new(Ty::Struct(ARC_SHAPE))),
        Ty::PtrMut(Box::new(Ty::Struct(ARC_SHAPE))),
    ] {
        let module = fixture(ty);
        let before = module.clone();
        assert!(reflect(&module).is_ok());
        assert_eq!(module, before);
    }
    for result in [false, true] {
        let mut module = fixture(Ty::Ptr);
        module.func_types.push(FuncTy {
            params: if result {
                vec![]
            } else {
                vec![Ty::Struct(ARC_SHAPE)]
            },
            returns: if result {
                vec![Ty::Struct(ARC_SHAPE)]
            } else {
                vec![]
            },
            abi: None,
            is_vararg: false,
        });
        assert!(
            refused_unchanged(&module)
                .to_string()
                .contains("nonvariadic scalar/thin-pointer")
        );
    }
    let mut loaded = fixture(Ty::Ptr);
    loaded.functions[0].blocks[0].body.insert(
        0,
        InstrNode::new(Inst::Load {
            ty: Ty::Struct(ARC_SHAPE),
            ptr: ValueId(0),
            volatile: false,
            align: Some(8),
        })
        .with_result(ValueId(1)),
    );
    assert!(crate::validate_module(&loaded).is_empty());
    assert!(
        refused_unchanged(&loaded)
            .to_string()
            .contains("aggregate memory")
    );
    // Separate, explicitly authored NativeC input fixture: the store refusal
    // must not be masked by a prior unsupported load or Unclassified ABI gate.
    let mut stored = fixture(Ty::Ptr);
    stored.target_info.as_mut().unwrap().struct_passing = StructPassingPolicy::NativeC;
    stored.func_types[0].params.push(Ty::Struct(ARC_SHAPE));
    stored.functions[0].blocks[0]
        .params
        .push((ValueId(1), Ty::Struct(ARC_SHAPE)));
    stored.functions[0].blocks[0].body.insert(
        0,
        InstrNode::new(Inst::Store {
            ty: Ty::Struct(ARC_SHAPE),
            ptr: ValueId(0),
            value: ValueId(1),
            volatile: false,
            align: Some(8),
        }),
    );
    assert!(crate::validate_module(&stored).is_empty());
    assert!(
        refused_unchanged(&stored)
            .to_string()
            .contains("aggregate memory")
    );
}

#[test]
fn rust_alloca_and_gep_keep_nominal_pointee_and_exact_descriptor() {
    let mut module = fixture(Ty::Ptr);
    module.functions[0].blocks[0].body = vec![
        InstrNode::new(Inst::Alloca {
            ty: Ty::Struct(ARC_SHAPE),
            count: None,
            align: Some(8),
        })
        .with_result(ValueId(1)),
        InstrNode::new(Inst::Const {
            ty: Ty::I64,
            value: Constant::Int(1),
        })
        .with_result(ValueId(2)),
        InstrNode::new(Inst::GEP {
            pointee_ty: Ty::Struct(ARC_SHAPE),
            base: ValueId(1),
            indices: vec![ValueId(2)],
            inbounds: false,
        })
        .with_result(ValueId(3)),
        InstrNode::new(Inst::Return {
            values: vec![ValueId(3)],
        }),
    ];
    assert!(crate::validate_module(&module).is_empty());
    let reflected = reflect(&module).unwrap();
    let context = reflected.context_term().get_app_args();
    let functions = elements(context[0].get_app_args()[0]);
    let blocks = elements(functions[0].get_app_args()[3]);
    let nodes = elements(blocks[0].get_app_args()[2]);
    assert_eq!(
        nodes[0],
        app(
            "IRNode.mk",
            [
                app(
                    "IRInst.alloca",
                    [nominal(ARC_SHAPE), app("IROption.none", [c("Nat")])]
                ),
                list("Nat", [nat(1)])
            ]
        )
    );
    assert_eq!(
        nodes[2],
        app(
            "IRNode.mk",
            [
                app(
                    "IRInst.gep",
                    [
                        nominal(ARC_SHAPE),
                        nat(1),
                        list("Nat", [nat(2)]),
                        boolean(false)
                    ]
                ),
                list("Nat", [nat(3)])
            ]
        )
    );
    let sites = elements(context[4]);
    assert_eq!(sites[0].get_app_args()[3], &nat(8));
    assert!(elements(context[1]).contains(&row(
        ARC_SHAPE,
        8,
        8,
        vec![c("IRTy.ptr_"), nominal(NESTED), nominal(EMPTY)],
        &[0, 8, 8]
    )));
}

#[test]
fn existing_c_and_transparent_layout_rules_are_not_strengthened_or_flattened() {
    let mut module = fixture(Ty::Ptr);
    module.structs[0].repr = StructRepr::Transparent;
    assert!(reflect(&module).is_ok());
    module.structs[3].repr = StructRepr::C;
    module.structs[3].fields[0].offset = None;
    // The existing C lane still accepts shared-helper ZST canonicalization;
    // exact-offset strictness added here is deliberately Rust-only.
    let reflected = reflect(&module).unwrap();
    assert!(
        elements(reflected.context_term().get_app_args()[1]).contains(&row(
            NESTED,
            0,
            1,
            vec![nominal(EMPTY)],
            &[0]
        ))
    );
    assert_eq!(reflected.module().structs[0].repr, StructRepr::Transparent);
    assert_eq!(reflected.module().structs[3].fields[0].offset, None);
}
