// Copyright 2026 Andrew Yates | SPDX-License-Identifier: Apache-2.0

//! Actual borrowed-module/profile controls, not checked execution authority.

use super::*;
use trust_ir::{
    Endianness, FieldDef, FuncTy, StructDef, StructId, StructPassingPolicy, StructRepr, TargetInfo,
};

const FUNCTION: FuncId = FuncId(7);
const BLOCK: BlockId = BlockId(17);
const BASE: ValueId = ValueId(19);
const INDEX: ValueId = ValueId(31);
const COUNT: ValueId = ValueId(37);
const AGGREGATE: ValueId = ValueId(41);
const RECORD: StructId = StructId(13);

fn fixture(index_ty: Ty, count_ty: Ty) -> Module {
    let mut module = Module::new("original_nominal_gep");
    module.target_info = Some(TargetInfo {
        triple: "aarch64-apple-darwin".into(),
        pointer_size: 8,
        endianness: Endianness::Little,
        abi: Some("aapcs64".into()),
        struct_passing: StructPassingPolicy::NativeC,
    });
    module.structs.push(StructDef {
        id: RECORD,
        name: "one_byte".into(),
        fields: vec![FieldDef {
            name: "value".into(),
            ty: Ty::U8,
            offset: Some(0),
        }],
        size: Some(1),
        align: Some(1),
        repr: StructRepr::C,
        origin: None,
    });
    let signature = module
        .add_func_type(FuncTy {
            abi: None,
            params: vec![
                Ty::Ptr,
                index_ty.clone(),
                count_ty.clone(),
                Ty::Struct(RECORD),
            ],
            returns: vec![Ty::Ptr],
            is_vararg: false,
        })
        .unwrap();
    let mut function = Function::new(FUNCTION, "original", signature, BLOCK);
    let mut block = Block::new(BLOCK);
    block.params = vec![
        (BASE, Ty::Ptr),
        (INDEX, index_ty),
        (COUNT, count_ty),
        (AGGREGATE, Ty::Struct(RECORD)),
    ];
    block.body = vec![
        InstrNode::new(Inst::Alloca {
            ty: Ty::U8,
            count: Some(COUNT),
            align: Some(8),
        })
        .with_result(ValueId(43)),
        InstrNode::new(Inst::GEP {
            pointee_ty: Ty::U8,
            base: BASE,
            indices: vec![INDEX],
            inbounds: false,
        })
        .with_result(ValueId(59)),
        InstrNode::new(Inst::ExtractField {
            ty: Ty::U8,
            aggregate: AGGREGATE,
            field: 0,
        })
        .with_result(ValueId(61)),
        InstrNode::new(Inst::Return {
            values: vec![ValueId(59)],
        }),
    ];
    function.blocks.push(block);
    module.functions.push(function);
    module
}

fn reflect(
    module: &Module,
    profile: CoreMemoryIndexProfileV1,
) -> Result<ReflectedCoreModuleV1<'_>> {
    reflect_core_module_v1_with_memory_profile(module, &[(FUNCTION, 4096)], profile)
}

fn elements(term: &Expr) -> Vec<&Expr> {
    let mut cursor = term;
    let mut values = Vec::new();
    while cursor.get_app_fn() == &c("IRList.cons") {
        let fields = cursor.get_app_args();
        assert_eq!(fields.len(), 3);
        values.push(fields[1]);
        cursor = fields[2];
    }
    assert_eq!(cursor.get_app_fn(), &c("IRList.nil"));
    values
}

fn sites<'a>(reflected: &'a ReflectedCoreModuleV1<'_>) -> Vec<&'a Expr> {
    elements(reflected.context_term().get_app_args()[4])
}

fn nominal(ty: &Ty) -> Expr {
    let (signed, width) = match ty {
        Ty::I8 => (true, 8),
        Ty::U8 => (false, 8),
        Ty::I16 => (true, 16),
        Ty::U16 => (false, 16),
        Ty::I32 => (true, 32),
        Ty::U32 => (false, 32),
        Ty::I64 => (true, 64),
        Ty::U64 => (false, 64),
        _ => panic!("explicit nominal test type"),
    };
    app(
        if signed { "IRTy.int_" } else { "IRTy.uint_" },
        [nat(width)],
    )
}

fn row(id: ValueId, ty: Expr) -> Expr {
    app("IRByteOperandV1.mk", [nat(id.0.into()), ty])
}

#[test]
fn typed_integer_gep_profile_retains_full_nominal_matrix_original_ids_and_borrowed_source() {
    for index_ty in [
        Ty::I8,
        Ty::U8,
        Ty::I16,
        Ty::U16,
        Ty::I32,
        Ty::U32,
        Ty::I64,
        Ty::U64,
    ] {
        for count_ty in [Ty::I64, Ty::U64] {
            let module = fixture(index_ty.clone(), count_ty.clone());
            assert!(crate::validate_module(&module).is_empty());
            let original = module.clone();
            let reflected =
                reflect(&module, CoreMemoryIndexProfileV1::TypedIntegerGepBoundedV1).unwrap();
            assert!(std::ptr::eq(reflected.module(), &module));
            assert!(std::ptr::eq(
                reflected.node(FUNCTION, BLOCK, 1).unwrap(),
                &module.functions[0].blocks[0].body[1]
            ));
            assert_eq!(module, original);
            let sites = sites(&reflected);
            assert_eq!(sites[1].get_app_fn(), &c("IRByteSiteV1.mki"));
            assert_eq!(
                sites[1].get_app_args()[6],
                &list("IRByteOperandV1", [row(INDEX, nominal(&index_ty))])
            );
            assert_eq!(sites[0].get_app_fn(), &c("IRByteSiteV1.mkt"));
            assert_eq!(
                sites[0].get_app_args()[6],
                &list("IRByteOperandV1", [row(COUNT, nominal(&count_ty))])
            );
            assert_eq!(sites[2].get_app_fn(), &c("IRByteSiteV1.mkt"));
            assert_eq!(
                sites[2].get_app_args()[6],
                &list(
                    "IRByteOperandV1",
                    [row(AGGREGATE, app("IRTy.struct_", [nat(RECORD.0.into())]))]
                )
            );
            assert_eq!(sites[3].get_app_fn(), &c("IRByteSiteV1.mk"));
        }
    }
}

#[test]
fn typed_integer_gep_profile_keeps_strict_and_typed64_contexts_and_allocation_field_denotations() {
    for index_ty in [Ty::I64, Ty::U64] {
        let module = fixture(index_ty.clone(), Ty::I64);
        let old = reflect(&module, CoreMemoryIndexProfileV1::TypedI64U64BoundedV1).unwrap();
        let new = reflect(&module, CoreMemoryIndexProfileV1::TypedIntegerGepBoundedV1).unwrap();
        assert_eq!(
            old.context_term().get_app_args()[..4],
            new.context_term().get_app_args()[..4]
        );
        let old_sites = sites(&old);
        let new_sites = sites(&new);
        assert_eq!(old_sites[1].get_app_fn(), &c("IRByteSiteV1.mkt"));
        assert_eq!(new_sites[1].get_app_fn(), &c("IRByteSiteV1.mki"));
        assert_eq!(old_sites[1].get_app_args(), new_sites[1].get_app_args());
        for pc in [0, 2, 3] {
            assert_eq!(old_sites[pc], new_sites[pc]);
        }
        if index_ty == Ty::I64 {
            let strict = reflect(&module, CoreMemoryIndexProfileV1::StrictI64).unwrap();
            let default = reflect_core_module_v1(&module, &[(FUNCTION, 4096)]).unwrap();
            assert_eq!(strict.context_term(), default.context_term());
            assert_eq!(sites(&strict)[1].get_app_fn(), &c("IRByteSiteV1.mk"));
        } else {
            assert!(reflect_core_module_v1(&module, &[(FUNCTION, 4096)]).is_err());
        }
    }
    for narrow in [Ty::I8, Ty::U8, Ty::I16, Ty::U16, Ty::I32, Ty::U32] {
        let module = fixture(narrow, Ty::I64);
        assert!(reflect(&module, CoreMemoryIndexProfileV1::StrictI64).is_err());
        assert!(reflect(&module, CoreMemoryIndexProfileV1::TypedI64U64BoundedV1).is_err());
    }
}

#[test]
fn typed_integer_gep_profile_does_not_widen_allocation_counts_or_unsupported_index_types() {
    for ty in [
        Ty::I8,
        Ty::U8,
        Ty::I16,
        Ty::U16,
        Ty::I32,
        Ty::U32,
        Ty::Isize,
        Ty::Usize,
        Ty::I128,
        Ty::U128,
        Ty::Bool,
        Ty::Ptr,
    ] {
        let module = fixture(Ty::I32, ty.clone());
        let original = module.clone();
        assert!(
            reflect(&module, CoreMemoryIndexProfileV1::TypedIntegerGepBoundedV1).is_err(),
            "count {ty:?}"
        );
        assert_eq!(module, original);
    }
    for ty in [
        Ty::Isize,
        Ty::Usize,
        Ty::I128,
        Ty::U128,
        Ty::Bool,
        Ty::Ptr,
        Ty::F32,
    ] {
        let module = fixture(ty.clone(), Ty::I64);
        for profile in [
            CoreMemoryIndexProfileV1::StrictI64,
            CoreMemoryIndexProfileV1::TypedI64U64BoundedV1,
            CoreMemoryIndexProfileV1::TypedIntegerGepBoundedV1,
        ] {
            assert!(
                reflect(&module, profile).is_err(),
                "index {ty:?}/{profile:?}"
            );
        }
    }
}

#[test]
fn typed_integer_gep_profile_deduplicates_catalog_not_repeated_ordered_ssa_ids() {
    let mut module = fixture(Ty::U32, Ty::I64);
    let Inst::GEP { indices, .. } = &mut module.functions[0].blocks[0].body[1].inst else {
        unreachable!()
    };
    *indices = vec![INDEX, COUNT, INDEX];
    assert!(crate::validate_module(&module).is_empty());
    let reflected = reflect(&module, CoreMemoryIndexProfileV1::TypedIntegerGepBoundedV1).unwrap();
    assert_eq!(
        sites(&reflected)[1].get_app_args()[6],
        &list(
            "IRByteOperandV1",
            [row(INDEX, nominal(&Ty::U32)), row(COUNT, nominal(&Ty::I64))]
        )
    );
    let ctx = reflected.context_term().get_app_args();
    let functions = elements(ctx[0].get_app_args()[0]);
    let blocks = elements(functions[0].get_app_args()[3]);
    let nodes = elements(blocks[0].get_app_args()[2]);
    assert_eq!(
        nodes[1].get_app_args()[0].get_app_args()[2],
        &ids(&[INDEX, COUNT, INDEX])
    );
}

#[test]
fn typed_integer_gep_profile_empty_indices_and_absent_count_remain_original_data() {
    let mut module = fixture(Ty::I32, Ty::I64);
    let Inst::Alloca { count, .. } = &mut module.functions[0].blocks[0].body[0].inst else {
        unreachable!()
    };
    *count = None;
    let Inst::GEP { indices, .. } = &mut module.functions[0].blocks[0].body[1].inst else {
        unreachable!()
    };
    indices.clear();
    let reflected = reflect(&module, CoreMemoryIndexProfileV1::TypedIntegerGepBoundedV1).unwrap();
    assert_eq!(sites(&reflected)[0].get_app_fn(), &c("IRByteSiteV1.mk"));
    assert_eq!(sites(&reflected)[1].get_app_fn(), &c("IRByteSiteV1.mki"));
    assert_eq!(
        sites(&reflected)[1].get_app_args()[6],
        &list("IRByteOperandV1", [])
    );
}

#[test]
fn typed_integer_gep_profile_never_relaxes_actual_target_or_missing_ssa_checks() {
    let original = fixture(Ty::I32, Ty::I64);
    for case in 0..4 {
        let mut module = original.clone();
        match case {
            0 => module.target_info = None,
            1 => module.target_info.as_mut().unwrap().pointer_size = 4,
            2 => module.target_info.as_mut().unwrap().endianness = Endianness::Big,
            _ => {
                let Inst::GEP { indices, .. } = &mut module.functions[0].blocks[0].body[1].inst
                else {
                    unreachable!()
                };
                *indices = vec![ValueId(999)];
            }
        }
        for profile in [
            CoreMemoryIndexProfileV1::StrictI64,
            CoreMemoryIndexProfileV1::TypedI64U64BoundedV1,
            CoreMemoryIndexProfileV1::TypedIntegerGepBoundedV1,
        ] {
            assert!(
                reflect(&module, profile).is_err(),
                "case {case}/{profile:?}"
            );
        }
    }
}
