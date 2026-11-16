// Copyright 2026 Andrew Yates | SPDX-License-Identifier: Apache-2.0
//! Positive-first controls for Storage's stricter cast epoch. The original
//! frozen oracle and all corpus/random/fixpoint/deep populations stay intact.
use super::*;

fn storage() -> Ty {
    Ty::Storage(trust_ir::StorageLayout::new(80, 8))
}

fn module() -> Module {
    let mut module = Module::new("storage-cast-epoch");
    module.target_info = Some(TargetInfo {
        triple: "aarch64-apple-darwin".into(),
        pointer_size: 8,
        endianness: Endianness::Little,
        abi: None,
        struct_passing: Default::default(),
    });
    module.structs.push(StructDef {
        id: StructId::new(0),
        name: "StorageParent".into(),
        fields: vec![FieldDef {
            name: "backing".into(),
            ty: storage(),
            offset: Some(0),
        }],
        size: Some(80),
        align: Some(8),
        repr: StructRepr::C,
        origin: None,
    });
    module
}

fn current_answers(
    module: &Module,
    op: CastOp,
    src: &Ty,
    dst: &Ty,
    expected: Result<CastLayoutEvidence, LayoutError>,
) {
    assert_eq!(
        oracle::layout_sensitive_cast_evidence(module, op, src, dst),
        expected,
        "independent current oracle: {op:?} {src:?} -> {dst:?}"
    );
    assert_eq!(
        module.layout_sensitive_cast_evidence(op, src, dst),
        expected,
        "Module: {op:?} {src:?} -> {dst:?}"
    );
    let table = module.layout_table();
    for pass in 0..2 {
        assert_eq!(
            table.layout_sensitive_cast_evidence(op, src, dst),
            expected,
            "shared table pass {pass}: {op:?} {src:?} -> {dst:?}"
        );
    }
}

#[test]
fn storage_epoch_retains_positive_casts_and_exact_first_causes() {
    let module = module();
    // Positive first: the existing scalar rule remains exact.
    current_answers(
        &module,
        CastOp::Bitcast,
        &Ty::U64,
        &Ty::U64,
        Ok(CastLayoutEvidence::SameSize {
            size_bits: 64,
            src_align_bits: Some(64),
            dst_align_bits: Some(64),
        }),
    );
    // An address to Storage is still only an address, never by-value Storage.
    let pointer = Ty::Ref(Box::new(storage()));
    let pointer_evidence = oracle::legacy_layout_sensitive_cast_evidence(
        &module,
        CastOp::PtrToPtr,
        &pointer,
        &Ty::Ptr,
    )
    .expect("the frozen thin-pointer positive");
    assert!(matches!(
        &pointer_evidence,
        CastLayoutEvidence::PointerCast { .. }
    ));
    current_answers(
        &module,
        CastOp::PtrToPtr,
        &pointer,
        &Ty::Ptr,
        Ok(pointer_evidence),
    );
    // Non-layout-sensitive operations retain the earlier immediate answer.
    current_answers(
        &module,
        CastOp::Trunc,
        &s(0),
        &Ty::U64,
        Ok(CastLayoutEvidence::NotLayoutSensitive),
    );

    // The exact retained native failure from storage_by_value_signature.json.
    let retained_destination = Ty::Ref(Box::new(s(0)));
    assert_eq!(
        oracle::legacy_layout_sensitive_cast_evidence(
            &module,
            CastOp::PtrToPtr,
            &storage(),
            &retained_destination,
        ),
        Err(LayoutError::NotPointer(trust_ir::shape::TyShape::Storage)),
    );
    current_answers(
        &module,
        CastOp::PtrToPtr,
        &storage(),
        &retained_destination,
        Err(LayoutError::UnsupportedTyShape(
            trust_ir::shape::TyShape::Storage,
        )),
    );

    // Preserve the causal legacy answer beside the new policy's exact refusal.
    assert_eq!(
        oracle::legacy_layout_sensitive_cast_evidence(&module, CastOp::PtrToPtr, &s(0), &Ty::Ptr,),
        Err(LayoutError::NotPointer(trust_ir::shape::TyShape::Struct)),
    );
    current_answers(
        &module,
        CastOp::PtrToPtr,
        &s(0),
        &Ty::Ptr,
        Err(LayoutError::UnsupportedTyShape(
            trust_ir::shape::TyShape::Storage,
        )),
    );

    // Storage refuses before later closure and Boolean laundering checks.
    let closure = Ty::Tuple(vec![storage(), Ty::Closure(ClosureTyId::new(0))]);
    assert_eq!(
        oracle::legacy_layout_sensitive_cast_evidence(&module, CastOp::Bitcast, &closure, &Ty::U64,),
        Err(LayoutError::ClosureCast {
            src: trust_ir::shape::TyShape::Tuple,
            dst: Ty::U64.shape(),
        }),
    );
    current_answers(
        &module,
        CastOp::Bitcast,
        &closure,
        &Ty::U64,
        Err(LayoutError::UnsupportedTyShape(
            trust_ir::shape::TyShape::Storage,
        )),
    );
    let boolean = Ty::Tuple(vec![storage(), Ty::Bool]);
    assert_eq!(
        oracle::legacy_layout_sensitive_cast_evidence(
            &module,
            CastOp::Transmute,
            &boolean,
            &Ty::Bool,
        ),
        Err(LayoutError::BoolLaneReinterpret {
            src: trust_ir::shape::TyShape::Tuple,
            dst: trust_ir::shape::TyShape::Bool,
        }),
    );
    current_answers(
        &module,
        CastOp::Transmute,
        &boolean,
        &Ty::Bool,
        Err(LayoutError::UnsupportedTyShape(
            trust_ir::shape::TyShape::Storage,
        )),
    );
    // Handle authority still refuses before Storage.
    let opaque = Ty::Tuple(vec![handle(), storage()]);
    current_answers(
        &module,
        CastOp::Bitcast,
        &opaque,
        &Ty::U64,
        Err(LayoutError::OpaqueHandleCast {
            src: trust_ir::shape::TyShape::Tuple,
            dst: Ty::U64.shape(),
        }),
    );
}

#[test]
fn independent_storage_walk_retains_all_raw_rows_and_address_boundaries() {
    let mut module = module();
    module.types.push(storage());
    module.func_types.push(FuncTy {
        params: vec![storage()],
        returns: vec![],
        is_vararg: false,
        abi: None,
    });
    module.closure_types.push(ClosureTy {
        func: FuncTyId::new(0),
        captures: vec![storage()],
    });
    module.closure_types.push(ClosureTy {
        func: FuncTyId::new(0),
        captures: vec![],
    });
    // All duplicate rows count, even when an earlier row has no seed.
    module.structs.insert(0, strukt(0, vec![Ty::U64]));
    // Seedless cycles add no Storage and terminate independently of query order.
    module.structs.push(strukt(1, vec![s(2)]));
    module.structs.push(strukt(2, vec![s(1)]));
    module.records.push(RecordDef {
        id: RecordId::new(0),
        name: "StorageRecord".into(),
        fields: vec![field(0, storage())],
    });
    // An uninhabited field does not erase a later declared Storage occurrence.
    module.enums.push(EnumDef::new(
        EnumId::new(0),
        "StorageEnum",
        vec![
            EnumVariant {
                name: "Absent".into(),
                fields: vec![Ty::Never, storage()],
                field_names: vec![],
            },
            EnumVariant {
                name: "Present".into(),
                fields: vec![Ty::U64],
                field_names: vec![],
            },
        ],
    ));

    let absent = [
        Ty::U64,
        Ty::Ptr,
        Ty::Ref(Box::new(storage())),
        Ty::RefMut(Box::new(storage())),
        Ty::PtrConst(Box::new(storage())),
        Ty::PtrMut(Box::new(storage())),
        Ty::Rc(Box::new(storage())),
        Ty::FatPtr(FatPtrKind::Slice(TyId::new(0))),
        Ty::Func(FuncTyId::new(0)),
        Ty::Closure(ClosureTyId::new(1)),
        Ty::Array(TyId::new(99), 1),
        s(1),
    ];
    let present = [
        storage(),
        Ty::Tuple(vec![Ty::U8, storage()]),
        Ty::Vector(Box::new(storage()), 0),
        Ty::Tensor(Box::new(storage()), 0),
        Ty::Array(TyId::new(0), 0),
        Ty::Refine(TyId::new(0), PredId::new(0)),
        Ty::Sequence(TyId::new(0)),
        Ty::Set(TyId::new(0), SetRepr::Boxed),
        s(0),
        Ty::Enum(EnumId::new(0)),
        Ty::Record(RecordId::new(0)),
        Ty::Closure(ClosureTyId::new(0)),
    ];
    // These are raw type-presence questions, including malformed spellings.
    // A positive answer grants no layout, initialized value or ABI admission.
    let table = module.layout_table();
    for pass in 0..2 {
        for (types, expected) in [(&absent[..], false), (&present[..], true)] {
            for ty in types {
                assert_eq!(
                    oracle::storage_value_present(&module, ty),
                    expected,
                    "{ty:?}"
                );
                assert_eq!(
                    module.type_contains_storage_by_value(ty),
                    expected,
                    "{ty:?}"
                );
                assert_eq!(
                    table.type_contains_storage_by_value(ty),
                    expected,
                    "shared table pass {pass}: {ty:?}"
                );
            }
        }
    }
}
