// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Authored descriptor controls transcribed from diagnostic capture body 2:
//! `faithful-literal-atomic.oNzuGz/capture.json`, SHA256
//! `3cb58a54dd30b2189fde1801fc9c89a1067eb1abb80ecd02e5cae95de70c3eb4`.
//! These are not freshly extracted Rust, execution evidence, or an ABI proof.
//! The unsized ArcInner<str> allocation is deliberately NOT a sized struct here.

use super::*;
use trust_ir::{
    Endianness, FatPtrKind, FieldDef, FuncTy, StructDef, StructId, StructPassingPolicy, StructRepr,
    TargetInfo,
};

const ARC: StructId = StructId(149);
const NONNULL: StructId = StructId(97);
const PHANTOM: StructId = StructId(31);
const GLOBAL: StructId = StructId(17);
const FUNCTION: FuncId = FuncId(4001);
const BLOCK: BlockId = BlockId(29);

fn field(name: &str, ty: Ty, offset: u64) -> FieldDef {
    FieldDef {
        name: name.into(),
        ty,
        offset: Some(offset),
    }
}

fn fixture(kind: FatPtrKind) -> Module {
    let mut module = Module::new("authored_arc_str_descriptor_shapes");
    module.target_info = Some(TargetInfo {
        triple: "aarch64-apple-darwin".into(),
        pointer_size: 8,
        endianness: Endianness::Little,
        abi: None,
        struct_passing: StructPassingPolicy::Unclassified,
    });
    // Sparse nominal IDs differ from table positions. Only these four SIZED
    // descriptors are copied: ContainerLen addresses the unsized header, not
    // a fictional 16-byte ArcInner allocation or a string-content pointer.
    for (id, name, repr, size, align, fields) in [
        (
            ARC,
            "Arc<str>",
            StructRepr::Rust,
            16,
            8,
            vec![
                field("ptr", Ty::Struct(NONNULL), 0),
                field("phantom", Ty::Struct(PHANTOM), 16),
                field("alloc", Ty::Struct(GLOBAL), 16),
            ],
        ),
        (GLOBAL, "Global", StructRepr::Rust, 0, 1, vec![]),
        (
            NONNULL,
            "NonNull<ArcInner<str>>",
            StructRepr::Transparent,
            16,
            8,
            vec![field("pointer", Ty::FatPtr(kind), 0)],
        ),
        (
            PHANTOM,
            "PhantomData<ArcInner<str>>",
            StructRepr::Rust,
            0,
            1,
            vec![],
        ),
    ] {
        module.structs.push(StructDef {
            id,
            name: name.into(),
            fields,
            size: Some(size),
            align: Some(align),
            repr,
            origin: None,
        });
    }
    let pointer = Ty::PtrConst(Box::new(Ty::Struct(ARC)));
    let signature = module
        .add_func_type(FuncTy {
            params: vec![pointer.clone(), Ty::U64],
            returns: vec![pointer.clone(), Ty::U64],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut function = Function::new(FUNCTION, "thin_pointer_scalar_leaf", signature, BLOCK);
    let mut block = Block::new(BLOCK);
    block.params = vec![(ValueId(19), pointer), (ValueId(23), Ty::U64)];
    block.body.push(InstrNode::new(Inst::Return {
        values: vec![ValueId(19), ValueId(23)],
    }));
    function.blocks.push(block);
    module.functions.push(function);
    module
}

fn reflect(module: &Module) -> Result<ReflectedCoreModuleV1<'_>> {
    reflect_core_module_v1(module, &[(FUNCTION, 4096)])
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

fn row(ty: Expr, size: u64, align: u64, fields: Vec<Expr>, offsets: &[u64]) -> Expr {
    app(
        "IRByteLayoutV1.mk",
        [
            ty,
            nat(size),
            nat(align),
            list("IRTy", fields),
            list("Nat", offsets.iter().copied().map(nat)),
        ],
    )
}

fn refused_unchanged(module: &Module, reason: &str) {
    let before = module.clone();
    let error = reflect(module).unwrap_err();
    assert!(error.to_string().contains(reason), "{error}");
    assert_eq!(module, &before);
}

#[test]
fn arc_str_descriptor_shapes_preserve_nested_fat_kind_sparse_ids_and_trailing_zsts() {
    let module = fixture(FatPtrKind::ContainerLen);
    let before = module.clone();
    assert!(crate::validate_module(&module).is_empty());
    let reflected = reflect(&module).unwrap();
    assert!(std::ptr::eq(reflected.module(), &module));
    assert!(std::ptr::eq(
        reflected.block(FUNCTION, BLOCK).unwrap(),
        &module.functions[0].blocks[0],
    ));
    let layouts = elements(reflected.context_term().get_app_args()[1]);
    for expected in [
        row(nominal(PHANTOM), 0, 1, vec![], &[]),
        row(nominal(GLOBAL), 0, 1, vec![], &[]),
        row(c("IRTy.containerlen_"), 16, 8, vec![], &[]),
        row(nominal(NONNULL), 16, 8, vec![c("IRTy.containerlen_")], &[0]),
        row(
            nominal(ARC),
            16,
            8,
            vec![nominal(NONNULL), nominal(PHANTOM), nominal(GLOBAL)],
            &[0, 16, 16],
        ),
    ] {
        assert!(
            layouts.contains(&expected),
            "missing exact row {expected:?}"
        );
    }
    assert_ne!(nominal(PHANTOM), nominal(GLOBAL));
    assert_eq!(module, before);
    let target = module.target_info.as_ref().unwrap();
    assert_eq!(target.struct_passing, StructPassingPolicy::Unclassified);
    assert!(target.abi.is_none());
    assert_eq!(module.structs[0].repr, StructRepr::Rust);
    assert_eq!(module.structs[2].repr, StructRepr::Transparent);
}

#[test]
fn arc_str_descriptor_shapes_refuse_missing_zst_offsets_and_incoherent_extent() {
    let baseline = fixture(FatPtrKind::ContainerLen);
    for index in [1, 2] {
        let mut changed = baseline.clone();
        changed.structs[0].fields[index].offset = None;
        // The shared shape helper can fill a missing ZST offset with zero;
        // reflection must refuse to substitute it for the captured 16.
        assert!(changed.ty_layout_shape(&Ty::Struct(ARC)).is_ok());
        refused_unchanged(&changed, "every field offset");
    }
    for bad_size in [0, 8] {
        let mut changed = baseline.clone();
        changed.structs[0].size = Some(bad_size);
        refused_unchanged(&changed, "StructLayoutInconsistent");
        refused_unchanged(&changed, "field offset is outside the declared struct size");
    }
    let mut displaced = baseline;
    displaced.structs[0].fields[1].offset = Some(17);
    refused_unchanged(
        &displaced,
        "field offset is outside the declared struct size",
    );
}

#[test]
fn nested_container_and_str_remain_distinct_without_granting_by_value_arc_abi() {
    let container = fixture(FatPtrKind::ContainerLen);
    // This is a different, independently valid authored descriptor, NOT a
    // source-faithful Arc<str> representation and NOT an expected rejection.
    let string_content = fixture(FatPtrKind::Str);
    let container_view = reflect(&container).unwrap();
    let string_view = reflect(&string_content).unwrap();
    assert_ne!(container_view.context_term(), string_view.context_term());
    let string_rows = elements(string_view.context_term().get_app_args()[1]);
    assert!(string_rows.contains(&row(nominal(NONNULL), 16, 8, vec![c("IRTy.fatstr_")], &[0],)));
    assert!(!string_rows.contains(&row(
        nominal(NONNULL),
        16,
        8,
        vec![c("IRTy.containerlen_")],
        &[0],
    )));
    for result in [false, true] {
        let mut changed = container.clone();
        changed.func_types.push(FuncTy {
            params: if result {
                vec![]
            } else {
                vec![Ty::Struct(ARC)]
            },
            returns: if result {
                vec![Ty::Struct(ARC)]
            } else {
                vec![]
            },
            abi: None,
            is_vararg: false,
        });
        // Even unused table signatures stay within the ABI boundary.
        refused_unchanged(&changed, "nonvariadic scalar/thin-pointer");
    }
}
