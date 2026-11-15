// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Exact wide-pointer identities and part operations; no Rust ABI or DST proof.

use super::*;
use trust_ir::{Endianness, FatPtrKind, FuncTy, StructPassingPolicy, TargetInfo, TyId};

fn fixture(kind: FatPtrKind) -> Module {
    let mut module = Module::new("nominal_fat_pointer_parts");
    module.target_info = Some(TargetInfo {
        triple: "aarch64-apple-darwin".into(),
        pointer_size: 8,
        endianness: Endianness::Little,
        abi: None,
        struct_passing: StructPassingPolicy::Unclassified,
    });
    module.types.push(Ty::U8);
    let metadata_ty = kind.metadata_ty(64).unwrap();
    let pointer_ty = Ty::FatPtr(kind);
    let sig = module
        .add_func_type(FuncTy {
            params: vec![Ty::Ptr, metadata_ty.clone()],
            returns: vec![Ty::Ptr, metadata_ty.clone()],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut function = Function::new(FuncId(7), "construct_and_split", sig, BlockId(3));
    let mut block = Block::new(BlockId(3));
    block.params = vec![(ValueId(19), Ty::Ptr), (ValueId(20), metadata_ty.clone())];
    block.body = vec![
        InstrNode::new(Inst::PtrFromParts {
            ptr_ty: pointer_ty.clone(),
            metadata_ty: metadata_ty.clone(),
            data: ValueId(19),
            metadata: ValueId(20),
        })
        .with_result(ValueId(30)),
        InstrNode::new(Inst::PtrData {
            ptr_ty: pointer_ty.clone(),
            ptr: ValueId(30),
        })
        .with_result(ValueId(31)),
        InstrNode::new(Inst::PtrMetadata {
            ptr_ty: pointer_ty,
            metadata_ty,
            ptr: ValueId(30),
        })
        .with_result(ValueId(32)),
        InstrNode::new(Inst::Return {
            values: vec![ValueId(31), ValueId(32)],
        }),
    ];
    function.blocks.push(block);
    module.functions.push(function);
    module
}

fn reflect(module: &Module) -> Result<ReflectedCoreModuleV1<'_>> {
    reflect_core_module_v1(module, &[(FuncId(7), 4096)])
}

fn elements(term: &Expr) -> Vec<&Expr> {
    let mut cursor = term;
    let mut values = vec![];
    while *cursor.get_app_fn() == c("IRList.cons") {
        let args = cursor.get_app_args();
        values.push(args[1]);
        cursor = args[2];
    }
    assert_eq!(*cursor.get_app_fn(), c("IRList.nil"));
    values
}

fn kinds() -> [(FatPtrKind, Expr); 6] {
    [
        (FatPtrKind::Str, c("IRTy.fatstr_")),
        (
            FatPtrKind::Slice(TyId(0)),
            app("IRTy.fatslice_", [app("IRTy.uint_", [nat(8)])]),
        ),
        (
            FatPtrKind::TraitObject { trait_id: 91 },
            app("IRTy.fatdyn_", [nat(91)]),
        ),
        (
            FatPtrKind::TraitObject { trait_id: 92 },
            app("IRTy.fatdyn_", [nat(92)]),
        ),
        (FatPtrKind::ContainerLen, c("IRTy.containerlen_")),
        (FatPtrKind::ContainerVtable, c("IRTy.containervtable_")),
    ]
}

#[test]
fn nominal_fat_kinds_keep_distinct_type_rows_exact_layouts_and_live_operands() {
    let mut contexts = vec![];
    for (kind, ty) in kinds() {
        let module = fixture(kind);
        let before = module.clone();
        assert!(crate::validate_module(&module).is_empty());
        let reflected = reflect(&module).unwrap();
        assert!(std::ptr::eq(reflected.module(), &module));
        let context = reflected.context_term().get_app_args();
        let row = app(
            "IRByteLayoutV1.mk",
            [
                ty.clone(),
                nat(16),
                nat(8),
                list("IRTy", []),
                list("Nat", []),
            ],
        );
        assert!(elements(context[1]).contains(&&row));
        let functions = elements(context[0].get_app_args()[0]);
        let blocks = elements(functions[0].get_app_args()[3]);
        let nodes = elements(blocks[0].get_app_args()[2]);
        let metadata = match kind {
            FatPtrKind::Str | FatPtrKind::Slice(_) | FatPtrKind::ContainerLen => {
                app("IRTy.uint_", [nat(64)])
            }
            FatPtrKind::TraitObject { .. } | FatPtrKind::ContainerVtable => c("IRTy.ptr_"),
        };
        for (index, instruction, destination) in [
            (
                0,
                app(
                    "IRInst.ptrfromparts",
                    [ty.clone(), metadata.clone(), nat(19), nat(20)],
                ),
                30,
            ),
            (1, app("IRInst.ptrdata", [ty.clone(), nat(30)]), 31),
            (2, app("IRInst.ptrmetadata", [ty, metadata, nat(30)]), 32),
        ] {
            assert_eq!(
                nodes[index],
                &app("IRNode.mk", [instruction, list("Nat", [nat(destination)])])
            );
        }
        for previous in &contexts {
            assert_ne!(previous, reflected.context_term());
        }
        contexts.push(reflected.context_term().clone());
        assert_eq!(module, before);
        assert_eq!(
            module.target_info.as_ref().unwrap().struct_passing,
            StructPassingPolicy::Unclassified
        );
    }
}

#[test]
fn fat_parts_reject_wrong_metadata_sorts_wrong_ssa_and_unresolved_slice_elements() {
    for (kind, _) in kinds() {
        for wrong in [
            Ty::Usize,
            Ty::U32,
            Ty::Unit,
            if kind.metadata_ty(64) == Some(Ty::Ptr) {
                Ty::U64
            } else {
                Ty::Ptr
            },
        ] {
            let mut module = fixture(kind);
            if let Inst::PtrMetadata { metadata_ty, .. } =
                &mut module.functions[0].blocks[0].body[2].inst
            {
                *metadata_ty = wrong;
            }
            assert!(reflect(&module).is_err());
        }
        let mut module = fixture(kind);
        if let Inst::PtrFromParts { data, .. } = &mut module.functions[0].blocks[0].body[0].inst {
            *data = ValueId(999);
        }
        assert!(reflect(&module).is_err());
    }
    assert!(reflect(&fixture(FatPtrKind::Slice(TyId(999)))).is_err());
    let mut cyclic = fixture(FatPtrKind::Slice(TyId(0)));
    cyclic.types[0] = Ty::FatPtr(FatPtrKind::Slice(TyId(0)));
    assert!(reflect(&cyclic).is_err());
}

#[test]
fn fat_data_admission_does_not_relax_abi_or_aggregate_memory_boundaries() {
    let baseline = fixture(FatPtrKind::ContainerLen);
    let ty = Ty::FatPtr(FatPtrKind::ContainerLen);
    let mut signature = baseline.clone();
    signature.func_types.push(FuncTy {
        params: vec![ty.clone()],
        returns: vec![],
        abi: None,
        is_vararg: false,
    });
    assert!(
        reflect(&signature)
            .unwrap_err()
            .to_string()
            .contains("scalar/thin-pointer")
    );
    for node in [
        InstrNode::new(Inst::Load {
            ty: ty.clone(),
            ptr: ValueId(19),
            volatile: false,
            align: Some(8),
        })
        .with_result(ValueId(33)),
        InstrNode::new(Inst::Store {
            ty,
            ptr: ValueId(19),
            value: ValueId(30),
            volatile: false,
            align: Some(8),
        }),
    ] {
        let mut module = baseline.clone();
        module.functions[0].blocks[0].body.insert(1, node);
        assert!(crate::validate_module(&module).is_empty());
        assert!(
            reflect(&module)
                .unwrap_err()
                .to_string()
                .contains("aggregate memory")
        );
    }
}
