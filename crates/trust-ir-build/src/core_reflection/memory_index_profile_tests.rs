// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Nominal memory-profile data controls. These do not execute or certify IR.

use super::*;
use trust_ir::{Endianness, FuncTy, StructPassingPolicy, TargetInfo};

const FUNCTION: FuncId = FuncId(7);
const BLOCK: BlockId = BlockId(17);
const BASE: ValueId = ValueId(19);
const INDEX: ValueId = ValueId(31);
const COUNT: ValueId = ValueId(37);

fn fixture(index_ty: Ty, count_ty: Ty) -> Module {
    let mut module = Module::new("ordinary_typed_memory");
    module.target_info = Some(TargetInfo {
        triple: "aarch64-apple-darwin".into(),
        pointer_size: 8,
        endianness: Endianness::Little,
        abi: Some("aapcs64".into()),
        struct_passing: StructPassingPolicy::NativeC,
    });
    let signature = module
        .add_func_type(FuncTy {
            abi: None,
            params: vec![Ty::Ptr, index_ty.clone(), count_ty.clone()],
            returns: vec![Ty::U64],
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut function = Function::new(FUNCTION, "memory", signature, BLOCK);
    let mut block = Block::new(BLOCK);
    block.params = vec![(BASE, Ty::Ptr), (INDEX, index_ty), (COUNT, count_ty)];
    block.body = vec![
        InstrNode::new(Inst::Const {
            ty: Ty::U64,
            value: Constant::Int(17),
        })
        .with_result(ValueId(47)),
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
        InstrNode::new(Inst::Store {
            ty: Ty::U64,
            ptr: ValueId(59),
            value: ValueId(47),
            volatile: false,
            align: Some(8),
        }),
        InstrNode::new(Inst::Load {
            ty: Ty::U64,
            ptr: ValueId(59),
            volatile: false,
            align: Some(8),
        })
        .with_result(ValueId(61)),
        InstrNode::new(Inst::Return {
            values: vec![ValueId(61)],
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

fn typed(module: &Module) -> Result<ReflectedCoreModuleV1<'_>> {
    reflect(module, CoreMemoryIndexProfileV1::TypedI64U64BoundedV1)
}

fn elements(term: &Expr) -> Vec<&Expr> {
    let mut cursor = term;
    let mut values = Vec::new();
    while cursor.get_app_fn() == &c("IRList.cons") {
        let args = cursor.get_app_args();
        assert_eq!(args.len(), 3);
        values.push(args[1]);
        cursor = args[2];
    }
    assert_eq!(cursor.get_app_fn(), &c("IRList.nil"));
    values
}

fn site<'a>(reflected: &'a ReflectedCoreModuleV1<'_>, pc: usize) -> &'a Expr {
    let context = reflected.context_term().get_app_args();
    let sites = elements(context[4]);
    let result = sites[pc];
    let fields = result.get_app_args();
    assert_eq!(fields[0], &nat(FUNCTION.0.into()));
    assert_eq!(fields[1], &nat(BLOCK.0.into()));
    assert_eq!(fields[2], &nat(pc as u64));
    result
}

fn nodes<'a>(reflected: &'a ReflectedCoreModuleV1<'_>) -> Vec<&'a Expr> {
    let context = reflected.context_term().get_app_args();
    let functions = elements(context[0].get_app_args()[0]);
    let blocks = elements(functions[0].get_app_args()[3]);
    elements(blocks[0].get_app_args()[2])
}

fn row(id: ValueId, ty: &str) -> Expr {
    app("IRByteOperandV1.mk", [nat(id.0.into()), app(ty, [nat(64)])])
}

#[test]
fn memory_index_profile_unsigned_retains_whole_original_module_ids_and_types() {
    let module = fixture(Ty::U64, Ty::U64);
    assert!(crate::validate_module(&module).is_empty());
    let before = module.clone();
    let reflected = typed(&module).unwrap();
    assert!(std::ptr::eq(reflected.module(), &module));
    assert!(std::ptr::eq(
        reflected.function(FUNCTION).unwrap(),
        &module.functions[0]
    ));
    assert!(std::ptr::eq(
        reflected.block(FUNCTION, BLOCK).unwrap(),
        &module.functions[0].blocks[0]
    ));
    for (pc, node) in module.functions[0].blocks[0].body.iter().enumerate() {
        assert!(std::ptr::eq(
            reflected.node(FUNCTION, BLOCK, pc).unwrap(),
            node
        ));
    }
    assert_eq!(
        reflected.memory_index_profile(),
        CoreMemoryIndexProfileV1::TypedI64U64BoundedV1
    );
    assert_eq!(module, before);
    assert!(reflect_core_module_v1(&module, &[(FUNCTION, 4096)]).is_err());
    assert!(reflect(&module, CoreMemoryIndexProfileV1::StrictI64).is_err());

    let actual_nodes = nodes(&reflected);
    assert_eq!(
        actual_nodes[1],
        &app(
            "IRNode.mk",
            [
                app(
                    "IRInst.alloca",
                    [
                        app("IRTy.uint_", [nat(8)]),
                        app("IROption.some", [c("Nat"), nat(COUNT.0.into())]),
                    ],
                ),
                ids(&[ValueId(43)]),
            ],
        )
    );
    assert_eq!(
        actual_nodes[2],
        &app(
            "IRNode.mk",
            [
                app(
                    "IRInst.gep",
                    [
                        app("IRTy.uint_", [nat(8)]),
                        nat(BASE.0.into()),
                        ids(&[INDEX]),
                        boolean(false),
                    ],
                ),
                ids(&[ValueId(59)]),
            ],
        )
    );
    for (pc, id) in [(1, COUNT), (2, INDEX)] {
        let actual_site = site(&reflected, pc);
        assert_eq!(actual_site.get_app_fn(), &c("IRByteSiteV1.mkt"));
        let fields = actual_site.get_app_args();
        assert_eq!(fields[5], &list("IRTy", [c("IRTy.ptr_")]));
        assert_eq!(fields[6], &list("IRByteOperandV1", [row(id, "IRTy.uint_")]));
    }
}

#[test]
fn memory_index_profile_strict_default_is_identical_and_typed_sites_are_explicit() {
    let module = fixture(Ty::I64, Ty::I64);
    let original = reflect_core_module_v1(&module, &[(FUNCTION, 4096)]).unwrap();
    let strict = reflect(&module, CoreMemoryIndexProfileV1::StrictI64).unwrap();
    assert_eq!(original.context_term(), strict.context_term());
    assert_eq!(
        strict.memory_index_profile(),
        CoreMemoryIndexProfileV1::StrictI64
    );
    let profiled = typed(&module).unwrap();
    let original_fields = original.context_term().get_app_args();
    let profiled_fields = profiled.context_term().get_app_args();
    assert_eq!(original_fields[..4], profiled_fields[..4]);
    for pc in 0..6 {
        if matches!(pc, 1 | 2) {
            assert_eq!(site(&original, pc).get_app_fn(), &c("IRByteSiteV1.mk"));
            assert_eq!(site(&profiled, pc).get_app_fn(), &c("IRByteSiteV1.mkt"));
            let id = if pc == 1 { COUNT } else { INDEX };
            assert_eq!(
                site(&profiled, pc).get_app_args()[6],
                &list("IRByteOperandV1", [row(id, "IRTy.int_")])
            );
        } else {
            assert_eq!(site(&original, pc), site(&profiled, pc));
        }
    }
}

#[test]
fn memory_index_profile_deduplicates_catalog_only_not_ordered_instruction_operands() {
    let mut module = fixture(Ty::U64, Ty::I64);
    let Inst::GEP { indices, .. } = &mut module.functions[0].blocks[0].body[2].inst else {
        unreachable!()
    };
    *indices = vec![INDEX, COUNT, INDEX];
    assert!(crate::validate_module(&module).is_empty());
    let reflected = typed(&module).unwrap();
    assert_eq!(
        site(&reflected, 2).get_app_args()[6],
        &list(
            "IRByteOperandV1",
            [row(INDEX, "IRTy.uint_"), row(COUNT, "IRTy.int_")],
        )
    );
    let actual_nodes = nodes(&reflected);
    let instruction = actual_nodes[2].get_app_args()[0];
    assert_eq!(instruction.get_app_args()[2], &ids(&[INDEX, COUNT, INDEX]));
}

#[test]
fn memory_index_profile_refuses_other_nominal_index_and_count_types() {
    for ty in [Ty::U32, Ty::Usize, Ty::U128, Ty::Bool, Ty::Ptr] {
        for module in [fixture(ty.clone(), Ty::I64), fixture(Ty::I64, ty.clone())] {
            let before = module.clone();
            assert!(typed(&module).is_err(), "unsupported operand type {ty:?}");
            assert!(reflect_core_module_v1(&module, &[(FUNCTION, 4096)]).is_err());
            assert_eq!(module, before);
        }
    }
    for (index_ty, count_ty) in [(Ty::I64, Ty::U64), (Ty::U64, Ty::I64)] {
        let module = fixture(index_ty, count_ty);
        assert!(crate::validate_module(&module).is_empty());
        assert!(typed(&module).is_ok());
    }
}

#[test]
fn memory_index_profile_preserves_absent_count_and_empty_index_list() {
    let mut module = fixture(Ty::I64, Ty::I64);
    let Inst::Alloca { count, .. } = &mut module.functions[0].blocks[0].body[1].inst else {
        unreachable!()
    };
    *count = None;
    let Inst::GEP { indices, .. } = &mut module.functions[0].blocks[0].body[2].inst else {
        unreachable!()
    };
    indices.clear();
    let reflected = typed(&module).unwrap();
    let actual_nodes = nodes(&reflected);
    let allocation = actual_nodes[1].get_app_args()[0];
    assert_eq!(
        allocation.get_app_args()[1],
        &app("IROption.none", [c("Nat")])
    );
    assert_eq!(site(&reflected, 1).get_app_fn(), &c("IRByteSiteV1.mk"));
    let gep = actual_nodes[2].get_app_args()[0];
    assert_eq!(gep.get_app_args()[2], &ids(&[]));
    assert_eq!(
        site(&reflected, 2).get_app_args()[6],
        &list("IRByteOperandV1", [])
    );
}

#[test]
fn memory_index_profile_high_half_constant_is_data_not_a_runtime_bound() {
    let mut module = fixture(Ty::U64, Ty::U64);
    module.functions[0].blocks[0].body.insert(
        1,
        InstrNode::new(Inst::Const {
            ty: Ty::U64,
            value: Constant::Int(i128::from(u64::MAX)),
        })
        .with_result(ValueId(71)),
    );
    let Inst::Alloca { count, .. } = &mut module.functions[0].blocks[0].body[2].inst else {
        unreachable!()
    };
    *count = Some(ValueId(71));
    let Inst::GEP { indices, .. } = &mut module.functions[0].blocks[0].body[3].inst else {
        unreachable!()
    };
    *indices = vec![ValueId(71)];
    assert!(crate::validate_module(&module).is_empty());
    let reflected = typed(&module).unwrap();
    let actual_nodes = nodes(&reflected);
    assert_eq!(
        actual_nodes[1].get_app_args()[0],
        &app(
            "IRInst.const_",
            [
                app("IRTy.uint_", [nat(64)]),
                app("IRConst.int_", [nat(u64::MAX)]),
            ],
        )
    );
    for pc in [2, 3] {
        assert_eq!(
            site(&reflected, pc).get_app_args()[6],
            &list("IRByteOperandV1", [row(ValueId(71), "IRTy.uint_")])
        );
    }
    // The unchanged ByteV1 evaluator, not this data reflector, rejects this
    // carrier as unmodelled. No execution/proof assertion is made here.
    assert!(reflect_core_module_v1(&module, &[(FUNCTION, 4096)]).is_err());
}

#[test]
fn memory_index_profile_keeps_target_metadata_and_original_ssa_refusals() {
    for mutation in 0..5 {
        let mut module = fixture(Ty::U64, Ty::U64);
        match mutation {
            0 => module.target_info = None,
            1 => module.target_info.as_mut().unwrap().pointer_size = 4,
            2 => module.functions[0].blocks[0].body[2]
                .proofs
                .push(trust_ir::ProofAnnotation::NoWrap),
            3 => module.functions[0].blocks[0].body[1].results[0] = INDEX,
            4 => {
                let Inst::GEP { indices, .. } = &mut module.functions[0].blocks[0].body[2].inst
                else {
                    unreachable!()
                };
                *indices = vec![ValueId(99)];
            }
            _ => unreachable!(),
        }
        let before = module.clone();
        assert!(typed(&module).is_err(), "mutation {mutation}");
        assert!(reflect_core_module_v1(&module, &[(FUNCTION, 4096)]).is_err());
        assert_eq!(module, before);
    }
}
