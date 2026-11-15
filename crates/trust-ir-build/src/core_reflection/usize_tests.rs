// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Distinct target-indexed data reflection, not a source or concurrency proof.

use super::*;
use trust_ir::{AtomicRMWOp, Endianness, FuncTy, Ordering, StructPassingPolicy, TargetInfo};

fn fixture(ty: Ty) -> Module {
    let mut module = Module::new("usize_data");
    module.target_info = Some(TargetInfo {
        triple: "arm64-apple-macosx".into(),
        pointer_size: 8,
        endianness: Endianness::Little,
        abi: None,
        struct_passing: StructPassingPolicy::Unclassified,
    });
    let signature = module
        .add_func_type(FuncTy {
            params: vec![Ty::Ptr],
            returns: vec![ty.clone()],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut function = Function::new(FuncId(7), "fetch_add", signature, BlockId(3));
    let mut block = Block::new(BlockId(3));
    block.params.push((ValueId(19), Ty::Ptr));
    block.body = vec![
        InstrNode::new(Inst::Const {
            ty: ty.clone(),
            value: Constant::Int(7),
        })
        .with_result(ValueId(11)),
        InstrNode::new(Inst::AtomicRMW {
            op: AtomicRMWOp::Add,
            ty,
            ptr: ValueId(19),
            value: ValueId(11),
            ordering: Ordering::Relaxed,
        })
        .with_result(ValueId(23)),
        InstrNode::new(Inst::Return {
            values: vec![ValueId(23)],
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

#[test]
fn usize64_reflection_preserves_nominal_type_width_ssa_and_exact_layout() {
    let mut module = fixture(Ty::Usize);
    module.types.push(Ty::U64); // Both equal-sized types must have distinct rows.
    let before = module.clone();
    assert!(crate::validate_module(&module).is_empty());
    let reflected = reflect(&module).unwrap();
    let ctx = reflected.context_term().get_app_args();
    let layouts = elements(ctx[1]);
    for name in ["IRTy.usize_", "IRTy.uint_"] {
        assert!(layouts.contains(&&app(
            "IRByteLayoutV1.mk",
            [
                app(name, [nat(64)]),
                nat(8),
                nat(8),
                list("IRTy", []),
                list("Nat", []),
            ]
        )));
    }
    let functions = elements(ctx[0].get_app_args()[0]);
    let blocks = elements(functions[0].get_app_args()[3]);
    let nodes = elements(blocks[0].get_app_args()[2]);
    assert_eq!(
        nodes[0],
        &app(
            "IRNode.mk",
            [
                app(
                    "IRInst.const_",
                    [app("IRTy.usize_", [nat(64)]), app("IRConst.int_", [nat(7)])]
                ),
                list("Nat", [nat(11)]),
            ]
        )
    );
    assert_eq!(
        nodes[1],
        &app(
            "IRNode.mk",
            [
                app(
                    "IRInst.atomic_fetch_add_relaxed_usize_seq",
                    [nat(64), nat(19), nat(11)]
                ),
                list("Nat", [nat(23)]),
            ]
        )
    );
    assert_eq!(module, before);
    assert!(std::ptr::eq(reflected.module(), &module));
    assert_ne!(
        reflected.context_term(),
        reflect(&fixture(Ty::U64)).unwrap().context_term()
    );
}

#[test]
fn usize64_reflection_requires_actual_supported_target() {
    for mutate in [
        |m: &mut Module| m.target_info = None,
        |m: &mut Module| m.target_info.as_mut().unwrap().pointer_size = 4,
        |m: &mut Module| m.target_info.as_mut().unwrap().endianness = Endianness::Big,
        |m: &mut Module| m.target_info.as_mut().unwrap().triple = "mystery-target".into(),
    ] {
        let mut module = fixture(Ty::Usize);
        mutate(&mut module);
        let before = module.clone();
        assert!(reflect(&module).is_err());
        assert_eq!(module, before);
    }
    for ty in [Ty::Isize, Ty::U32, Ty::I64, Ty::U128] {
        assert!(reflect(&fixture(ty)).is_err());
    }
}

#[test]
fn usize64_atomic_reflection_admits_only_add_relaxed() {
    for op in [
        AtomicRMWOp::Xchg,
        AtomicRMWOp::Add,
        AtomicRMWOp::Sub,
        AtomicRMWOp::And,
        AtomicRMWOp::Or,
        AtomicRMWOp::Xor,
        AtomicRMWOp::Max,
        AtomicRMWOp::Min,
        AtomicRMWOp::UMax,
        AtomicRMWOp::UMin,
    ] {
        for ordering in [
            Ordering::Relaxed,
            Ordering::Acquire,
            Ordering::Release,
            Ordering::AcqRel,
            Ordering::SeqCst,
        ] {
            let mut module = fixture(Ty::Usize);
            let Inst::AtomicRMW {
                op: actual_op,
                ordering: actual_order,
                ..
            } = &mut module.functions[0].blocks[0].body[1].inst
            else {
                unreachable!()
            };
            *actual_op = op;
            *actual_order = ordering;
            assert_eq!(
                reflect(&module).is_ok(),
                op == AtomicRMWOp::Add && ordering == Ordering::Relaxed
            );
        }
    }
}

#[test]
fn usize64_scalar_memory_retains_type_alignment_and_volatile_refusals() {
    let mut module = fixture(Ty::Usize);
    module.functions[0].blocks[0].body.insert(
        1,
        InstrNode::new(Inst::Store {
            ty: Ty::Usize,
            ptr: ValueId(19),
            value: ValueId(11),
            volatile: false,
            align: Some(8),
        }),
    );
    module.functions[0].blocks[0].body[2] = InstrNode::new(Inst::Load {
        ty: Ty::Usize,
        ptr: ValueId(19),
        volatile: false,
        align: Some(8),
    })
    .with_result(ValueId(23));
    assert!(crate::validate_module(&module).is_empty());
    assert!(reflect(&module).is_ok());
    for site in [1, 2] {
        let mut changed = module.clone();
        match &mut changed.functions[0].blocks[0].body[site].inst {
            Inst::Load { volatile, .. } | Inst::Store { volatile, .. } => *volatile = true,
            _ => unreachable!(),
        }
        assert!(reflect(&changed).is_err());
    }
    let mut wrong_lane = module.clone();
    let Inst::Store { ty, .. } = &mut wrong_lane.functions[0].blocks[0].body[1].inst else {
        unreachable!()
    };
    *ty = Ty::U64;
    assert!(
        reflect(&wrong_lane).is_err(),
        "equal widths do not license mixed typed stores"
    );
}
