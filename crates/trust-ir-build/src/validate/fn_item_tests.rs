// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
use trust_ir::{Block, FuncTy, FuncTyId, InstrNode};

fn fixture() -> Module {
    let mut module = Module::new("fn-item-validator");
    let signature = module
        .add_func_type(FuncTy::unrecorded(vec![], vec![Ty::I32], false))
        .unwrap();
    for (id, value) in [(7, 1), (42, 2)] {
        let mut function = Function::new(
            FuncId::new(id),
            format!("pick_{value}"),
            signature,
            BlockId::new(0),
        );
        let mut block = Block::new(BlockId::new(0));
        block.body.push(
            InstrNode::new(Inst::Const {
                ty: Ty::I32,
                value: Constant::Int(value),
            })
            .with_result(ValueId::new(0)),
        );
        block.body.push(InstrNode::new(Inst::Return {
            values: vec![ValueId::new(0)],
        }));
        function.blocks.push(block);
        module.functions.push(function);
    }
    module
}

fn caller(
    module: &mut Module,
    constant: FuncId,
    signature: FuncTyId,
    convention: trust_ir::CallingConv,
) {
    let mut function = Function::new(FuncId::new(0), "caller", FuncTyId::new(0), BlockId::new(0));
    let mut block = Block::new(BlockId::new(0));
    block.body.push(
        InstrNode::new(Inst::Const {
            ty: Ty::FnItem(FuncId::new(7)),
            value: Constant::FnItem(constant),
        })
        .with_result(ValueId::new(0)),
    );
    block.body.push(
        InstrNode::new(Inst::CallIndirect {
            callee: ValueId::new(0),
            sig: signature,
            args: vec![],
            calling_conv: convention,
        })
        .with_result(ValueId::new(1)),
    );
    block.body.push(InstrNode::new(Inst::Return {
        values: vec![ValueId::new(1)],
    }));
    function.blocks.push(block);
    module.functions.push(function);
}

#[test]
fn nominal_item_validator_authenticates_unused_types_and_constant_ids() {
    let mut module = fixture();
    module.types.push(Ty::FnItem(FuncId::new(99)));
    assert!(validate_module(&module).iter().any(|error| matches!(
        error,
        ValidationError::DanglingTypeReference {
            kind: "function_item",
            ..
        }
    )));
    module.types.clear();
    caller(
        &mut module,
        FuncId::new(42),
        FuncTyId::new(0),
        trust_ir::CallingConv::C,
    );
    assert!(
        validate_module(&module)
            .iter()
            .any(|error| matches!(error, ValidationError::ConstTypeMismatch { .. }))
    );
}

#[test]
fn nominal_item_indirect_calls_require_exact_signature_and_convention() {
    let mut module = fixture();
    caller(
        &mut module,
        FuncId::new(7),
        FuncTyId::new(0),
        trust_ir::CallingConv::C,
    );
    assert!(
        validate_module(&module).is_empty(),
        "{:?}",
        validate_module(&module)
    );
    module.functions.pop();
    let same_shape = module.add_func_type(module.func_types[0].clone()).unwrap();
    caller(
        &mut module,
        FuncId::new(7),
        same_shape,
        trust_ir::CallingConv::C,
    );
    assert!(
        validate_module(&module)
            .iter()
            .any(|error| matches!(error, ValidationError::CallEdgeSignatureMismatch { .. }))
    );
    module.functions.pop();
    caller(
        &mut module,
        FuncId::new(7),
        FuncTyId::new(0),
        trust_ir::CallingConv::Rust,
    );
    assert!(
        validate_module(&module)
            .iter()
            .any(|error| matches!(error, ValidationError::CallEdgeConvMismatch { .. }))
    );
}

#[test]
fn nominal_item_abi_count_is_zero_and_missing_header_is_no_count() {
    let mut module = fixture();
    let layouts = module.layout_table();
    let lanes = abi_lanes::AbiLanes::default();
    assert_eq!(
        abi_lanes::abi_lanes(&layouts, &lanes, &Ty::FnItem(FuncId::new(7))),
        Some(0)
    );
    assert_eq!(
        abi_lanes::abi_lanes(&layouts, &lanes, &Ty::FnItem(FuncId::new(99))),
        None
    );
    drop(layouts);
    module.functions[1].id = FuncId::new(7);
    assert_eq!(
        abi_lanes::abi_lanes(
            &module.layout_table(),
            &abi_lanes::AbiLanes::default(),
            &Ty::FnItem(FuncId::new(7))
        ),
        None
    );
}
