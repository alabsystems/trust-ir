// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
use super::*;
pub(super) fn v(id: u32) -> ValueId {
    ValueId::new(id)
}
pub(super) fn b(id: u32) -> BlockId {
    BlockId::new(id)
}
pub(super) fn node(instruction: Inst, values: &[u32]) -> InstrNode {
    InstrNode::new(instruction).with_results(values.iter().copied().map(v))
}
pub(super) fn function(nodes: Vec<InstrNode>) -> Function {
    let mut function = Function::new(FuncId::new(191), "claims", FuncTyId::new(0), b(0));
    let mut block = Block::new(b(0));
    block.body = nodes;
    function.blocks.push(block);
    function
}
pub(super) fn shared() -> ValidationError {
    ValidationError::BorrowMutThroughSharedRef { block: 0 }
}
pub(super) fn end() -> ValidationError {
    ValidationError::EndBorrowOfNonBorrow { block: 0 }
}
pub(super) fn fixture() -> Function {
    function(vec![
        node(Inst::Borrow { ptr: v(99) }, &[1]),
        node(
            Inst::Copy {
                ty: Ty::Ptr,
                operand: v(1),
            },
            &[2],
        ),
        node(Inst::BorrowMut { ptr: v(2) }, &[3]),
        node(Inst::EndBorrow { borrow_ptr: v(2) }, &[]),
        node(Inst::EndBorrow { borrow_ptr: v(3) }, &[]),
    ])
}
pub(super) fn invokes() -> Vec<Inst> {
    vec![
        Inst::Invoke {
            callee: FuncId::new(9),
            args: vec![],
            normal_dest: b(1),
            normal_args: vec![v(1)],
            unwind_dest: b(2),
        },
        Inst::InvokeIndirect {
            callee: v(99),
            sig: FuncTyId::new(0),
            args: vec![],
            calling_conv: CallingConv::C,
            normal_dest: b(1),
            normal_args: vec![v(1)],
            unwind_dest: b(2),
        },
        Inst::DropInvoke {
            ty: Ty::Ptr,
            ptr: v(99),
            normal_dest: b(1),
            normal_args: vec![v(1)],
            unwind_dest: b(2),
        },
        Inst::AssertInvoke {
            cond: v(99),
            kind: trust_ir::AssertKind::NullPtr,
            site: PanicSite {
                entry: FuncId::new(9),
                location: PanicLocation::Value(v(99)),
            },
            normal_dest: b(1),
            normal_args: vec![v(1)],
            unwind_dest: b(2),
        },
    ]
}
