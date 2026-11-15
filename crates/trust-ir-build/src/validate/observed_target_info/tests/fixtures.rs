// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
pub(super) fn function(id: u32, name: &str, conv: CallingConv) -> Function {
    let mut f = Function::new(FuncId::new(id), name, FuncTyId::new(0), BlockId::new(0));
    f.calling_conv = conv;
    f.linkage = Linkage::Internal;
    f.blocks = vec![Block::new(BlockId::new(0))];
    f
}
pub(super) fn edge(kind: usize, conv: CallingConv) -> Inst {
    let callee = FuncId::new(5);
    let v = ValueId::new(0);
    let sig = FuncTyId::new(0);
    let normal_dest = BlockId::new(0);
    let unwind_dest = BlockId::new(1);
    let site = trust_ir::inst::PanicSite {
        entry: callee,
        location: trust_ir::inst::PanicLocation::Value(v),
    };
    match kind {
        0 => Inst::Call {
            callee,
            args: vec![],
        },
        1 => Inst::CallCannotUnwind {
            callee,
            args: vec![],
        },
        2 => Inst::Invoke {
            callee,
            args: vec![],
            normal_dest,
            normal_args: vec![],
            unwind_dest,
        },
        3 => Inst::Assert {
            cond: v,
            kind: trust_ir::inst::AssertKind::Unspecified,
            site: Some(site),
        },
        4 => Inst::AssertInvoke {
            cond: v,
            kind: trust_ir::inst::AssertKind::Unspecified,
            site,
            normal_dest,
            normal_args: vec![],
            unwind_dest,
        },
        5 => Inst::CallIndirect {
            callee: v,
            sig,
            args: vec![],
            calling_conv: conv,
        },
        6 => Inst::CallIndirectCannotUnwind {
            callee: v,
            sig,
            args: vec![],
            calling_conv: conv,
        },
        7 => Inst::InvokeIndirect {
            callee: v,
            sig,
            args: vec![],
            calling_conv: conv,
            normal_dest,
            normal_args: vec![],
            unwind_dest,
        },
        _ => unreachable!(),
    }
}
pub(super) fn module(kind: usize) -> Module {
    let mut m = Module::new("target");
    let mut caller = function(10, "caller", CallingConv::Rust);
    caller.blocks[0]
        .body
        .push(InstrNode::new(edge(kind, CallingConv::C)));
    m.functions = vec![caller, function(5, "callee", CallingConv::C)];
    m
}
pub(super) fn target() -> trust_ir::TargetInfo {
    trust_ir::TargetInfo {
        triple: "x86_64-unknown-linux-gnu".into(),
        pointer_size: 8,
        endianness: trust_ir::Endianness::Little,
        abi: None,
        struct_passing: Default::default(),
    }
}
