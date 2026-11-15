// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use trust_ir::{BodyGate, CallingConv, StructPassingPolicy};

/// Mixed ordinary/non-propagating direct and indirect calls. This exercises
/// transport and structural typing, not source FnAbi provenance or EH execution.
pub fn build_call_unwind_boundary() -> Result<Module, FixtureError> {
    let mut module = Module::new("call_unwind_boundary");
    // The non-default indirect convention is a genuine cross-convention ABI
    // boundary, so the fixture records the required concrete target contract.
    module.target_info = Some(TargetInfo {
        triple: "aarch64-apple-darwin".into(),
        pointer_size: 8,
        endianness: Endianness::Little,
        abi: Some("aapcs64".into()),
        struct_passing: StructPassingPolicy::NativeC,
    });
    let sig = module
        .add_func_type(FuncTy {
            abi: None,
            params: vec![Ty::U64],
            returns: vec![Ty::U64],
            is_vararg: false,
        })
        .or_fixture("Module::add_func_type")?;
    let caller_sig = module
        .add_func_type(FuncTy {
            abi: None,
            params: vec![Ty::Func(sig), Ty::U64],
            returns: vec![Ty::U64],
            is_vararg: false,
        })
        .or_fixture("Module::add_func_type")?;
    let mut leaf = Function::new(FuncId(0), "identity", sig, BlockId(2));
    leaf.body_gate = Some(BodyGate::Ungated);
    let mut entry = Block::new(BlockId(2));
    entry.params.push((ValueId(4), Ty::U64));
    entry.body.push(InstrNode::new(Inst::Return {
        values: vec![ValueId(4)],
    }));
    leaf.blocks.push(entry);
    let mut caller = Function::new(FuncId(1), "all_call_shapes", caller_sig, BlockId(11));
    caller.body_gate = Some(BodyGate::Ungated);
    let mut entry = Block::new(BlockId(11));
    entry
        .params
        .extend([(ValueId(20), Ty::Func(sig)), (ValueId(21), Ty::U64)]);
    for (inst, result) in [
        (
            Inst::Call {
                callee: leaf.id,
                args: vec![ValueId(21)],
            },
            ValueId(22),
        ),
        (
            Inst::CallCannotUnwind {
                callee: leaf.id,
                args: vec![ValueId(22)],
            },
            ValueId(23),
        ),
        (
            Inst::CallIndirect {
                callee: ValueId(20),
                sig,
                args: vec![ValueId(23)],
                calling_conv: CallingConv::C,
            },
            ValueId(24),
        ),
        (
            Inst::CallIndirectCannotUnwind {
                callee: ValueId(20),
                sig,
                args: vec![ValueId(24)],
                calling_conv: CallingConv::Fast,
            },
            ValueId(25),
        ),
    ] {
        let mut node = InstrNode::new(inst);
        node.results.push(result);
        entry.body.push(node);
    }
    entry.body.push(InstrNode::new(Inst::Return {
        values: vec![ValueId(25)],
    }));
    caller.blocks.push(entry);
    module.functions.extend([leaf, caller]);
    Ok(module)
}
