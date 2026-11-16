// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! Validated frame handles retain nominal item slots across ordinary pointer
//! transport. This family is separate from the existing 120 codec cells.

use super::{Batch, Comparison, Oracle, Val, Verdict, differential, oracle, semr_target};
use trust_ir::inst::{BindingFrameDef, BindingSlot};
use trust_ir::value::BindingFrameId;
use trust_ir::{
    Block, BlockId, CallingConv, Constant, FuncId, FuncTy, Function, Inst, InstrNode, Module,
    TargetInfo, Ty, ValueId,
};

#[derive(Clone, Copy, Debug)]
enum Transport {
    SameBlock,
    LocalCfgParameter,
    UnusedCallParameter,
}

fn frame_module(target: TargetInfo, transport: Transport) -> Module {
    let v = ValueId::new;
    let bb = BlockId::new;
    let mut module = Module::new("frame_fnitem_transport");
    module.target_info = Some(target);
    let result_sig = module
        .add_func_type(FuncTy::unrecorded(vec![], vec![Ty::I32], false))
        .unwrap();
    let sink_sig = module
        .add_func_type(FuncTy::unrecorded(vec![Ty::Ptr], vec![], false))
        .unwrap();
    let item = Ty::FnItem(FuncId::new(7));

    // Real, uniquely resolvable target header and body; expected result is 1.
    let mut target = Function::new(FuncId::new(7), "pick_one", result_sig, bb(0));
    let mut body = Block::new(bb(0));
    body.body.push(
        InstrNode::new(Inst::Const {
            ty: Ty::I32,
            value: Constant::Int(1),
        })
        .with_result(v(0)),
    );
    body.body
        .push(InstrNode::new(Inst::Return { values: vec![v(0)] }));
    target.blocks.push(body);
    module.try_add_function(target).unwrap();

    // The callee does NOT inspect or close the frame. Its Ptr argument is
    // unused, so this function makes no unsupported frame-provenance claim.
    let mut sink = Function::new(FuncId::new(1), "unused_frame", sink_sig, bb(0));
    let mut body = Block::new(bb(0));
    body.params.push((v(0), Ty::Ptr));
    body.body
        .push(InstrNode::new(Inst::Return { values: vec![] }));
    sink.blocks.push(body);
    module.try_add_function(sink).unwrap();

    let mut entry = Function::new(FuncId::new(0), "entry", result_sig, bb(0));
    let mut body = Block::new(bb(0));
    body.body.push(
        InstrNode::new(Inst::OpenFrame {
            def: BindingFrameDef::new(
                BindingFrameId::new(0),
                "items",
                vec![BindingSlot::new("callee", item.clone())],
            ),
        })
        .with_result(v(0)),
    );
    body.body.push(
        InstrNode::new(Inst::Const {
            ty: item.clone(),
            value: Constant::FnItem(FuncId::new(7)),
        })
        .with_result(v(1)),
    );
    body.body.push(
        InstrNode::new(Inst::BindSlot {
            frame: v(0),
            slot: 0,
            value: v(1),
        })
        .with_result(v(2)),
    );

    let (handle, loaded, answer) = match transport {
        Transport::SameBlock => (v(2), v(3), v(4)),
        Transport::UnusedCallParameter => {
            body.body.push(InstrNode::new(Inst::Call {
                callee: FuncId::new(1),
                args: vec![v(2)],
            }));
            (v(2), v(3), v(4))
        }
        Transport::LocalCfgParameter => {
            body.body.push(InstrNode::new(Inst::Br {
                target: bb(1),
                args: vec![v(2)],
            }));
            entry.blocks.push(body);
            body = Block::new(bb(1));
            body.params.push((v(10), Ty::Ptr));
            (v(10), v(11), v(12))
        }
    };
    body.body.push(
        InstrNode::new(Inst::LoadSlot {
            frame: handle,
            slot: 0,
            ty: item,
        })
        .with_result(loaded),
    );
    body.body
        .push(InstrNode::new(Inst::CloseFrame { frame: handle }));
    body.body.push(
        InstrNode::new(Inst::CallIndirect {
            callee: loaded,
            sig: result_sig,
            args: vec![],
            calling_conv: CallingConv::C,
        })
        .with_result(answer),
    );
    body.body.push(InstrNode::new(Inst::Return {
        values: vec![answer],
    }));
    entry.blocks.push(body);
    module.try_add_function(entry).unwrap();
    module
}

#[test]
fn nominal_function_item_frame_pointer_transport_has_exact_execution() {
    let modules: Vec<_> = [32, 64]
        .into_iter()
        .flat_map(|bits| {
            [
                Transport::SameBlock,
                Transport::LocalCfgParameter,
                Transport::UnusedCallParameter,
            ]
            .map(move |transport| {
                (
                    format!("{bits}/{transport:?}"),
                    frame_module(semr_target(bits), transport),
                )
            })
        })
        .collect();
    assert_eq!(modules.len(), 6);
    for (label, module) in &modules {
        let errors = trust_ir_build::validate_module(module);
        assert!(errors.is_empty(), "{label}: {errors:?}");
    }
    let Oracle::Ready(exe) = oracle() else { return };
    let batches: Vec<_> = modules
        .iter()
        .map(|(label, module)| Batch {
            label: label.clone(),
            module,
            runs: vec![(FuncId::new(0), vec![])],
        })
        .collect();
    let reports = differential(exe, &batches);
    assert_eq!(reports.len(), 6);
    let expected = Verdict::Ok(vec![Val::Int { width: 32, raw: 1 }]);
    let failed: Vec<_> = reports
        .iter()
        .filter(|report| {
            report.rust != expected
                || report.lean != expected
                || report.comparison != Comparison::Agree
        })
        .collect();
    assert!(
        failed.is_empty(),
        "validated frame transport failures: {failed:#?}"
    );
}
