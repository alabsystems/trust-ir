// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Authored UNRUN. The unchanged complete ordinary Body is the set oracle.
#![allow(
    clippy::drop_non_drop,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::super::Body;
use super::*;
use std::{cell::Cell, rc::Rc};
use trust_ir::dialect::DialectInst;
use trust_ir::inst::{
    AllocOrigin, AssertKind, AtomicRMWOp, BinOp, BindingFrameDef, BindingSlot, FCmpOp, ICmpOp,
    Ordering, OverflowOp, PanicLocation, PanicSite, SwitchCase, UnOp,
};
use trust_ir::interpret::{InstructionSite, InterpretOptions};
use trust_ir::value::{BindingFrameId, BlockId, FuncId, FuncTyId, GlobalId, TyId};
use trust_ir::{Block, Constant, InstrNode, Ty};
mod custody;
mod entry;
mod parity;
mod stops;
mod witnesses;
#[derive(Default)]
struct Observer {
    events: Vec<ExecutionProgress>,
    calls: Rc<Cell<usize>>,
    stop: Option<usize>,
    next: Option<Rc<Cell<bool>>>,
    cleanup: bool,
    work: usize,
    bytes: usize,
    cap: Option<usize>,
    byte_cap: Option<usize>,
}
impl ExecutionObserver for Observer {
    type Refusal = &'static str;
    fn admit(&mut self, event: ExecutionProgress) -> Result<(), Self::Refusal> {
        self.events.push(event);
        self.calls.set(self.events.len());
        if self.stop == Some(self.events.len())
            || self.next.as_ref().is_some_and(|v| v.replace(false))
        {
            return Err("original root stop");
        }
        if self.cleanup && event.phase == ExecutionPhase::ScratchRetirement {
            return Err("cleanup");
        }
        self.work = self.work.checked_add(event.work).ok_or("overflow")?;
        self.bytes = self.bytes.checked_add(event.copy_bytes).ok_or("overflow")?;
        if self.cap.is_some_and(|cap| self.work > cap) {
            return Err("work");
        }
        if self.byte_cap.is_some_and(|cap| self.bytes > cap) {
            return Err("bytes");
        }
        Ok(())
    }
}
fn site() -> ExecutionSite {
    ExecutionSite::Entry(FuncId::new(131))
}
fn v(id: u32) -> ValueId {
    ValueId::new(id)
}
fn node(inst: Inst, results: &[u32]) -> InstrNode {
    InstrNode::new(inst).with_results(results.iter().copied().map(v))
}
fn function(nodes: Vec<InstrNode>) -> Function {
    let mut function = Function::new(FuncId::new(131), "roots", FuncTyId::new(0), BlockId::new(0));
    let mut block = Block::new(BlockId::new(0));
    block.params = vec![(v(1), Ty::Ptr), (v(2), Ty::Ptr)];
    block.body = nodes;
    function.blocks.push(block);
    function
}
fn alloca() -> Inst {
    Inst::Alloca {
        ty: Ty::U32,
        count: None,
        align: None,
    }
}
fn copy(value: u32) -> Inst {
    Inst::Copy {
        ty: Ty::Ptr,
        operand: v(value),
    }
}
fn select(then_val: u32, else_val: u32) -> Inst {
    Inst::Select {
        ty: Ty::Ptr,
        cond: v(999),
        then_val: v(then_val),
        else_val: v(else_val),
    }
}
fn frame(count: usize) -> Inst {
    Inst::OpenFrame {
        def: BindingFrameDef::new(
            BindingFrameId::new(71),
            "frame",
            (0..count)
                .map(|i| BindingSlot::new(i.to_string(), Ty::Tuple(vec![Ty::U32])))
                .collect(),
        ),
    }
}
fn dialect(count: usize) -> Inst {
    let mut op = DialectInst::new("observed", "effects");
    op.result_tys = (0..count).map(|_| Ty::Tuple(vec![Ty::U8])).collect();
    Inst::DialectOp(Box::new(op))
}
fn body_fixture(function: &Function) -> ObservedBody<'_> {
    let original = Body::new(function);
    ObservedBody {
        function,
        entry: original.entry,
        entry_params_are_formals: original.entry_params_are_formals,
    }
}
fn expected(function: &Function, address: u32) -> Vec<Root> {
    Body::new(function).roots(v(address)).into_iter().collect()
}
fn run(function: &Function, address: u32) -> Vec<Root> {
    let mut observer = Observer::default();
    let mut original = ObservedSession::new(InterpretOptions::default(), &mut observer);
    let body = ObservedBody::new_observed(function, &mut original, site()).unwrap();
    assert_eq!(
        body.entry_params_are_formals,
        Body::new(function).entry_params_are_formals
    );
    let roots = body
        .roots_observed(v(address), &mut original, site())
        .unwrap();
    let mut rows = Vec::new();
    let mut index = 0;
    while let Some(root) = roots.at_observed(index, &mut original, site()).unwrap() {
        rows.push(root);
        index += 1;
    }
    assert_eq!(rows, expected(function, address));
    roots.retire_observed(&mut original, site()).unwrap();
    body.retire_observed(&mut original, site()).unwrap();
    assert!(original.first_refusal().is_none());
    assert_eq!(original.remaining_fuel(), InterpretOptions::default().fuel);
    drop(original);
    assert!(observer.events.iter().all(|event| event.site == site()));
    rows
}
// Query-only baseline/replay share identical borrowed metadata. The constructor
// itself has separate complete parity/refusal controls. Latch before disposing
// the successful caller-owned result, whose events cannot become query cuts.
fn query_trace(function: &Function, address: u32) -> (Observer, usize) {
    let body = body_fixture(function);
    let mut observer = Observer::default();
    let calls = observer.calls.clone();
    let mut original = ObservedSession::new(InterpretOptions::default(), &mut observer);
    let roots = body
        .roots_observed(v(address), &mut original, site())
        .unwrap();
    let bound = calls.get();
    assert_eq!(roots.rows, expected(function, address));
    roots.retire_observed(&mut original, site()).unwrap();
    drop(original);
    (observer, bound)
}
fn mixed() -> Function {
    function(vec![
        node(alloca(), &[3]),
        node(
            Inst::GlobalAddr {
                global: GlobalId::new(9),
            },
            &[4],
        ),
        node(select(1, 3), &[5]),
        node(select(4, 5), &[6]),
        node(select(6, 1000), &[7]),
    ])
}
