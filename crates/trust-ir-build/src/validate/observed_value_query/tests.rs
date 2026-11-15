// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//! Authored controls, all UNRUN.
use super::*;
use std::{cell::Cell, rc::Rc};
use trust_ir::dialect::DialectInst;
use trust_ir::inst::{
    AllocOrigin, AssertKind, AtomicRMWOp, BindingFrameDef, BindingSlot, FCmpOp, ICmpOp, InstShape,
    Ordering, OverflowOp, PanicLocation, PanicSite, SwitchCase,
};
use trust_ir::interpret::InterpretOptions;
use trust_ir::value::{BindingFrameId, BlockId, FuncId, FuncTyId, GlobalId, PredId, TyId};
use trust_ir::{BinOp, Block, CastOp, Constant, FatPtrKind, InstrNode, UnOp};
mod borrows;
mod parity;
mod stops;
mod witnesses;

#[derive(Default)]
struct Observer {
    events: Vec<ExecutionProgress>,
    stop: Option<usize>,
    work: usize,
    bytes: usize,
    work_cap: Option<usize>,
    byte_cap: Option<usize>,
    retirement_stop: Option<Rc<Cell<bool>>>,
}
impl ExecutionObserver for Observer {
    type Refusal = &'static str;
    fn admit(&mut self, event: ExecutionProgress) -> Result<(), Self::Refusal> {
        self.events.push(event);
        if self.stop == Some(self.events.len()) {
            return Err("original query stop");
        }
        if event.phase == ExecutionPhase::ScratchRetirement
            && self.retirement_stop.as_ref().is_some_and(|arm| arm.get())
        {
            return Err("original retirement stop");
        }
        self.work = self.work.checked_add(event.work).ok_or("overflow")?;
        self.bytes = self.bytes.checked_add(event.copy_bytes).ok_or("overflow")?;
        if self.work_cap.is_some_and(|cap| self.work > cap) {
            return Err("work");
        }
        if self.byte_cap.is_some_and(|cap| self.bytes > cap) {
            return Err("bytes");
        }
        Ok(())
    }
}
fn site() -> ExecutionSite {
    ExecutionSite::Entry(FuncId::new(71))
}
fn id(value: u32) -> ValueId {
    ValueId::new(value)
}
fn v() -> ValueId {
    id(0)
}
fn b(value: u32) -> BlockId {
    BlockId::new(value)
}
fn frame(count: usize) -> Inst {
    Inst::OpenFrame {
        def: BindingFrameDef::new(
            BindingFrameId::new(71),
            "frame",
            (0..count)
                .map(|index| BindingSlot::new(index.to_string(), Ty::Tuple(vec![Ty::U32])))
                .collect(),
        ),
    }
}
fn dialect(types: usize) -> Inst {
    let mut op = DialectInst::new("observed", "query");
    op.result_tys = vec![Ty::U8; types];
    Inst::DialectOp(Box::new(op))
}
fn node(inst: Inst, values: &[u32]) -> InstrNode {
    InstrNode::new(inst).with_results(values.iter().copied().map(id))
}
fn function(nodes: Vec<InstrNode>) -> Function {
    let mut f = Function::new(FuncId::new(71), "query", FuncTyId::new(0), b(0));
    let mut block = Block::new(b(0));
    block.body = nodes;
    f.blocks.push(block);
    f
}
fn fixture() -> Function {
    function(vec![node(
        Inst::Undef {
            ty: Ty::Tuple(vec![Ty::Ref(Box::new(Ty::U32)), Ty::Tuple(vec![Ty::Bool])]),
        },
        &[7, 8],
    )])
}
fn run(f: &Function, value: u32) -> (Option<Ty>, Observer) {
    let mut observer = Observer::default();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    let result = function_value_type_observed(f, id(value), &mut session, site()).unwrap();
    assert!(session.first_refusal().is_none());
    assert_eq!(session.remaining_fuel(), InterpretOptions::default().fuel);
    (result, observer)
}
fn parity(f: &Function, value: u32) -> Option<Ty> {
    let (actual, observer) = run(f, value);
    assert_eq!(actual, super::super::value_type(f, id(value)));
    assert!(observer.events.iter().all(|e| e.site == site()));
    assert_eq!(
        observer.events.last().unwrap().phase,
        ExecutionPhase::Publication
    );
    actual
}
