// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Authored UNRUN; complete ordinary effects::validate_effect_summary oracle.
#![allow(
    clippy::drop_non_drop,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
use std::{cell::Cell, rc::Rc};
use trust_ir::dialect::DialectInst;
use trust_ir::inst::{
    AllocOrigin, AtomicRMWOp, BinOp, BindingFrameDef, BindingSlot, CastOp, FCmpOp, ICmpOp,
    Ordering, OverflowOp, PanicLocation, SwitchCase, UnOp,
};
use trust_ir::interpret::{InstructionSite, InterpretOptions};
use trust_ir::value::{BindingFrameId, BlockId, FuncTyId, GlobalId, TyId};
use trust_ir::{Block, Constant, FunctionSummary, InstrNode, Ty};
mod calls;
mod custody;
mod parity;
mod stops;
mod witnesses;
#[derive(Default)]
pub(super) struct Observer {
    pub(super) events: Vec<ExecutionProgress>,
    pub(super) calls: Rc<Cell<usize>>,
    pub(super) stop: Option<usize>,
    pub(super) work: usize,
    pub(super) bytes: usize,
    pub(super) cap: Option<usize>,
    pub(super) byte_cap: Option<usize>,
    pub(super) cleanup: bool,
    pub(super) cleanup_after: Option<usize>,
}
impl ExecutionObserver for Observer {
    type Refusal = &'static str;
    fn admit(&mut self, e: ExecutionProgress) -> Result<(), Self::Refusal> {
        self.events.push(e);
        self.calls.set(self.events.len());
        if self.stop == Some(self.events.len()) {
            return Err("original effects stop");
        }
        if self.cleanup
            && self.cleanup_after.is_none_or(|n| self.events.len() > n)
            && e.phase == ExecutionPhase::ScratchRetirement
        {
            return Err("cleanup");
        }
        self.work = self.work.checked_add(e.work).ok_or("overflow")?;
        self.bytes = self.bytes.checked_add(e.copy_bytes).ok_or("overflow")?;
        if self.cap.is_some_and(|n| self.work > n) {
            return Err("work");
        }
        if self.byte_cap.is_some_and(|n| self.bytes > n) {
            return Err("copy");
        }
        Ok(())
    }
}
pub(super) fn site() -> ExecutionSite {
    ExecutionSite::Entry(FuncId::new(271))
}
fn v(id: u32) -> ValueId {
    ValueId::new(id)
}
fn p(index: u32) -> EffectPlace {
    EffectPlace::ParamPointee { index }
}
fn g(index: u32) -> EffectPlace {
    EffectPlace::Global(GlobalId::new(index))
}
fn node(inst: Inst, results: &[u32]) -> InstrNode {
    InstrNode::new(inst).with_results(results.iter().copied().map(v))
}
fn function(nodes: Vec<InstrNode>) -> Function {
    let mut f = Function::new(FuncId::new(0), "bodyλ\0", FuncTyId::new(0), BlockId::new(0));
    let mut block = Block::new(BlockId::new(0));
    block.params = vec![(v(1), Ty::Ptr), (v(2), Ty::Ptr)];
    block.body = nodes;
    f.blocks.push(block);
    let mut summary = FunctionSummary::new();
    summary.effects = Some(EffectSummary::pure());
    f.summary = Some(summary);
    f
}
fn fixture(nodes: Vec<InstrNode>) -> (Module, Function) {
    let f = function(nodes);
    let mut m = Module::new("effectsλ");
    m.functions.push(f.clone());
    (m, f)
}
fn callee(m: &mut Module, id: u32, effects: EffectSummary, declaration: bool) {
    let mut f = Function::new(
        FuncId::new(id),
        "calleeλ\0",
        FuncTyId::new(0),
        BlockId::new(0),
    );
    if !declaration {
        f.blocks.push(Block::new(BlockId::new(0)))
    }
    let mut summary = FunctionSummary::new();
    summary.effects = Some(effects);
    f.summary = Some(summary);
    m.functions.push(f);
}
fn load(ptr: u32) -> Inst {
    Inst::Load {
        ty: Ty::U32,
        ptr: v(ptr),
        volatile: false,
        align: None,
    }
}
fn store(ptr: u32) -> Inst {
    Inst::Store {
        ty: Ty::U32,
        ptr: v(ptr),
        value: v(2),
        volatile: false,
        align: None,
    }
}
fn alloca() -> Inst {
    Inst::Alloca {
        ty: Ty::U32,
        count: None,
        align: None,
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
fn run(
    m: &Module,
    f: &Function,
    policy: ImportPolicy<'_>,
) -> (Vec<ValidationError>, Observer, usize) {
    let expected = super::super::validate_effect_summary(m, f, policy);
    let mut o = Observer::default();
    let calls = o.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let actual = validate_effect_summary_observed(m, f, policy, &mut s, site()).unwrap();
    assert_eq!(actual, expected);
    let copy = actual.clone();
    let bound = calls.get();
    retire_validation_errors_observed(actual, &mut s, site()).unwrap();
    assert!(s.first_refusal().is_none());
    assert_eq!(s.remaining_fuel(), InterpretOptions::default().fuel);
    drop(s);
    assert!(o.events.iter().all(|e| e.site == site()));
    assert_eq!(o.events[bound - 1].phase, ExecutionPhase::Publication);
    (copy, o, bound)
}
