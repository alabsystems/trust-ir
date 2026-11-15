// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Authored controls, all UNRUN.
use super::*;
use trust_ir::dialect::DialectInst;
use trust_ir::inst::{
    AllocOrigin, AssertKind, AtomicRMWOp, BindingFrameDef, BindingSlot, FCmpOp, ICmpOp, InstShape,
    Ordering, OverflowOp, PanicLocation, PanicSite, SwitchCase,
};
use trust_ir::interpret::InterpretOptions;
use trust_ir::value::{BindingFrameId, FuncTyId, GlobalId, TyId};
use trust_ir::{Block, InstrNode};
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
}
impl ExecutionObserver for Observer {
    type Refusal = &'static str;
    fn admit(&mut self, event: ExecutionProgress) -> Result<(), Self::Refusal> {
        self.events.push(event);
        if self.stop == Some(self.events.len()) {
            return Err("original count stop");
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
    ExecutionSite::Entry(FuncId::new(77))
}
fn v() -> ValueId {
    ValueId::new(0)
}
fn b(id: u32) -> BlockId {
    BlockId::new(id)
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
fn dialect(count: usize) -> Inst {
    let mut op = DialectInst::new("observed", "types");
    op.result_tys = vec![Ty::U8; count];
    Inst::DialectOp(Box::new(op))
}
fn node(inst: Inst, count: usize) -> InstrNode {
    InstrNode::new(inst).with_results((0..count).map(|id| ValueId::new(id as u32)))
}
fn module(nodes: Vec<InstrNode>) -> Module {
    let mut module = Module::new("arities");
    let mut function = Function::new(FuncId::new(77), "caller", FuncTyId::new(0), b(0));
    let mut block = Block::new(b(0));
    block.body = nodes;
    function.blocks.push(block);
    module.functions.push(function);
    module
}
fn fixture() -> Module {
    module(vec![
        node(Inst::Undef { ty: Ty::U32 }, 0),
        node(
            Inst::LandingPad {
                is_cleanup: true,
                catch_type_indices: vec![],
            },
            1,
        ),
        node(Inst::Return { values: vec![] }, 2),
        node(dialect(3), 4),
    ])
}
fn run(module: &Module) -> (Vec<ValidationError>, Observer) {
    let mut observer = Observer::default();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    let result = validate_module_result_arities_observed(module, &mut session, site()).unwrap();
    assert!(session.first_refusal().is_none());
    assert_eq!(session.remaining_fuel(), InterpretOptions::default().fuel);
    (result, observer)
}
fn parity(module: &Module) -> Vec<ValidationError> {
    let (actual, observer) = run(module);
    assert_eq!(actual, validate_instruction_result_arities(module));
    assert!(observer.events.iter().all(|event| event.site == site()));
    assert_eq!(
        observer.events.last().unwrap().phase,
        ExecutionPhase::Publication
    );
    actual
}
