// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Source-authored controls, UNRUN.
use super::*;
use trust_ir::inst::{AssertKind, PanicLocation, PanicSite};
use trust_ir::interpret::InterpretOptions;
use trust_ir::{Block, FuncTyId, InstrNode};
mod parity;
mod stops;
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
            return Err("original stop");
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
    ExecutionSite::Entry(FuncId::new(97))
}
fn function(blocks: Vec<Block>) -> Function {
    let mut f = Function::new(FuncId::new(97), "ssa", FuncTyId::new(0), BlockId::new(0));
    f.blocks = blocks;
    f
}
fn block(id: u32, body: Vec<InstrNode>) -> Block {
    let mut block = Block::new(BlockId::new(id));
    block.body = body;
    block
}
fn copy(value: u32, result: u32) -> InstrNode {
    InstrNode::new(Inst::Copy {
        ty: Ty::Bool,
        operand: ValueId::new(value),
    })
    .with_result(ValueId::new(result))
}
fn branch(target: u32, args: &[u32]) -> InstrNode {
    InstrNode::new(Inst::Br {
        target: BlockId::new(target),
        args: args.iter().copied().map(ValueId::new).collect(),
    })
}
fn ret(values: &[u32]) -> InstrNode {
    InstrNode::new(Inst::Return {
        values: values.iter().copied().map(ValueId::new).collect(),
    })
}
fn fixture() -> Function {
    let entry = block(
        0,
        vec![
            copy(99, 1),
            copy(2, 2),
            InstrNode::new(Inst::NullPtr).with_result(ValueId::new(0)),
            branch(1, &[1, 1]),
        ],
    )
    .with_param(ValueId::new(0), Ty::Bool);
    function(vec![
        entry,
        block(1, vec![ret(&[2])]),
        block(2, vec![copy(777, 5), ret(&[5])]),
    ])
}
fn ordinary(f: &Function) -> Vec<ValidationError> {
    let analysis = StaticFunctionPointerAnalysis::new(f);
    validate_ssa(f, &analysis)
}
fn observed(f: &Function) -> (Vec<ValidationError>, Observer) {
    let mut observer = Observer::default();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    let errors = validate_function_ssa_observed(f, &mut session, site()).unwrap();
    assert!(session.first_refusal().is_none());
    assert_eq!(session.remaining_fuel(), InterpretOptions::default().fuel);
    (errors, observer)
}
fn parity(f: &Function) -> Vec<ValidationError> {
    let (actual, observer) = observed(f);
    assert_eq!(actual, ordinary(f));
    assert!(observer.events.iter().all(|event| event.site == site()));
    assert_eq!(
        observer.events.last().unwrap().phase,
        ExecutionPhase::Publication
    );
    actual
}
