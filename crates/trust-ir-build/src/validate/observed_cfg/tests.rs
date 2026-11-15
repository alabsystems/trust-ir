// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Source-authored Rust controls, UNRUN.
use super::*;
use trust_ir::inst::{AssertKind, PanicLocation, PanicSite, SwitchCase};
use trust_ir::interpret::InterpretOptions;
use trust_ir::{Block, FuncTyId, InstrNode};
mod parity;
mod stops;
#[derive(Default)]
struct Observer {
    events: Vec<ExecutionProgress>,
    stop_at: Option<usize>,
    work: usize,
    bytes: usize,
    work_cap: Option<usize>,
    byte_cap: Option<usize>,
}
impl ExecutionObserver for Observer {
    type Refusal = &'static str;
    fn admit(&mut self, event: ExecutionProgress) -> Result<(), Self::Refusal> {
        self.events.push(event);
        if self.stop_at == Some(self.events.len()) {
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
    ExecutionSite::Entry(FuncId::new(92))
}
fn block(id: u32, instruction: Inst) -> Block {
    let mut block = Block::new(BlockId::new(id));
    block.body.push(InstrNode::new(instruction));
    block
}
fn function(blocks: Vec<Block>, entry: u32) -> Function {
    let mut function = Function::new(
        FuncId::new(92),
        "cfg",
        FuncTyId::new(0),
        BlockId::new(entry),
    );
    function.blocks = blocks;
    function
}
fn return_block(id: u32) -> Block {
    block(id, Inst::Return { values: vec![] })
}
fn branch(id: u32, target: u32) -> Block {
    block(
        id,
        Inst::Br {
            target: BlockId::new(target),
            args: vec![],
        },
    )
}
fn switch(cases: Vec<Constant>, targets: Vec<u32>, default: u32) -> Inst {
    Inst::Switch {
        value: ValueId::new(0),
        default: BlockId::new(default),
        default_args: vec![],
        cases: cases
            .into_iter()
            .zip(targets)
            .map(|(value, target)| SwitchCase {
                value,
                target: BlockId::new(target),
                args: vec![],
            })
            .collect(),
        exhaustive_enum_unreachable: false,
    }
}
fn fixture() -> Function {
    function(
        vec![
            block(
                0,
                switch(
                    vec![Constant::Int(0), Constant::U128(0), Constant::Int(1)],
                    vec![8, 7, 1],
                    99,
                ),
            ),
            branch(1, 0),
            return_block(2),
            branch(0, 3),
            return_block(3),
        ],
        0,
    )
}
fn ordinary(function: &Function) -> Vec<ValidationError> {
    let ids = function
        .blocks
        .iter()
        .map(|block| block.id.index())
        .collect();
    validate_control_flow(function, &ids)
}
fn observed(function: &Function) -> (Vec<ValidationError>, Observer) {
    let mut observer = Observer::default();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    let errors = validate_function_control_flow_observed(function, &mut session, site()).unwrap();
    assert!(session.first_refusal().is_none());
    assert_eq!(session.remaining_fuel(), InterpretOptions::default().fuel);
    (errors, observer)
}
fn parity(function: &Function) -> Vec<ValidationError> {
    let (actual, observer) = observed(function);
    assert_eq!(actual, ordinary(function));
    assert!(observer.events.iter().all(|event| event.site == site()));
    assert_eq!(
        observer.events.last().unwrap().phase,
        ExecutionPhase::Publication
    );
    actual
}
