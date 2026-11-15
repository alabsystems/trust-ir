// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! Source-authored controls; every Rust control is UNRUN.
use super::*;
use trust_ir::inst::{AssertKind, PanicLocation, PanicSite, SwitchCase};
use trust_ir::interpret::InterpretOptions;
use trust_ir::{Block, FuncTyId, InstrNode, TyId};
mod parity;
mod stops;

#[derive(Default)]
struct Observer {
    events: Vec<ExecutionProgress>,
    stop_at: Option<usize>,
    stop_phase: Option<ExecutionPhase>,
    work: usize,
    bytes: usize,
    work_cap: Option<usize>,
    byte_cap: Option<usize>,
}
impl ExecutionObserver for Observer {
    type Refusal = &'static str;
    fn admit(&mut self, event: ExecutionProgress) -> Result<(), Self::Refusal> {
        self.events.push(event);
        if self.stop_at == Some(self.events.len()) || self.stop_phase == Some(event.phase) {
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
    ExecutionSite::Entry(FuncId::new(107))
}
fn v(id: u32) -> ValueId {
    ValueId::new(id)
}
fn ids(values: &[u32]) -> Vec<ValueId> {
    values.iter().copied().map(v).collect()
}
fn block(id: u32, nodes: Vec<InstrNode>) -> Block {
    let mut block = Block::new(BlockId::new(id));
    block.body = nodes;
    block
}
fn function(blocks: Vec<Block>) -> Function {
    let mut function = Function::new(
        FuncId::new(107),
        "information_flow",
        FuncTyId::new(0),
        BlockId::new(0),
    );
    function.blocks = blocks;
    function
}
fn seed(id: u32) -> InstrNode {
    InstrNode::new(Inst::Const {
        ty: Ty::U32,
        value: Constant::Int(0),
    })
    .with_result(v(id))
    .with_proof(ProofAnnotation::Tainted)
}
fn copy(operand: u32, result: u32) -> InstrNode {
    InstrNode::new(Inst::Copy {
        ty: Ty::U32,
        operand: v(operand),
    })
    .with_result(v(result))
}
fn sink(values: &[u32]) -> InstrNode {
    InstrNode::new(Inst::Return {
        values: ids(values),
    })
    .with_proof(ProofAnnotation::TrustedSink)
}
fn fixture() -> Function {
    function(vec![
        block(
            7,
            vec![
                sink(&[4, 1, 4, 99]),
                copy(3, 4),
                copy(2, 3),
                copy(1, 2),
                seed(1),
            ],
        ),
        block(2, vec![sink(&[2, 1]), copy(4, 1)]),
    ])
}
fn errors(pairs: &[(u32, u32)]) -> Vec<ValidationError> {
    pairs
        .iter()
        .map(|&(block, value)| ValidationError::TaintedValueReachesTrustedSink { block, value })
        .collect()
}
fn observed(function: &Function) -> (Vec<ValidationError>, Observer) {
    let mut observer = Observer::default();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    let actual =
        validate_function_information_flow_observed(function, &mut session, site()).unwrap();
    assert!(session.first_refusal().is_none());
    assert_eq!(session.remaining_fuel(), InterpretOptions::default().fuel);
    (actual, observer)
}
fn parity(function: &Function) -> Vec<ValidationError> {
    let (actual, observer) = observed(function);
    assert_eq!(actual, validate_information_flow(function));
    assert!(observer.events.iter().all(|event| event.site == site()));
    assert_eq!(
        observer.events.last().unwrap().phase,
        ExecutionPhase::Publication
    );
    actual
}
