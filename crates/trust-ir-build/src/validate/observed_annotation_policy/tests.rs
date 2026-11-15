// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Authored source controls, UNRUN.
use super::*;
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
#[derive(Clone, Copy)]
enum Case {
    Memory,
    Havoc,
}
fn site() -> ExecutionSite {
    ExecutionSite::Entry(FuncId::new(95))
}
fn function(nodes: Vec<InstrNode>) -> Function {
    let mut function = Function::new(
        FuncId::new(95),
        "raw'λ\nfunction",
        FuncTyId::new(0),
        BlockId::new(0),
    );
    let mut block = Block::new(BlockId::new(0));
    block.body = nodes;
    function.blocks = vec![block];
    function
}
fn fixture() -> Function {
    let mut node = InstrNode::new(Inst::NullPtr).with_result(ValueId::new(7));
    node.proofs = vec![
        ProofAnnotation::ReadonlyTable,
        ProofAnnotation::AtomicSetInsert,
        ProofAnnotation::FreshSymbolicHavoc,
        ProofAnnotation::RegionHavocStore,
    ];
    let mut f = function(vec![node]);
    f.name = "λ".repeat(3000);
    f.proofs = vec![
        ProofAnnotation::ReadonlyTable,
        ProofAnnotation::AppendOnlyBuffer,
        ProofAnnotation::FreshSymbolicHavoc,
        ProofAnnotation::RegionHavocStore,
    ];
    f
}
fn run(
    f: &Function,
    case: Case,
    session: &mut ObservedSession<'_, Observer>,
) -> R<Vec<ValidationError>> {
    match case {
        Case::Memory => validate_function_memory_roles_observed(f, session, site()),
        Case::Havoc => validate_function_havoc_placement_observed(f, session, site()),
    }
}
fn ordinary(f: &Function, case: Case) -> Vec<ValidationError> {
    match case {
        Case::Memory => validate_memory_roles(f),
        Case::Havoc => validate_havoc_marker_placement(f),
    }
}
fn observed(f: &Function, case: Case) -> (Vec<ValidationError>, Observer) {
    let mut observer = Observer::default();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    let errors = run(f, case, &mut session).unwrap();
    assert!(session.first_refusal().is_none());
    assert_eq!(session.remaining_fuel(), InterpretOptions::default().fuel);
    (errors, observer)
}
fn parity(f: &Function, case: Case) -> Vec<ValidationError> {
    let (actual, observer) = observed(f, case);
    assert_eq!(actual, ordinary(f, case));
    assert!(observer.events.iter().all(|event| event.site == site()));
    assert_eq!(
        observer.events.last().unwrap().phase,
        ExecutionPhase::Publication
    );
    actual
}
