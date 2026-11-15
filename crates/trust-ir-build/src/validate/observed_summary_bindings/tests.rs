// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Authored UNRUN; exact complete original first loop is the oracle.
use super::*;
use std::{cell::Cell, rc::Rc};
use trust_ir::interpret::{InstructionSite, InterpretOptions};
use trust_ir::value::FuncTyId;
use trust_ir::{Block, InstrNode};
mod oracle;
mod parity;
mod stops;
mod types;
#[derive(Default)]
struct Observer {
    events: Vec<ExecutionProgress>,
    stop: Option<usize>,
    work: usize,
    bytes: usize,
    work_cap: Option<usize>,
    byte_cap: Option<usize>,
    cleanup: Option<Rc<Cell<bool>>>,
}
impl ExecutionObserver for Observer {
    type Refusal = &'static str;
    fn admit(&mut self, e: ExecutionProgress) -> Result<(), Self::Refusal> {
        self.events.push(e);
        if self.stop == Some(self.events.len()) {
            return Err("original binding stop");
        }
        if self.cleanup.as_ref().is_some_and(|arm| arm.get())
            && e.phase == ExecutionPhase::ScratchRetirement
        {
            return Err("cleanup");
        }
        self.work = self.work.checked_add(e.work).ok_or("work overflow")?;
        self.bytes = self
            .bytes
            .checked_add(e.copy_bytes)
            .ok_or("copy overflow")?;
        if self.work_cap.is_some_and(|cap| self.work > cap) {
            return Err("work");
        }
        if self.byte_cap.is_some_and(|cap| self.bytes > cap) {
            return Err("copy");
        }
        Ok(())
    }
}
fn site() -> ExecutionSite {
    ExecutionSite::Entry(FuncId::new(190))
}
fn v(id: u32) -> ValueId {
    ValueId::new(id)
}
fn clause(sort: ClauseSort, place: ClausePlace) -> ProofFormula {
    let mut c = ProofFormula::new("opaque", "not parsed");
    c.bindings.push(("x".into(), ClauseBinding { sort, place }));
    c
}
fn fixture() -> (Module, Function, FunctionSummary) {
    let mut m = Module::new("summary");
    m.func_types.push(FuncTy::unrecorded(
        vec![
            Ty::U8,
            Ty::RefMut(Box::new(Ty::U16)),
            Ty::Ref(Box::new(Ty::Bool)),
            Ty::PtrMut(Box::new(Ty::I32)),
        ],
        vec![Ty::Bool],
        false,
    ));
    let mut f = Function::new(FuncId::new(7), "f", FuncTyId::new(0), BlockId::new(0));
    let mut b = Block::new(BlockId::new(0));
    b.params.push((v(4), Ty::U32));
    b.body.push(
        InstrNode::new(Inst::Copy {
            ty: Ty::Bool,
            operand: v(4),
        })
        .with_results([v(5)]),
    );
    f.blocks.push(b);
    m.functions.push(f.clone());
    (m, f, FunctionSummary::new())
}
fn with_role(summary: &mut FunctionSummary, role: usize, c: ProofFormula) {
    match role {
        0 => summary.requires.push(c),
        1 => summary.ensures.push(c),
        _ => summary.decreases.push(c),
    }
}
fn run(m: &Module, f: &Function, summary: &FunctionSummary) -> (Vec<ValidationError>, Observer) {
    let mut o = Observer::default();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let actual =
        validate_function_summary_bindings_observed(m, f, summary, &mut s, site()).unwrap();
    assert_eq!(actual, oracle::oracle(m, f, summary));
    assert!(s.first_refusal().is_none());
    assert_eq!(s.remaining_fuel(), InterpretOptions::default().fuel);
    assert!(o.events.iter().all(|e| e.site == site()));
    assert_eq!(o.events.last().unwrap().phase, ExecutionPhase::Publication);
    (actual, o)
}
fn raw_trace(m: &Module, f: &Function, summary: &FunctionSummary) -> Observer {
    let mut o = Observer::default();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let mut w = Work {
        session: &mut s,
        site: site(),
    };
    let mut state = State::default();
    state.walk(m, f, summary, &mut w).unwrap();
    assert_eq!(state.errors, oracle::oracle(m, f, summary));
    let out = state.finish(Ok(()), &mut w).unwrap();
    assert!(empty(&state));
    assert_eq!(out, oracle::oracle(m, f, summary));
    o
}
fn empty(state: &State) -> bool {
    state.detail.capacity() == 0
        && state.render.is_none()
        && state.values.is_none()
        && state.errors.capacity() == 0
}
fn bad() -> (Module, Function, FunctionSummary) {
    let (m, f, mut s) = fixture();
    s.requires
        .push(clause(ClauseSort::Int, ClausePlace::Param { index: 2 }));
    (m, f, s)
}
