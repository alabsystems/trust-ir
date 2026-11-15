// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Authored UNRUN. Actual ordinary full-module output filtered ONLY for this
//! exact diagnostic family; other original errors are never called success.
#![allow(
    clippy::drop_non_drop,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
use std::{cell::Cell, rc::Rc};
use trust_ir::interpret::InterpretOptions;
use trust_ir::value::{FuncTyId, PredId, TyId};
use trust_ir::{Block, InstrNode};
mod custody;
mod parity;
mod stops;
#[derive(Default)]
pub(super) struct Observer {
    pub(super) events: Vec<ExecutionProgress>,
    pub(super) calls: Rc<Cell<usize>>,
    pub(super) work: Rc<Cell<usize>>,
    pub(super) bytes: Rc<Cell<usize>>,
    pub(super) stop: Option<usize>,
    pub(super) cleanup_after: Option<usize>,
    pub(super) work_cap: Option<usize>,
    pub(super) byte_cap: Option<usize>,
}
impl ExecutionObserver for Observer {
    type Refusal = &'static str;
    fn admit(&mut self, e: ExecutionProgress) -> Result<(), Self::Refusal> {
        self.events.push(e);
        self.calls.set(self.events.len());
        if self.stop == Some(self.events.len()) {
            return Err("original entry parameter stop");
        }
        if e.phase == ExecutionPhase::ScratchRetirement
            && self.cleanup_after.is_some_and(|n| self.events.len() > n)
        {
            return Err("cleanup");
        }
        self.work
            .set(self.work.get().checked_add(e.work).ok_or("overflow")?);
        self.bytes.set(
            self.bytes
                .get()
                .checked_add(e.copy_bytes)
                .ok_or("overflow")?,
        );
        if self.work_cap.is_some_and(|n| self.work.get() > n) {
            return Err("work");
        }
        if self.byte_cap.is_some_and(|n| self.bytes.get() > n) {
            return Err("copy");
        }
        Ok(())
    }
}

fn site() -> ExecutionSite {
    ExecutionSite::Entry(FuncId::new(1103))
}
fn fixture() -> (Module, Function) {
    let mut m = Module::new("");
    m.types = vec![Ty::Bool];
    m.func_types = vec![FuncTy::unrecorded(vec![Ty::Bool, Ty::U64], vec![], false)];
    let mut f = Function::new(FuncId::new(1103), "F", FuncTyId::new(0), BlockId::new(1));
    let mut b = Block::new(f.entry);
    b.params = vec![(ValueId::new(0), Ty::Bool), (ValueId::new(1), Ty::U64)];
    b.body.push(InstrNode::new(Inst::Return { values: vec![] }));
    f.blocks.push(b);
    (m, f)
}
fn run(m: &Module, f: &Function) -> (Vec<ValidationError>, Observer, usize) {
    let mut ordinary = m.clone();
    ordinary.functions = vec![f.clone()];
    let expected: Vec<_> = super::super::validate_module(&ordinary)
        .into_iter()
        .filter(|e| matches!(e, ValidationError::EntryParamsMismatch { .. }))
        .collect();
    let mut o = Observer::default();
    let calls = o.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let out = validate_entry_params_observed(m, f, &mut s, site()).unwrap();
    let end = calls.get();
    assert_eq!(out, expected);
    retire_validation_errors_observed(out, &mut s, site()).unwrap();
    assert!(s.first_refusal().is_none());
    assert_eq!(s.remaining_fuel(), InterpretOptions::default().fuel);
    drop(s);
    assert!(o.events.iter().all(|e| e.site == site()));
    (expected, o, end)
}
fn mismatch() -> (Module, Function) {
    let (m, mut f) = fixture();
    f.blocks[0].params[1].1 = Ty::Tuple(vec![Ty::handle("Name", "rt::Name"), Ty::Bool]);
    (m, f)
}
fn empty(state: &State) -> bool {
    state.render.capacity() == 0
        && state.name.capacity() == 0
        && state.expected.capacity() == 0
        && state.actual.capacity() == 0
        && state.errors.capacity() == 0
}
fn drain<O: ExecutionObserver>(state: &mut State, work: &mut Work<'_, '_, O>) {
    state.retire_scratch(work);
    let _ = retire_validation_errors_observed(take(&mut state.errors), work.session, work.site);
}
