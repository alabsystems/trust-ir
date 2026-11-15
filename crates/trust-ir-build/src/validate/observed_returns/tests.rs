// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Authored UNRUN; actual original signature getter and check_return_values.
#![allow(
    clippy::drop_non_drop,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::super::observed_value_types::build_module_value_types_observed;
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
            return Err("original return rule stop");
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
    ExecutionSite::Entry(FuncId::new(1109))
}
fn v(id: u32) -> ValueId {
    ValueId::new(id)
}
fn fixture() -> (Module, Function) {
    let mut m = Module::new("");
    m.types = vec![Ty::U64];
    m.func_types = vec![FuncTy::unrecorded(
        vec![Ty::Bool, Ty::U64, Ty::Ptr],
        vec![Ty::U64, Ty::Bool],
        false,
    )];
    let mut f = Function::new(FuncId::new(1109), "F", FuncTyId::new(0), BlockId::new(1));
    let mut b = Block::new(f.entry);
    b.params = vec![(v(0), Ty::Bool), (v(1), Ty::U64), (v(2), Ty::Ptr)];
    b.body.push(InstrNode::new(Inst::Return { values: vec![] }));
    f.blocks.push(b);
    (m, f)
}
fn suspend(value: u32) -> Inst {
    Inst::CoroSuspend {
        frame: v(2),
        state_slot: 0,
        next_state: 1,
        value: v(value),
    }
}
fn setup<'m, O: ExecutionObserver>(
    m: &'m Module,
    f: &Function,
    s: &mut ObservedSession<'_, O>,
) -> (ObservedValueTypes, &'m FuncTy) {
    let values = build_module_value_types_observed(f, m, s, site()).unwrap();
    let signature = function_signature_observed(m, f, s, site())
        .unwrap()
        .unwrap();
    (values, signature)
}
fn run(m: &Module, f: &Function, inst: &Inst) -> (Vec<ValidationError>, Observer, usize, usize) {
    let old = super::super::build_module_value_types(f, m);
    let mut expected = vec![];
    match inst {
        Inst::Return { values } => {
            super::super::check_return_values(1, values, &m.func_types[0], &old, &mut expected)
        }
        Inst::CoroSuspend { value, .. } => {
            super::super::check_return_values(1, &[*value], &m.func_types[0], &old, &mut expected)
        }
        _ => {}
    }
    let mut o = Observer::default();
    let calls = o.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let (values, signature) = setup(m, f, &mut s);
    let begin = calls.get();
    let out =
        validate_return_instruction_observed(inst, signature, &values, f.entry, &mut s, site())
            .unwrap();
    let end = calls.get();
    assert_eq!(out, expected);
    retire_validation_errors_observed(out, &mut s, site()).unwrap();
    values.retire_observed(&mut s, site()).unwrap();
    assert!(s.first_refusal().is_none());
    drop(s);
    assert!(o.events.iter().all(|e| e.site == site()));
    (expected, o, begin, end)
}
fn getter(m: &Module, f: &Function) -> (Result<(), ValidationError>, Observer, usize) {
    let mut expected = vec![];
    let ordinary = super::super::get_func_ty(m, &f.name, f.ty, &mut expected);
    let mut o = Observer::default();
    let calls = o.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let result = function_signature_observed(m, f, &mut s, site()).unwrap();
    let end = calls.get();
    let answer = match (ordinary, result) {
        (Some(old), Ok(actual)) => {
            assert!(core::ptr::eq(old, actual));
            Ok(())
        }
        (None, Err(error)) => {
            assert_eq!(expected, vec![error.clone()]);
            retire_validation_error_observed(error, &mut s, site()).unwrap();
            Err(expected.pop().unwrap())
        }
        _ => panic!("same exact original lookup"),
    };
    assert!(s.first_refusal().is_none());
    drop(s);
    (answer, o, end)
}
fn empty(s: &State) -> bool {
    s.expected.capacity() == 0 && s.actual.capacity() == 0 && s.errors.capacity() == 0
}
fn drain<O: ExecutionObserver>(state: &mut State, work: &mut Work<'_, '_, O>) {
    state.retire_scratch(work);
    let _ = retire_validation_errors_observed(take(&mut state.errors), work.session, work.site);
}
