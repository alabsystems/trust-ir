// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Authored UNRUN; exact ordinary namespace/key functions are the oracle.
use super::*;
use std::{cell::Cell, rc::Rc};
use trust_ir::interpret::InterpretOptions;
use trust_ir::value::FuncTyId;
mod fixtures;
mod parity;
mod stops;
use fixtures::*;
#[derive(Clone, Copy)]
enum Stage {
    Name,
    Reserved,
}
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
            return Err("original spec reservation stop");
        }
        if self.cleanup.as_ref().is_some_and(|a| a.get())
            && e.phase == ExecutionPhase::ScratchRetirement
        {
            return Err("cleanup");
        }
        self.work = self.work.checked_add(e.work).ok_or("overflow")?;
        self.bytes = self.bytes.checked_add(e.copy_bytes).ok_or("overflow")?;
        if self.work_cap.is_some_and(|n| self.work > n) {
            return Err("work");
        }
        if self.byte_cap.is_some_and(|n| self.bytes > n) {
            return Err("bytes");
        }
        Ok(())
    }
}
fn site() -> ExecutionSite {
    ExecutionSite::Entry(FuncId::new(140))
}
fn call<O: ExecutionObserver>(
    m: &Module,
    stage: Stage,
    s: &mut ObservedSession<'_, O>,
) -> R<Vec<ValidationError>> {
    match stage {
        Stage::Name => validate_module_name_observed(m, s, site()),
        Stage::Reserved => validate_reserved_spec_module_names_observed(m, s, site()),
    }
}
fn oracle(m: &Module, stage: Stage) -> Vec<ValidationError> {
    match stage {
        Stage::Name => {
            if m.name.trim().is_empty() {
                vec![ValidationError::BlankModuleName]
            } else {
                vec![]
            }
        }
        Stage::Reserved => reserved_spec_module_errors(m),
    }
}
fn run(m: &Module, stage: Stage) -> (Vec<ValidationError>, Observer) {
    let mut o = Observer::default();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let out = call(m, stage, &mut s).unwrap();
    assert_eq!(out, oracle(m, stage));
    assert!(s.first_refusal().is_none());
    assert_eq!(s.remaining_fuel(), InterpretOptions::default().fuel);
    assert!(o.events.iter().all(|e| e.site == site()));
    assert_eq!(o.events.last().unwrap().phase, ExecutionPhase::Publication);
    (out, o)
}
fn private_trace(m: &Module) -> Observer {
    let mut o = Observer::default();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let mut work = Work {
        session: &mut s,
        site: site(),
    };
    let mut state = State::default();
    state.run(m, &mut work).unwrap();
    assert_eq!(state.errors, reserved_spec_module_errors(m));
    drain(&mut state, &mut work);
    assert!(empty(&state));
    o
}
fn drain(state: &mut State, work: &mut Work<'_, '_, impl ExecutionObserver>) {
    state.retire_scratch(work);
    let _ = retire_validation_errors_observed(take(&mut state.errors), work.session, work.site);
}
fn empty(s: &State) -> bool {
    s.name.capacity() == 0 && s.detail.capacity() == 0 && s.errors.capacity() == 0
}
fn detail(e: &ValidationError) -> &str {
    match e {
        ValidationError::ReservedSpecModuleName { detail, .. } => detail,
        _ => panic!("wrong variant"),
    }
}
