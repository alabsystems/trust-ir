// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//! Authored controls, all UNRUN.
use super::*;
use std::{cell::Cell, rc::Rc};
use trust_ir::interpret::InterpretOptions;
use trust_ir::value::{BlockId, FuncId, FuncTyId};
use trust_ir::{Block, CallingConv, FuncTy, InstrNode, Module, PanicLocation, PanicSite, Producer};
mod fixtures;
mod parity;
mod stops;
use fixtures::*;

#[derive(Default)]
struct Observer {
    events: Vec<ExecutionProgress>,
    count: Rc<Cell<usize>>,
    stop: Option<usize>,
    work: usize,
    bytes: usize,
    work_cap: Option<usize>,
    byte_cap: Option<usize>,
    retire_stop: Option<Rc<Cell<bool>>>,
}
impl ExecutionObserver for Observer {
    type Refusal = &'static str;
    fn admit(&mut self, event: ExecutionProgress) -> Result<(), Self::Refusal> {
        self.events.push(event);
        self.count.set(self.events.len());
        if self.stop == Some(self.events.len()) {
            return Err("original claim stop");
        }
        if event.phase == ExecutionPhase::ScratchRetirement
            && self.retire_stop.as_ref().is_some_and(|arm| arm.get())
        {
            return Err("original claim retirement");
        }
        self.work = self.work.checked_add(event.work).ok_or("overflow")?;
        self.bytes = self.bytes.checked_add(event.copy_bytes).ok_or("overflow")?;
        if self.work_cap.is_some_and(|limit| self.work > limit) {
            return Err("work");
        }
        if self.byte_cap.is_some_and(|limit| self.bytes > limit) {
            return Err("bytes");
        }
        Ok(())
    }
}
fn site() -> ExecutionSite {
    ExecutionSite::Entry(FuncId::new(191))
}
fn run(function: &Function, module: Option<&Module>) -> (Vec<ValidationError>, Observer, usize) {
    let mut observer = Observer::default();
    let count = observer.count.clone();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    let types = match module {
        None => super::super::build_function_value_types_observed(function, &mut session, site()),
        Some(module) => {
            super::super::build_module_value_types_observed(function, module, &mut session, site())
        }
    }
    .unwrap();
    let prefix = count.get();
    let errors =
        validate_function_borrow_structure_observed(function, &types, &mut session, site())
            .unwrap();
    assert!(session.first_refusal().is_none());
    assert_eq!(session.remaining_fuel(), InterpretOptions::default().fuel);
    // Successful input/context disposal is caller-owned, not subject evidence.
    (errors, observer, prefix)
}
fn parity(function: &Function) -> Vec<ValidationError> {
    let (errors, observer, prefix) = run(function, None);
    let ordinary = super::super::build_function_value_types(function);
    assert_eq!(
        errors,
        super::super::claims::validate_borrow_structure(function, &ordinary)
    );
    assert!(
        observer
            .events
            .iter()
            .skip(prefix)
            .all(|event| event.site == site())
    );
    assert_eq!(
        observer.events.last().unwrap().phase,
        ExecutionPhase::Publication
    );
    errors
}
fn reference_parity(function: &Function) -> Vec<ValidationError> {
    let mut observer = Observer::default();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    let errors =
        validate_function_rust_reference_spelling_observed(function, &mut session, site()).unwrap();
    assert!(session.first_refusal().is_none());
    assert_eq!(
        errors,
        super::super::claims::validate_rust_reference_spelling(function)
    );
    errors
}
