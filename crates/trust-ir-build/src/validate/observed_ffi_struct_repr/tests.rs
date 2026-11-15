// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Authored UNRUN controls; parity uses the unchanged ordinary validators.
use super::*;
use std::{cell::Cell, rc::Rc};
use trust_ir::Block;
use trust_ir::interpret::InterpretOptions;
use trust_ir::value::{FuncTyId, PredId, StructId, TyId};
mod custody;
mod fixtures;
mod parity;
mod stops;
use fixtures::{fixture, function, linkages, strukt};

#[derive(Clone, Copy)]
enum Rule {
    Ffi,
    Vararg,
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
    fn admit(&mut self, event: ExecutionProgress) -> Result<(), Self::Refusal> {
        self.events.push(event);
        if self.stop == Some(self.events.len()) {
            return Err("original ABI stop");
        }
        if self.cleanup.as_ref().is_some_and(|arm| arm.get())
            && event.phase == ExecutionPhase::ScratchRetirement
        {
            return Err("cleanup");
        }
        self.work = self.work.checked_add(event.work).ok_or("work overflow")?;
        self.bytes = self
            .bytes
            .checked_add(event.copy_bytes)
            .ok_or("bytes overflow")?;
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
    ExecutionSite::Entry(FuncId::new(132))
}
fn call<O: ExecutionObserver>(
    module: &Module,
    function: &Function,
    rule: Rule,
    session: &mut ObservedSession<'_, O>,
) -> R<Vec<ValidationError>> {
    match rule {
        Rule::Ffi => validate_module_ffi_struct_repr_observed(module, session, site()),
        Rule::Vararg => {
            validate_function_rust_abi_is_not_variadic_observed(module, function, session, site())
        }
    }
}
fn raw<O: ExecutionObserver>(
    state: &mut State,
    module: &Module,
    function: &Function,
    rule: Rule,
    work: &mut Work<'_, '_, O>,
) -> R {
    match rule {
        Rule::Ffi => state.ffi(module, work),
        Rule::Vararg => state.vararg(module, function, work),
    }
}
fn oracle(module: &Module, function: &Function, rule: Rule) -> Vec<ValidationError> {
    match rule {
        Rule::Ffi => validate_ffi_struct_repr(module),
        Rule::Vararg => validate_rust_abi_is_not_variadic(module, function),
    }
}
fn run(module: &Module, function: &Function, rule: Rule) -> (Vec<ValidationError>, Observer) {
    let mut observer = Observer::default();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    let out = call(module, function, rule, &mut session).unwrap();
    assert_eq!(out, oracle(module, function, rule));
    assert!(session.first_refusal().is_none());
    assert_eq!(session.remaining_fuel(), InterpretOptions::default().fuel);
    assert!(observer.events.iter().all(|event| event.site == site()));
    assert_eq!(
        observer.events.last().unwrap().phase,
        ExecutionPhase::Publication
    );
    (out, observer)
}
fn drain<O: ExecutionObserver>(state: &mut State, work: &mut Work<'_, '_, O>) {
    state.retire_scratch(work);
    let _ = retire_validation_errors_observed(take(&mut state.errors), work.session, work.site);
}
fn private_trace(module: &Module, function: &Function, rule: Rule) -> Observer {
    // All private-state ordinal replays use this identical raw entry path,
    // without the public wrapper's additional initial-header callback.
    let mut observer = Observer::default();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    let mut work = Work {
        session: &mut session,
        site: site(),
    };
    let mut state = State::default();
    raw(&mut state, module, function, rule, &mut work).unwrap();
    assert_eq!(state.errors, oracle(module, function, rule));
    drain(&mut state, &mut work);
    assert!(empty(&state));
    observer
}
fn empty(state: &State) -> bool {
    state.reprs.capacity() == 0
        && state.name.capacity() == 0
        && state.detail.capacity() == 0
        && state.errors.capacity() == 0
}
