// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Authored source controls only; every Rust control remains UNRUN.
use super::*;
use trust_ir::interpret::InterpretOptions;
use trust_ir::value::{BlockId, FuncId, FuncTyId};
mod custody;
mod fixtures;
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
    cleanup: bool,
}
impl ExecutionObserver for Observer {
    type Refusal = &'static str;
    fn admit(&mut self, event: ExecutionProgress) -> Result<(), Self::Refusal> {
        self.events.push(event);
        if self.stop == Some(self.events.len()) {
            return Err("original symbol stop");
        }
        if self.cleanup && event.phase == ExecutionPhase::ScratchRetirement {
            return Err("cleanup stop");
        }
        self.work = self.work.checked_add(event.work).ok_or("work overflow")?;
        self.bytes = self
            .bytes
            .checked_add(event.copy_bytes)
            .ok_or("copy overflow")?;
        if self.work_cap.is_some_and(|n| self.work > n) {
            return Err("work cap");
        }
        if self.byte_cap.is_some_and(|n| self.bytes > n) {
            return Err("copy cap");
        }
        Ok(())
    }
}
fn site() -> ExecutionSite {
    ExecutionSite::Entry(FuncId::new(129))
}
fn function(id: u32, name: &str) -> Function {
    Function::new(FuncId::new(id), name, FuncTyId::new(0), BlockId::new(0))
}
fn module(functions: Vec<Function>) -> Module {
    let mut module = Module::new("function-symbols");
    module.functions = functions;
    module
}
fn run(module: &Module) -> (Vec<ValidationError>, Observer) {
    let mut observer = Observer::default();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    let result = validate_module_function_symbols_observed(module, &mut session, site()).unwrap();
    assert_eq!(result, fixtures::ordinary(module));
    assert!(session.first_refusal().is_none());
    assert_eq!(session.remaining_fuel(), InterpretOptions::default().fuel);
    assert!(observer.events.iter().all(|e| e.site == site()));
    assert_eq!(
        observer.events.last().unwrap().phase,
        ExecutionPhase::Publication
    );
    (result, observer)
}
fn drain(state: &mut State, work: &mut Work<'_, '_, impl ExecutionObserver>) {
    state.retire_pending(work);
    let _ = retire_validation_errors_observed(take(&mut state.errors), work.session, work.site);
}
fn empty(state: &State) -> bool {
    state.name.capacity() == 0
        && state.first_producer.is_none()
        && state.second_producer.is_none()
        && state.first_path.is_none()
        && state.second_path.is_none()
        && state.errors.capacity() == 0
}
