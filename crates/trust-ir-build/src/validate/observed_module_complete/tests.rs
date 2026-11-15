// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Authored source controls only; all remain UNRUN.
use super::super::validate_module_complete;
use super::*;
use trust_ir::interpret::InterpretOptions;
use trust_ir::value::FuncId;
mod cleanup;
mod custody;
mod display_custody;
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
            return Err("original completeness stop");
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
    ExecutionSite::Entry(FuncId::new(127))
}
fn row(symbol: &str, path: Option<&str>, reason: &str) -> UnloweredRow {
    UnloweredRow {
        symbol: symbol.to_owned(),
        display_path: path.map(str::to_owned),
        reason: reason.to_owned(),
    }
}
fn partial(rows: Vec<UnloweredRow>) -> Module {
    let mut module = Module::new("strict-claim");
    module.completeness = Some(ModuleCompleteness::Partial(rows));
    module
}
fn run(module: &Module) -> (Result<(), CompletenessError>, Observer) {
    let mut observer = Observer::default();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    let result = validate_module_complete_observed(module, &mut session, site()).unwrap();
    assert_eq!(result, validate_module_complete(module));
    assert!(session.first_refusal().is_none());
    assert_eq!(session.remaining_fuel(), InterpretOptions::default().fuel);
    assert!(observer.events.iter().all(|e| e.site == site()));
    assert_eq!(
        observer.events.last().unwrap().phase,
        ExecutionPhase::Publication
    );
    (result, observer)
}
fn text(error: &CompletenessError) -> (String, Observer) {
    let mut observer = Observer::default();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    let result = error.display_observed(&mut session, site()).unwrap();
    assert_eq!(result, error.to_string());
    assert!(session.first_refusal().is_none());
    assert_eq!(session.remaining_fuel(), InterpretOptions::default().fuel);
    assert!(observer.events.iter().all(|e| e.site == site()));
    (result, observer)
}
fn retired(error: CompletenessError) -> Observer {
    let mut observer = Observer::default();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    error.retire_observed(&mut session, site()).unwrap();
    assert!(session.first_refusal().is_none());
    observer
}
fn drain(state: &mut State, work: &mut Work<'_, '_, impl ExecutionObserver>) {
    state.retire_scratch(work);
    retirement::outcome(core::mem::replace(&mut state.outcome, Ok(())), work);
}
fn empty(state: &State) -> bool {
    state.symbol.capacity() == 0
        && state.path.is_none()
        && state.reason.capacity() == 0
        && state.rows.capacity() == 0
        && state.outcome.is_ok()
}
