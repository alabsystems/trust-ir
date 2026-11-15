// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Authored UNRUN source controls, no execution evidence.
use super::*;
use trust_ir::imports::IdentityScheme;
use trust_ir::interpret::InterpretOptions;
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
            return Err("original import stop");
        }
        if self.cleanup && event.phase == ExecutionPhase::ScratchRetirement {
            return Err("original cleanup");
        }
        self.work = self.work.checked_add(event.work).ok_or("overflow")?;
        self.bytes = self.bytes.checked_add(event.copy_bytes).ok_or("overflow")?;
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
    ExecutionSite::Entry(FuncId::new(124))
}
fn row(name: &str) -> ModuleImport {
    ModuleImport::new(name, trust_ir::ProofDigest::sha256([1; 32]))
}
fn fixture() -> Module {
    let mut m = Module::new("imports");
    m.imports = vec![row("a"), row("a"), row("b"), row("b")];
    m
}
fn run(m: &Module) -> (Vec<ValidationError>, Observer) {
    let mut o = Observer::default();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let result = validate_module_imports_observed(m, &mut s, site()).unwrap();
    assert!(s.first_refusal().is_none());
    assert_eq!(s.remaining_fuel(), InterpretOptions::default().fuel);
    let mut expected = validate_import_table_interned(m);
    expected.extend(validate_import_identity(m));
    assert_eq!(result, expected);
    assert!(o.events.iter().all(|e| e.site == site()));
    assert_eq!(o.events.last().unwrap().phase, ExecutionPhase::Publication);
    (result, o)
}
fn drain(state: &mut State, work: &mut Work<'_, '_, impl ExecutionObserver>) {
    state.retire_text(work);
    let _ = retire_validation_errors_observed(take(&mut state.errors), work.session, work.site);
}
fn empty(state: &State) -> bool {
    state.first.capacity() == 0 && state.second.capacity() == 0 && state.errors.capacity() == 0
}
