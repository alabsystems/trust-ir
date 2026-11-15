// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Authored UNRUN controls for the actual original child/parent ownership seam.
#![allow(
    clippy::drop_non_drop,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
use std::{cell::Cell, rc::Rc};
use trust_ir::interpret::InterpretOptions;
use trust_ir::{SpecEnforcementMode, SpecModule, SpecVar};
mod parity;
mod stops;
#[derive(Default)]
struct Observer {
    events: Vec<ExecutionProgress>,
    stop: Option<usize>,
    trigger: Option<Rc<Cell<bool>>>,
    cleanup: Option<Rc<Cell<bool>>>,
    work: usize,
    bytes: usize,
    work_cap: Option<usize>,
    byte_cap: Option<usize>,
}
impl ExecutionObserver for Observer {
    type Refusal = &'static str;
    fn admit(&mut self, e: ExecutionProgress) -> Result<(), Self::Refusal> {
        self.events.push(e);
        if self.stop == Some(self.events.len()) || self.trigger.as_ref().is_some_and(|v| v.get()) {
            return Err("original structural mapping");
        }
        if self.cleanup.as_ref().is_some_and(|v| v.get())
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
    ExecutionSite::Entry(FuncId::new(156))
}
fn input() -> Module {
    let mut m = Module::new("mapping");
    let mut spec = SpecModule::new("M");
    spec.actions = vec!["".into()];
    m.spec_modules.push(spec);
    m
}
fn wrapped(m: &Module) -> Vec<ValidationError> {
    trust_ir::validate_spec_structure(&m.spec_modules)
        .into_iter()
        .map(|violation| ValidationError::InvalidSpecStructure { violation })
        .collect()
}
fn run(m: &Module) -> (Vec<ValidationError>, Observer) {
    let mut o = Observer::default();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let out = validate_module_spec_structure_observed(m, &mut s, site()).unwrap();
    assert_eq!(out, wrapped(m));
    assert!(s.first_refusal().is_none());
    assert_eq!(s.remaining_fuel(), InterpretOptions::default().fuel);
    drop(s);
    assert!(o.events.iter().all(|e| e.site == site()));
    (out, o)
}
fn rows() -> Vec<SpecLinkViolation> {
    (0..3)
        .map(|n| SpecLinkViolation::MachineMissing {
            machine: format!("machine{n}λ").repeat(1000),
            action: format!("action{n}").repeat(1000),
            from: "anchor",
            detail: format!("detail{n}λ").repeat(1000),
        })
        .collect()
}
fn drain<O: ExecutionObserver>(state: &mut State, w: &mut Work<'_, '_, O>) {
    state.retire_scratch(w);
    let _ = retire_validation_errors_observed(take(&mut state.errors), w.session, w.site);
}
fn empty(s: &State) -> bool {
    s.batch.is_none() && s.pending.is_none() && s.errors.capacity() == 0
}
