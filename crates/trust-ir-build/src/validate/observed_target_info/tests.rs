// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Authored UNRUN controls; original catalog/present-target rules are the oracle.
use super::*;
use std::{cell::Cell, rc::Rc};
use trust_ir::interpret::InterpretOptions;
use trust_ir::value::FuncTyId;
use trust_ir::{Block, InstrNode};
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
    cleanup: Option<Rc<Cell<bool>>>,
}
impl ExecutionObserver for Observer {
    type Refusal = &'static str;
    fn admit(&mut self, e: ExecutionProgress) -> Result<(), Self::Refusal> {
        self.events.push(e);
        if self.stop == Some(self.events.len()) {
            return Err("original target stop");
        }
        if self.cleanup.as_ref().is_some_and(|arm| arm.get())
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
    ExecutionSite::Entry(FuncId::new(130))
}
fn ordinary(m: &Module) -> Vec<ValidationError> {
    let mut out = vec![];
    if let Some(ti) = &m.target_info {
        if !matches!(ti.pointer_size, 1 | 2 | 4 | 8) {
            out.push(ValidationError::TargetPointerSizeInvalid {
                pointer_size: ti.pointer_size,
            });
        }
        if ti.triple.is_empty() {
            out.push(ValidationError::TargetTripleEmpty);
        }
    } else if let Some(boundary) = ModuleFunctionCatalog::new(m).first_ffi_boundary() {
        out.push(ValidationError::TargetInfoRequired { boundary });
    }
    out
}
fn run(m: &Module) -> (Vec<ValidationError>, Observer) {
    let mut o = Observer::default();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let out = validate_module_target_info_observed(m, &mut s, site()).unwrap();
    assert_eq!(out, ordinary(m));
    assert!(s.first_refusal().is_none());
    assert_eq!(s.remaining_fuel(), InterpretOptions::default().fuel);
    assert!(o.events.iter().all(|e| e.site == site()));
    (out, o)
}
fn drain(state: &mut State, work: &mut Work<'_, '_, impl ExecutionObserver>) {
    work.retire_text(&mut state.boundary);
    let _ = retire_validation_errors_observed(take(&mut state.errors), work.session, work.site);
}
fn empty(state: &State) -> bool {
    state.boundary.capacity() == 0 && state.errors.capacity() == 0
}
