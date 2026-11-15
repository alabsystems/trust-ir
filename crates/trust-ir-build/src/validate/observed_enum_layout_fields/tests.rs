// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Authored UNRUN controls; the oracle retains the exact ordinary field block.
use super::*;
use std::{cell::Cell, rc::Rc};
use trust_ir::interpret::InterpretOptions;
use trust_ir::ty::{EnumTagEncoding, EnumTagRepr, EnumVariant, FieldDef, StructDef};
use trust_ir::value::{EnumId, StructId, TyId};
mod custody;
mod fixtures;
mod original;
mod parity;
mod stops;
use fixtures::{compact, fixture, strukt, target, variant};

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
            return Err("original field stop");
        }
        if self.cleanup.as_ref().is_some_and(|arm| arm.get())
            && event.phase == ExecutionPhase::ScratchRetirement
        {
            return Err("original cleanup stop");
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
    ExecutionSite::Entry(FuncId::new(134))
}
fn call<O: ExecutionObserver>(
    m: &Module,
    e: &EnumDef,
    d: &EnumLayoutDescriptor,
    s: &mut ObservedSession<'_, O>,
) -> R<Vec<ValidationError>> {
    validate_enum_layout_fields_observed(m, e, d, s, site())
}
fn run(m: &Module, e: &EnumDef, d: &EnumLayoutDescriptor) -> (Vec<ValidationError>, Observer) {
    let mut observer = Observer::default();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    let out = call(m, e, d, &mut session).unwrap();
    assert_eq!(out, original::run(m, e, d));
    assert!(session.first_refusal().is_none());
    assert_eq!(session.remaining_fuel(), InterpretOptions::default().fuel);
    assert!(observer.events.iter().all(|event| event.site == site()));
    assert_eq!(
        observer.events.last().unwrap().phase,
        ExecutionPhase::Publication
    );
    (out, observer)
}
fn drain<O: ExecutionObserver>(state: &mut State<'_>, work: &mut Work<'_, '_, O>) {
    state.retire_scratch(work);
    let _ = retire_validation_errors_observed(take(&mut state.errors), work.session, work.site);
}
fn empty(state: &State<'_>) -> bool {
    state.table.is_none()
        && state.shape.is_none()
        && state.error.is_none()
        && state.reason.is_none()
        && state.tytext.is_none()
        && state.location.capacity() == 0
        && state.expected.capacity() == 0
        && state.actual.capacity() == 0
        && state.ranges.capacity() == 0
        && state.errors.capacity() == 0
}
fn private_trace(m: &Module, e: &EnumDef, d: &EnumLayoutDescriptor) -> Observer {
    // Exact same private State.run entry as every private replay; no public
    // wrapper header is present in either baseline or replay.
    let mut observer = Observer::default();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    let mut work = Work {
        session: &mut session,
        site: site(),
    };
    let mut state = State::default();
    state.run(m, e, d, &mut work).unwrap();
    assert_eq!(state.errors, original::run(m, e, d));
    drain(&mut state, &mut work);
    assert!(empty(&state));
    observer
}
fn parts(error: &ValidationError) -> (&str, &str, &str) {
    let ValidationError::ConstTypeMismatch {
        location,
        expected,
        actual,
    } = error
    else {
        panic!("field error variant")
    };
    (location, expected, actual)
}
