// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Authored UNRUN; the complete unchanged ordinary SCC pass is the oracle.
#![allow(
    clippy::drop_non_drop,
    clippy::field_reassign_with_default,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
use std::{cell::Cell, rc::Rc};
use trust_ir::interpret::InterpretOptions;
use trust_ir::ty::{ClosureTy, EnumDef, EnumVariant, FieldDef, RecordDef, StructDef, StructRepr};
use trust_ir::value::{ClosureTyId, EnumId, FuncTyId, PredId, RecordId, StructId, TyId};
mod custody;
mod fixtures;
mod parity;
mod stops;
use fixtures::*;
#[derive(Default)]
struct Observer {
    events: Vec<ExecutionProgress>,
    calls: Rc<Cell<usize>>,
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
        self.calls.set(self.events.len());
        if self.stop == Some(self.events.len()) {
            return Err("original inline cycle stop");
        }
        if self.cleanup.as_ref().is_some_and(|arm| arm.get())
            && event.phase == ExecutionPhase::ScratchRetirement
        {
            return Err("cleanup");
        }
        self.work = self.work.checked_add(event.work).ok_or("overflow")?;
        self.bytes = self.bytes.checked_add(event.copy_bytes).ok_or("overflow")?;
        if self.work_cap.is_some_and(|cap| self.work > cap) {
            return Err("work");
        }
        if self.byte_cap.is_some_and(|cap| self.bytes > cap) {
            return Err("copy");
        }
        Ok(())
    }
}
fn site() -> ExecutionSite {
    ExecutionSite::Entry(FuncId::new(6701))
}
fn ordinary(m: &Module) -> Vec<ValidationError> {
    super::super::inline_cycles::validate_inline_aggregate_cycles(m)
}
fn call<O: ExecutionObserver>(
    m: &Module,
    s: &mut ObservedSession<'_, O>,
) -> R<Vec<ValidationError>> {
    validate_inline_aggregate_cycles_observed(m, s, site())
}
fn run(m: &Module) -> (Vec<ValidationError>, Observer, usize) {
    let before = m.clone();
    let expected = ordinary(m);
    let mut o = Observer {
        work_cap: Some(1_000_000_000),
        byte_cap: Some(512 * 1024 * 1024),
        ..Observer::default()
    };
    let calls = o.calls.clone();
    let mut opt = InterpretOptions::default();
    opt.fuel = 0;
    let mut s = ObservedSession::new(opt, &mut o);
    let result = call(m, &mut s).unwrap();
    let end = calls.get();
    assert_eq!(result, expected);
    retire_validation_errors_observed(result, &mut s, site()).unwrap();
    assert!(s.first_refusal().is_none());
    assert_eq!(s.remaining_fuel(), 0);
    drop(s);
    assert!(o.events.iter().all(|e| e.site == site()));
    assert_eq!(m, &before);
    (expected, o, end)
}
fn private_run<'m, O: ExecutionObserver>(
    state: &mut State<'m>,
    m: &'m Module,
    w: &mut Work<'_, '_, O>,
) -> R {
    // The same three actual production calls in the public entry; both private
    // baselines and interrupted calls omit its one initial header identically.
    state.graph(m, w)?;
    state.components(w)?;
    state.describe_cycles(m, w)
}
fn drain<O: ExecutionObserver>(state: &mut State<'_>, w: &mut Work<'_, '_, O>) {
    state.retire_scratch(w);
    let _ = retire_validation_errors_observed(take(&mut state.errors), w.session, w.site);
}
fn empty(state: &State<'_>) {
    assert_eq!(
        state.nodes.capacity()
            + state.pending.capacity()
            + state.edges.capacity()
            + state.successors.capacity()
            + state.marks.capacity()
            + state.stack.capacity()
            + state.calls.capacity()
            + state.component.capacity()
            + state.cycles.capacity()
            + state.text.capacity()
            + state.render.capacity()
            + state.errors.capacity(),
        0
    );
}
