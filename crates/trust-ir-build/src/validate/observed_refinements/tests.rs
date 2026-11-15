// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Authored controls only; all Rust/native execution UNRUN.
#![allow(
    clippy::drop_non_drop,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
use std::{cell::Cell, rc::Rc};
use trust_ir::inst::{
    AtomicRMWOp, BinOp, BindingFrameDef, BindingSlot, CastOp, Ordering, SwitchCase,
};
use trust_ir::interpret::InterpretOptions;
use trust_ir::ty::{EnumDef, EnumVariant, FieldDef, FuncTy, RecordDef, StructDef, StructRepr};
use trust_ir::value::{BindingFrameId, BlockId, EnumId, FuncTyId, RecordId, StructId, TyId};
use trust_ir::{Block, CallingConv, InstrNode};
mod algorithms;
mod custody;
mod fixtures;
mod parity;
mod stops;
mod values;
use fixtures::*;
#[derive(Default)]
struct Observer {
    events: Vec<ExecutionProgress>,
    calls: Rc<Cell<usize>>,
    stop: Rc<Cell<Option<usize>>>,
    work: usize,
    copy: usize,
    work_cap: Option<usize>,
    copy_cap: Option<usize>,
    cleanup_stop: bool,
}
impl ExecutionObserver for Observer {
    type Refusal = &'static str;
    fn admit(&mut self, e: ExecutionProgress) -> Result<(), Self::Refusal> {
        self.events.push(e);
        self.calls.set(self.events.len());
        if self.stop.get() == Some(self.events.len()) {
            return Err("original refinement stop");
        }
        if self.cleanup_stop && e.phase == ExecutionPhase::ScratchRetirement {
            return Err("cleanup");
        }
        self.work = self.work.checked_add(e.work).ok_or("work overflow")?;
        self.copy = self.copy.checked_add(e.copy_bytes).ok_or("copy overflow")?;
        if self.work_cap.is_some_and(|n| self.work > n) {
            return Err("work");
        }
        if self.copy_cap.is_some_and(|n| self.copy > n) {
            return Err("copy");
        }
        Ok(())
    }
}
fn site() -> ExecutionSite {
    ExecutionSite::Entry(FuncId::new(2361))
}
fn ordinary(m: &Module) -> Vec<ValidationError> {
    super::super::validate_refinements(m, &ModuleFunctionCatalog::new(m))
}
fn run(m: &Module) -> (Vec<ValidationError>, Observer, usize) {
    let expected = ordinary(m);
    let mut observer = Observer::default();
    let calls = observer.calls.clone();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    let output = validate_module_refinements_observed(m, &mut session, site()).unwrap();
    let end = calls.get();
    assert_eq!(output, expected);
    assert!(session.first_refusal().is_none());
    assert_eq!(session.remaining_fuel(), InterpretOptions::default().fuel);
    retire_validation_errors_observed(output, &mut session, site()).unwrap();
    drop(session);
    assert!(observer.events.iter().all(|e| e.site == site()));
    assert_eq!(
        observer.events[end - 1],
        ExecutionProgress {
            phase: ExecutionPhase::Publication,
            site: site(),
            work: 1,
            copy_bytes: size_of::<Vec<ValidationError>>()
        }
    );
    (expected, observer, end)
}
fn drain(state: &mut State<'_>, work: &mut Work<'_, '_, impl ExecutionObserver>) {
    state.retire(work);
    work.errors(&mut state.errors);
}
fn empty(state: &State<'_>) -> bool {
    state.errors.capacity() == 0
        && state.scratch.capacity() == 0
        && state.refusals.capacity() == 0
        && state.location.capacity() == 0
        && state.base_location.capacity() == 0
        && state.detail.capacity() == 0
        && state.actual.capacity() == 0
        && state.required.capacity() == 0
        && state.key.capacity() == 0
        && state.seen_universes.capacity() == 0
        && state.seen_preds.capacity() == 0
        && state.type_stack.capacity() == 0
        && state.pred_stack.capacity() == 0
        && state.pred_path.capacity() == 0
        && state.inline_types.capacity() == 0
}
