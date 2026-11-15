// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Authored UNRUN; actual whole original ABI module group is the parity oracle.
#![allow(
    clippy::drop_non_drop,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::super::abi_lanes::AbiLanes;
use super::*;
use std::{
    cell::{Cell, RefCell},
    rc::Rc,
};
use trust_ir::interpret::InterpretOptions;
use trust_ir::value::{FuncTyId, TyId};
use trust_ir::{Endianness, StructPassingPolicy, TargetInfo};
mod custody;
mod descriptor;
mod fixtures;
mod parity;
mod stops;
use fixtures::*;
#[derive(Default)]
struct Observer {
    events: Vec<ExecutionProgress>,
    trace: Rc<RefCell<Vec<ExecutionProgress>>>,
    interrupt: Option<Rc<Cell<bool>>>,
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
    fn admit(&mut self, e: ExecutionProgress) -> Result<(), Self::Refusal> {
        self.events.push(e);
        self.trace.borrow_mut().push(e);
        self.calls.set(self.events.len());
        if self.stop == Some(self.events.len()) {
            return Err("original ABI-group stop");
        }
        if self.interrupt.as_ref().is_some_and(|a| a.get()) {
            return Err("interrupt");
        }
        if self.cleanup.as_ref().is_some_and(|a| a.get())
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
            return Err("copy");
        }
        Ok(())
    }
}

fn site() -> ExecutionSite {
    ExecutionSite::Entry(FuncId::new(6601))
}
fn dispose<O: ExecutionObserver>(table: LayoutTable<'_>, s: &mut ObservedSession<'_, O>) {
    s.retirement_step(site(), size_of::<LayoutTable<'_>>() + 1);
    drop(table);
    s.retirement_poll(site());
}
fn original(module: &Module) -> Vec<ValidationError> {
    let layouts = module.layout_table();
    let mut errors = Vec::new();
    let lane_counts = AbiLanes::default();
    for func in &module.functions {
        errors.extend(validate_abi_slot_facts(&layouts, &lane_counts, func));
        if let Some(abi) = module.func_type(func.ty).and_then(|sig| sig.abi.as_ref())
            && let Err(detail) = abi.reconcile_function(func)
        {
            errors.push(ValidationError::InvalidSignatureAbi {
                signature: func.ty.index(),
                detail,
            });
        }
    }
    for (index, signature) in module.func_types.iter().enumerate() {
        if let Some(abi) = &signature.abi
            && let Err(detail) = abi
                .validate(signature)
                .and_then(|()| abi.validate_target(module.target_info.as_ref()))
        {
            errors.push(ValidationError::InvalidSignatureAbi {
                signature: index as u32,
                detail,
            });
        }
    }

    errors
}
fn run(m: &Module) -> (Vec<ValidationError>, Observer, usize, usize) {
    let expected = original(m);
    let mut o = Observer::default();
    let calls = o.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let table = LayoutTable::new_observed(m, &mut s, site()).unwrap();
    let begin = calls.get();
    let errors = validate_module_abi_facts_observed(&table, &mut s, site()).unwrap();
    let end = calls.get();
    assert_eq!(errors, expected);
    let copy = errors.clone();
    retire_validation_errors_observed(errors, &mut s, site()).unwrap();
    dispose(table, &mut s);
    assert!(s.first_refusal().is_none());
    assert_eq!(s.remaining_fuel(), InterpretOptions::default().fuel);
    drop(s);
    assert!(o.events.iter().all(|e| e.site == site()));
    (copy, o, begin, end)
}
fn empty(state: &State<'_>) {
    assert!(state.lanes.is_none() && state.layout.is_none() && state.pending_abi.is_none());
    assert_eq!(
        state.render.capacity()
            + state.slot.capacity()
            + state.pending_slot.capacity()
            + state.detail.capacity()
            + state.errors.capacity(),
        0
    );
}
fn drain<O: ExecutionObserver>(state: &mut State<'_>, w: &mut Work<'_, '_, O>) {
    let _ = state.retire_scratch(w);
    let _ = retire_validation_errors_observed(take(&mut state.errors), w.session, w.site);
}
