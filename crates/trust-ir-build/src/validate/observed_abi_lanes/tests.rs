// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Authored UNRUN. Full actual ordinary solver is the parity oracle.
#![allow(
    clippy::drop_non_drop,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::super::abi_lanes::{AbiLanes, abi_lanes};
use super::*;
use std::{
    cell::{Cell, RefCell},
    rc::Rc,
};
use trust_ir::interpret::InterpretOptions;
use trust_ir::ty::{EnumVariant, FatPtrKind, StructDef, StructRepr};
use trust_ir::value::{ClosureTyId, FuncTyId, PredId, RecordId, TyId};
use trust_ir::{Endianness, TargetInfo};
mod custody;
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
            return Err("original ABI-lane stop");
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
    ExecutionSite::Entry(FuncId::new(6501))
}
fn setup<'m, O: ExecutionObserver>(
    m: &'m Module,
    s: &mut ObservedSession<'_, O>,
) -> (LayoutTable<'m>, ObservedAbiLanes<'m>) {
    let table = LayoutTable::new_observed(m, s, site()).unwrap();
    let lanes = ObservedAbiLanes::new_observed(&table, s, site()).unwrap();
    (table, lanes)
}
fn dispose<O: ExecutionObserver>(
    table: LayoutTable<'_>,
    lanes: ObservedAbiLanes<'_>,
    s: &mut ObservedSession<'_, O>,
) {
    let _ = lanes.retire_observed(s, site());
    s.retirement_step(site(), size_of::<LayoutTable<'_>>() + 1);
    drop(table);
    s.retirement_poll(site());
}
fn run(m: &Module, ty: &Ty) -> (Option<usize>, Observer, usize, usize) {
    let expected = abi_lanes(&m.layout_table(), &AbiLanes::default(), ty);
    let mut o = Observer::default();
    let calls = o.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let (table, mut lanes) = setup(m, &mut s);
    let begin = calls.get();
    let answer = lanes.lanes_observed(&table, ty, &mut s, site()).unwrap();
    let end = calls.get();
    assert_eq!(answer, expected);
    assert!(
        lanes
            .nodes
            .iter()
            .all(|(_, slot)| matches!(slot, Slot::Counted(_)))
    );
    dispose(table, lanes, &mut s);
    assert_eq!(s.remaining_fuel(), InterpretOptions::default().fuel);
    assert!(s.first_refusal().is_none());
    drop(s);
    assert!(o.events.iter().all(|e| e.site == site()));
    (answer, o, begin, end)
}
fn empty(state: &State<'_>, lanes: &ObservedAbiLanes<'_>) {
    assert!(state.layout.is_none());
    assert_eq!(state.frames.capacity() + lanes.nodes.capacity(), 0);
}
fn drain<O: ExecutionObserver>(
    state: &mut State<'_>,
    lanes: &mut ObservedAbiLanes<'_>,
    w: &mut Work<'_, '_, O>,
) {
    let _ = state.retire(w);
    lanes.retire_nodes(w);
}
