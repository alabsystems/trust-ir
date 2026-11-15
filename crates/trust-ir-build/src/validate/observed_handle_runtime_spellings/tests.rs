// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Authored UNRUN: exact original runtime namespace/order and original custody.
#![allow(
    clippy::drop_non_drop,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
use std::{cell::Cell, rc::Rc};
use trust_ir::interpret::InterpretOptions;
use trust_ir::value::{EnumId, RecordId, StructId};
use trust_ir::{EnumDef, RecordDef, StructDef, StructRepr};
mod custody;
mod parity;
mod stops;
#[derive(Default)]
struct Observer {
    events: Vec<ExecutionProgress>,
    calls: Rc<Cell<usize>>,
    stop: Option<usize>,
    cleanup_after: Option<usize>,
    work: usize,
    bytes: usize,
    work_cap: Option<usize>,
    byte_cap: Option<usize>,
}
impl ExecutionObserver for Observer {
    type Refusal = &'static str;
    fn admit(&mut self, e: ExecutionProgress) -> Result<(), Self::Refusal> {
        self.events.push(e);
        self.calls.set(self.events.len());
        if self.stop == Some(self.events.len()) {
            return Err("original runtime spelling stop");
        }
        if e.phase == ExecutionPhase::ScratchRetirement
            && self.cleanup_after.is_some_and(|n| self.events.len() > n)
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
    ExecutionSite::Entry(FuncId::new(911))
}
fn pin(runtime: &'static str) -> HandleRuntimePin {
    HandleRuntimePin {
        name: "OpaqueName",
        runtime,
        calling_conv: trust_ir::CallingConv::C,
        entry_points: &[],
    }
}
fn registry() -> HandleRegistry {
    HandleRegistry {
        pins: vec![pin("rt::Zero"), pin("rt::One"), pin("rt::Zero")],
    }
}
fn structure(id: u32, name: &str) -> StructDef {
    StructDef {
        id: StructId::new(id),
        name: name.into(),
        fields: vec![],
        size: None,
        align: None,
        repr: StructRepr::Rust,
        origin: None,
    }
}
fn record(id: u32, name: &str) -> RecordDef {
    RecordDef {
        id: RecordId::new(id),
        name: name.into(),
        fields: vec![],
    }
}
fn fixture() -> Module {
    let mut m = Module::new("");
    m.structs = vec![structure(17, "rt::One"), structure(0, "rt::Zero")];
    m.enums = vec![EnumDef::new(EnumId::new(9), "rt::Zero", vec![])];
    m.records = vec![record(u32::MAX, "rt::One")];
    m
}
fn run(m: &Module, r: &HandleRegistry) -> (Vec<ValidationError>, Observer, usize) {
    let expected = super::super::validate_handle_runtime_spellings(m, r);
    let mut o = Observer::default();
    let calls = o.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let output = validate_handle_runtime_spellings_observed(m, r, &mut s, site()).unwrap();
    let bound = calls.get();
    assert_eq!(output, expected);
    retire_validation_errors_observed(output, &mut s, site()).unwrap();
    assert!(s.first_refusal().is_none());
    assert_eq!(s.remaining_fuel(), InterpretOptions::default().fuel);
    drop(s);
    assert!(o.events.iter().all(|e| e.site == site()));
    assert_eq!(o.events[bound - 1].phase, ExecutionPhase::Publication);
    (expected, o, bound)
}
fn prior() -> ValidationError {
    ValidationError::InvalidDialectType {
        location: "prior λ\0FULL".into(),
        detail: "prior 尾\0FULL".into(),
    }
}
fn drain<O: ExecutionObserver>(state: &mut State, work: &mut Work<'_, '_, O>) {
    state.retire_scratch(work);
    let _ = retire_validation_errors_observed(take(&mut state.errors), work.session, work.site);
}
fn empty(state: &State) -> bool {
    state.def.capacity() == 0 && state.runtime.capacity() == 0 && state.errors.capacity() == 0
}
