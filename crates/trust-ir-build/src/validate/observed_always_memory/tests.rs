// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Authored UNRUN; actual ordinary AlwaysMemory validator is the oracle.
use super::*;
use std::{cell::Cell, rc::Rc};
use trust_ir::interpret::InterpretOptions;
use trust_ir::value::{ClosureTyId, EnumId, PredId, RecordId, StructId, TyId};
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
            return Err("original AlwaysMemory stop");
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
            return Err("bytes");
        }
        Ok(())
    }
}
fn site() -> ExecutionSite {
    ExecutionSite::Entry(FuncId::new(139))
}
fn target(policy: trust_ir::StructPassingPolicy) -> trust_ir::TargetInfo {
    trust_ir::TargetInfo {
        triple: "aarch64-unknown-linux-gnu".into(),
        pointer_size: 8,
        endianness: trust_ir::Endianness::Little,
        abi: None,
        struct_passing: policy,
    }
}
fn fixture() -> Module {
    let mut m = Module::new("AlwaysMemory");
    m.target_info = Some(target(trust_ir::StructPassingPolicy::AlwaysMemory));
    m.func_types = vec![trust_ir::FuncTy::unrecorded(
        vec![
            Ty::U8,
            Ty::Tuple(vec![Ty::U8]),
            Ty::Struct(StructId::new(0)),
        ],
        vec![Ty::Array(TyId::new(0), 0)],
        false,
    )];
    m
}
fn run(m: &Module) -> (Vec<ValidationError>, Observer) {
    let mut o = Observer::default();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let out = validate_module_always_memory_struct_passing_observed(m, &mut s, site()).unwrap();
    assert_eq!(out, validate_always_memory_struct_passing(m));
    assert!(s.first_refusal().is_none());
    assert_eq!(s.remaining_fuel(), InterpretOptions::default().fuel);
    assert!(o.events.iter().all(|e| e.site == site()));
    (out, o)
}
fn private_trace(m: &Module) -> Observer {
    let mut o = Observer::default();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let mut work = Work {
        session: &mut s,
        site: site(),
    };
    let mut state = State::default();
    state.run(m, &mut work).unwrap();
    assert_eq!(state.errors, validate_always_memory_struct_passing(m));
    drain(&mut state, &mut work);
    assert!(empty(&state));
    o
}
fn drain(state: &mut State, work: &mut Work<'_, '_, impl ExecutionObserver>) {
    state.retire_scratch(work);
    let _ = retire_validation_errors_observed(take(&mut state.errors), work.session, work.site);
}
fn empty(s: &State) -> bool {
    s.slot.capacity() == 0 && s.tytext.is_none() && s.errors.capacity() == 0
}
