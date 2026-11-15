// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Authored UNRUN; ordinary actual validator is the parity oracle.
use super::*;
use std::{cell::Cell, rc::Rc};
use trust_ir::interpret::InterpretOptions;
use trust_ir::value::{FuncTyId, PredId, TyId};
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
            return Err("original parameter ABI stop");
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
    ExecutionSite::Entry(FuncId::new(136))
}
fn attrs(byval: bool, sret: bool) -> trust_ir::ParamAttrs {
    trust_ir::ParamAttrs {
        byval,
        sret,
        ..Default::default()
    }
}
fn fixture() -> Module {
    let mut m = Module::new("param ABI");
    m.func_types.push(trust_ir::FuncTy::unrecorded(
        vec![Ty::U8, Ty::Ptr],
        vec![Ty::U8],
        false,
    ));
    let mut f = Function::new(
        FuncId::new(7),
        "fullλ'\nname",
        FuncTyId::new(0),
        BlockId::new(0),
    );
    f.attrs.params = vec![attrs(true, true), attrs(false, true), attrs(true, true)];
    m.functions.push(f);
    m
}
fn run(m: &Module) -> (Vec<ValidationError>, Observer) {
    let mut o = Observer::default();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let out = validate_module_param_abi_attrs_observed(m, &mut s, site()).unwrap();
    assert_eq!(out, validate_param_abi_attrs(m));
    assert!(s.first_refusal().is_none());
    assert_eq!(s.remaining_fuel(), InterpretOptions::default().fuel);
    assert!(o.events.iter().all(|e| e.site == site()));
    assert_eq!(o.events.last().unwrap().phase, ExecutionPhase::Publication);
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
    assert_eq!(state.errors, validate_param_abi_attrs(m));
    drain(&mut state, &mut work);
    assert!(empty(&state));
    o
}
fn drain(state: &mut State, work: &mut Work<'_, '_, impl ExecutionObserver>) {
    state.retire_scratch(work);
    let _ = retire_validation_errors_observed(take(&mut state.errors), work.session, work.site);
}
fn empty(s: &State) -> bool {
    s.name.capacity() == 0 && s.errors.capacity() == 0
}
