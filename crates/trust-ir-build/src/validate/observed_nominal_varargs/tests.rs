// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Authored UNRUN against actual ordinary last-definition map and nominal graph.
#![allow(
    clippy::drop_non_drop,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
use std::{cell::Cell, rc::Rc};
use trust_ir::interpret::InterpretOptions;
use trust_ir::value::{FuncTyId, TyId};
mod custody;
mod parity;
mod stops;
#[derive(Default)]
struct Observer {
    events: Vec<ExecutionProgress>,
    calls: Rc<Cell<usize>>,
    work: Rc<Cell<usize>>,
    bytes: Rc<Cell<usize>>,
    stop: Option<usize>,
    cleanup_after: Option<usize>,
    work_cap: Option<usize>,
    byte_cap: Option<usize>,
}
impl ExecutionObserver for Observer {
    type Refusal = &'static str;
    fn admit(&mut self, e: ExecutionProgress) -> Result<(), Self::Refusal> {
        self.events.push(e);
        self.calls.set(self.events.len());
        if self.stop == Some(self.events.len()) {
            return Err("original varargs stop");
        }
        if e.phase == ExecutionPhase::ScratchRetirement
            && self.cleanup_after.is_some_and(|n| self.events.len() > n)
        {
            return Err("cleanup");
        }
        self.work
            .set(self.work.get().checked_add(e.work).ok_or("overflow")?);
        self.bytes.set(
            self.bytes
                .get()
                .checked_add(e.copy_bytes)
                .ok_or("overflow")?,
        );
        if self.work_cap.is_some_and(|n| self.work.get() > n) {
            return Err("work");
        }
        if self.byte_cap.is_some_and(|n| self.bytes.get() > n) {
            return Err("copy");
        }
        Ok(())
    }
}
#[derive(Clone, Copy)]
enum Mode {
    Present,
    Absent,
}
fn site() -> ExecutionSite {
    ExecutionSite::Entry(FuncId::new(719))
}
fn v(id: u32) -> ValueId {
    ValueId::new(id)
}
fn fixture() -> (Module, Function) {
    let mut m = Module::new("");
    m.types = vec![
        Ty::handle("Name", "rt::Name"),
        Ty::Dialect(Box::new(trust_ir::DialectTy::new("ns", "Name", 1))),
        Ty::Tuple(vec![Ty::Array(TyId::new(0), 0), Ty::Array(TyId::new(1), 0)]),
    ];
    let mut f = Function::new(FuncId::new(719), "F", FuncTyId::new(0), BlockId::new(0));
    let mut b = trust_ir::Block::new(BlockId::new(0));
    b.params = vec![
        (v(0), Ty::Bool),
        (v(1), Ty::Array(TyId::new(0), 0)),
        (v(2), Ty::Array(TyId::new(1), 0)),
        (v(3), Ty::Array(TyId::new(2), 0)),
        (v(4), Ty::Func(FuncTyId::new(99))),
    ];
    f.blocks.push(b);
    (m, f)
}
fn args() -> Vec<ValueId> {
    vec![v(0), v(1), v(2), v(3), v(4), v(99), v(1)]
}
fn run(
    m: &Module,
    f: &Function,
    args: &[ValueId],
    fixed: usize,
    location: &str,
    mode: Mode,
) -> (Vec<ValidationError>, Observer, usize, usize) {
    let old_values = build_function_value_types(f);
    let old_nominal = m.nominal_type_reachability();
    let mut expected = vec![];
    super::super::validate_nominal_varargs(
        args,
        fixed,
        &old_values,
        match mode {
            Mode::Present => Some(&old_nominal),
            Mode::Absent => None,
        },
        location,
        &mut expected,
    );
    let mut o = Observer::default();
    let calls = o.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let values = build_function_value_types_observed(f, &mut s, site()).unwrap();
    let nominal = m
        .nominal_type_reachability_observed(&mut s, site())
        .unwrap();
    let start = calls.get();
    let output = validate_nominal_varargs_observed(
        args,
        fixed,
        &values,
        match mode {
            Mode::Present => Some(&nominal),
            Mode::Absent => None,
        },
        location,
        &mut s,
        site(),
    )
    .unwrap();
    let end = calls.get();
    assert_eq!(output, expected);
    retire_validation_errors_observed(output, &mut s, site()).unwrap();
    nominal.retire_observed(&mut s, site()).unwrap();
    values.retire_observed(&mut s, site()).unwrap();
    assert!(s.first_refusal().is_none());
    assert_eq!(s.remaining_fuel(), InterpretOptions::default().fuel);
    drop(s);
    assert!(o.events.iter().all(|e| e.site == site()));
    assert_eq!(o.events[end - 1].phase, ExecutionPhase::Publication);
    (expected, o, start, end)
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
    state.location.capacity() == 0 && state.detail.capacity() == 0 && state.errors.capacity() == 0
}
