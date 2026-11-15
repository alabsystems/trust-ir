// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Authored UNRUN. Actual ordinary whole-module diagnostic projection for
//! callee/count/types/nominal-varargs; missing signature tested explicitly.
#![allow(
    clippy::drop_non_drop,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::super::observed_value_types::build_module_value_types_observed;
use super::*;
use std::{cell::Cell, rc::Rc};
use trust_ir::interpret::InterpretOptions;
use trust_ir::value::{FuncTyId, PredId, TyId};
use trust_ir::{Block, InstrNode};
mod custody;
mod parity;
mod stops;
#[derive(Default)]
pub(super) struct Observer {
    pub(super) events: Vec<ExecutionProgress>,
    pub(super) calls: Rc<Cell<usize>>,
    pub(super) work: Rc<Cell<usize>>,
    pub(super) bytes: Rc<Cell<usize>>,
    pub(super) stop: Option<usize>,
    pub(super) cleanup_after: Option<usize>,
    pub(super) work_cap: Option<usize>,
    pub(super) byte_cap: Option<usize>,
}
impl ExecutionObserver for Observer {
    type Refusal = &'static str;
    fn admit(&mut self, e: ExecutionProgress) -> Result<(), Self::Refusal> {
        self.events.push(e);
        self.calls.set(self.events.len());
        if self.stop == Some(self.events.len()) {
            return Err("original direct call stop");
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

fn site() -> ExecutionSite {
    ExecutionSite::Entry(FuncId::new(1107))
}
fn v(id: u32) -> ValueId {
    ValueId::new(id)
}
fn h() -> Ty {
    Ty::handle("Name", "rt::Name")
}
fn d() -> Ty {
    Ty::Dialect(Box::new(trust_ir::DialectTy::new("ns", "Name", 1)))
}
fn fixture() -> Module {
    let mut m = Module::new("");
    m.types = vec![Ty::Bool];
    m.func_types = vec![
        FuncTy::unrecorded(vec![Ty::Bool, Ty::U64, h(), d()], vec![], false),
        FuncTy::unrecorded(vec![Ty::U64, Ty::Bool], vec![], false),
    ];
    let mut f = Function::new(
        FuncId::new(1107),
        "caller",
        FuncTyId::new(0),
        BlockId::new(1),
    );
    let mut b = Block::new(f.entry);
    b.params = vec![(v(0), Ty::Bool), (v(1), Ty::U64), (v(2), h()), (v(3), d())];
    b.body = vec![InstrNode::new(Inst::Return { values: vec![] })];
    f.blocks.push(b);
    let callee = Function::new(FuncId::new(9), "target", FuncTyId::new(1), BlockId::new(0));
    m.functions = vec![f, callee];
    m
}
fn call(args: &[u32]) -> Inst {
    Inst::Call {
        callee: FuncId::new(9),
        args: args.iter().copied().map(v).collect(),
    }
}
fn setup<'m, O: ExecutionObserver>(
    m: &'m Module,
    present: bool,
    s: &mut ObservedSession<'_, O>,
) -> (
    ModuleFunctionCatalog<'m>,
    ObservedValueTypes,
    Option<ObservedNominalTypeReachability<'m>>,
) {
    let catalog = ModuleFunctionCatalog::new_observed(m, s, site()).unwrap();
    let values = build_module_value_types_observed(&m.functions[0], m, s, site()).unwrap();
    let nominal = if present {
        Some(m.nominal_type_reachability_observed(s, site()).unwrap())
    } else {
        None
    };
    (catalog, values, nominal)
}
fn dispose<O: ExecutionObserver>(
    catalog: ModuleFunctionCatalog<'_>,
    values: ObservedValueTypes,
    nominal: Option<ObservedNominalTypeReachability<'_>>,
    s: &mut ObservedSession<'_, O>,
) {
    let _ = values.retire_observed(s, site());
    if let Some(nominal) = nominal {
        let _ = nominal.retire_observed(s, site());
    }
    let _ = catalog.retire_observed(s, site());
}
fn wanted(e: &ValidationError) -> bool {
    matches!(
        e,
        ValidationError::CallArgCountMismatch { .. }
            | ValidationError::CallArgTypeMismatch { .. }
            | ValidationError::CalleeNotFound { .. }
            | ValidationError::InvalidHandleUse { .. }
            | ValidationError::InvalidDialectType { .. }
    )
}
fn run(m: &Module, inst: &Inst, present: bool) -> (Vec<ValidationError>, Observer, usize, usize) {
    let mut original = m.clone();
    original.functions[0].blocks[0]
        .body
        .insert(0, InstrNode::new(inst.clone()));
    let expected: Vec<_> = super::super::validate_module(&original)
        .into_iter()
        .filter(wanted)
        .collect();
    let mut o = Observer::default();
    let calls = o.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let (catalog, values, nominal) = setup(m, present, &mut s);
    let begin = calls.get();
    let out = validate_direct_call_observed(
        &catalog,
        &m.functions[0],
        inst,
        &values,
        nominal.as_ref(),
        BlockId::new(1),
        &mut s,
        site(),
    )
    .unwrap();
    let end = calls.get();
    assert_eq!(out, expected);
    retire_validation_errors_observed(out, &mut s, site()).unwrap();
    dispose(catalog, values, nominal, &mut s);
    assert!(s.first_refusal().is_none());
    drop(s);
    assert!(o.events[begin..].iter().all(|e| e.site == site()));
    (expected, o, begin, end)
}
fn empty(s: &State) -> bool {
    s.name.capacity() == 0
        && s.expected.capacity() == 0
        && s.actual.capacity() == 0
        && s.caller.is_none()
        && s.callee.is_none()
        && s.pending.capacity() == 0
        && s.errors.capacity() == 0
}
fn drain<O: ExecutionObserver>(state: &mut State, work: &mut Work<'_, '_, O>) {
    state.retire_scratch(work);
    let _ = retire_validation_errors_observed(take(&mut state.errors), work.session, work.site);
}
