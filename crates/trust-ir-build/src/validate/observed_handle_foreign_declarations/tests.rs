// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Authored UNRUN; exact original rule is the oracle, not authority.
#![allow(
    clippy::drop_non_drop,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
use std::{cell::Cell, rc::Rc};
use trust_ir::interpret::InterpretOptions;
use trust_ir::value::{FuncTyId, ImportId, TyId};
use trust_ir::{ExternRef, FunctionSummary};
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
            return Err("original foreign stop");
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
    ExecutionSite::Entry(FuncId::new(1013))
}
fn declaration(id: u32, name: &str, ty: u32) -> Function {
    Function::new(FuncId::new(id), name, FuncTyId::new(ty), BlockId::new(0))
}
fn registry() -> HandleRegistry {
    HandleRegistry {
        pins: vec![HandleRuntimePin {
            name: "Name",
            runtime: "rt::Name",
            calling_conv: trust_ir::CallingConv::C,
            entry_points: Box::leak(
                vec![HandleEntryPoint {
                    role: "role",
                    symbol: "pinned",
                    def_path: "unused::path",
                    params: &[],
                    returns: &[],
                }]
                .into_boxed_slice(),
            ),
        }],
    }
}
fn fixture() -> (Module, HandleRegistry) {
    let mut m = Module::new("");
    m.types = vec![
        Ty::handle("Name", "rt::Name"),
        Ty::Tuple(vec![
            Ty::Array(TyId::new(0), 0),
            Ty::handle("Second", "rt::Second"),
        ]),
    ];
    m.func_types = vec![
        FuncTy::unrecorded(vec![Ty::Bool], vec![Ty::Array(TyId::new(1), 0)], false),
        FuncTy::unrecorded(vec![Ty::Bool], vec![], false),
    ];
    let mut backed = declaration(7, "backed λ'\n", 0);
    let mut summary = FunctionSummary::new();
    summary.backed_by = Some(ExternRef::new(ImportId::new(u32::MAX), "unread symbol"));
    backed.summary = Some(summary);
    let mut defined = declaration(8, "defined", 0);
    defined.blocks.push(trust_ir::Block::new(BlockId::new(0)));
    m.functions = vec![
        declaration(u32::MAX, "no backing λ'\"\n\0", 0),
        backed,
        declaration(9, "pinned", 0),
        defined,
        declaration(10, "dangling", u32::MAX),
        declaration(11, "scalar", 1),
    ];
    (m, registry())
}
fn run(
    m: &Module,
    r: &HandleRegistry,
    policy: ImportPolicy<'_>,
) -> (Vec<ValidationError>, Observer, usize, usize) {
    let old = m.nominal_type_reachability();
    let expected = super::super::validate_handle_foreign_declarations(m, r, &old, policy);
    let mut o = Observer::default();
    let calls = o.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let nominal = m
        .nominal_type_reachability_observed(&mut s, site())
        .unwrap();
    let begin = calls.get();
    let output =
        validate_handle_foreign_declarations_observed(m, r, &nominal, policy, &mut s, site())
            .unwrap();
    let end = calls.get();
    assert_eq!(output, expected);
    assert!(s.first_refusal().is_none());
    assert_eq!(s.remaining_fuel(), InterpretOptions::default().fuel);
    retire_validation_errors_observed(output.clone(), &mut s, site()).unwrap();
    nominal.retire_observed(&mut s, site()).unwrap();
    drop(s);
    assert!(o.events.iter().all(|e| e.site == site()));
    assert_eq!(
        o.events[end - 1].copy_bytes,
        size_of::<Vec<ValidationError>>()
    );
    (output, o, begin, end)
}
pub(crate) fn run_for_linked(
    m: &Module,
    r: &HandleRegistry,
    policy: ImportPolicy<'_>,
) -> Vec<ValidationError> {
    run(m, r, policy).0
}
fn empty(state: &State) -> bool {
    state.name.capacity() == 0
        && state.handles.capacity() == 0
        && state.detail.capacity() == 0
        && state.errors.capacity() == 0
}
fn drain<O: ExecutionObserver>(state: &mut State, work: &mut Work<'_, '_, O>) {
    state.retire_scratch(work);
    let _ = retire_validation_errors_observed(take(&mut state.errors), work.session, work.site);
}

pub(crate) fn call_for_linked<O: ExecutionObserver>(
    m: &Module,
    r: &HandleRegistry,
    nominal: &ObservedNominalTypeReachability<'_>,
    policy: ImportPolicy<'_>,
    session: &mut ObservedSession<'_, O>,
    site: ExecutionSite,
) -> Result<Vec<ValidationError>, ObservedValueError> {
    validate_handle_foreign_declarations_observed(m, r, nominal, policy, session, site)
}
