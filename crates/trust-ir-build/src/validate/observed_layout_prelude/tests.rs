// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Authored UNRUN source controls, not execution evidence.
use super::*;
use std::{cell::Cell, rc::Rc};
use trust_ir::interpret::InterpretOptions;
use trust_ir::value::{ClosureTyId, FuncId, FuncTyId, TyId};
use trust_ir::{ClosureLayoutDescriptor, TupleLayoutDescriptor};
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
    fn admit(&mut self, event: ExecutionProgress) -> Result<(), Self::Refusal> {
        self.events.push(event);
        if self.stop == Some(self.events.len()) {
            return Err("original layout prelude stop");
        }
        if self.cleanup.as_ref().is_some_and(|arm| arm.get())
            && event.phase == ExecutionPhase::ScratchRetirement
        {
            return Err("cleanup");
        }
        self.work = self.work.checked_add(event.work).ok_or("overflow")?;
        self.bytes = self.bytes.checked_add(event.copy_bytes).ok_or("overflow")?;
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
    ExecutionSite::Entry(FuncId::new(126))
}
fn valid() -> Module {
    let mut m = Module::new("layout-prelude");
    m.target_info = Some(trust_ir::TargetInfo {
        triple: "x86_64-unknown-linux-gnu".into(),
        pointer_size: 8,
        endianness: trust_ir::Endianness::Little,
        abi: None,
        struct_passing: Default::default(),
    });
    m.types.push(Ty::Tuple(vec![Ty::U8, Ty::U64, Ty::Unit]));
    m.tuple_layouts.push(TupleLayoutDescriptor {
        tuple_type: TyId::new(0),
        size: 16,
        align: 8,
        field_offsets: vec![8, 0, 16],
    });
    m.closure_types.push(trust_ir::ty::ClosureTy {
        func: FuncTyId::new(0),
        captures: vec![Ty::U8, Ty::U64],
    });
    m.closure_layouts.push(ClosureLayoutDescriptor {
        origin: None,
        closure: ClosureTyId::new(0),
        size: 16,
        align: 8,
        capture_offsets: vec![8, 0],
    });
    m
}
fn invalid() -> Module {
    let mut m = Module::new("missing");
    m.tuple_layouts.push(TupleLayoutDescriptor {
        tuple_type: TyId::new(7),
        size: 0,
        align: 1,
        field_offsets: vec![],
    });
    m.closure_layouts.push(ClosureLayoutDescriptor {
        origin: None,
        closure: ClosureTyId::new(9),
        size: 0,
        align: 1,
        capture_offsets: vec![],
    });
    m
}
fn ordinary(m: &Module) -> Vec<ValidationError> {
    let table = m.layout_table();
    let mut out = vec![];
    if let Err(error) = table.validate_tuple_layouts() {
        out.push(ValidationError::TupleLayoutInconsistent {
            reason: error.to_string(),
        });
    }
    if let Err(error) = m.validate_closure_layouts() {
        out.push(ValidationError::TupleLayoutInconsistent {
            reason: format!("{CLOSURE_LAYOUT_TABLE_REASON_PREFIX}{error}"),
        });
    }
    out
}
fn run(m: &Module) -> (Vec<ValidationError>, Observer) {
    let mut o = Observer::default();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let out = validate_module_layout_prelude_observed(m, &mut s, site()).unwrap();
    assert_eq!(out, ordinary(m));
    assert!(s.first_refusal().is_none());
    assert_eq!(s.remaining_fuel(), InterpretOptions::default().fuel);
    assert!(o.events.iter().all(|e| e.site == site()));
    (out, o)
}
fn drain(state: &mut State<'_>, work: &mut Work<'_, '_, impl ExecutionObserver>) {
    state.retire_scratch(work);
    let _ = retire_validation_errors_observed(take(&mut state.errors), work.session, work.site);
}
fn empty(state: &State<'_>) -> bool {
    state.table.is_none()
        && state.pending.is_none()
        && state.spelled.capacity() == 0
        && state.reason.capacity() == 0
        && state.errors.capacity() == 0
}
