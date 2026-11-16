// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Authored UNRUN; exact whole original rule and real original-owner children.
#![allow(
    clippy::drop_non_drop,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::super::observed_value_types::build_module_value_types_observed;
use super::*;
use std::{cell::Cell, rc::Rc};
use trust_ir::interpret::InterpretOptions;
use trust_ir::value::FuncTyId;
use trust_ir::{Block, DialectTy};
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
            return Err("original nominal instruction stop");
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
    ExecutionSite::Entry(FuncId::new(1101))
}
fn v(id: u32) -> ValueId {
    ValueId::new(id)
}
fn handle() -> Ty {
    Ty::handle("Name", "rt::Name")
}
fn dialect() -> Ty {
    Ty::Dialect(Box::new(DialectTy::new("ns", "Name", 1)))
}
fn mixed() -> Ty {
    Ty::Tuple(vec![handle(), dialect()])
}
fn fixture() -> (Module, Function) {
    let mut m = Module::new("");
    m.func_types = vec![
        FuncTy::unrecorded(vec![], vec![], false),
        FuncTy::unrecorded(vec![handle()], vec![handle()], false),
        FuncTy::unrecorded(vec![dialect()], vec![dialect()], false),
        FuncTy::unrecorded(vec![dialect()], vec![Ty::Bool], false),
        FuncTy::unrecorded(vec![handle()], vec![Ty::Bool], false),
    ];
    let mut f = Function::new(FuncId::new(1101), "F", FuncTyId::new(0), BlockId::new(1));
    let mut b = Block::new(f.entry);
    b.params = vec![
        (v(0), Ty::Bool),
        (v(1), handle()),
        (v(2), dialect()),
        (v(3), mixed()),
        (v(4), Ty::Ptr),
        (v(5), Ty::Func(FuncTyId::new(1))),
        (v(6), Ty::U8),
        (v(7), Ty::Func(FuncTyId::new(2))),
        (v(8), Ty::Func(FuncTyId::new(99))),
    ];
    b.body = vec![
        InstrNode::new(Inst::Alloca {
            ty: handle(),
            count: None,
            align: None,
        })
        .with_result(v(10)),
        InstrNode::new(Inst::Store {
            ty: handle(),
            ptr: v(10),
            value: v(1),
            volatile: false,
            align: None,
        }),
        InstrNode::new(Inst::Load {
            ty: handle(),
            ptr: v(10),
            volatile: false,
            align: None,
        })
        .with_result(v(11)),
        InstrNode::new(Inst::Return { values: vec![] }),
    ];
    f.blocks.push(b);
    (m, f)
}
fn setup<'m, 'f, O: ExecutionObserver>(
    m: &'m Module,
    f: &'f Function,
    guard: bool,
    slot: bool,
    s: &mut ObservedSession<'_, O>,
) -> (
    trust_ir::LayoutTable<'m>,
    ObservedNominalTypeReachability<'m>,
    ObservedValueTypes,
    Option<ObservedHandleEnumGuards<'f>>,
    Option<ObservedSealedHandleSlots<'f>>,
) {
    let table = trust_ir::LayoutTable::new_observed(m, s, site()).unwrap();
    let nominal = m.nominal_type_reachability_observed(s, site()).unwrap();
    let values = build_module_value_types_observed(f, m, s, site()).unwrap();
    let guards = if guard {
        Some(ObservedHandleEnumGuards::new_observed(f, s, site()).unwrap())
    } else {
        None
    };
    let slots = if slot {
        Some(ObservedSealedHandleSlots::new_observed(&table, f, &nominal, s, site()).unwrap())
    } else {
        None
    };
    (table, nominal, values, guards, slots)
}
fn dispose<O: ExecutionObserver>(
    table: trust_ir::LayoutTable<'_>,
    nominal: ObservedNominalTypeReachability<'_>,
    values: ObservedValueTypes,
    guards: Option<ObservedHandleEnumGuards<'_>>,
    slots: Option<ObservedSealedHandleSlots<'_>>,
    s: &mut ObservedSession<'_, O>,
) {
    if let Some(slots) = slots {
        let _ = slots.retire_observed(s, site());
    }
    if let Some(guards) = guards {
        let _ = guards.retire_observed(s, site());
    }
    let _ = values.retire_observed(s, site());
    let _ = nominal.retire_observed(s, site());
    s.retirement_step(site(), size_of::<trust_ir::LayoutTable<'_>>() + 1);
    drop(table);
    s.retirement_poll(site());
}
fn run(
    m: &Module,
    f: &Function,
    node: &InstrNode,
    point: (BlockId, usize),
    guard: bool,
    slot: bool,
    location: &str,
) -> (Vec<ValidationError>, Observer, usize, usize) {
    let old_table = trust_ir::LayoutTable::new(m);
    let old_nominal = m.nominal_type_reachability();
    let old_values = super::super::build_module_value_types(f, m);
    let old_guards = if guard {
        Some(super::super::HandleEnumGuards::new(f))
    } else {
        None
    };
    let old_slots = if slot {
        Some(super::super::handle_slots::SealedHandleSlots::new(
            &old_table,
            f,
            &old_nominal,
        ))
    } else {
        None
    };
    let mut expected = vec![];
    super::super::validate_nominal_instruction_types(
        m,
        &ModuleFunctionCatalog::new(m),
        node,
        &old_values,
        &old_nominal,
        point.0,
        point.1,
        old_guards.as_ref(),
        old_slots.as_ref(),
        location,
        &mut expected,
    );
    let mut o = Observer::default();
    let calls = o.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let (table, nominal, values, guards, slots) = setup(m, f, guard, slot, &mut s);
    let begin = calls.get();
    let out = validate_nominal_instruction_types_observed(
        m,
        node,
        &values,
        &nominal,
        point.0,
        point.1,
        guards.as_ref(),
        slots.as_ref(),
        location,
        &mut s,
        site(),
    )
    .unwrap();
    let end = calls.get();
    assert_eq!(out, expected);
    retire_validation_errors_observed(out, &mut s, site()).unwrap();
    dispose(table, nominal, values, guards, slots, &mut s);
    assert!(s.first_refusal().is_none());
    assert_eq!(s.remaining_fuel(), InterpretOptions::default().fuel);
    drop(s);
    assert!(o.events.iter().all(|e| e.site == site()));
    (expected, o, begin, end)
}
fn check(m: &Module, f: &Function, inst: Inst) -> Vec<ValidationError> {
    run(
        m,
        f,
        &InstrNode::new(inst),
        (f.entry, 3),
        false,
        false,
        "loc",
    )
    .0
}
fn empty(s: &State) -> bool {
    s.operands.capacity() == 0
        && s.location.capacity() == 0
        && s.detail.capacity() == 0
        && s.errors.capacity() == 0
}
fn drain<O: ExecutionObserver>(state: &mut State, work: &mut Work<'_, '_, O>) {
    state.retire_scratch(work);
    let _ = retire_validation_errors_observed(take(&mut state.errors), work.session, work.site);
}
