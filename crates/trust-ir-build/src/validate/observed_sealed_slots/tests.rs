// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Authored UNRUN. Actual original constructor/rule through cfg(test) oracles.
//! Constituent parity never grants a complete valid-module/source capability.
#![allow(
    clippy::drop_non_drop,
    clippy::type_complexity,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::super::observed_value_types::build_module_value_types_observed;
use super::*;
use std::{cell::Cell, rc::Rc};
use trust_ir::interpret::InterpretOptions;
use trust_ir::ty::{FieldDef, StructDef, StructRepr};
use trust_ir::value::{FuncTyId, StructId};
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
            return Err("original sealed analysis stop");
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

pub(super) fn site() -> ExecutionSite {
    ExecutionSite::Entry(FuncId::new(1099))
}
fn v(i: u32) -> ValueId {
    ValueId::new(i)
}
fn handle() -> Ty {
    Ty::handle("Name", "rt::Name")
}
fn allocation(ty: Ty, count: Option<ValueId>, align: Option<u64>, result: u32) -> InstrNode {
    InstrNode::new(Inst::Alloca { ty, count, align }).with_result(v(result))
}
fn store(ty: Ty, ptr: u32, value: u32) -> InstrNode {
    InstrNode::new(Inst::Store {
        ty,
        ptr: v(ptr),
        value: v(value),
        volatile: false,
        align: None,
    })
}
fn load(ty: Ty, ptr: u32, result: u32) -> InstrNode {
    InstrNode::new(Inst::Load {
        ty,
        ptr: v(ptr),
        volatile: false,
        align: None,
    })
    .with_result(v(result))
}
fn fixture() -> (Module, Function) {
    let mut m = Module::new("");
    m.func_types = vec![FuncTy::unrecorded(vec![handle(), Ty::Ptr], vec![], false)];
    m.structs = vec![StructDef {
        id: StructId::new(0),
        name: "S".into(),
        fields: vec![FieldDef {
            name: "H".into(),
            ty: handle(),
            offset: Some(0),
        }],
        size: Some(8),
        align: Some(8),
        repr: StructRepr::Rust,
        origin: None,
    }];
    let mut f = Function::new(FuncId::new(1099), "F", FuncTyId::new(0), BlockId::new(1));
    let mut b = Block::new(f.entry);
    b.params = vec![(v(0), handle()), (v(99), Ty::Ptr)];
    b.body = vec![
        allocation(handle(), None, None, 10),
        store(handle(), 10, 0),
        load(handle(), 10, 20),
        InstrNode::new(Inst::Return { values: vec![] }),
    ];
    f.blocks.push(b);
    (m, f)
}
fn setup<'m, 'f, O: ExecutionObserver>(
    m: &'m Module,
    f: &'f Function,
    present: bool,
    s: &mut ObservedSession<'_, O>,
) -> (
    trust_ir::LayoutTable<'m>,
    trust_ir::ObservedNominalTypeReachability<'m>,
    ObservedValueTypes,
    Option<ObservedSealedHandleSlots<'f>>,
) {
    let table = trust_ir::LayoutTable::new_observed(m, s, site()).unwrap();
    let nominal = m.nominal_type_reachability_observed(s, site()).unwrap();
    let values = build_module_value_types_observed(f, m, s, site()).unwrap();
    let analysis = if present {
        Some(ObservedSealedHandleSlots::new_observed(&table, f, &nominal, s, site()).unwrap())
    } else {
        None
    };
    (table, nominal, values, analysis)
}
fn dispose<O: ExecutionObserver>(
    table: trust_ir::LayoutTable<'_>,
    nominal: trust_ir::ObservedNominalTypeReachability<'_>,
    values: ObservedValueTypes,
    analysis: Option<ObservedSealedHandleSlots<'_>>,
    s: &mut ObservedSession<'_, O>,
) {
    if let Some(analysis) = analysis {
        let _ = analysis.retire_observed(s, site());
    }
    let _ = values.retire_observed(s, site());
    let _ = nominal.retire_observed(s, site());
    // Fresh observed-only fixture table; this is not general table disposal.
    s.retirement_step(site(), size_of::<trust_ir::LayoutTable<'_>>() + 1);
    drop(table);
    s.retirement_poll(site());
}
fn snapshot(
    a: &ObservedSealedHandleSlots<'_>,
) -> (
    Vec<(u32, Ty, Point, Option<u64>, Option<String>, Vec<Point>)>,
    Vec<(u32, (u32, Point))>,
) {
    (
        a.slots
            .iter()
            .map(|(key, slot)| {
                (
                    *key,
                    slot.ty.clone(),
                    slot.site,
                    slot.natural_align,
                    slot.unsealed.clone(),
                    slot.stores.clone(),
                )
            })
            .collect(),
        a.members
            .iter()
            .map(|(key, value)| (*key, *value))
            .collect(),
    )
}
fn run(m: &Module, f: &Function) -> (Observer, usize, usize) {
    let old_table = trust_ir::LayoutTable::new(m);
    let old_nominal = m.nominal_type_reachability();
    let expected =
        super::super::handle_slots::sealed_slots_test_snapshot(&old_table, f, &old_nominal);
    let mut o = Observer::default();
    let calls = o.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let table = trust_ir::LayoutTable::new_observed(m, &mut s, site()).unwrap();
    let nominal = m
        .nominal_type_reachability_observed(&mut s, site())
        .unwrap();
    let begin = calls.get();
    let a = ObservedSealedHandleSlots::new_observed(&table, f, &nominal, &mut s, site()).unwrap();
    let end = calls.get();
    assert_eq!(snapshot(&a), expected);
    assert_eq!(
        ObservedSealedHandleSlots::function_allocates_a_handle_observed(
            f,
            &nominal,
            &mut s,
            site()
        )
        .unwrap(),
        super::super::handle_slots::allocates_handle_test_oracle(f, &old_nominal)
    );
    a.retire_observed(&mut s, site()).unwrap();
    nominal.retire_observed(&mut s, site()).unwrap();
    s.retirement_step(site(), size_of::<trust_ir::LayoutTable<'_>>() + 1);
    drop(table);
    s.retirement_poll(site());
    assert!(s.first_refusal().is_none());
    assert_eq!(s.remaining_fuel(), InterpretOptions::default().fuel);
    drop(s);
    assert!(o.events.iter().all(|e| e.site == site()));
    assert_eq!(
        o.events[end - 1],
        ExecutionProgress {
            phase: ExecutionPhase::Publication,
            site: site(),
            work: 1,
            copy_bytes: size_of::<ObservedSealedHandleSlots<'_>>()
        }
    );
    (o, begin, end)
}
fn access(
    m: &Module,
    f: &Function,
    inst: &Inst,
    results: &[ValueId],
    at: Point,
    present: bool,
) -> (Result<(), String>, Observer, usize, usize) {
    let old_table = trust_ir::LayoutTable::new(m);
    let old_nominal = m.nominal_type_reachability();
    let old_values = super::super::build_module_value_types(f, m);
    let expected = super::super::handle_slots::sealed_slot_access_test_oracle(
        &old_table,
        f,
        &old_nominal,
        inst,
        results,
        &old_values,
        at.0,
        at.1,
        present,
    );
    let mut o = Observer::default();
    let calls = o.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let (table, nominal, values, a) = setup(m, f, present, &mut s);
    let begin = calls.get();
    let result = handle_slot_rule_observed(
        inst,
        results,
        &values,
        at.0,
        at.1,
        a.as_ref(),
        &mut s,
        site(),
    )
    .unwrap();
    let end = calls.get();
    assert_eq!(result, expected);
    if let Err(reason) = result {
        Work {
            session: &mut s,
            site: site(),
        }
        .flat(reason);
    }
    dispose(table, nominal, values, a, &mut s);
    assert!(s.first_refusal().is_none());
    drop(s);
    assert!(o.events.iter().all(|e| e.site == site()));
    (expected, o, begin, end)
}
fn node_access(m: &Module, f: &Function, block: usize, node: usize) -> Result<(), String> {
    let b = &f.blocks[block];
    let n = &b.body[node];
    access(m, f, &n.inst, &n.results, (b.id, node), true).0
}
fn empty(state: &State) -> bool {
    state.dominators.is_none()
        && state.definitions.is_empty()
        && state.slots.is_empty()
        && state.members.is_empty()
        && state.multiply_defined.capacity() == 0
        && state.operands.capacity() == 0
        && state.unsealing.capacity() == 0
        && state.pending_type.is_none()
        && state.pending_slot.is_none()
        && state.old_slot.is_none()
        && state.pending_unsealed.is_none()
        && state.pending_natural.is_none()
        && state.reason.capacity() == 0
        && state.render.capacity() == 0
}
fn drain<O: ExecutionObserver>(state: &mut State, work: &mut Work<'_, '_, O>) {
    state.retire_scratch(work);
    state.retire_analysis(work);
}
