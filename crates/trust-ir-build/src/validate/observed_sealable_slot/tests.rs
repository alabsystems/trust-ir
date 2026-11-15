// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Authored UNRUN against exact ordinary predicate through cfg(test) wrapper.
#![allow(
    clippy::drop_non_drop,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
use std::{cell::Cell, rc::Rc};
use trust_ir::interpret::InterpretOptions;
use trust_ir::ty::{EnumDef, EnumVariant, StructRepr};
use trust_ir::value::{EnumId, TyId};
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
            return Err("original sealable stop");
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
    ExecutionSite::Entry(FuncId::new(1095))
}
fn handle() -> Ty {
    Ty::handle("Name", "rt::Name")
}
fn structure(id: u32, fields: Vec<Ty>) -> StructDef {
    StructDef {
        id: StructId::new(id),
        name: format!("S{id}"),
        fields: fields
            .into_iter()
            .enumerate()
            .map(|(i, ty)| FieldDef {
                name: i.to_string(),
                ty,
                offset: None,
            })
            .collect(),
        size: None,
        align: None,
        repr: StructRepr::Rust,
        origin: None,
    }
}
fn fixture() -> Module {
    let mut m = Module::new("");
    m.types = vec![handle()];
    m.structs = vec![
        structure(0, vec![handle(), Ty::Bool]),
        structure(1, vec![Ty::Struct(StructId::new(0)), Ty::Ptr]),
    ];
    m.enums = vec![EnumDef::new(
        EnumId::new(0),
        "E",
        vec![EnumVariant {
            name: "V".into(),
            fields: vec![handle()],
            field_names: vec![],
        }],
    )];
    m
}
fn run(m: &Module, ty: &Ty) -> (bool, Observer, usize, usize) {
    let old = m.nominal_type_reachability();
    let expected = super::super::handle_slots::sealable_slot_type_test_oracle(m, &old, ty);
    let mut o = Observer::default();
    let calls = o.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let nominal = m
        .nominal_type_reachability_observed(&mut s, site())
        .unwrap();
    let begin = calls.get();
    let actual = sealable_slot_type_observed(m, &nominal, ty, &mut s, site()).unwrap();
    let end = calls.get();
    assert_eq!(actual, expected);
    assert!(s.first_refusal().is_none());
    assert_eq!(s.remaining_fuel(), InterpretOptions::default().fuel);
    nominal.retire_observed(&mut s, site()).unwrap();
    drop(s);
    assert!(o.events.iter().all(|e| e.site == site()));
    assert_eq!(
        o.events[end - 1],
        ExecutionProgress {
            phase: ExecutionPhase::Publication,
            site: site(),
            work: 1,
            copy_bytes: size_of::<bool>()
        }
    );
    (expected, o, begin, end)
}
fn empty(state: &State<'_>) -> bool {
    state.frames.capacity() == 0 && state.visiting.capacity() == 0
}
