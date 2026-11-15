// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Authored UNRUN: actual original niche/nominal/layout children are oracles.
#![allow(
    clippy::drop_non_drop,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
use std::{cell::Cell, rc::Rc};
use trust_ir::interpret::InterpretOptions;
use trust_ir::ty::{EnumLayoutDescriptor, EnumTagRepr, EnumVariant};
use trust_ir::value::{EnumId, TyId};
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
            return Err("original handle-lane stop");
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
    ExecutionSite::Entry(FuncId::new(1021))
}
fn handle() -> Ty {
    Ty::handle("Name", "rt::Name")
}
fn enumeration(id: u32, name: &str, fields: Vec<Ty>, offsets: Vec<u64>, niche: u64) -> EnumDef {
    let mut e = EnumDef::new(
        EnumId::new(id),
        name,
        vec![EnumVariant {
            name: "Variant".into(),
            fields,
            field_names: vec![],
        }],
    );
    e.layout = Some(EnumLayoutDescriptor {
        encoding: EnumTagEncoding::Niche {
            untagged_variant: 0,
            niche_variants_start: 1,
            niche_variants_end: 1,
            niche_start: 0,
            niche_offset: niche,
            niche_ty: EnumTagRepr::U8,
        },
        size: 32,
        align: 8,
        variant_field_offsets: vec![offsets],
    });
    e
}
fn fixture() -> Module {
    let mut m = Module::new("");
    m.enums = vec![enumeration(
        17,
        "raw enum λ'\0",
        vec![Ty::Bool, handle()],
        vec![16, 0],
        0,
    )];
    m
}
fn semantic_ty() -> Ty {
    Ty::Tuple(vec![
        handle(),
        Ty::Dialect(Box::new(trust_ir::DialectTy::new("raw", "Opaque", 1))),
    ])
}
fn setup<'m, O: ExecutionObserver>(
    m: &'m Module,
    s: &mut ObservedSession<'_, O>,
) -> (LayoutTable<'m>, ObservedNominalTypeReachability<'m>) {
    let table = LayoutTable::new_observed(m, s, site()).unwrap();
    let nominal = m.nominal_type_reachability_observed(s, site()).unwrap();
    (table, nominal)
}
fn dispose<O: ExecutionObserver>(
    table: LayoutTable<'_>,
    nominal: ObservedNominalTypeReachability<'_>,
    s: &mut ObservedSession<'_, O>,
) {
    let _ = nominal.retire_observed(s, site());
    // This fixture creates a fresh observed table and uses only observed
    // queries, whose source never populates its ordinary memo. This is NOT
    // a general table-retirement API or proof about arbitrary borrowed tables.
    s.retirement_step(site(), size_of::<LayoutTable<'_>>() + 1);
    drop(table);
    s.retirement_poll(site());
}
fn run(m: &Module) -> (Vec<ValidationError>, Observer, usize, usize) {
    let old = LayoutTable::new(m);
    let old_nominal = m.nominal_type_reachability();
    let expected = super::super::validate_handle_enum_layouts(&old, &old_nominal);
    let mut o = Observer::default();
    let calls = o.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let (table, nominal) = setup(m, &mut s);
    let begin = calls.get();
    let out = validate_handle_enum_layouts_observed(&table, &nominal, &mut s, site()).unwrap();
    let end = calls.get();
    assert_eq!(out, expected);
    assert!(s.first_refusal().is_none());
    assert_eq!(s.remaining_fuel(), InterpretOptions::default().fuel);
    retire_validation_errors_observed(out, &mut s, site()).unwrap();
    dispose(table, nominal, &mut s);
    drop(s);
    assert!(o.events.iter().all(|e| e.site == site()));
    assert_eq!(
        o.events[end - 1].copy_bytes,
        size_of::<Vec<ValidationError>>()
    );
    (expected, o, begin, end)
}
fn drain<O: ExecutionObserver>(state: &mut State, work: &mut Work<'_, '_, O>) {
    state.retire_scratch(work);
    let _ = retire_validation_errors_observed(take(&mut state.errors), work.session, work.site);
}
fn empty(s: &State) -> bool {
    s.shape.is_none()
        && s.error.is_none()
        && s.name.capacity() == 0
        && s.detail.capacity() == 0
        && s.render.capacity() == 0
        && s.errors.capacity() == 0
}
