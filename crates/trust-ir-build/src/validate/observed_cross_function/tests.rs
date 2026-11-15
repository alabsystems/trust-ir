// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Authored UNRUN. The whole actual ordinary closure is the parity oracle.
#![allow(
    clippy::drop_non_drop,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
use std::{
    cell::{Cell, RefCell},
    rc::Rc,
};
use trust_ir::dialect::DialectInst;
use trust_ir::dialect::schema::DialectSchema;
use trust_ir::interpret::InterpretOptions;
use trust_ir::value::{FuncTyId, PredId, TyId};
use trust_ir::{AssertKind, Block, CallingConv, InstrNode, PanicLocation, PanicSite};
mod custody;
mod fixtures;
mod original;
mod parity;
mod stops;
use fixtures::*;
#[derive(Default)]
struct Observer {
    events: Vec<ExecutionProgress>,
    trace: Rc<RefCell<Vec<ExecutionProgress>>>,
    interrupt: Option<Rc<Cell<bool>>>,
    calls: Rc<Cell<usize>>,
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
        self.trace.borrow_mut().push(e);
        self.calls.set(self.events.len());
        if self.stop == Some(self.events.len()) {
            return Err("original cross-function stop");
        }
        if self.interrupt.as_ref().is_some_and(|a| a.get()) {
            return Err("interrupt");
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
            return Err("copy");
        }
        Ok(())
    }
}

fn site() -> ExecutionSite {
    ExecutionSite::Entry(FuncId::new(6301))
}
fn v(n: u32) -> ValueId {
    ValueId::new(n)
}
fn registry() -> HandleRegistry {
    HandleRegistry {
        pins: TRUSTED_HANDLE_RUNTIMES.to_vec(),
    }
}
fn setup<'m, O: ExecutionObserver>(
    m: &'m Module,
    s: &mut ObservedSession<'_, O>,
) -> (
    trust_ir::LayoutTable<'m>,
    ModuleFunctionCatalog<'m>,
    NominalCensus,
    Option<ObservedNominalTypeReachability<'m>>,
) {
    let layouts = trust_ir::LayoutTable::new_observed(m, s, site()).unwrap();
    let catalog = ModuleFunctionCatalog::new_observed(m, s, site()).unwrap();
    let (errors, census) =
        super::super::observed_type_inventory::validate_type_table_references_observed(
            m,
            &registry(),
            s,
            site(),
        )
        .unwrap();
    retire_validation_errors_observed(errors, s, site()).unwrap();
    let nominal = if census.handle || census.dialect {
        Some(m.nominal_type_reachability_observed(s, site()).unwrap())
    } else {
        None
    };
    (layouts, catalog, census, nominal)
}
fn dispose<O: ExecutionObserver>(
    layouts: trust_ir::LayoutTable<'_>,
    catalog: ModuleFunctionCatalog<'_>,
    nominal: Option<ObservedNominalTypeReachability<'_>>,
    s: &mut ObservedSession<'_, O>,
) {
    if let Some(nominal) = nominal {
        let _ = nominal.retire_observed(s, site());
    }
    let _ = catalog.retire_observed(s, site());
    // Exact corrected observed constructor leaves ordinary memo=None. No
    // ordinary layout query is used by this test setup or actual observed pass.
    s.retirement_step(site(), size_of::<trust_ir::LayoutTable<'_>>() + 1);
    drop(layouts);
    s.retirement_poll(site());
}
fn run(
    m: &Module,
    physical: usize,
    schemas: Option<&DialectSchemaRegistry>,
) -> (Vec<ValidationError>, Observer, usize, usize) {
    let expected = original::run(m, physical, schemas);
    let mut o = Observer::default();
    let calls = o.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let (layouts, catalog, census, nominal) = setup(m, &mut s);
    let begin = calls.get();
    let out = validate_cross_function_observed(
        &layouts,
        &catalog,
        physical,
        census,
        nominal.as_ref(),
        schemas,
        &mut s,
        site(),
    )
    .unwrap();
    let end = calls.get();
    assert_eq!(out, expected);
    retire_validation_errors_observed(out, &mut s, site()).unwrap();
    dispose(layouts, catalog, nominal, &mut s);
    assert!(s.first_refusal().is_none());
    assert_eq!(s.remaining_fuel(), InterpretOptions::default().fuel);
    drop(s);
    assert!(o.events[begin..].iter().all(|e| e.site == site()));
    (expected, o, begin, end)
}
fn empty(s: &State<'_, '_>) {
    assert!(
        s.signature.is_none()
            && s.getter.is_none()
            && s.values.is_none()
            && s.guards.is_none()
            && s.slots.is_none()
            && s.indirect.is_none()
    );
    assert_eq!(s.pending.capacity() + s.errors.capacity(), 0);
}
fn drain<O: ExecutionObserver>(s: &mut State<'_, '_>, w: &mut Work<'_, '_, O>) {
    let _ = s.retire_children(w);
    let _ = retire_validation_errors_observed(take(&mut s.errors), w.session, w.site);
}
