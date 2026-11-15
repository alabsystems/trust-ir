// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Authored UNRUN; actual original set/catalog loops are oracles.
#![allow(
    clippy::drop_non_drop,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
use std::{cell::Cell, rc::Rc};
use trust_ir::interpret::InterpretOptions;
use trust_ir::value::{FuncTyId, StructId};
mod custody;
mod parity;
mod stops;
#[derive(Clone, Copy)]
enum Group {
    Structs,
    Functions,
}
#[derive(Default)]
struct Observer {
    events: Vec<ExecutionProgress>,
    calls: Rc<Cell<usize>>,
    stop: Option<usize>,
    arm: Option<Rc<Cell<bool>>>,
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
        self.calls.set(self.events.len());
        if self.stop == Some(self.events.len()) || self.arm.as_ref().is_some_and(|a| a.get()) {
            return Err("original module IDs");
        }
        if self.cleanup.as_ref().is_some_and(|a| a.get())
            && e.phase == ExecutionPhase::ScratchRetirement
        {
            return Err("cleanup");
        }
        self.work = self.work.checked_add(e.work).ok_or("overflow")?;
        self.bytes = self.bytes.checked_add(e.copy_bytes).ok_or("overflow")?;
        if self.work_cap.is_some_and(|c| self.work > c) {
            return Err("work");
        }
        if self.byte_cap.is_some_and(|c| self.bytes > c) {
            return Err("copy");
        }
        Ok(())
    }
}
fn site() -> ExecutionSite {
    ExecutionSite::Entry(FuncId::new(7601))
}
fn module(ids: &[u32]) -> Module {
    let mut m = Module::new("IDs");
    for id in ids {
        m.structs.push(trust_ir::ty::StructDef {
            id: StructId::new(*id),
            name: format!("s{id}"),
            fields: vec![],
            size: None,
            align: None,
            repr: trust_ir::StructRepr::Rust,
            origin: None,
        });
        m.functions.push(Function::new(
            FuncId::new(*id),
            format!("f{id}"),
            FuncTyId::new(0),
            BlockId::new(0),
        ));
    }
    m
}
fn expected(m: &Module, group: Group) -> Vec<ValidationError> {
    match group {
        Group::Structs => {
            let mut seen = BTreeSet::new();
            m.structs
                .iter()
                .filter_map(|s| {
                    (!seen.insert(s.id.index()))
                        .then_some(ValidationError::DuplicateStructId(s.id.index()))
                })
                .collect()
        }
        Group::Functions => ModuleFunctionCatalog::new(m)
            .ambiguous_ids()
            .map(ValidationError::DuplicateFuncId)
            .collect(),
    }
}
fn call<O: ExecutionObserver>(
    m: &Module,
    catalog: &ModuleFunctionCatalog<'_>,
    group: Group,
    s: &mut ObservedSession<'_, O>,
) -> R<Vec<ValidationError>> {
    match group {
        Group::Structs => validate_module_struct_ids_observed(m, s, site()),
        Group::Functions => validate_module_function_ids_observed(catalog, s, site()),
    }
}
fn run(m: &Module, group: Group) -> (Vec<ValidationError>, Observer, usize) {
    let catalog = ModuleFunctionCatalog::new(m);
    let mut o = Observer::default();
    let calls = o.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let errors = call(m, &catalog, group, &mut s).unwrap();
    let end = calls.get();
    assert_eq!(errors, expected(m, group));
    let copy = errors.clone();
    retire_validation_errors_observed(errors, &mut s, site()).unwrap();
    assert!(s.first_refusal().is_none());
    assert_eq!(s.remaining_fuel(), InterpretOptions::default().fuel);
    drop(s);
    assert!(o.events.iter().all(|e| e.site == site()));
    (copy, o, end)
}
fn drain<O: ExecutionObserver>(state: &mut State, w: &mut Work<'_, '_, O>) {
    w.rows(take(&mut state.ids));
    let _ = retire_validation_errors_observed(take(&mut state.errors), w.session, w.site);
}
fn empty(state: &State) {
    assert_eq!(state.ids.capacity() + state.errors.capacity(), 0);
}

mod error_precedence;
