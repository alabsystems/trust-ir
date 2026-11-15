// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Complete original weak-declaration use and local copy-origin rule.
#![allow(
    dead_code,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
use core::mem::{size_of, take};
use trust_ir::interpret::{
    ExecutionObserver, ExecutionPhase, ExecutionProgress, ExecutionSite, ObservedSession,
    ObservedValueError,
};
use trust_ir::value::FuncTyId;
mod definitions;
mod diagnostics;
mod queries;
mod render;
mod scan;
mod storage;
#[cfg(test)]
mod tests;
mod tree;
use storage::Work;
type R<T = ()> = Result<T, ObservedValueError>;
#[derive(Clone, Copy)]
enum Children<'m> {
    Values(&'m [Constant]),
    Fields(&'m [(String, Constant)]),
    One(Option<&'m Constant>),
    None,
}
#[derive(Clone, Copy)]
struct Frame<'m> {
    children: Children<'m>,
    remaining: usize,
}
#[derive(Default)]
struct State<'m> {
    definitions: Vec<(u32, &'m Inst)>,
    current: Option<&'m Constant>,
    frames: Vec<Frame<'m>>,
    location: String,
    here: String,
    name: String,
    symbol: String,
    detail: String,
    declared: String,
    actual: String,
    render: String,
    errors: Vec<ValidationError>,
}
/// Same actual catalog source and original function/block/node/case order.
/// Actual weak-name queries choose the LAST same-name bodyless ExternalWeak
/// declaration, while FnDef/closure IDs use the unique catalog. Definitions
/// retain each singleton result's last physical Inst; Copy origins have the
/// exact unique-definition-count+1 step bound, not stronger pointer authority.
/// Switch trees keep root-before-reverse-sibling DFS of the original stack.
/// Every actual source/query/child/byte/growth/error work is observed with this
/// SAME original session/site; all scratch and owning outputs remain held
/// through transfer/full retirement. No new owner/grant/deadline/TLS/fuel/flag,
/// callback/map/accepting fallback, validation/proof/source capability or
/// physical std/allocator/OOM/panic/unwind/RSS/hard-time guarantee.
pub(super) fn validate_weak_declaration_uses_observed<O: ExecutionObserver>(
    catalog: &ModuleFunctionCatalog<'_>,
    session: &mut ObservedSession<'_, O>,
    site: ExecutionSite,
) -> R<Vec<ValidationError>> {
    let mut work = Work { session, site };
    work.admit(1, size_of::<State<'_>>() + size_of::<Work<'_, '_, O>>())?;
    let mut state = State::default();
    let result = state.run(catalog, &mut work);
    state.retire_scratch(&mut work);
    match result.and_then(|()| work.publication()) {
        Ok(()) => Ok(take(&mut state.errors)),
        Err(e) => {
            let _ =
                retire_validation_errors_observed(take(&mut state.errors), work.session, work.site);
            Err(work.terminal(e))
        }
    }
}
impl State<'_> {
    fn retire_tree<O: ExecutionObserver>(&mut self, work: &mut Work<'_, '_, O>) {
        work.fixed(self.current.take());
        work.rows(take(&mut self.frames));
    }
    fn retire_definitions<O: ExecutionObserver>(&mut self, work: &mut Work<'_, '_, O>) {
        work.rows(take(&mut self.definitions));
    }
    fn retire_scratch<O: ExecutionObserver>(&mut self, work: &mut Work<'_, '_, O>) {
        self.retire_tree(work);
        self.retire_definitions(work);
        work.flat(take(&mut self.location));
        work.flat(take(&mut self.here));
        work.flat(take(&mut self.name));
        work.flat(take(&mut self.symbol));
        work.flat(take(&mut self.detail));
        work.flat(take(&mut self.declared));
        work.flat(take(&mut self.actual));
        work.flat(take(&mut self.render));
    }
}
