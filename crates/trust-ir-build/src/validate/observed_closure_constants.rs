// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Full original module closure-constant environment walk and diagnostics.
#![allow(
    dead_code,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
use core::mem::{size_of, take};
use trust_ir::constant::ConstantChildren;
use trust_ir::interpret::{
    ExecutionObserver, ExecutionPhase, ExecutionProgress, ExecutionSite, ObservedSession,
    ObservedValueError,
};
mod diagnostics;
mod scan;
mod storage;
#[cfg(test)]
mod tests;
mod tree;
use storage::Work;
type R<T = ()> = Result<T, ObservedValueError>;
#[derive(Clone, Copy)]
struct Item<'a> {
    constant: &'a Constant,
    ty: &'a Ty,
    parent: Option<(u32, usize)>,
}
struct Frame<'a> {
    children: ConstantChildren<'a>,
    types: &'a [Ty],
    closure_id: Option<u32>,
    index: usize,
}
#[derive(Default)]
struct State<'a> {
    location: String,
    detail: String,
    expected: String,
    actual: String,
    current: Option<Item<'a>>,
    pending: Vec<Frame<'a>>,
    errors: Vec<ValidationError>,
}
/// Same global-then-function/block/node order and complete actual constant
/// children (splat once, record values in stored order). Only declared closure
/// environments are checked; unknown aggregate child types keep the original
/// Unit sentinel. Arity diagnostics precede child errors, integer/vector
/// values keep the original explicit module pointer width. Module-checked
/// pointer spellings retain the original local defer, never pointer authority.
/// Every actual variable value/tree/UTF8/stack/error operation uses the same
/// supplied original session/site; all partial/prior state drains on typed
/// refusal. No owner/grant/deadline/TLS/fuel/flag/fallback or source/proof
/// capability; complete module/typed-pointer/caller physical bounds stay OPEN.
pub(super) fn validate_closure_constants_observed<O: ExecutionObserver>(
    module: &Module,
    session: &mut ObservedSession<'_, O>,
    site: ExecutionSite,
) -> R<Vec<ValidationError>> {
    let mut work = Work { session, site };
    work.admit(1, size_of::<State<'_>>() + size_of::<Work<'_, '_, O>>())?;
    let mut state = State::default();
    let result = state.run(module, &mut work);
    state.retire(&mut work);
    match result.and_then(|()| work.publication()) {
        Ok(()) => Ok(take(&mut state.errors)),
        Err(error) => {
            let _ =
                retire_validation_errors_observed(take(&mut state.errors), work.session, work.site);
            Err(work.terminal(error))
        }
    }
}
impl State<'_> {
    fn retire_tree<O: ExecutionObserver>(&mut self, work: &mut Work<'_, '_, O>) {
        work.retire(self.current.take());
        loop {
            work.step(size_of::<Option<Frame<'_>>>().saturating_add(1));
            let Some(frame) = self.pending.pop() else {
                break;
            };
            work.retire(frame);
        }
        work.retire(take(&mut self.pending));
    }
    fn retire<O: ExecutionObserver>(&mut self, work: &mut Work<'_, '_, O>) {
        self.retire_tree(work);
        work.flat(take(&mut self.location));
        work.flat(take(&mut self.detail));
        work.flat(take(&mut self.expected));
        work.flat(take(&mut self.actual));
    }
}
