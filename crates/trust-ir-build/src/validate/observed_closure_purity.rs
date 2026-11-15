// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Complete actual module Pure/stateful-closure signature and node rule.
#![allow(
    dead_code,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::observed_value_types::module_closure_results_observed;
use super::*;
use core::mem::{size_of, take};
use trust_ir::interpret::{
    ExecutionObserver, ExecutionPhase, ExecutionProgress, ExecutionSite, ObservedSession,
    ObservedValueError,
};
use trust_ir::value::ClosureTyId;
mod scan;
mod storage;
#[cfg(test)]
mod tests;
use storage::Work;
type R<T = ()> = Result<T, ObservedValueError>;
#[derive(Default)]
struct State {
    name: String,
    capture: String,
    results: Vec<(usize, ClosureTyId)>,
    errors: Vec<ValidationError>,
}
/// Full original function order, first state-referencing signature capture
/// per function, then every Pure node's actual module-resolved result ordinal
/// and first state-referencing capture. Only exact outer RefMut/PtrMut/Rc are
/// stateful, matching the current ordinary heuristic; no recursive widening.
/// Same original session/site/fuel. Pure annotation scans compare the tag
/// only, never deep unrelated annotation data. Borrowed actual result plans
/// omit redundant full Ty clones, not checks or missing-result diagnostics.
/// No owner/grant/deadline/TLS/callback authority/fallback. This is diagnostic
/// data, not full module/source/proof authority or physical hard-time credit.
pub(super) fn validate_closure_purity_observed<O: ExecutionObserver>(
    module: &Module,
    session: &mut ObservedSession<'_, O>,
    site: ExecutionSite,
) -> R<Vec<ValidationError>> {
    let mut work = Work { session, site };
    work.admit(1, size_of::<State>() + size_of::<Work<'_, '_, O>>())?;
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
impl State {
    fn retire<O: ExecutionObserver>(&mut self, work: &mut Work<'_, '_, O>) {
        work.flat(take(&mut self.name));
        work.flat(take(&mut self.capture));
        work.rows(take(&mut self.results));
    }
}
