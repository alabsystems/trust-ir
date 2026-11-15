// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Actual Call/CallCannotUnwind/Invoke module argument diagnostics.
#![allow(
    dead_code,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::observed_nominal_varargs::validate_nominal_varargs_observed;
use super::*;
use core::mem::{size_of, take};
use trust_ir::interpret::{
    ExecutionObserver, ExecutionPhase, ExecutionProgress, ExecutionSite, ObservedSession,
    ObservedValueError,
};
use trust_ir::{ObservedNominalTypeReachability, Producer};
mod diagnostics;
mod merge;
mod producer;
mod storage;
#[cfg(test)]
mod tests;
mod walk;
use storage::Work;
type R<T = ()> = Result<T, ObservedValueError>;
#[derive(Default)]
struct State {
    name: String,
    expected: String,
    actual: String,
    caller: Option<String>,
    callee: Option<String>,
    pending: Vec<ValidationError>,
    errors: Vec<ValidationError>,
}
/// Complete original direct-edge callee/signature/vararg/count/type diagnostics.
/// Derives the actual module only from its supplied bound catalog; no alternate
/// module, result callback or candidate declaration can select a callee.
/// Permanent ambiguity is semantic CalleeNotFound, never arbitrary selection.
/// The original function/value map/optional nominal identity remains mandatory
/// caller context. None nominal is only the original census-derived legacy
/// lane, never a replacement for operational refusal.
///
/// This diagnostic constituent is not calling-convention, edge, source, SSA,
/// refinement, handle-origin, runtime, module or proof authority. Ordinary Call
/// and Invoke refinement behavior stays exactly distinct. Every full child,
/// producer/type string and prior error is owned before the next fallible fee;
/// all are consumed after stop before any shorter output could escape. Original
/// session/site/fuel/grant/deadline remain unchanged. Physical/caller duties OPEN.
pub(super) fn validate_direct_call_observed<O: ExecutionObserver>(
    catalog: &ModuleFunctionCatalog<'_>,
    caller: &Function,
    inst: &Inst,
    values: &ObservedValueTypes,
    nominal: Option<&ObservedNominalTypeReachability<'_>>,
    block: BlockId,
    session: &mut ObservedSession<'_, O>,
    site: ExecutionSite,
) -> R<Vec<ValidationError>> {
    let mut work = Work { session, site };
    work.admit(1, size_of::<State>() + size_of::<Work<'_, '_, O>>())?;
    let mut state = State::default();
    let result = state.run(catalog, caller, inst, values, nominal, block, &mut work);
    state.retire_scratch(&mut work);
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
    fn retire_scratch<O: ExecutionObserver>(&mut self, work: &mut Work<'_, '_, O>) {
        work.flat(take(&mut self.name));
        work.flat(take(&mut self.expected));
        work.flat(take(&mut self.actual));
        work.step(2 * size_of::<Option<String>>() + 1);
        if let Some(text) = self.caller.take() {
            work.flat(text);
        }
        if let Some(text) = self.callee.take() {
            work.flat(text);
        }
        work.poll();
        self.retire_pending(work);
    }
    fn retire_pending<O: ExecutionObserver>(&mut self, work: &mut Work<'_, '_, O>) {
        let _ = retire_validation_errors_observed(take(&mut self.pending), work.session, work.site);
    }
}
