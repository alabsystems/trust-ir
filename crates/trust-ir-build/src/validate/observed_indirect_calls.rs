// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Exact indirect-edge diagnostics from actual catalog/function coordinates.
#![allow(
    dead_code,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::observed_closure_targets::ObservedLocalClosureTargets;
use super::observed_nominal_varargs::validate_nominal_varargs_observed;
use super::*;
use core::mem::{size_of, take};
use trust_ir::analysis::ObservedStaticFunctionPointerAnalysis;
use trust_ir::interpret::{
    ExecutionObserver, ExecutionPhase, ExecutionProgress, ExecutionSite, ObservedSession,
    ObservedValueError,
};
use trust_ir::{CallingConv, ObservedNominalTypeReachability};
mod checks;
mod closures;
mod context;
mod diagnostics;
mod merge;
mod pointers;
mod render;
mod storage;
#[cfg(test)]
mod tests;
use storage::Work;
type R<T = ()> = Result<T, ObservedValueError>;
/// Actual physical function borrowed from this exact catalog source. Owns the
/// actual once-per-function closure map and lazy typed-pointer caches, never a
/// candidate callback/map or another same-ID function's analysis. This is only
/// diagnostic data, not module/source/proof/transformation authority.
pub(super) struct ObservedIndirectCalls<'c, 'm> {
    catalog: &'c ModuleFunctionCatalog<'m>,
    function: &'m Function,
    closures: Option<ObservedLocalClosureTargets<'m>>,
    pointers: Option<ObservedStaticFunctionPointerAnalysis<'m>>,
    item_origins: Option<bool>,
}
#[derive(Default)]
struct State {
    name: String,
    detail: String,
    expected: String,
    actual: String,
    render: String,
    pending: Vec<ValidationError>,
    errors: Vec<ValidationError>,
}
impl ObservedIndirectCalls<'_, '_> {
    /// Derive the actual node from physical source coordinates; all three
    /// indirect families take identical original checks. Missing signature
    /// remains one semantic diagnostic followed by the original immediate skip;
    /// operational errors never become dynamic None or omit later errors.
    /// Optional nominal summary is only the original complete census lane.
    /// Same original session/site/grant/deadline/TLS/fuel; logical standard
    /// primitives give no physical allocator/panic/RSS/hard-time guarantee.
    pub(super) fn validate_at_observed<O: ExecutionObserver>(
        &mut self,
        physical_block: usize,
        instruction: usize,
        values: &ObservedValueTypes,
        nominal: Option<&ObservedNominalTypeReachability<'_>>,
        session: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> R<Vec<ValidationError>> {
        let mut work = Work { session, site };
        if let Err(error) = work.admit(1, size_of::<State>() + size_of::<Work<'_, '_, O>>()) {
            self.retire_inner(&mut work);
            return Err(work.terminal(error));
        }
        if self.closures.is_none() || self.pointers.is_none() {
            self.retire_inner(&mut work);
            return Err(work.terminal(ObservedValueError::InvalidRange));
        }
        let mut state = State::default();
        let result = state.run(
            self,
            physical_block,
            instruction,
            values,
            nominal,
            &mut work,
        );
        state.retire_scratch(&mut work);
        match result.and_then(|()| work.publication(size_of::<Vec<ValidationError>>())) {
            Ok(()) => Ok(take(&mut state.errors)),
            Err(error) => {
                let _ = retire_validation_errors_observed(
                    take(&mut state.errors),
                    work.session,
                    work.site,
                );
                self.retire_inner(&mut work);
                Err(work.terminal(error))
            }
        }
    }
}
impl State {
    fn retire_scratch<O: ExecutionObserver>(&mut self, work: &mut Work<'_, '_, O>) {
        work.flat(take(&mut self.name));
        work.flat(take(&mut self.detail));
        work.flat(take(&mut self.expected));
        work.flat(take(&mut self.actual));
        work.flat(take(&mut self.render));
        self.retire_pending(work);
    }
    fn retire_pending<O: ExecutionObserver>(&mut self, work: &mut Work<'_, '_, O>) {
        let _ = retire_validation_errors_observed(take(&mut self.pending), work.session, work.site);
    }
}
