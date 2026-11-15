// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Complete original layout-cast and value-fact tail constituents.
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
use trust_ir::{CastLayoutEvidence, LayoutError};
mod casts;
mod facts;
mod storage;
#[cfg(test)]
mod tests;
use storage::Work;
type R<T = ()> = Result<T, ObservedValueError>;
#[derive(Default)]
struct State {
    result: Option<Result<CastLayoutEvidence, LayoutError>>,
    op: String,
    src: String,
    dst: String,
    reason: String,
    errors: Vec<ValidationError>,
}
/// Complete original module layout-sensitive Cast diagnostic scan. The source
/// is this actual borrowed table's module; no source/layout/proof authority,
/// memo evidence, new owner/grant/deadline/TLS/fuel/flag or callback is created.
pub(super) fn validate_layout_sensitive_casts_observed<O: ExecutionObserver>(
    layouts: &trust_ir::LayoutTable<'_>,
    session: &mut ObservedSession<'_, O>,
    site: ExecutionSite,
) -> R<Vec<ValidationError>> {
    let mut work = Work { session, site };
    work.admit(1, size_of::<State>() + size_of::<Work<'_, '_, O>>())?;
    let mut state = State::default();
    let result = state.casts(layouts, &mut work);
    state.finish(result, &mut work)
}
/// Complete original function-then-node ValueRange/KnownBits consistency scan.
/// These are the same unverified claims, not evidence or an authority grant.
/// Every real source/annotation/error row uses the same original owner/site.
pub(super) fn validate_value_facts_observed<O: ExecutionObserver>(
    module: &Module,
    session: &mut ObservedSession<'_, O>,
    site: ExecutionSite,
) -> R<Vec<ValidationError>> {
    let mut work = Work { session, site };
    work.admit(1, size_of::<State>() + size_of::<Work<'_, '_, O>>())?;
    let mut state = State::default();
    let result = state.facts(module, &mut work);
    state.finish(result, &mut work)
}
impl State {
    fn retire_result<O: ExecutionObserver>(&mut self, work: &mut Work<'_, '_, O>) {
        work.step(size_of::<Option<Result<CastLayoutEvidence, LayoutError>>>().saturating_add(1));
        if let Some(result) = self.result.take() {
            match result {
                Err(error) => {
                    let _ = error.retire_observed(work.session, work.site);
                }
                // Exhaustive Copy-bound payload destruction: a future owning field cannot
                // silently enter a generic Drop fallback or this fixed retirement guard.
                Ok(CastLayoutEvidence::NotLayoutSensitive) => work.fixed(()),
                Ok(CastLayoutEvidence::PointerCast { src, dst }) => work.fixed((src, dst)),
                Ok(CastLayoutEvidence::SameSize {
                    size_bits,
                    src_align_bits,
                    dst_align_bits,
                }) => work.fixed((size_bits, src_align_bits, dst_align_bits)),
                Ok(CastLayoutEvidence::ReifyFnPointer { pointer_bits }) => work.fixed(pointer_bits),
            }
        }
        work.poll();
    }
    fn retire_scratch<O: ExecutionObserver>(&mut self, work: &mut Work<'_, '_, O>) {
        self.retire_result(work);
        work.flat(take(&mut self.op));
        work.flat(take(&mut self.src));
        work.flat(take(&mut self.dst));
        work.flat(take(&mut self.reason));
    }
    fn finish<O: ExecutionObserver>(
        &mut self,
        result: R,
        work: &mut Work<'_, '_, O>,
    ) -> R<Vec<ValidationError>> {
        self.retire_scratch(work);
        match result.and_then(|()| work.publication()) {
            Ok(()) => Ok(take(&mut self.errors)),
            Err(error) => {
                let _ = retire_validation_errors_observed(
                    take(&mut self.errors),
                    work.session,
                    work.site,
                );
                Err(work.terminal(error))
            }
        }
    }
}
