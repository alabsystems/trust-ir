// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Actual original declared-struct rules and prior-error suppression.
#![allow(
    dead_code,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
use core::mem::{size_of, take};
use std::sync::Arc;
use trust_ir::interpret::{
    ExecutionObserver, ExecutionPhase, ExecutionProgress, ExecutionSite, ObservedSession,
    ObservedValueError,
};
use trust_ir::shape::TyLayoutShape;
use trust_ir::{LayoutError, LayoutTable};
mod precise;
mod query;
mod scan;
mod storage;
#[cfg(test)]
mod tests;
use storage::Work;
type R<T = ()> = Result<T, ObservedValueError>;
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct Summary {
    size: Option<u64>,
    align: Option<u64>,
}
#[derive(Default)]
struct State<'m> {
    table: Option<LayoutTable<'m>>,
    shape: Option<Arc<TyLayoutShape>>,
    error: Option<LayoutError>,
    triple: String,
    ranges: Vec<(u64, u64)>,
    reported: Vec<u32>,
    errors: Vec<ValidationError>,
}
/// Exact original precise struct layout rules, followed by the same generic
/// coherence refusal and original `prior` suppression. This private constituent
/// accepts only its enclosing module pass's prior diagnostics; it does not turn
/// caller-selected suppression data into an externally admissible verdict. It
/// constructs a fresh
/// private table and uses only its observed queries, which never fill ordinary
/// memo; fixed empty-memo release is specific to this owning path. Repeated
/// queries and pair comparisons charge actual work, without claiming original
/// memo/sweep complexity. No unobserved validator/layout/format callback runs.
///
/// Actual returned Arc/error is retained before subsequent fallible work and
/// fully consumed under the supplied same original session/site before any
/// outward publication. No partial list or accepting fallback, authority, new
/// owner/grant/deadline/TLS/fuel/flag. Full module/source/HIR/proof/native and MC
/// orchestration remain OPEN, as do successful caller/input disposal and
/// physical std/allocator/deallocator/OOM/panic/unwind/RSS/hard100ms limits.
pub(super) fn validate_module_declared_struct_layouts_observed<O: ExecutionObserver>(
    module: &Module,
    prior: &[ValidationError],
    session: &mut ObservedSession<'_, O>,
    site: ExecutionSite,
) -> R<Vec<ValidationError>> {
    session.admit(ExecutionProgress {
        phase: ExecutionPhase::Validation,
        site,
        work: 1,
        copy_bytes: size_of::<State<'_>>() + size_of::<Work<'_, '_, O>>(),
    })?;
    let mut state = State::default();
    let mut work = Work { session, site };
    let result = state.run(module, prior, &mut work);
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
impl State<'_> {
    fn push<O: ExecutionObserver>(
        &mut self,
        id: u32,
        reason: &'static str,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        work.reserve(&mut self.errors)?;
        work.admit(1, size_of::<ValidationError>())?;
        self.errors.push(ValidationError::StructLayoutInconsistent {
            struct_id: id,
            reason,
        });
        Ok(())
    }
    fn target_error<O: ExecutionObserver>(&mut self, id: u32, work: &mut Work<'_, '_, O>) -> R {
        work.reserve(&mut self.errors)?;
        work.admit(1, size_of::<ValidationError>())?;
        self.errors
            .push(ValidationError::TargetScalarLayoutUnavailable {
                struct_id: id,
                triple: take(&mut self.triple),
            });
        Ok(())
    }
    fn retire_shape<O: ExecutionObserver>(&mut self, work: &mut Work<'_, '_, O>) {
        work.session.retirement_step(
            work.site,
            size_of::<Option<Arc<TyLayoutShape>>>().saturating_add(1),
        );
        if let Some(shape) = self.shape.take() {
            let _ = shape.retire_arc_observed(work.session, work.site);
        }
        work.session.retirement_poll(work.site);
    }
    fn retire_error<O: ExecutionObserver>(&mut self, work: &mut Work<'_, '_, O>) {
        work.session.retirement_step(
            work.site,
            size_of::<Option<LayoutError>>().saturating_add(1),
        );
        if let Some(error) = self.error.take() {
            let _ = error.retire_observed(work.session, work.site);
        }
        work.session.retirement_poll(work.site);
    }
    fn retire_scratch<O: ExecutionObserver>(&mut self, work: &mut Work<'_, '_, O>) {
        self.retire_shape(work);
        self.retire_error(work);
        work.retire_text(&mut self.triple);
        retire_fixed(take(&mut self.ranges), work);
        retire_fixed(take(&mut self.reported), work);
        work.session.retirement_step(
            work.site,
            size_of::<Option<LayoutTable<'_>>>().saturating_add(1),
        );
        drop(self.table.take());
        work.session.retirement_poll(work.site);
    }
}
fn retire_fixed<T: Copy, O: ExecutionObserver>(mut rows: Vec<T>, work: &mut Work<'_, '_, O>) {
    loop {
        work.session
            .retirement_step(work.site, size_of::<Option<T>>().saturating_add(1));
        if rows.pop().is_none() {
            break;
        }
    }
    work.session
        .retirement_step(work.site, size_of::<Vec<T>>().saturating_add(1));
    drop(rows);
    work.session.retirement_poll(work.site);
}
