// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Original debug-span, branch-weight and diagnostic-obligation constituents.
use super::*;
use core::mem::{size_of, take};
use trust_ir::interpret::{
    ExecutionObserver, ExecutionPhase, ExecutionProgress, ExecutionSite, ObservedSession,
    ObservedValueError,
};
mod scan;
mod storage;
#[cfg(test)]
mod tests;
use storage::Work;
type R<T = ()> = Result<T, ObservedValueError>;
#[derive(Default)]
struct State {
    ids: Vec<u32>,
    errors: Vec<ValidationError>,
}
#[derive(Clone, Copy)]
enum Component {
    Spans,
    Weights,
    Diagnostics,
}
#[derive(Clone, Copy)]
enum FixedError {
    Span { file: u32, file_count: usize },
    Weights(&'static str),
    Diagnostic(u32),
}
/// Exact original file-table range diagnostics, in physical scope/node/sidecar
/// order. Empty file tables retain the original no-check meaning, not authority.
pub fn validate_module_span_files_observed<O: ExecutionObserver>(
    module: &Module,
    session: &mut ObservedSession<'_, O>,
    site: ExecutionSite,
) -> R<Vec<ValidationError>> {
    component(module, Component::Spans, session, site)
}
/// Exact original function/node branch-weight placement and arity diagnostics.
/// The weights' numeric payload is irrelevant to this original rule.
pub fn validate_module_branch_weights_observed<O: ExecutionObserver>(
    module: &Module,
    session: &mut ObservedSession<'_, O>,
    site: ExecutionSite,
) -> R<Vec<ValidationError>> {
    component(module, Component::Weights, session, site)
}
/// Exact original diagnostic-to-obligation-ID membership diagnostics. Every
/// original ID is visited first, then each physical diagnostic is checked.
/// Borrowed scalar membership searches replace only the discarded tree index;
/// real repeated comparisons are charged, without a complexity-parity claim.
pub fn validate_module_diagnostic_obligations_observed<O: ExecutionObserver>(
    module: &Module,
    session: &mut ObservedSession<'_, O>,
    site: ExecutionSite,
) -> R<Vec<ValidationError>> {
    component(module, Component::Diagnostics, session, site)
}
// All three APIs retain the same supplied original owner/session/site. Refusal
// consumes all helper scratch/completed diagnostics and never publishes a
// shorter list. No source/proof/completeness authority or whole-module result.
// Successful output/input disposal and physical allocator/deallocator/OOM/
// panic/unwind/RSS/stdlib/hard100ms remain OPEN. No grant/deadline/TLS/fuel/flag.
fn component<O: ExecutionObserver>(
    module: &Module,
    kind: Component,
    session: &mut ObservedSession<'_, O>,
    site: ExecutionSite,
) -> R<Vec<ValidationError>> {
    session.admit(ExecutionProgress {
        phase: ExecutionPhase::Validation,
        site,
        work: 1,
        copy_bytes: size_of::<State>() + size_of::<Work<'_, '_, O>>(),
    })?;
    let mut state = State::default();
    let mut work = Work { session, site };
    let result = match kind {
        Component::Spans => state.spans(module, &mut work),
        Component::Weights => state.weights(module, &mut work),
        Component::Diagnostics => state.diagnostics(module, &mut work),
    };
    state.retire_ids(&mut work);
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
    fn push<O: ExecutionObserver>(&mut self, error: FixedError, work: &mut Work<'_, '_, O>) -> R {
        // This private enum accepts only fixed scalar/static payloads; no owned
        // error can be implicitly dropped if output allocation/admission stops.
        work.reserve(&mut self.errors)?;
        work.admit(1, size_of::<ValidationError>())?;
        self.errors.push(match error {
            FixedError::Span { file, file_count } => {
                ValidationError::SpanFileIndexOutOfRange { file, file_count }
            }
            FixedError::Weights(reason) => ValidationError::BranchWeightsMismatch { reason },
            FixedError::Diagnostic(obligation) => {
                ValidationError::DanglingDiagnosticObligation { obligation }
            }
        });
        Ok(())
    }
    fn retire_ids<O: ExecutionObserver>(&mut self, work: &mut Work<'_, '_, O>) {
        loop {
            work.session
                .retirement_step(work.site, size_of::<Option<u32>>().saturating_add(1));
            if self.ids.pop().is_none() {
                break;
            }
        }
        work.session
            .retirement_step(work.site, size_of::<Vec<u32>>().saturating_add(1));
        drop(take(&mut self.ids));
        work.session.retirement_poll(work.site);
    }
}
