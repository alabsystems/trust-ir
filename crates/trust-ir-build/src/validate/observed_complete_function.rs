// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Complete original function-local pass orchestration, not module authority.
use super::*;
use core::mem::{size_of, take};
use trust_ir::interpret::{
    ExecutionObserver, ExecutionPhase, ExecutionProgress, ExecutionSite, ObservedSession,
    ObservedValueError,
};
mod storage;
#[cfg(test)]
mod tests;
mod walk;
use storage::Work;
type R<T = ()> = Result<T, ObservedValueError>;
#[derive(Default)]
struct State {
    errors: Vec<ValidationError>,
    pending: Vec<ValidationError>,
    indirect: bool,
}

/// Run every original standalone function-local pass in its original diagnostic
/// order, including full source/body digests when a carrier is present. This
/// diagnostic API does not provide the module tables needed by refinements,
/// callee/layout/enum-case checks or compiler-owned source/proof authority.
/// The ordinary standalone refinement and effect/call refusals remain intact.
/// Every actual constituent, aggregation and failed-output retirement uses the
/// same supplied original session/site. No partial list escapes a stop.
/// Successful diagnostics and immutable input disposal remain caller-owned.
/// Physical allocator/deallocator/OOM/panic/RSS/hard-time bounds are separate.
pub fn validate_function_observed<O: ExecutionObserver>(
    function: &Function,
    session: &mut ObservedSession<'_, O>,
    site: ExecutionSite,
) -> R<Vec<ValidationError>> {
    let result = validate_function_with_context_observed(function, None, session, site)?;
    // The complete report was just admitted/published; no intervening fallible
    // operation may lose its retained Vec. The unused classification is Copy.
    Ok(result.errors)
}

/// Internal counterpart of the original context report. The exact containing
/// module is still a caller obligation, not a capability minted by this helper.
/// A module caller must additionally run every original cross-function/module
/// validator and retain the returned indirect-call classification.
pub(super) fn validate_function_with_context_observed<O: ExecutionObserver>(
    function: &Function,
    module: Option<&Module>,
    session: &mut ObservedSession<'_, O>,
    site: ExecutionSite,
) -> R<FunctionValidationReport> {
    session.admit(ExecutionProgress {
        phase: ExecutionPhase::Validation,
        site,
        work: 4,
        copy_bytes: size_of::<State>() + size_of::<Work<'_, '_, O>>() + size_of::<u32>(),
    })?;
    // Fixed optional target field/checked multiplication, as in the ordinary
    // original context. No target string/table traversal occurs here.
    let pointer_bits = module.map_or(DEFAULT_POINTER_BITS, Module::pointer_bits);
    let mut state = State::default();
    let mut work = Work { session, site };
    let result = state.run(function, module, pointer_bits, &mut work);
    state.retire_pending(&mut work);
    match result.and_then(|()| work.publication()) {
        Ok(()) => Ok(FunctionValidationReport {
            errors: take(&mut state.errors),
            has_indirect_call: state.indirect,
        }),
        Err(error) => {
            let _ =
                retire_validation_errors_observed(take(&mut state.errors), work.session, work.site);
            Err(work.terminal(error))
        }
    }
}
impl State {
    fn retire_pending<O: ExecutionObserver>(&mut self, work: &mut Work<'_, '_, O>) {
        work.session.retirement_step(
            work.site,
            size_of::<Vec<ValidationError>>().saturating_add(1),
        );
        let _ = retire_validation_errors_observed(take(&mut self.pending), work.session, work.site);
    }
}
