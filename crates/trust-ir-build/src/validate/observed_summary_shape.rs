// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Original summary parameter-count and effect-set shape constituent only.
use super::*;
use core::mem::{size_of, take};
use trust_ir::interpret::{
    ExecutionObserver, ExecutionPhase, ExecutionProgress, ExecutionSite, ObservedSession,
    ObservedValueError,
};
use trust_ir::{EffectPlace, EffectSet, FunctionSummary};
mod scan;
mod storage;
#[cfg(test)]
mod tests;
use storage::Work;
type R<T = ()> = Result<T, ObservedValueError>;
#[derive(Default)]
struct State {
    detail: String,
    errors: Vec<ValidationError>,
}

/// Exact contiguous signature/effect-shape block in validate_function_summary.
/// Does not check clause bindings/backing, body effects, imports or proofs.
/// `summary` is the original borrowed supplied row, not an authenticated claim.
pub fn validate_function_summary_signature_effect_shape_observed<O: ExecutionObserver>(
    module: &Module,
    function: &Function,
    summary: &FunctionSummary,
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
    let result = state.run(module, function, summary, &mut work);
    state.finish(result, &mut work)
}
impl State {
    fn issue<O: ExecutionObserver>(
        &mut self,
        function: &Function,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        work.reserve(&mut self.errors)?;
        work.admit(1, size_of::<ValidationError>())?;
        self.errors.push(ValidationError::InvalidFunctionSummary {
            function: function.id.index(),
            detail: take(&mut self.detail),
        });
        Ok(())
    }
    fn side<O: ExecutionObserver>(&mut self, side: &str, work: &mut Work<'_, '_, O>) -> R {
        work.text("effects.", &mut self.detail)?;
        work.text(side, &mut self.detail)
    }
    fn finish<O: ExecutionObserver>(
        &mut self,
        result: R,
        work: &mut Work<'_, '_, O>,
    ) -> R<Vec<ValidationError>> {
        work.retire_text(take(&mut self.detail));
        match result.and_then(|()| work.publication(1, size_of::<Vec<ValidationError>>())) {
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
