// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! The final local `summary.proved` block only; no import authentication.
#![allow(
    dead_code,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::observed_summary_backing::SummaryCitation;
use super::*;
use core::mem::{size_of, take};
use trust_ir::FunctionSummary;
use trust_ir::interpret::{
    ExecutionObserver, ExecutionPhase, ExecutionProgress, ExecutionSite, ObservedSession,
    ObservedValueError,
};
use trust_ir::proof::{ProofFormula, ProofStatus};
mod render;
mod rows;
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

/// Rechecks only the original final local-row block. `citation` is the existing
/// syntactic citation result, including a refused citation, never a receipt.
/// Success returns caller-owned diagnostics, not a proof or complete validity.
pub(crate) fn validate_function_summary_local_backing_observed<O: ExecutionObserver>(
    module: &Module,
    function: &Function,
    summary: &FunctionSummary,
    citation: SummaryCitation,
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
    let result = state.run(module, function, summary, citation, &mut work);
    state.finish(result, &mut work)
}
impl State {
    fn issue<O: ExecutionObserver>(
        &mut self,
        function: &Function,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        // Keep the complete detail owned until every fallible output admission.
        work.reserve(&mut self.errors)?;
        work.admit(2, size_of::<ValidationError>())?;
        self.errors.push(ValidationError::InvalidFunctionSummary {
            function: function.id.index(),
            detail: take(&mut self.detail),
        });
        Ok(())
    }
    fn run<O: ExecutionObserver>(
        &mut self,
        module: &Module,
        function: &Function,
        summary: &FunctionSummary,
        citation: SummaryCitation,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        work.admit(1, 0)?;
        if !summary.proved {
            return Ok(());
        }
        self.duplicates(function, summary, work)?;
        // A body is exactly physical block presence, regardless of linkage/CFG.
        work.admit(2, size_of::<bool>())?;
        let counts_locally = !function.blocks.is_empty();
        self.failed_rows(module, function, work)?;
        work.admit(2, 0)?;
        if citation == SummaryCitation::Absent || counts_locally {
            self.missing_rows(module, function, summary, counts_locally, work)?;
        }
        Ok(())
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
