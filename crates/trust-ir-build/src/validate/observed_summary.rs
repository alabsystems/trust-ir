// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Complete original function-summary validator; no proof authentication.
#![allow(
    dead_code,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::observed_summary_backing::{
    SummaryCitation, validate_function_summary_import_backing_observed,
};
use super::observed_summary_local::validate_function_summary_local_backing_observed;
use super::*;
use core::mem::{size_of, take};
use std::vec::IntoIter;
use trust_ir::FunctionSummary;
use trust_ir::interpret::{
    ExecutionObserver, ExecutionPhase, ExecutionProgress, ExecutionSite, ObservedSession,
    ObservedValueError,
};
mod merge;
mod retirement;
mod storage;
#[cfg(test)]
pub(crate) mod tests;
use storage::Work;
type R<T = ()> = Result<T, ObservedValueError>;
struct State {
    errors: Vec<ValidationError>,
    batch: Option<IntoIter<ValidationError>>,
    pending: Option<ValidationError>,
    imported: Option<(Vec<ValidationError>, SummaryCitation)>,
    citation: SummaryCitation,
}
impl Default for State {
    fn default() -> Self {
        Self {
            errors: Vec::new(),
            batch: None,
            pending: None,
            imported: None,
            citation: SummaryCitation::Absent,
        }
    }
}
/// Exact ordered composition of every original validate_function_summary
/// check, under the caller's original import policy, session and site. This
/// reads carried claims and returns complete diagnostics; neither structural
/// success nor a stored syntactic citation creates proof/import authority.
/// Body effects and other module rules are separate original constituents.
pub(crate) fn validate_function_summary_observed<O: ExecutionObserver>(
    module: &Module,
    function: &Function,
    summary: &FunctionSummary,
    policy: ImportPolicy<'_>,
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
    let result = state.run(module, function, summary, policy, &mut work);
    state.finish(result, &mut work)
}
impl State {
    fn run<O: ExecutionObserver>(
        &mut self,
        module: &Module,
        function: &Function,
        summary: &FunctionSummary,
        policy: ImportPolicy<'_>,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        self.prepare(work)?;
        self.batch = Some(
            validate_function_summary_bindings_observed(
                module,
                function,
                summary,
                work.session,
                work.site,
            )?
            .into_iter(),
        );
        self.merge(work)?;
        self.prepare(work)?;
        self.batch = Some(
            validate_function_summary_signature_effect_shape_observed(
                module,
                function,
                summary,
                work.session,
                work.site,
            )?
            .into_iter(),
        );
        self.merge(work)?;
        self.prepare(work)?;
        // The complete tuple is retained immediately on return. A following
        // refusal cannot drop its owned Vec before original-owner retirement.
        self.imported = Some(validate_function_summary_import_backing_observed(
            module,
            function,
            summary,
            policy,
            work.session,
            work.site,
        )?);
        work.admit(
            3,
            size_of::<Option<(Vec<ValidationError>, SummaryCitation)>>()
                + size_of::<Option<IntoIter<ValidationError>>>(),
        )?;
        let (errors, citation) = self
            .imported
            .take()
            .ok_or(ObservedValueError::InvalidRange)?;
        self.citation = citation;
        self.batch = Some(errors.into_iter());
        self.merge(work)?;
        self.prepare(work)?;
        self.batch = Some(
            validate_function_summary_local_backing_observed(
                module,
                function,
                summary,
                self.citation,
                work.session,
                work.site,
            )?
            .into_iter(),
        );
        self.merge(work)
    }
    fn prepare<O: ExecutionObserver>(&self, work: &mut Work<'_, '_, O>) -> R {
        // Price all incoming Vec/iterator/tuple/pending descriptors BEFORE the
        // child call can return owned data. The actual child owns its own
        // partial results until that call returns, with the same session/site.
        work.admit(
            4,
            size_of::<Option<IntoIter<ValidationError>>>()
                + size_of::<Option<ValidationError>>()
                + size_of::<Option<(Vec<ValidationError>, SummaryCitation)>>(),
        )?;
        if self.batch.is_some() || self.pending.is_some() || self.imported.is_some() {
            return Err(ObservedValueError::InvalidRange);
        }
        Ok(())
    }
    fn finish<O: ExecutionObserver>(
        &mut self,
        result: R,
        work: &mut Work<'_, '_, O>,
    ) -> R<Vec<ValidationError>> {
        self.retire_scratch(work);
        match result.and_then(|()| work.publish(size_of::<Vec<ValidationError>>())) {
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
