// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Original import-citation shape/policy, never an authentication producer.
#![allow(
    dead_code,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
use crate::linked::SiteOutcome;
use core::mem::{size_of, take};
use trust_ir::FunctionSummary;
use trust_ir::interpret::{
    ExecutionObserver, ExecutionPhase, ExecutionProgress, ExecutionSite, ObservedSession,
    ObservedValueError,
};
mod storage;
#[cfg(test)]
mod tests;
use storage::Work;
type R<T = ()> = Result<T, ObservedValueError>;
/// The original syntactic proof-bearing citation flag, including on a refused
/// citation. This is not an authenticated-import or proof capability.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum SummaryCitation {
    Absent,
    ProofBearing,
}
#[derive(Clone, Copy)]
enum Issue {
    Dangling,
    Refused(u32),
}
#[derive(Default)]
struct State {
    detail: String,
    errors: Vec<ValidationError>,
}
pub(crate) fn validate_function_summary_import_backing_observed<O: ExecutionObserver>(
    module: &Module,
    function: &Function,
    summary: &FunctionSummary,
    policy: ImportPolicy<'_>,
    session: &mut ObservedSession<'_, O>,
    site: ExecutionSite,
) -> R<(Vec<ValidationError>, SummaryCitation)> {
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
    fn issue<O: ExecutionObserver>(&mut self, kind: Issue, work: &mut Work<'_, '_, O>) -> R {
        work.reserve(&mut self.errors)?;
        work.admit(2, size_of::<ValidationError>())?;
        let detail = take(&mut self.detail);
        self.errors.push(match kind {
            Issue::Dangling => ValidationError::DanglingExternRef { detail },
            Issue::Refused(import) => ValidationError::UnauthenticatedImport {
                import,
                site: "backed_by",
                detail,
            },
        });
        Ok(())
    }
    fn run<O: ExecutionObserver>(
        &mut self,
        module: &Module,
        function: &Function,
        summary: &FunctionSummary,
        policy: ImportPolicy<'_>,
        work: &mut Work<'_, '_, O>,
    ) -> R<SummaryCitation> {
        work.admit(
            1,
            size_of::<Option<&trust_ir::ExternRef>>() + size_of::<Issue>(),
        )?;
        let Some(reference) = &summary.backed_by else {
            return Ok(SummaryCitation::Absent);
        };
        let resolves = work
            .at(&module.imports, reference.module.index() as usize)?
            .is_some();
        if !resolves {
            work.text("function #", &mut self.detail)?;
            work.number(function.id.index() as u128, &mut self.detail)?;
            work.text(" carries a summary backed by import #", &mut self.detail)?;
            work.number(reference.module.index() as u128, &mut self.detail)?;
            work.text(
                ", which is not declared in `Module::imports`",
                &mut self.detail,
            )?;
            self.issue(Issue::Dangling, work)?;
        }
        work.admit(3, 2 * size_of::<bool>())?;
        let proof_bearing = resolves && reference.obligation.is_some();
        if proof_bearing && summary.proved {
            work.admit(3, size_of::<Issue>())?;
            let import = reference.module.index();
            match policy {
                ImportPolicy::Structural => {}
                ImportPolicy::Refuse => {
                    work.text("function #", &mut self.detail)?;
                    work.number(function.id.index() as u128, &mut self.detail)?;
                    work.text(" cites obligation #", &mut self.detail)?;
                    work.number(
                        reference.obligation.map_or(0, |o| o.index()) as u128,
                        &mut self.detail,
                    )?;
                    work.text(" of ", &mut self.detail)?;
                    work.quoted(&reference.symbol, &mut self.detail)?;
                    work.text(" in import #", &mut self.detail)?;
                    work.number(import as u128, &mut self.detail)?;
                    work.text(", but this entry point has no import resolver and takes no cross-crate claim on faith; authenticate it with `validate_linked_module`",&mut self.detail)?;
                    self.issue(Issue::Refused(import), work)?;
                }
                ImportPolicy::Authenticated(authenticated) => {
                    match authenticated.backed_by_outcome_observed(
                        function.id,
                        work.session,
                        work.site,
                    )? {
                        Some(SiteOutcome::Authenticated) | Some(SiteOutcome::Reported) => {}
                        Some(SiteOutcome::Refused(detail)) => {
                            work.text(detail, &mut self.detail)?;
                            self.issue(Issue::Refused(import), work)?;
                        }
                        None => {
                            work.text("function #", &mut self.detail)?;
                            work.number(function.id.index() as u128, &mut self.detail)?;
                            work.text(
                                "'s citation was not examined by the linked validator",
                                &mut self.detail,
                            )?;
                            self.issue(Issue::Refused(import), work)?;
                        }
                    }
                }
            }
        }
        Ok(if proof_bearing {
            SummaryCitation::ProofBearing
        } else {
            SummaryCitation::Absent
        })
    }
    fn finish<O: ExecutionObserver>(
        &mut self,
        result: R<SummaryCitation>,
        work: &mut Work<'_, '_, O>,
    ) -> R<(Vec<ValidationError>, SummaryCitation)> {
        work.retire_text(take(&mut self.detail));
        match result.and_then(|claim| {
            work.publication(
                1,
                size_of::<Vec<ValidationError>>() + size_of::<SummaryCitation>(),
            )?;
            Ok(claim)
        }) {
            Ok(claim) => Ok((take(&mut self.errors), claim)),
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
