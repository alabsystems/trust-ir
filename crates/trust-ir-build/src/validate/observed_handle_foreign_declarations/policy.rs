// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    dead_code,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
use crate::linked::SiteOutcome;
const NO_BACKING_PREFIX: &str = "no `backed_by` binds it to an import; a call into a dependency's handle-typed function is spelled as a declaration carrying `backed_by: ExternRef { module, symbol: ";
const NO_BACKING_SUFFIX: &str = ", obligation: None }`, admitted only by validate_linked_module";
const STRUCTURAL_PREFIX: &str = "it carries a `backed_by` into import #";
const STRUCTURAL_SUFFIX: &str = ", but an import-backed declaration is admitted only by validate_linked_module, which authenticates the dependency and resolves the symbol to its definition";
const UNEXAMINED: &str = "its `backed_by` was not examined by the linked validator";
impl State {
    /// True means report the already-refused origin, false means the sealed
    /// linked walk authenticated or already reported it. A typed stop never
    /// becomes either policy choice, and this function cannot mint an outcome.
    pub(super) fn policy<O: ExecutionObserver>(
        &mut self,
        function: &Function,
        policy: ImportPolicy<'_>,
        work: &mut Work<'_, '_, O>,
    ) -> R<bool> {
        work.admit(
            2,
            size_of::<Option<&trust_ir::FunctionSummary>>()
                + size_of::<Option<&trust_ir::ExternRef>>()
                + size_of::<ImportPolicy<'_>>(),
        )?;
        let backing = function
            .summary
            .as_ref()
            .and_then(|summary| summary.backed_by.as_ref());
        match (backing, policy) {
            (None, _) => {
                work.text(NO_BACKING_PREFIX, &mut self.detail)?;
                work.quoted(&function.name, &mut self.detail)?;
                work.text(NO_BACKING_SUFFIX, &mut self.detail)?;
            }
            (Some(reference), ImportPolicy::Structural | ImportPolicy::Refuse) => {
                work.text(STRUCTURAL_PREFIX, &mut self.detail)?;
                work.admit(1, size_of::<u32>())?;
                work.number(reference.module.index(), &mut self.detail)?;
                work.text(STRUCTURAL_SUFFIX, &mut self.detail)?;
            }
            (Some(_), ImportPolicy::Authenticated(authenticated)) => {
                match authenticated.handle_declaration_outcome_observed(
                    function.id,
                    work.session,
                    work.site,
                )? {
                    Some(SiteOutcome::Authenticated | SiteOutcome::Reported) => return Ok(false),
                    Some(SiteOutcome::Refused(detail)) => work.text(detail, &mut self.detail)?,
                    None => work.text(UNEXAMINED, &mut self.detail)?,
                }
            }
        }
        Ok(true)
    }
}
