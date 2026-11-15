// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Actual structural spec diagnostics mapped into their original build errors.
use super::*;
use core::mem::{size_of, take};
use std::vec::IntoIter;
use trust_ir::SpecLinkViolation;
use trust_ir::interpret::{
    ExecutionObserver, ExecutionPhase, ExecutionProgress, ExecutionSite, ObservedSession,
    ObservedValueError,
};
mod storage;
#[cfg(test)]
mod tests;
use storage::Work;
type R<T = ()> = Result<T, ObservedValueError>;
#[derive(Default)]
struct State {
    batch: Option<IntoIter<SpecLinkViolation>>,
    pending: Option<SpecLinkViolation>,
    errors: Vec<ValidationError>,
}
/// Only the structural mapping stage of validate_spec_module_semantics.
/// Blank module name, linked SMT surface and reserved-name rules are separate
/// original stages. No executable/module/proof/source authority is returned.
pub fn validate_module_spec_structure_observed<O: ExecutionObserver>(
    module: &Module,
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
    let result = (|| {
        // Prepay the fixed return/transport headers before the child can
        // create an owning result. Capture it immediately, before any stop.
        work.admit(
            3,
            size_of::<Vec<SpecLinkViolation>>()
                + size_of::<IntoIter<SpecLinkViolation>>()
                + size_of::<Option<SpecLinkViolation>>(),
        )?;
        state.batch = Some(
            trust_ir::validate_spec_structure_observed(
                &module.spec_modules,
                work.session,
                work.site,
            )?
            .into_iter(),
        );
        state.merge(&mut work)
    })();
    state.finish(result, &mut work)
}
impl State {
    fn merge<O: ExecutionObserver>(&mut self, work: &mut Work<'_, '_, O>) -> R {
        loop {
            work.admit(1, size_of::<Option<SpecLinkViolation>>())?;
            if self.pending.is_some() {
                return Err(ObservedValueError::InvalidRange);
            }
            self.pending = self
                .batch
                .as_mut()
                .ok_or(ObservedValueError::InvalidRange)?
                .next();
            if self.pending.is_none() {
                break;
            }
            work.reserve(&mut self.errors)?;
            work.admit(1, size_of::<ValidationError>())?;
            let Some(violation) = self.pending.take() else {
                return Err(ObservedValueError::InvalidRange);
            };
            self.errors
                .push(ValidationError::InvalidSpecStructure { violation });
        }
        self.retire_empty_batch(work);
        work.admit(1, 0)
    }
    fn retire_empty_batch<O: ExecutionObserver>(&mut self, work: &mut Work<'_, '_, O>) {
        work.step(size_of::<Option<IntoIter<SpecLinkViolation>>>().saturating_add(1));
        // Only called after merge/drain consumed every actual owned row.
        drop(self.batch.take());
        work.poll();
    }
    fn retire_scratch<O: ExecutionObserver>(&mut self, work: &mut Work<'_, '_, O>) {
        work.step(size_of::<Option<SpecLinkViolation>>().saturating_add(1));
        if let Some(violation) = self.pending.take() {
            let _ = violation.retire_observed(work.session, work.site);
        }
        loop {
            work.step(size_of::<Option<SpecLinkViolation>>().saturating_add(1));
            let Some(violation) = self.batch.as_mut().and_then(Iterator::next) else {
                break;
            };
            let _ = violation.retire_observed(work.session, work.site);
        }
        self.retire_empty_batch(work);
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
