// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! One original owner through the complete ordinary proof-integrity groups.
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
mod storage;
#[cfg(test)]
mod tests;
use storage::Work;
type R<T = ()> = Result<T, ObservedValueError>;
#[derive(Default)]
struct State {
    errors: Vec<ValidationError>,
    batch: Vec<ValidationError>,
    row: Option<ValidationError>,
}
/// Execute every original `validate_proof_obligation_integrity` group in its
/// exact original order, with the same supplied original session and request
/// site through all actual inner work: header (duplicate IDs then namespaces),
/// formula inventory/two-text decision, source/public identity, certificate
/// consistency/Trusted attribution. A child return is kept whole before any
/// parent aggregation fee, and a popped owned row is held before any fallible
/// parent reserve/transfer. No callback or cached result stands in for a child.
///
/// This complete diagnostic constituent does not replay kernels or establish
/// proof/module/source authority; other module rules remain mandatory. A typed
/// child, aggregation, cleanup or final-publication refusal returns no prefix.
/// All batches, pending rows and previous errors are consumed after sticky
/// refusal. Successful caller input/result disposal and physical std/Unicode/
/// allocator/deallocator/OOM/panic/unwind/RSS/hardtime remain OPEN. No owner,
/// grant, deadline, TLS or interpreter fuel is created or renewed.
pub(crate) fn validate_module_proof_obligation_integrity_observed<O: ExecutionObserver>(
    module: &Module,
    session: &mut ObservedSession<'_, O>,
    site: ExecutionSite,
) -> R<Vec<ValidationError>> {
    let mut work = Work { session, site };
    work.admit(1, size_of::<State>() + size_of::<Work<'_, '_, O>>())?;
    let mut state = State::default();
    let result = state.run(module, &mut work);
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
impl State {
    fn run<O: ExecutionObserver>(&mut self, module: &Module, work: &mut Work<'_, '_, O>) -> R {
        self.before_child(work)?;
        self.batch =
            validate_module_proof_obligation_header_observed(module, work.session, work.site)?;
        self.append(work)?;
        self.before_child(work)?;
        self.batch = validate_module_formula_texts_observed(module, work.session, work.site)?;
        self.append(work)?;
        self.before_child(work)?;
        self.batch = validate_module_obligation_source_observed(module, work.session, work.site)?;
        self.append(work)?;
        self.before_child(work)?;
        self.batch =
            validate_module_certificate_integrity_tail_observed(module, work.session, work.site)?;
        self.append(work)
    }
    fn before_child<O: ExecutionObserver>(&self, work: &mut Work<'_, '_, O>) -> R {
        work.admit(
            3,
            size_of::<Vec<ValidationError>>() + size_of::<Option<ValidationError>>(),
        )?;
        if self.batch.capacity() != 0 || self.row.is_some() {
            return Err(ObservedValueError::InvalidRange);
        }
        Ok(())
    }
    fn append<O: ExecutionObserver>(&mut self, work: &mut Work<'_, '_, O>) -> R {
        // Actual bounded header swaps, not opaque reverse/append/drain work.
        // Reverse then pop preserves source order without new iterator custody.
        work.admit(2, 2 * size_of::<usize>())?;
        let mut left = 0usize;
        let mut right = self.batch.len();
        while left < right {
            work.admit(2, size_of::<usize>())?;
            right = right
                .checked_sub(1)
                .ok_or(ObservedValueError::CapacityOverflow)?;
            if left >= right {
                break;
            }
            work.admit(1, 3 * size_of::<ValidationError>())?;
            self.batch.swap(left, right);
            work.next(&mut left)?;
        }
        loop {
            work.admit(2, size_of::<Option<ValidationError>>())?;
            if self.row.is_some() {
                return Err(ObservedValueError::InvalidRange);
            }
            // Full row is held before the next fallible output fee.
            self.row = self.batch.pop();
            if self.row.is_none() {
                break;
            }
            work.reserve(&mut self.errors)?;
            work.admit(
                1,
                size_of::<ValidationError>() + size_of::<Option<ValidationError>>(),
            )?;
            let row = self.row.take().ok_or(ObservedValueError::InvalidRange)?;
            self.errors.push(row);
        }
        self.retire_batch(work);
        work.admit(1, 0)
    }
    fn retire_batch<O: ExecutionObserver>(&mut self, work: &mut Work<'_, '_, O>) {
        let _ = retire_validation_errors_observed(take(&mut self.batch), work.session, work.site);
    }
    fn retire_scratch<O: ExecutionObserver>(&mut self, work: &mut Work<'_, '_, O>) {
        work.step(size_of::<Option<ValidationError>>().saturating_add(1));
        if let Some(row) = self.row.take() {
            let _ = retire_validation_error_observed(row, work.session, work.site);
        }
        self.retire_batch(work);
        work.poll();
    }
}
