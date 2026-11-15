// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    dead_code,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
impl State {
    pub(super) fn merge<O: ExecutionObserver>(&mut self, work: &mut Work<'_, '_, O>) -> R {
        loop {
            work.admit(2, size_of::<Option<ValidationError>>())?;
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
            // Pending remains held with the complete remaining batch and
            // accumulated prior output across every fallible admission.
            work.reserve(&mut self.errors)?;
            work.admit(1, size_of::<ValidationError>())?;
            let error = self
                .pending
                .take()
                .ok_or(ObservedValueError::InvalidRange)?;
            self.errors.push(error);
        }
        work.admit(1, size_of::<usize>())?;
        if self
            .batch
            .as_ref()
            .ok_or(ObservedValueError::InvalidRange)?
            .len()
            != 0
        {
            return Err(ObservedValueError::InvalidRange);
        }
        // All actual elements have been moved, and pending is None. Only the
        // empty iterator/buffer remains; never Drop an unconsumed child Vec.
        work.step(size_of::<Option<IntoIter<ValidationError>>>().saturating_add(1));
        drop(self.batch.take());
        work.poll();
        work.admit(1, 0)
    }
}
