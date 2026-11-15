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
            work.reserve(&mut self.errors)?;
            work.admit(1, size_of::<ValidationError>())?;
            let error = self
                .pending
                .take()
                .ok_or(ObservedValueError::InvalidRange)?;
            self.errors.push(error);
        }
        // All child elements moved; retain even the empty buffer until its
        // same-owner disposal has run, and check cleanup before continuing.
        work.step(size_of::<Option<IntoIter<ValidationError>>>().saturating_add(1));
        drop(self.batch.take());
        work.poll();
        work.admit(1, 0)
    }
    pub(super) fn retire_scratch<O: ExecutionObserver>(&mut self, work: &mut Work<'_, '_, O>) {
        self.retire_pending(work);
        if self.batch.is_some() {
            loop {
                work.step(size_of::<Option<ValidationError>>().saturating_add(1));
                self.pending = self.batch.as_mut().and_then(Iterator::next);
                if self.pending.is_none() {
                    break;
                }
                self.retire_pending(work);
            }
        }
        work.step(size_of::<Option<IntoIter<ValidationError>>>().saturating_add(1));
        drop(self.batch.take());
        work.poll();
    }
    fn retire_pending<O: ExecutionObserver>(&mut self, work: &mut Work<'_, '_, O>) {
        work.step(size_of::<Option<ValidationError>>().saturating_add(1));
        if let Some(error) = self.pending.take() {
            let _ = retire_validation_error_observed(error, work.session, work.site);
        }
    }
}
