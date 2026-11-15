// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    dead_code,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
impl State {
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
        work.step(size_of::<Option<(Vec<ValidationError>, SummaryCitation)>>().saturating_add(1));
        if let Some((errors, citation)) = self.imported.take() {
            let _ = retire_validation_errors_observed(errors, work.session, work.site);
            work.step(size_of::<SummaryCitation>().saturating_add(1));
            let _ = citation;
        }
    }
    fn retire_pending<O: ExecutionObserver>(&mut self, work: &mut Work<'_, '_, O>) {
        work.step(size_of::<Option<ValidationError>>().saturating_add(1));
        if let Some(error) = self.pending.take() {
            let _ = retire_validation_error_observed(error, work.session, work.site);
        }
    }
}
