// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
impl Checking<'_> {
    pub(super) fn retire_edges<O: ExecutionObserver>(&mut self, work: &mut Work<'_, '_, O>) {
        while !self.edges.is_empty() {
            work.session.retirement_step(work.site, 1);
            self.edges.pop();
        }
        work.retire(take(&mut self.edges));
    }
    pub(super) fn retire_scratch<O: ExecutionObserver>(&mut self, work: &mut Work<'_, '_, O>) {
        if let Some(error) = self.pending.take() {
            retire_error(error, work);
        }
        work.retire(take(&mut self.text));
        self.retire_edges(work);
        work.retire(take(&mut self.leading));
        work.retire(take(&mut self.unwind));
        work.retire(take(&mut self.normal));
        work.retire(take(&mut self.results));
        work.retire(take(&mut self.literals));
    }
    pub(super) fn retire_errors<O: ExecutionObserver>(&mut self, work: &mut Work<'_, '_, O>) {
        while !self.errors.is_empty() {
            work.session.retirement_step(work.site, 1);
            if let Some(error) = self.errors.pop() {
                retire_error(error, work);
            }
        }
        work.retire(take(&mut self.errors));
    }
}
fn retire_error<O: ExecutionObserver>(error: ValidationError, work: &mut Work<'_, '_, O>) {
    work.session.retirement_step(work.site, 1);
    match error {
        ValidationError::MisplacedLandingPad { reason, .. } => work.retire(reason),
        // Only fixed UnwindDestWithoutLandingPad is otherwise constructed.
        fixed => work.retire(fixed),
    }
    work.session.retirement_poll(work.site);
}
