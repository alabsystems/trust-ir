// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
use super::*;
impl State<'_> {
    pub(super) fn retire_edges<O: ExecutionObserver>(&mut self, work: &mut Work<'_, '_, O>) {
        while !self.edges.is_empty() {
            work.session.retirement_step(work.site, 1);
            self.edges.pop();
        }
        work.flat(take(&mut self.edges));
    }
    pub(super) fn retire_scratch<O: ExecutionObserver>(&mut self, work: &mut Work<'_, '_, O>) {
        self.retire_edges(work);
        work.session.retirement_step(work.site, 1);
        if let Some(values) = self.values.take() {
            let _ = values.retire_observed(work.session, work.site);
        }
        work.session.retirement_poll(work.site);
        self.diagnostics.retire_scratch(work);
    }
}
fn error<O: ExecutionObserver>(error: ValidationError, work: &mut Work<'_, '_, O>) {
    work.session.retirement_step(work.site, 1);
    match error {
        ValidationError::BranchArgTypeMismatch {
            expected, actual, ..
        } => {
            work.flat(expected);
            work.flat(actual);
        }
        fixed => work.flat(fixed),
    }
    work.session.retirement_poll(work.site);
}
impl Diagnostics {
    pub(super) fn retire_scratch<O: ExecutionObserver>(&mut self, work: &mut Work<'_, '_, O>) {
        work.session.retirement_step(work.site, 1);
        if let Some(pending) = self.pending.take() {
            error(pending, work);
        }
        work.flat(take(&mut self.expected));
        work.flat(take(&mut self.actual));
    }
    pub(super) fn retire_errors<O: ExecutionObserver>(&mut self, work: &mut Work<'_, '_, O>) {
        while !self.errors.is_empty() {
            work.session.retirement_step(work.site, 1);
            if let Some(value) = self.errors.pop() {
                error(value, work);
            }
        }
        work.flat(take(&mut self.errors));
    }
}
