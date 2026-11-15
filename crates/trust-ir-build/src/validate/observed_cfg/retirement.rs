// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
impl Checking<'_> {
    pub(super) fn retire_keys<O: ExecutionObserver>(&mut self, work: &mut Work<'_, '_, O>) {
        while !self.keys.is_empty() {
            work.session.retirement_step(work.site, 1);
            if let Some(key) = self.keys.pop() {
                work.retire(key);
            }
        }
    }
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
        self.retire_keys(work);
        work.retire(take(&mut self.keys));
        self.retire_edges(work);
        while !self.successors.is_empty() {
            work.session.retirement_step(work.site, 1);
            if let Some(row) = self.successors.pop() {
                work.retire(row.targets);
            }
        }
        work.retire(take(&mut self.successors));
        work.retire(take(&mut self.targets));
        work.retire(take(&mut self.blocks));
        work.retire(take(&mut self.reachable));
        work.retire(take(&mut self.queue));
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
        ValidationError::DuplicateSwitchCase { value, .. } => work.retire(value),
        // Only BranchTargetNotFound and UnreachableBlock are made here.
        fixed => work.retire(fixed),
    }
    work.session.retirement_poll(work.site);
}
