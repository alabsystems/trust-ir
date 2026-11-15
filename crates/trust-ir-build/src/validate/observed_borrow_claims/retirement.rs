// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
use super::*;
impl State<'_> {
    pub(super) fn retire_edges<O: ExecutionObserver>(&mut self, work: &mut Work<'_, '_, O>) {
        work.retire_rows(&mut self.edges);
    }
    pub(super) fn retire_walk<O: ExecutionObserver>(&mut self, work: &mut Work<'_, '_, O>) {
        work.retire_rows(&mut self.stack);
        work.retire_rows(&mut self.seen);
    }
    pub(super) fn retire_scratch<O: ExecutionObserver>(&mut self, work: &mut Work<'_, '_, O>) {
        self.retire_edges(work);
        self.retire_walk(work);
        work.session.retirement_step(work.site, 1);
        if let Some(mut rows) = self.definitions.take() {
            work.retire_rows(&mut rows);
        }
        work.session.retirement_poll(work.site);
        work.session.retirement_step(work.site, 1);
        if let Some(mut rows) = self.incoming.take() {
            work.retire_rows(&mut rows);
        }
        work.session.retirement_poll(work.site);
        work.retire(take(&mut self.name));
    }
    pub(super) fn retire_errors<O: ExecutionObserver>(&mut self, work: &mut Work<'_, '_, O>) {
        while !self.errors.is_empty() {
            work.session.retirement_step(work.site, 1);
            if let Some(error) = self.errors.pop() {
                match error {
                    ValidationError::RustReferenceAsPermissionBorrow { function, .. } => {
                        work.retire(function)
                    }
                    // The other private constructors hold only a block ID.
                    fixed => work.retire(fixed),
                }
            }
            work.session.retirement_poll(work.site);
        }
        work.retire(take(&mut self.errors));
    }
}
