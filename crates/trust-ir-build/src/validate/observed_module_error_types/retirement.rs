// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
impl State<'_> {
    pub(super) fn retire_scratch<O: ExecutionObserver>(&mut self, work: &mut Work<'_, '_, O>) {
        work.retire_refs(&mut self.frames);
        work.retire_refs(&mut self.types);
        work.retire(take(&mut self.location));
        work.retire(take(&mut self.attribute));
        work.retire(take(&mut self.pending_location));
        work.retire(take(&mut self.pending_expected));
        work.retire(take(&mut self.pending_actual));
    }
    pub(super) fn retire_errors<O: ExecutionObserver>(&mut self, work: &mut Work<'_, '_, O>) {
        while !self.errors.is_empty() {
            work.session.retirement_step(work.site, 1);
            if let Some(error) = self.errors.pop() {
                // The private constructors produce only these two variants.
                match error {
                    ValidationError::ConstTypeMismatch {
                        location,
                        expected,
                        actual,
                    } => {
                        work.retire(location);
                        work.retire(expected);
                        work.retire(actual);
                    }
                    ValidationError::GlobalAlignInvalid { global, .. } => work.retire(global),
                    other => work.retire(other),
                }
                work.session.retirement_poll(work.site);
            }
        }
        work.retire(take(&mut self.errors));
    }
}
