// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;

impl Checking<'_> {
    pub(super) fn retire_scratch<O: ExecutionObserver>(&mut self, work: &mut Work<'_, '_, O>) {
        work.retire_refs(&mut self.frames);
        work.retire_refs(&mut self.types);
        work.retire(take(&mut self.location));
        work.retire(take(&mut self.detail));
    }

    pub(super) fn retire_errors<O: ExecutionObserver>(&mut self, work: &mut Work<'_, '_, O>) {
        while !self.errors.is_empty() {
            work.session.retirement_step(work.site, 1);
            if let Some(error) = self.errors.pop() {
                // Only this exact owned-string variant can be produced by the
                // private diagnostic constructor. Retire its fields separately.
                match error {
                    ValidationError::RefinementTypeInvalid { location, detail } => {
                        work.retire(location);
                        work.retire(detail);
                    }
                    other => work.retire(other),
                }
                work.session.retirement_poll(work.site);
            }
        }
        work.retire(take(&mut self.errors));
    }
}
