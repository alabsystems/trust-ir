// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
impl State<'_> {
    pub(super) fn retire_scratch<O: ExecutionObserver>(&mut self, work: &mut Work<'_, '_, O>) {
        work.retire_refs(&mut self.frames);
        work.retire(take(&mut self.location));
        work.retire(take(&mut self.pending_location));
        work.retire(take(&mut self.pending_ty));
        work.retire(take(&mut self.pending_reason));
    }

    pub(super) fn retire_errors<O: ExecutionObserver>(&mut self, work: &mut Work<'_, '_, O>) {
        while !self.errors.is_empty() {
            work.session.retirement_step(work.site, 1);
            if let Some(error) = self.errors.pop() {
                match error {
                    ValidationError::InvalidVectorType { ty, reason, .. } => {
                        work.retire(ty);
                        work.retire(reason);
                    }
                    ValidationError::InvalidModuleVectorType {
                        location,
                        ty,
                        reason,
                    } => {
                        work.retire(location);
                        work.retire(ty);
                        work.retire(reason);
                    }
                    // Only the two private constructors above populate rows.
                    other => work.retire(other),
                }
                work.session.retirement_poll(work.site);
            }
        }
        work.retire(take(&mut self.errors));
    }
}
