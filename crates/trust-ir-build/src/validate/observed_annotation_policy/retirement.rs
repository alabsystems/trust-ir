// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
fn strings<O: ExecutionObserver>(mut values: Vec<String>, work: &mut Work<'_, '_, O>) {
    while !values.is_empty() {
        work.session.retirement_step(work.site, 1);
        if let Some(value) = values.pop() {
            work.retire(value);
        }
    }
    work.retire(values);
}
fn error<O: ExecutionObserver>(error: ValidationError, work: &mut Work<'_, '_, O>) {
    work.session.retirement_step(work.site, 1);
    match error {
        ValidationError::ConflictingFunctionMemoryRoles { func_name, roles } => {
            work.retire(func_name);
            strings(roles, work);
        }
        ValidationError::ConflictingMemoryRoles { roles, .. } => strings(roles, work),
        ValidationError::HavocMarkerMisplaced { location, .. } => work.retire(location),
        // No other variant can be made by this private builder.
        fixed => work.retire(fixed),
    }
    work.session.retirement_poll(work.site);
}
impl Checking {
    pub(super) fn retire_scratch<O: ExecutionObserver>(&mut self, work: &mut Work<'_, '_, O>) {
        if let Some(pending) = self.pending.take() {
            error(pending, work);
        }
        work.retire(take(&mut self.text));
        work.retire(take(&mut self.name));
        strings(take(&mut self.roles), work);
    }
    pub(super) fn retire_errors<O: ExecutionObserver>(&mut self, work: &mut Work<'_, '_, O>) {
        while !self.errors.is_empty() {
            work.session.retirement_step(work.site, 1);
            if let Some(value) = self.errors.pop() {
                error(value, work);
            }
        }
        work.retire(take(&mut self.errors));
    }
}
