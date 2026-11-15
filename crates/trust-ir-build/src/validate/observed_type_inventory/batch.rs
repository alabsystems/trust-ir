// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    dead_code,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
impl State<'_> {
    pub(super) fn append<O: ExecutionObserver>(&mut self, work: &mut Work<'_, '_, O>) -> R {
        // Actual bounded header swaps, not opaque reverse/append/drain work.
        // Reverse then pop preserves source order without new iterator custody.
        work.admit(2, 2 * size_of::<usize>())?;
        let mut left = 0usize;
        let mut right = self.batch.len();
        while left < right {
            work.admit(2, size_of::<usize>())?;
            right = right
                .checked_sub(1)
                .ok_or(ObservedValueError::CapacityOverflow)?;
            if left >= right {
                break;
            }
            work.admit(1, 3 * size_of::<ValidationError>())?;
            self.batch.swap(left, right);
            work.next(&mut left)?;
        }
        loop {
            work.admit(2, size_of::<Option<ValidationError>>())?;
            if self.row.is_some() {
                return Err(ObservedValueError::InvalidRange);
            }
            // Full row is held before the next fallible output fee.
            self.row = self.batch.pop();
            if self.row.is_none() {
                break;
            }
            work.reserve(&mut self.errors)?;
            work.admit(
                1,
                size_of::<ValidationError>() + size_of::<Option<ValidationError>>(),
            )?;
            let row = self.row.take().ok_or(ObservedValueError::InvalidRange)?;
            self.errors.push(row);
        }
        self.retire_batch(work);
        work.admit(1, 0)
    }
    pub(super) fn retire_batch<O: ExecutionObserver>(&mut self, work: &mut Work<'_, '_, O>) {
        let _ = retire_validation_errors_observed(take(&mut self.batch), work.session, work.site);
    }
}
