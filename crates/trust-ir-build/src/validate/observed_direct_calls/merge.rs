// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    dead_code,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
impl State {
    pub(super) fn merge<O: ExecutionObserver>(&mut self, work: &mut Work<'_, '_, O>) -> R {
        let start = self.errors.len();
        loop {
            work.admit(1, 0)?;
            if self.pending.is_empty() {
                break;
            }
            // Reserve and price both fixed error-header moves before popping;
            // a refusal keeps every owned payload in one of the two Vecs.
            work.reserve(&mut self.errors)?;
            work.admit(2, 2 * size_of::<ValidationError>())?;
            let error = self.pending.pop().ok_or(ObservedValueError::InvalidRange)?;
            self.errors.push(error);
        }
        self.retire_pending(work);
        work.admit(1, 0)?;
        let mut left = start;
        let mut right = self.errors.len();
        loop {
            work.admit(2, 0)?;
            if right.saturating_sub(left) < 2 {
                return Ok(());
            }
            right = right
                .checked_sub(1)
                .ok_or(ObservedValueError::InvalidRange)?;
            work.admit(1, 3 * size_of::<ValidationError>())?;
            self.errors.swap(left, right);
            left = left
                .checked_add(1)
                .ok_or(ObservedValueError::CapacityOverflow)?;
        }
    }
}
