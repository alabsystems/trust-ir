// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
impl State<'_> {
    pub(super) fn merge<O: ExecutionObserver>(&mut self, work: &mut Work<'_, '_, O>) -> R {
        work.admit(1, 2 * size_of::<usize>())?;
        let mut at = 0;
        let half = self.pending.len() / 2;
        while at < half {
            work.admit(3, 3 * size_of::<ValidationError>())?;
            let end = self
                .pending
                .len()
                .checked_sub(at)
                .and_then(|n| n.checked_sub(1))
                .ok_or(ObservedValueError::CapacityOverflow)?;
            self.pending.swap(at, end);
            work.next(&mut at)?;
        }
        loop {
            work.admit(1, size_of::<Option<ValidationError>>())?;
            self.row = self.pending.pop();
            if self.row.is_none() {
                break;
            }
            work.reserve(&mut self.errors)?;
            work.admit(1, size_of::<ValidationError>())?;
            self.errors
                .push(self.row.take().ok_or(ObservedValueError::InvalidRange)?);
        }
        work.fixed(take(&mut self.pending));
        work.admit(1, 0)
    }
}
