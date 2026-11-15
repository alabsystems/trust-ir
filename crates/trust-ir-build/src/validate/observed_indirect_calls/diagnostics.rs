// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    dead_code,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
impl State {
    pub(super) fn ready<O: ExecutionObserver>(&self, work: &mut Work<'_, '_, O>) -> R {
        work.admit(1, 0)?;
        if self.name.capacity() != 0
            || self.detail.capacity() != 0
            || self.expected.capacity() != 0
            || self.actual.capacity() != 0
            || self.render.capacity() != 0
        {
            return Err(ObservedValueError::InvalidRange);
        }
        Ok(())
    }
    pub(super) fn push<O: ExecutionObserver>(
        &mut self,
        error: ValidationError,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        // Only scalar payload variants call this helper. Owning String/Vec
        // errors stay in State before every reserve/admit/transfer instead.
        work.reserve(&mut self.errors)?;
        work.admit(1, size_of::<ValidationError>())?;
        self.errors.push(error);
        Ok(())
    }
}
