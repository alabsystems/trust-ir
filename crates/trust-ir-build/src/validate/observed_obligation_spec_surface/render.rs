// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    dead_code,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
impl State {
    pub(super) fn prefix<O: ExecutionObserver>(
        &mut self,
        name: &str,
        index: u32,
        primed: bool,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        work.admit(1, size_of::<bool>())?;
        if self.detail.capacity() != 0 {
            return Err(ObservedValueError::InvalidRange);
        }
        work.text("binds ", &mut self.detail)?;
        work.quoted(name, &mut self.detail)?;
        work.text(" to ", &mut self.detail)?;
        work.text(
            if primed { "SpecVarNext " } else { "SpecVar " },
            &mut self.detail,
        )?;
        work.number(u128::from(index), &mut self.detail)
    }
}
