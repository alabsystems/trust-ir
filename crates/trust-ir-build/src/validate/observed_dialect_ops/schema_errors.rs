// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    dead_code,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
impl State<'_> {
    pub(super) fn head<O: ExecutionObserver>(
        &mut self,
        name: &str,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        work.text("dialect schema mismatch: ", &mut self.reason)?;
        work.text(name, &mut self.reason)
    }
    pub(super) fn named<O: ExecutionObserver>(
        &mut self,
        name: &str,
        value: &str,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        self.head(name, work)?;
        work.text("(", &mut self.reason)?;
        work.quoted(value, &mut self.reason)?;
        work.text(")", &mut self.reason)
    }
    pub(super) fn count<O: ExecutionObserver>(
        &mut self,
        name: &str,
        expected: usize,
        actual: usize,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        self.head(name, work)?;
        work.text(" { expected: ", &mut self.reason)?;
        work.unsigned(expected as u128, &mut self.reason)?;
        work.text(", actual: ", &mut self.reason)?;
        work.unsigned(actual as u128, &mut self.reason)?;
        work.text(" }", &mut self.reason)
    }
    pub(super) fn raw_types<O: ExecutionObserver>(
        &mut self,
        types: &[Ty],
        work: &mut Work<'_, '_, O>,
    ) -> R {
        work.text("[", &mut self.reason)?;
        let mut at = 0;
        while let Some(ty) = work.at(types, at)? {
            if at != 0 {
                work.text(", ", &mut self.reason)?;
            }
            self.raw_ty(ty, work)?;
            work.next(&mut at)?;
        }
        work.text("]", &mut self.reason)
    }
}
