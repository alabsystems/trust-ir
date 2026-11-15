// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    dead_code,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
impl State {
    pub(super) fn multiply_defined<O: ExecutionObserver>(
        &mut self,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        work.lookup(self.members.len())?;
        work.admit(
            1,
            size_of::<std::collections::btree_map::Iter<'_, u32, (u32, Point)>>(),
        )?;
        let mut rows = self.members.iter();
        loop {
            work.lookup(self.members.len())?;
            work.admit(1, size_of::<Option<(&u32, &(u32, Point))>>())?;
            let Some((value, member)) = rows.next() else {
                break;
            };
            work.admit(1, 2 * size_of::<u32>())?;
            let value = *value;
            let owner = member.0;
            if work.read(&self.definitions, value)?.unwrap_or(0) != 1 {
                work.push_copy(&mut self.multiply_defined, (value, owner))?;
            }
        }
        let mut at = 0;
        while let Some(row) = work.at(&self.multiply_defined, at)? {
            work.admit(1, size_of::<(u32, u32)>())?;
            let (value, owner) = *row;
            work.text("its slot pointer %", &mut self.reason)?;
            work.unsigned(u128::from(value), &mut self.reason)?;
            work.text(" is defined more than once", &mut self.reason)?;
            self.unseal(owner, work)?;
            work.next(&mut at)?;
        }
        Ok(())
    }
}
