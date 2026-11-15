// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    dead_code,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
impl State {
    pub(super) fn definitions<O: ExecutionObserver>(
        &mut self,
        function: &Function,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        let mut b = 0;
        while let Some(block) = work.at(&function.blocks, b)? {
            let mut p = 0;
            while let Some((value, _)) = work.at(&block.params, p)? {
                work.admit(1, size_of::<u32>())?;
                self.define(value.index(), work)?;
                work.next(&mut p)?;
            }
            let mut n = 0;
            while let Some(node) = work.at(&block.body, n)? {
                let mut r = 0;
                while let Some(value) = work.at(&node.results, r)? {
                    work.admit(1, size_of::<u32>())?;
                    self.define(value.index(), work)?;
                    work.next(&mut r)?;
                }
                work.next(&mut n)?;
            }
            work.next(&mut b)?;
        }
        Ok(())
    }
    fn define<O: ExecutionObserver>(&mut self, key: u32, work: &mut Work<'_, '_, O>) -> R {
        let previous = work.read(&self.definitions, key)?.unwrap_or(0);
        work.admit(1, size_of::<usize>())?;
        let count = previous
            .checked_add(1)
            .ok_or(ObservedValueError::CapacityOverflow)?;
        let _ = work.insert_copy(&mut self.definitions, key, count)?;
        Ok(())
    }
}
