// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    dead_code,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
impl State {
    pub(super) fn unseal<O: ExecutionObserver>(
        &mut self,
        owner: u32,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        let transferred = {
            if let Some(slot) = work.slot_mut(&mut self.slots, owner)? {
                work.admit(1, size_of::<bool>())?;
                if slot.unsealed.is_none() {
                    work.admit(1, size_of::<Option<String>>() + size_of::<String>())?;
                    slot.unsealed = Some(take(&mut self.reason));
                    true
                } else {
                    false
                }
            } else {
                false
            }
        };
        if !transferred {
            work.flat(take(&mut self.reason));
        }
        work.admit(1, 0)
    }
    pub(super) fn queue_unseal<O: ExecutionObserver>(
        &mut self,
        owner: u32,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        work.reserve(&mut self.unsealing)?;
        work.admit(1, size_of::<(u32, String)>())?;
        self.unsealing.push((owner, take(&mut self.reason)));
        Ok(())
    }
    pub(super) fn apply_unsealing<O: ExecutionObserver>(
        &mut self,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        // Retain this original per-node vector in State while moving each
        // whole reason into the pending owner before the next lookup fee.
        // Reverse once, then pop, using paid header swaps to preserve source order.
        work.admit(1, 2 * size_of::<usize>())?;
        if self.reason.capacity() != 0 {
            return Err(ObservedValueError::InvalidRange);
        }
        let mut left = 0usize;
        let mut right = self.unsealing.len();
        while left < right {
            work.admit(1, 2 * size_of::<usize>())?;
            right = right
                .checked_sub(1)
                .ok_or(ObservedValueError::CapacityOverflow)?;
            if left >= right {
                break;
            }
            work.admit(1, 2 * size_of::<(u32, String)>())?;
            self.unsealing.swap(left, right);
            work.next(&mut left)?;
        }
        loop {
            work.admit(1, size_of::<Option<(u32, String)>>())?;
            let Some((owner, reason)) = self.unsealing.pop() else {
                break;
            };
            // No intervening fallible step may lose this complete String.
            self.reason = reason;
            self.unseal(owner, work)?;
        }
        Ok(())
    }
}
