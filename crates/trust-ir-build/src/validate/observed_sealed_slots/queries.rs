// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    dead_code,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
impl ObservedSealedHandleSlots<'_> {
    pub(super) fn slot_of<'a, O: ExecutionObserver>(
        &'a self,
        pointer: ValueId,
        work: &mut Work<'_, '_, O>,
    ) -> R<Option<(u32, &'a Slot)>> {
        let Some((owner, _)) = work.read(&self.members, pointer.index())? else {
            return Ok(None);
        };
        Ok(work.slot(&self.slots, owner)?.map(|slot| (owner, slot)))
    }
    pub(super) fn initialized_at<O: ExecutionObserver>(
        &self,
        slot: &Slot,
        at: Point,
        work: &mut Work<'_, '_, O>,
    ) -> R<bool> {
        let mut i = 0;
        while let Some(store) = work.at(&slot.stores, i)? {
            work.admit(1, size_of::<Point>())?;
            let store = *store;
            if dominance::precedes(&self.dominators, slot.site, store, work)?
                && dominance::precedes(&self.dominators, store, at, work)?
            {
                return Ok(true);
            }
            work.next(&mut i)?;
        }
        Ok(false)
    }
}
