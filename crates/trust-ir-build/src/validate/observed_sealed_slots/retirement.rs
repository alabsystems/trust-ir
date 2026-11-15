// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    dead_code,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
pub(super) fn slot<O: ExecutionObserver>(value: Slot, work: &mut Work<'_, '_, O>) {
    work.step(size_of::<Slot>() + 1);
    let Slot {
        ty,
        site: _,
        natural_align: _,
        unsealed,
        stores,
    } = value;
    let _ = ty.retire_observed(work.session, work.site);
    work.step(size_of::<Option<String>>() + 1);
    if let Some(reason) = unsealed {
        work.flat(reason);
    }
    work.poll();
    work.rows(stores);
}
impl State {
    pub(super) fn retire_old_slot<O: ExecutionObserver>(&mut self, work: &mut Work<'_, '_, O>) {
        work.step(size_of::<Option<Slot>>() + 1);
        if let Some(value) = self.old_slot.take() {
            slot(value, work);
        }
        work.poll();
    }
    pub(super) fn retire_scratch<O: ExecutionObserver>(&mut self, work: &mut Work<'_, '_, O>) {
        self.retire_old_slot(work);
        work.step(size_of::<Option<Slot>>() + 1);
        if let Some(value) = self.pending_slot.take() {
            slot(value, work);
        }
        work.poll();
        work.step(size_of::<Option<Ty>>() + 1);
        if let Some(ty) = self.pending_type.take() {
            let _ = ty.retire_observed(work.session, work.site);
        }
        work.poll();
        work.step(size_of::<Option<String>>() + size_of::<Option<u64>>() + 1);
        if let Some(reason) = self.pending_unsealed.take() {
            work.flat(reason);
        }
        self.pending_natural = None;
        work.poll();
        while work.pop_first(&mut self.definitions).is_some() {}
        work.step(size_of::<BTreeMap<u32, usize>>() + 1);
        drop(take(&mut self.definitions));
        work.poll();
        work.rows(take(&mut self.multiply_defined));
        work.rows(take(&mut self.operands));
        loop {
            work.step(size_of::<Option<(u32, String)>>() + 1);
            let Some((_, reason)) = self.unsealing.pop() else {
                break;
            };
            work.flat(reason);
        }
        work.step(size_of::<Vec<(u32, String)>>() + 1);
        drop(take(&mut self.unsealing));
        work.poll();
        work.flat(take(&mut self.reason));
        work.flat(take(&mut self.render));
    }
    pub(super) fn retire_analysis<O: ExecutionObserver>(&mut self, work: &mut Work<'_, '_, O>) {
        while let Some((_, value)) = work.pop_first(&mut self.slots) {
            slot(value, work);
        }
        work.step(size_of::<BTreeMap<u32, Slot>>() + 1);
        drop(take(&mut self.slots));
        work.poll();
        while work.pop_first(&mut self.members).is_some() {}
        work.step(size_of::<BTreeMap<u32, (u32, Point)>>() + 1);
        drop(take(&mut self.members));
        work.poll();
        work.step(size_of::<Option<DominatorTree>>() + 1);
        if let Some(tree) = self.dominators.take() {
            let _ = tree.retire_observed(work.session, work.site);
        }
        work.poll();
    }
}
