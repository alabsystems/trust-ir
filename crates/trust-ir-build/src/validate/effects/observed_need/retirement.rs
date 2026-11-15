// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    dead_code,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
impl ObservedNeed {
    pub(in super::super) fn retire_observed<O: ExecutionObserver>(
        mut self,
        session: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> R {
        let mut work = Work { session, site };
        self.drain(&mut work);
        work.publication(0)
    }
    pub(super) fn drain<O: ExecutionObserver>(&mut self, work: &mut Work<'_, '_, O>) {
        work.step(size_of::<Self>().saturating_add(1));
        work.retire_text(take(&mut self.detail));
        retire_side(&mut self.reads, work);
        retire_side(&mut self.writes, work);
        retire_optional(&mut self.allocates, work);
        retire_optional(&mut self.frees, work);
        retire_optional(&mut self.may_unwind, work);
        retire_optional(&mut self.io, work);
    }
}
fn retire_reason<O: ExecutionObserver>((_, text): Reason, work: &mut Work<'_, '_, O>) {
    work.step(size_of::<Reason>().saturating_add(1));
    work.retire_text(text);
}
fn retire_optional<O: ExecutionObserver>(reason: &mut Option<Reason>, work: &mut Work<'_, '_, O>) {
    work.step(size_of::<Option<Reason>>().saturating_add(1));
    if let Some(reason) = reason.take() {
        retire_reason(reason, work)
    }
    work.poll();
}
fn retire_side<O: ExecutionObserver>(side: &mut ObservedSide, work: &mut Work<'_, '_, O>) {
    retire_optional(&mut side.everything, work);
    loop {
        work.step(size_of::<Option<PlaceReason>>().saturating_add(1));
        let Some((_, reason)) = side.places.pop() else {
            break;
        };
        work.step(size_of::<EffectPlace>().saturating_add(1));
        retire_reason(reason, work);
    }
    work.step(size_of::<Vec<PlaceReason>>().saturating_add(1));
    drop(take(&mut side.places));
    work.poll();
}
