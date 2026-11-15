// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    dead_code,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
impl ObservedNeed {
    fn flag(&mut self, flag: Flag) -> &mut Option<Reason> {
        match flag {
            Flag::Allocates => &mut self.allocates,
            Flag::Frees => &mut self.frees,
            Flag::MayUnwind => &mut self.may_unwind,
            Flag::Io => &mut self.io,
        }
    }
    pub(in super::super) fn add_flag_observed<O: ExecutionObserver>(
        &mut self,
        flag: Flag,
        block: u32,
        pieces: &[Piece<'_>],
        session: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> R {
        let mut work = Work { session, site };
        work.admit(
            4,
            size_of::<Flag>()
                + size_of::<Option<&Reason>>()
                + size_of::<&[Piece<'_>]>()
                + size_of::<Work<'_, '_, O>>(),
        )?;
        self.begin(&mut work)?;
        if self.flag(flag).is_some() {
            return work.publication(0);
        }
        self.render(pieces, &mut work)?;
        work.admit(2, size_of::<Reason>() + size_of::<Option<Reason>>())?;
        let reason = (block, take(&mut self.detail));
        *self.flag(flag) = Some(reason);
        work.publication(0)
    }
}
