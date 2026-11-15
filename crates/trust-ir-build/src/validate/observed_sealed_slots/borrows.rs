// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    dead_code,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
impl State {
    pub(super) fn borrows<O: ExecutionObserver>(
        &mut self,
        function: &Function,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        loop {
            work.admit(1, size_of::<bool>())?;
            let mut grew = false;
            let mut b = 0;
            while let Some(block) = work.at(&function.blocks, b)? {
                let mut n = 0;
                while let Some(node) = work.at(&block.body, n)? {
                    work.admit(1, size_of::<&Inst>())?;
                    if let Inst::Borrow { ptr } | Inst::BorrowMut { ptr } = &node.inst
                        && let Some((owner, _)) = work.read(&self.members, ptr.index())?
                    {
                        let mut r = 0;
                        while let Some(result) = work.at(&node.results, r)? {
                            work.admit(1, size_of::<u32>())?;
                            let key = result.index();
                            if work.read(&self.members, key)?.is_none() {
                                let _ = work.insert_copy(
                                    &mut self.members,
                                    key,
                                    (owner, (block.id, n)),
                                )?;
                                work.admit(1, size_of::<bool>())?;
                                grew = true;
                            }
                            work.next(&mut r)?;
                        }
                    }
                    work.next(&mut n)?;
                }
                work.next(&mut b)?;
            }
            work.admit(1, size_of::<bool>())?;
            if !grew {
                return Ok(());
            }
        }
    }
}
