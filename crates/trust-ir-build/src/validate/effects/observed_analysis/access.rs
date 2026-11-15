// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    dead_code,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
impl Analysis<'_, '_> {
    pub(super) fn access<O: ExecutionObserver>(
        &mut self,
        side: Side,
        address: ValueId,
        block: u32,
        what: What,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        work.admit(
            2,
            size_of::<ObservedRoots>() + size_of::<Option<ObservedRoots>>(),
        )?;
        if self.roots.is_some() {
            return Err(ObservedValueError::InvalidRange);
        }
        self.roots = Some(
            self.body
                .as_ref()
                .ok_or(ObservedValueError::InvalidRange)?
                .roots_observed(address, work.session, work.site)?,
        );
        let result = (|| -> R {
            let mut at = 0usize;
            loop {
                work.admit(1, size_of::<Option<Root>>())?;
                let root = self
                    .roots
                    .as_ref()
                    .ok_or(ObservedValueError::InvalidRange)?
                    .at_observed(at, work.session, work.site)?;
                let Some(root) = root else { return Ok(()) };
                work.admit(3, size_of::<Root>() + 11 * size_of::<Piece<'_>>())?;
                match root {
                    Root::Local => {}
                    Root::Untraceable => {
                        let prefix = what.parts_observed(work.session, work.site)?;
                        let parts = [
                            prefix[0],
                            prefix[1],
                            prefix[2],
                            prefix[3],
                            prefix[4],
                            prefix[5],
                            prefix[6],
                            Piece::Text(
                                " through an address that does not trace to a parameter, a global or a local alloca",
                            ),
                        ];
                        self.side(side, None, block, &parts, work)?;
                    }
                    Root::Place(place) => {
                        let prefix = what.parts_observed(work.session, work.site)?;
                        let label =
                            root_label_observed(place, self.module, work.session, work.site)?;
                        let parts = [
                            prefix[0],
                            prefix[1],
                            prefix[2],
                            prefix[3],
                            prefix[4],
                            prefix[5],
                            prefix[6],
                            Piece::Text(" through "),
                            label[0],
                            label[1],
                            label[2],
                        ];
                        self.side(side, Some(place), block, &parts, work)?;
                    }
                }
                work.next(&mut at)?;
            }
        })();
        self.retire_roots(work);
        result
            .and_then(|()| work.admit(1, 0))
            .map_err(|e| work.terminal(e))
    }
}
