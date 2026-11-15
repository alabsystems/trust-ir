// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    dead_code,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
pub(super) fn precedes<O: ExecutionObserver>(
    tree: &DominatorTree,
    earlier: Point,
    later: Point,
    work: &mut Work<'_, '_, O>,
) -> R<bool> {
    if !tree.is_reachable_observed(later.0, work.session, work.site)? {
        return Ok(false);
    }
    work.admit(1, size_of::<bool>())?;
    if earlier.0 == later.0 {
        work.admit(1, size_of::<bool>())?;
        Ok(earlier.1 < later.1)
    } else {
        tree.strictly_dominates_observed(earlier.0, later.0, work.session, work.site)
    }
}
