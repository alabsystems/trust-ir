// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    dead_code,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
/// Exact direct-slot-then-first-physical-match lookup, including malformed
/// duplicate-ID behavior. This neither strengthens lookup to uniqueness nor
/// treats a successful reference as a validated-function capability.
pub(crate) fn function_by_id_observed<'m, O: ExecutionObserver>(
    module: &'m Module,
    callee: FuncId,
    session: &mut ObservedSession<'_, O>,
    site: ExecutionSite,
) -> R<Option<&'m Function>> {
    let mut work = Work { session, site };
    work.admit(1, size_of::<Option<&Function>>() + size_of::<usize>())?;
    if let Some(target) = module.functions.get(callee.as_usize()) {
        work.admit(1, 2 * size_of::<FuncId>())?;
        if target.id == callee {
            return work.publication(Some(target));
        }
    }
    work.admit(1, size_of::<usize>())?;
    let mut index = 0usize;
    loop {
        work.admit(1, size_of::<Option<&Function>>())?;
        let Some(target) = module.functions.get(index) else {
            return work.publication(None);
        };
        work.admit(1, 2 * size_of::<FuncId>())?;
        if target.id == callee {
            return work.publication(Some(target));
        }
        work.admit(1, size_of::<usize>())?;
        index = index
            .checked_add(1)
            .ok_or(ObservedValueError::CapacityOverflow)?;
    }
}
