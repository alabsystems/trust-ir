// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    dead_code,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
pub(super) fn exists<O: ExecutionObserver>(module: &Module, work: &mut Work<'_, '_, O>) -> R<bool> {
    let mut at = 0;
    while let Some(f) = work.at(&module.functions, at)? {
        work.admit(8, size_of::<bool>())?;
        if f.is_weak_declaration() {
            return Ok(true);
        }
        work.next(&mut at)?;
    }
    Ok(false)
}
pub(super) fn last<'m, O: ExecutionObserver>(
    module: &'m Module,
    name: &str,
    work: &mut Work<'_, '_, O>,
) -> R<Option<&'m Function>> {
    work.admit(1, size_of::<Option<&Function>>())?;
    let mut found = None;
    let mut at = 0;
    while let Some(f) = work.at(&module.functions, at)? {
        work.admit(8, size_of::<bool>())?;
        if f.is_weak_declaration() && work.equal(&f.name, name)? {
            work.admit(1, size_of::<Option<&Function>>())?;
            found = Some(f);
        }
        work.next(&mut at)?;
    }
    Ok(found)
}
