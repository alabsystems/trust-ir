// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    dead_code,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
pub(super) fn structure<'m, O: ExecutionObserver>(
    module: &'m Module,
    id: StructId,
    work: &mut Work<'_, '_, O>,
) -> R<Option<&'m StructDef>> {
    work.admit(1, size_of::<usize>())?;
    if let Some(def) = work.at(&module.structs, id.as_usize())? {
        work.admit(1, size_of::<bool>())?;
        if def.id == id {
            return Ok(Some(def));
        }
    }
    let mut at = 0;
    while let Some(def) = work.at(&module.structs, at)? {
        work.admit(1, size_of::<bool>())?;
        if def.id == id {
            return Ok(Some(def));
        }
        work.next(&mut at)?;
    }
    Ok(None)
}
pub(super) fn enumeration<'m, O: ExecutionObserver>(
    module: &'m Module,
    id: EnumId,
    work: &mut Work<'_, '_, O>,
) -> R<Option<&'m EnumDef>> {
    work.admit(1, size_of::<usize>())?;
    if let Some(def) = work.at(&module.enums, id.as_usize())? {
        work.admit(1, size_of::<bool>())?;
        if def.id == id {
            return Ok(Some(def));
        }
    }
    let mut at = 0;
    while let Some(def) = work.at(&module.enums, at)? {
        work.admit(1, size_of::<bool>())?;
        if def.id == id {
            return Ok(Some(def));
        }
        work.next(&mut at)?;
    }
    Ok(None)
}
