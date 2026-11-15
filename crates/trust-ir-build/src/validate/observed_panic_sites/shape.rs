// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    dead_code,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
pub(super) fn valid<O: ExecutionObserver>(
    signature: &FuncTy,
    operands: usize,
    work: &mut Work<'_, '_, O>,
) -> R<bool> {
    work.admit(8, 2 * size_of::<usize>() + size_of::<bool>())?;
    let count = operands
        .checked_add(1)
        .ok_or(ObservedValueError::CapacityOverflow)?;
    if signature.is_vararg || !signature.returns.is_empty() || signature.params.len() != count {
        return Ok(false);
    }
    let mut at = 0;
    while at < operands {
        let ty = work
            .at(&signature.params, at)?
            .ok_or(ObservedValueError::InvalidRange)?;
        work.admit(1, size_of::<bool>())?;
        if !matches!(ty, Ty::Usize) {
            return Ok(false);
        }
        work.next(&mut at)?;
    }
    let last = work
        .at(&signature.params, operands)?
        .ok_or(ObservedValueError::InvalidRange)?;
    // Actual original predicate inspects only the outer tag, not pointee data.
    work.admit(8, size_of::<bool>())?;
    Ok(is_panic_location_ty(last))
}
