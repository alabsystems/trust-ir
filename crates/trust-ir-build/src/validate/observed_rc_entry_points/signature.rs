// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    dead_code,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
/// Exact derived FuncTy field order. The private actual-table lookup supplies
/// this borrowed static entry; RcEntryPoint::func_ty fixes vararg=false/ABI=None.
/// Compare its exact slices without constructing redundant owned clones. Actual
/// present ABI payloads remain unequal and unread, never erased or normalized.
pub(super) fn same<O: ExecutionObserver>(
    actual: &FuncTy,
    expected: &RcEntryPoint,
    work: &mut Work<'_, '_, O>,
) -> R<bool> {
    work.admit(1, size_of::<&FuncTy>())?;
    if !types(&actual.params, expected.params, work)? {
        return Ok(false);
    }
    if !types(&actual.returns, expected.returns, work)? {
        return Ok(false);
    }
    work.admit(1, 2 * size_of::<bool>())?;
    if actual.is_vararg {
        return Ok(false);
    }
    work.admit(1, size_of::<bool>())?;
    Ok(actual.abi.is_none())
}
fn types<O: ExecutionObserver>(
    actual: &[Ty],
    expected: &[Ty],
    work: &mut Work<'_, '_, O>,
) -> R<bool> {
    work.admit(1, 2 * size_of::<usize>())?;
    if actual.len() != expected.len() {
        return Ok(false);
    }
    let mut at = 0usize;
    while let Some(a) = work.at(actual, at)? {
        let b = work
            .at(expected, at)?
            .ok_or(ObservedValueError::InvalidRange)?;
        if !a.structural_eq_observed(b, work.session, work.site)? {
            return Ok(false);
        }
        work.next(&mut at)?;
    }
    Ok(true)
}
