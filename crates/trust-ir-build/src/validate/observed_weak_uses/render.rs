// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    dead_code,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
pub(super) fn list<O: ExecutionObserver>(
    source: &[Ty],
    render: &mut String,
    out: &mut String,
    work: &mut Work<'_, '_, O>,
) -> R {
    let mut at = 0;
    while let Some(ty) = work.at(source, at)? {
        if at != 0 {
            work.text(", ", out)?;
        }
        work.admit(1, size_of::<String>())?;
        if render.capacity() != 0 {
            return Err(ObservedValueError::InvalidRange);
        }
        *render = ty.display_observed(work.session, work.site)?;
        work.text(render, out)?;
        work.flat(take(render));
        work.admit(1, 0)?;
        work.next(&mut at)?;
    }
    Ok(())
}

/// Exact original format_ty_list substitution, including empty () lists.
pub(super) fn wrapped_list<O: ExecutionObserver>(
    source: &[Ty],
    render: &mut String,
    out: &mut String,
    work: &mut Work<'_, '_, O>,
) -> R {
    work.text("(", out)?;
    list(source, render, out, work)?;
    work.text(")", out)
}

pub(super) fn convention<O: ExecutionObserver>(
    conv: CallingConv,
    out: &mut String,
    work: &mut Work<'_, '_, O>,
) -> R {
    // Actual closed Copy enum Display writes one fixed <=12-byte literal;
    // no variable string formatter/iteration or alternative spelling table.
    work.admit(64, size_of::<String>() + 64)?;
    *out = conv.to_string();
    Ok(())
}
