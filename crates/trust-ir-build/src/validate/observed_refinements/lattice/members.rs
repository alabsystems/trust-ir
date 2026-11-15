// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    dead_code,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
pub(in super::super) fn canonical<O: ExecutionObserver>(
    items: Members<'_>,
    work: &mut Work<'_, '_, O>,
) -> R<bool> {
    work.admit(1, size_of::<Option<Scalar>>())?;
    if items.len() == 0 || items.len() > trust_ir::pred::MAX_ENUMERATED_MEMBERS {
        return Ok(false);
    }
    let mut prev = None;
    for i in 0..items.len() {
        let Some(key) = items.key(i, work)? else {
            return Ok(false);
        };
        if prev.is_some_and(|p| key <= p) {
            return Ok(false);
        }
        prev = Some(key);
    }
    Ok(true)
}
fn contains<O: ExecutionObserver>(
    items: Members<'_>,
    key: Scalar,
    work: &mut Work<'_, '_, O>,
) -> R<bool> {
    let (mut lo, mut hi) = (0, items.len());
    while lo < hi {
        work.admit(1, 2 * size_of::<usize>())?;
        let mid = lo + (hi - lo) / 2;
        let found = items.key(mid, work)?.unwrap_or((u8::MAX, i128::MAX));
        if found == key {
            return Ok(true);
        }
        if found < key { lo = mid + 1 } else { hi = mid }
    }
    Ok(false)
}
pub(in super::super) fn int_bounds<O: ExecutionObserver>(
    items: Members<'_>,
    work: &mut Work<'_, '_, O>,
) -> R<Option<(i128, i128)>> {
    if !canonical(items, work)? {
        return Ok(None);
    }
    let (mut lo, mut hi) = (i128::MAX, i128::MIN);
    for i in 0..items.len() {
        work.admit(1, 0)?;
        match items.key(i, work)? {
            Some((0, v)) => {
                lo = lo.min(v);
                hi = hi.max(v)
            }
            _ => return Ok(None),
        }
    }
    Ok((lo <= hi).then_some((lo, hi)))
}
pub(in super::super) fn interval<O: ExecutionObserver>(
    items: Members<'_>,
    lo: i128,
    hi: i128,
    work: &mut Work<'_, '_, O>,
) -> R<bool> {
    work.admit(1, 2 * size_of::<i128>())?;
    if lo > hi {
        return Ok(true);
    }
    if !canonical(items, work)? {
        return Ok(false);
    }
    let Some(span) = hi.checked_sub(lo) else {
        return Ok(false);
    };
    if span >= items.len() as i128 {
        return Ok(false);
    }
    let mut v = lo;
    loop {
        work.admit(1, 0)?;
        if !contains(items, (0, v), work)? {
            return Ok(false);
        }
        if v == hi {
            return Ok(true);
        }
        v = v
            .checked_add(1)
            .ok_or(ObservedValueError::CapacityOverflow)?;
    }
}
pub(in super::super) fn subset<O: ExecutionObserver>(
    a: Members<'_>,
    b: Members<'_>,
    work: &mut Work<'_, '_, O>,
) -> R<bool> {
    if !canonical(a, work)? || !canonical(b, work)? {
        return Ok(false);
    }
    for i in 0..a.len() {
        work.admit(1, 0)?;
        let Some(key) = a.key(i, work)? else {
            return Ok(false);
        };
        if !contains(b, key, work)? {
            return Ok(false);
        }
    }
    Ok(true)
}
pub(in super::super) fn cardinality<O: ExecutionObserver>(
    u: &Universe,
    work: &mut Work<'_, '_, O>,
) -> R<Option<u128>> {
    work.admit(1, size_of::<Option<u128>>())?;
    Ok(match u {
        Universe::IntRange { lo, hi } => {
            if lo > hi {
                None
            } else {
                (hi.wrapping_sub(*lo) as u128).checked_add(1)
            }
        }
        Universe::Members(v) => canonical(Members::Constants(v), work)?.then_some(v.len() as u128),
    })
}
fn universe_canonical<O: ExecutionObserver>(u: &Universe, work: &mut Work<'_, '_, O>) -> R<bool> {
    work.admit(1, 0)?;
    match u {
        Universe::IntRange { lo, hi } => Ok(lo <= hi),
        Universe::Members(v) => canonical(Members::Constants(v), work),
    }
}
pub(in super::super) fn universe_bounds<O: ExecutionObserver>(
    u: &Universe,
    work: &mut Work<'_, '_, O>,
) -> R<Option<(i128, i128)>> {
    work.admit(1, 0)?;
    match u {
        Universe::IntRange { lo, hi } => Ok((lo <= hi).then_some((*lo, *hi))),
        Universe::Members(v) => int_bounds(Members::Constants(v), work),
    }
}
pub(in super::super) fn universe_subset<O: ExecutionObserver>(
    a: &Universe,
    b: &Universe,
    work: &mut Work<'_, '_, O>,
) -> R<bool> {
    if !universe_canonical(a, work)? || !universe_canonical(b, work)? {
        return Ok(false);
    }
    match (a, b) {
        (Universe::IntRange { lo, hi }, Universe::IntRange { lo: bl, hi: bh }) => {
            Ok(bl <= lo && hi <= bh)
        }
        (Universe::IntRange { lo, hi }, Universe::Members(v)) => {
            interval(Members::Constants(v), *lo, *hi, work)
        }
        (Universe::Members(v), Universe::IntRange { lo, hi }) => {
            for c in v {
                work.admit(1, 0)?;
                match trust_ir::pred::constant_key(c) {
                    Some((0, n)) if *lo <= n && n <= *hi => {}
                    _ => return Ok(false),
                }
            }
            Ok(true)
        }
        (Universe::Members(a), Universe::Members(b)) => {
            subset(Members::Constants(a), Members::Constants(b), work)
        }
    }
}
