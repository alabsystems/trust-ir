// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    dead_code,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
// Exactly the pinned ordinary MAX_PRED_DEPTH, not a new validation limit.
const DEPTH: u32 = 64;
pub(in super::super) fn bounds<O: ExecutionObserver>(
    module: &Module,
    p: View<'_>,
    depth: u32,
    work: &mut Work<'_, '_, O>,
) -> R<Option<(i128, i128)>> {
    work.admit(1, size_of::<(View<'_>, u32, Option<(i128, i128)>)>())?;
    if depth > DEPTH {
        return Ok(None);
    }
    match p {
        View::Interval(lo, hi) => Ok((lo <= hi).then_some((lo, hi))),
        View::Set(v) => members::int_bounds(v, work),
        View::Universe(u, Space::Member) => match universe(module, u, work)? {
            Some(u) => members::universe_bounds(u, work),
            None => Ok(None),
        },
        View::Universe(u, Space::Index) => {
            let Some(u) = universe(module, u, work)? else {
                return Ok(None);
            };
            Ok(cardinality(u, work)?
                .filter(|n| *n > 0)
                .and_then(|n| i128::try_from(n - 1).ok())
                .map(|hi| (0, hi)))
        }
        View::Conj(children) => {
            let mut acc: Option<(i128, i128)> = None;
            for c in children {
                work.admit(1, 0)?;
                if let Some(cp) = pred(module, *c, work)?
                    && let Some((clo, chi)) = bounds(module, cp, depth + 1, work)?
                {
                    acc = Some(match acc {
                        None => (clo, chi),
                        Some((lo, hi)) => (lo.max(clo), hi.min(chi)),
                    });
                }
            }
            Ok(acc.filter(|(lo, hi)| lo <= hi))
        }
        View::Disj(children) => {
            let (mut lo, mut hi) = (i128::MAX, i128::MIN);
            for c in children {
                work.admit(1, 0)?;
                let Some(cp) = pred(module, *c, work)? else {
                    return Ok(None);
                };
                let Some((clo, chi)) = bounds(module, cp, depth + 1, work)? else {
                    return Ok(None);
                };
                lo = lo.min(clo);
                hi = hi.max(chi);
            }
            Ok((lo <= hi).then_some((lo, hi)))
        }
        View::Bottom => Ok(Some((0, 0))),
        _ => Ok(None),
    }
}
pub(in super::super) fn implies<O: ExecutionObserver>(
    module: &Module,
    a: View<'_>,
    b: View<'_>,
    depth: u32,
    work: &mut Work<'_, '_, O>,
) -> R<bool> {
    work.admit(1, size_of::<(View<'_>, View<'_>, u32, bool)>())?;
    if depth > DEPTH {
        return Ok(false);
    }
    if matches!(a, View::Bottom) {
        return Ok(true);
    }
    if matches!(b, View::Bottom) {
        return Ok(false);
    }
    if matches!(b, View::Top) {
        return Ok(true);
    }
    if matches!(a, View::Top) {
        return Ok(false);
    }
    if equal(a, b, work)? {
        return Ok(true);
    }
    if let View::Conj(children) = a {
        for c in children {
            work.admit(1, 0)?;
            if let Some(p) = pred(module, *c, work)?
                && implies(module, p, b, depth + 1, work)?
            {
                return Ok(true);
            }
        }
    }
    if let View::Disj(children) = b {
        for c in children {
            work.admit(1, 0)?;
            if let Some(p) = pred(module, *c, work)?
                && implies(module, a, p, depth + 1, work)?
            {
                return Ok(true);
            }
        }
    }
    if let View::Conj(children) = b {
        for c in children {
            work.admit(1, 0)?;
            let Some(p) = pred(module, *c, work)? else {
                return Ok(false);
            };
            if !implies(module, a, p, depth + 1, work)? {
                return Ok(false);
            }
        }
        return Ok(true);
    }
    if let View::Disj(children) = a {
        for c in children {
            work.admit(1, 0)?;
            let Some(p) = pred(module, *c, work)? else {
                return Ok(false);
            };
            if !implies(module, p, b, depth + 1, work)? {
                return Ok(false);
            }
        }
        return Ok(true);
    }
    match b {
        View::Universe(ub, sb) => {
            let View::Universe(ua, sa) = a else {
                return Ok(false);
            };
            if sa != sb {
                return Ok(false);
            }
            let (Some(ua), Some(ub)) = (universe(module, ua, work)?, universe(module, ub, work)?)
            else {
                return Ok(false);
            };
            if !members::universe_subset(ua, ub, work)? {
                return Ok(false);
            }
            if sa == Space::Index {
                members::universe_subset(ub, ua, work)
            } else {
                Ok(true)
            }
        }
        View::Interval(lo, hi) => Ok(
            bounds(module, a, depth + 1, work)?.is_some_and(|(alo, ahi)| lo <= alo && ahi <= hi)
        ),
        View::Set(target) => match a {
            View::Set(src) => members::subset(src, target, work),
            View::Interval(lo, hi) => members::interval(target, lo, hi, work),
            View::Universe(u, s) => match (universe(module, u, work)?, s) {
                (Some(Universe::Members(v)), Space::Member) => {
                    members::subset(Members::Constants(v), target, work)
                }
                (Some(Universe::IntRange { lo, hi }), Space::Member) => {
                    members::interval(target, *lo, *hi, work)
                }
                (Some(u), Space::Index) => match cardinality(u, work)? {
                    Some(n) if n > 0 => match i128::try_from(n - 1) {
                        Ok(hi) => members::interval(target, 0, hi, work),
                        Err(_) => Ok(false),
                    },
                    _ => Ok(false),
                },
                _ => Ok(false),
            },
            _ => Ok(false),
        },
        View::NonZero => {
            Ok(bounds(module, a, depth + 1, work)?.is_some_and(|(lo, hi)| lo > 0 || hi < 0))
        }
        _ => Ok(false),
    }
}
