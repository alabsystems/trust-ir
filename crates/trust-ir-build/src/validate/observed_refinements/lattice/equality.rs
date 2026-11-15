// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    dead_code,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
pub(in super::super) fn equal<O: ExecutionObserver>(
    a: View<'_>,
    b: View<'_>,
    work: &mut Work<'_, '_, O>,
) -> R<bool> {
    work.admit(1, 2 * size_of::<View<'_>>())?;
    match (a, b) {
        (View::Interval(a, b), View::Interval(c, d)) => Ok(a == c && b == d),
        (View::Universe(a, s), View::Universe(b, t)) => Ok(a == b && s == t),
        (View::Conj(a), View::Conj(b)) | (View::Disj(a), View::Disj(b)) => {
            if a.len() != b.len() {
                return Ok(false);
            }
            for i in 0..a.len() {
                work.admit(1, 0)?;
                if a[i] != b[i] {
                    return Ok(false);
                }
            }
            Ok(true)
        }
        (View::Set(a), View::Set(b)) => {
            if a.len() != b.len() {
                return Ok(false);
            }
            for i in 0..a.len() {
                work.admit(1, 0)?;
                match (a, b) {
                    (Members::Constants(a), Members::Constants(b)) => {
                        if !constant(&a[i], &b[i], work)? {
                            return Ok(false);
                        }
                    }
                    _ => {
                        if a.key(i, work)? != b.key(i, work)? {
                            return Ok(false);
                        }
                    }
                }
            }
            Ok(true)
        }
        (View::Top, View::Top)
        | (View::Bottom, View::Bottom)
        | (View::NonZero, View::NonZero)
        | (View::NonNull, View::NonNull) => Ok(true),
        _ => Ok(false),
    }
}
#[derive(Clone, Copy)]
enum Pair<'a> {
    Value(&'a Constant, &'a Constant),
    Values(&'a [Constant], &'a [Constant]),
    Fields(&'a [(String, Constant)], &'a [(String, Constant)]),
}
fn constant<O: ExecutionObserver>(
    a: &Constant,
    b: &Constant,
    work: &mut Work<'_, '_, O>,
) -> R<bool> {
    work.admit(1, size_of::<Vec<Pair<'_>>>() + size_of::<Pair<'_>>())?;
    let mut stack = Vec::new();
    let result = (|| {
        work.push(&mut stack, Pair::Value(a, b))?;
        while let Some(pair) = stack.last().copied() {
            work.admit(1, size_of::<Pair<'_>>())?;
            stack.pop();
            match pair {
                Pair::Values(a, b) => {
                    if a.len() != b.len() {
                        return Ok(false);
                    }
                    if let (Some((a, at)), Some((b, bt))) = (a.split_first(), b.split_first()) {
                        work.push(&mut stack, Pair::Values(at, bt))?;
                        work.push(&mut stack, Pair::Value(a, b))?;
                    }
                }
                Pair::Fields(a, b) => {
                    if a.len() != b.len() {
                        return Ok(false);
                    }
                    if let (Some(((an, a), at)), Some(((bn, b), bt))) =
                        (a.split_first(), b.split_first())
                    {
                        if !work.eq_bytes(an.as_bytes(), bn.as_bytes())? {
                            return Ok(false);
                        }
                        work.push(&mut stack, Pair::Fields(at, bt))?;
                        work.push(&mut stack, Pair::Value(a, b))?;
                    }
                }
                Pair::Value(a, b) => {
                    use trust_ir::constant::ConstantG::*;
                    if core::mem::discriminant(a) != core::mem::discriminant(b) {
                        return Ok(false);
                    }
                    match (a, b) {
                        (Int(a), Int(b)) => {
                            if a != b {
                                return Ok(false);
                            }
                        }
                        (U128(a), U128(b)) => {
                            if a != b {
                                return Ok(false);
                            }
                        }
                        (Float(a), Float(b)) => {
                            if a.to_bits() != b.to_bits() {
                                return Ok(false);
                            }
                        }
                        (Bool(a), Bool(b)) => {
                            if a != b {
                                return Ok(false);
                            }
                        }
                        (Bytes { data: a, utf8: u }, Bytes { data: b, utf8: v }) => {
                            if !work.eq_bytes(a, b)? || u != v {
                                return Ok(false);
                            }
                        }
                        (Aggregate(a), Aggregate(b))
                        | (Array(a), Array(b))
                        | (Vector(a), Vector(b))
                        | (Sequence(a), Sequence(b))
                        | (Set(a), Set(b)) => work.push(&mut stack, Pair::Values(a, b))?,
                        (Splat { elem: a, len: n }, Splat { elem: b, len: m }) => {
                            if n != m {
                                return Ok(false);
                            }
                            work.push(&mut stack, Pair::Value(a, b))?
                        }
                        (Record(a), Record(b)) => work.push(&mut stack, Pair::Fields(a, b))?,
                        (
                            Closure {
                                func: a,
                                captures: x,
                            },
                            Closure {
                                func: b,
                                captures: y,
                            },
                        ) => {
                            if a != b {
                                return Ok(false);
                            }
                            work.push(&mut stack, Pair::Values(x, y))?
                        }
                        (FnDef(a), FnDef(b)) => {
                            if a != b {
                                return Ok(false);
                            }
                        }
                        (
                            SymbolAddr {
                                symbol: a,
                                addend: x,
                            },
                            SymbolAddr {
                                symbol: b,
                                addend: y,
                            },
                        ) => {
                            if !work.eq_bytes(a.as_bytes(), b.as_bytes())? || x != y {
                                return Ok(false);
                            }
                        }
                        (PhantomData, PhantomData) | (Uninit, Uninit) => {}
                        (Ext(x), _) => match *x {},
                        _ => return Ok(false),
                    }
                }
            }
        }
        Ok(true)
    })();
    work.retire_vec(&mut stack);
    result
}
