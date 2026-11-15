// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    dead_code,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
mod equality;
mod members;
mod relation;
pub(super) use equality::equal;
pub(super) use members::cardinality;
pub(super) use relation::{bounds, implies};
pub(super) type Scalar = (u8, i128);
#[derive(Clone, Copy)]
pub(super) enum Members<'a> {
    Constants(&'a [Constant]),
    Keys(&'a [Scalar]),
}
impl Members<'_> {
    pub(super) fn len(self) -> usize {
        match self {
            Self::Constants(v) => v.len(),
            Self::Keys(v) => v.len(),
        }
    }
    pub(super) fn key<O: ExecutionObserver>(
        self,
        index: usize,
        work: &mut Work<'_, '_, O>,
    ) -> R<Option<Scalar>> {
        work.admit(1, size_of::<Option<Scalar>>())?;
        Ok(match self {
            Self::Constants(v) => v.get(index).and_then(trust_ir::pred::constant_key),
            Self::Keys(v) => v.get(index).copied(),
        })
    }
}
#[derive(Clone, Copy)]
pub(super) enum View<'a> {
    Interval(i128, i128),
    Set(Members<'a>),
    Universe(UnivId, Space),
    NonZero,
    NonNull,
    Conj(&'a [PredId]),
    Disj(&'a [PredId]),
    Top,
    Bottom,
}
impl<'a> View<'a> {
    pub(super) fn node(p: &'a Pred) -> Self {
        match p {
            Pred::Interval { lo, hi } => Self::Interval(*lo, *hi),
            Pred::FiniteSet(v) => Self::Set(Members::Constants(v)),
            Pred::InUniverse(u, s) => Self::Universe(*u, *s),
            Pred::NonZero => Self::NonZero,
            Pred::NonNull => Self::NonNull,
            Pred::Conj(v) => Self::Conj(v),
            Pred::Disj(v) => Self::Disj(v),
            Pred::Top => Self::Top,
            Pred::Bottom => Self::Bottom,
        }
    }
    pub(super) fn top(self) -> bool {
        matches!(self, Self::Top)
    }
}
pub(super) fn pred<'a, O: ExecutionObserver>(
    module: &'a Module,
    id: PredId,
    work: &mut Work<'_, '_, O>,
) -> R<Option<View<'a>>> {
    Ok(work.at(&module.predicates, id.as_usize())?.map(View::node))
}
pub(super) fn universe<'a, O: ExecutionObserver>(
    module: &'a Module,
    id: UnivId,
    work: &mut Work<'_, '_, O>,
) -> R<Option<&'a Universe>> {
    work.at(&module.universes, id.as_usize())
}
