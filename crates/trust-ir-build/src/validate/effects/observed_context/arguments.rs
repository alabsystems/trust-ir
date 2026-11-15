// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    dead_code,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
impl<'i> Arguments<'i> {
    /// Exact kind operands followed by location; no Vec or ordinary operands
    /// callback is hidden behind the fixed seven-way dispatch.
    pub(in super::super) fn panic_observed<O: ExecutionObserver>(
        kind: &AssertKind,
        location: PanicLocation,
        session: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> R<Self> {
        let mut work = begin(
            session,
            site,
            7,
            size_of::<AssertKind>()
                + size_of::<PanicLocation>()
                + size_of::<Option<[ValueId; 2]>>()
                + size_of::<Self>(),
        )?;
        let operands = match kind {
            AssertKind::BoundsCheck { index, len } => Some([*index, *len]),
            AssertKind::MisalignedPtr { required, found } => Some([*required, *found]),
            AssertKind::Unspecified
            | AssertKind::Overflow(_)
            | AssertKind::DivByZero
            | AssertKind::RemByZero
            | AssertKind::NullPtr => None,
        };
        let answer = Self::Panic { operands, location };
        work.publish(answer)
    }
    pub(in super::super) fn get_observed<O: ExecutionObserver>(
        &self,
        index: usize,
        session: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> R<Option<Arg>> {
        let mut work = begin(
            session,
            site,
            3,
            size_of::<Self>() + size_of::<usize>() + size_of::<Option<Arg>>(),
        )?;
        let answer = match self {
            Self::Values(values) => {
                work.admit(1, size_of::<Option<&ValueId>>())?;
                match values.get(index) {
                    Some(value) => {
                        work.admit(1, size_of::<ValueId>() + size_of::<Arg>())?;
                        Some(Arg::Value(*value))
                    }
                    None => None,
                }
            }
            Self::ElementSlot => (index == 0).then_some(Arg::Untraceable),
            Self::Panic { operands, location } => {
                work.admit(2, size_of::<Option<[ValueId; 2]>>())?;
                match operands {
                    Some(values) if index < 2 => {
                        work.admit(1, size_of::<ValueId>() + size_of::<Arg>())?;
                        Some(Arg::Value(values[index]))
                    }
                    Some(_) if index == 2 => Some(location_arg(location, &mut work)?),
                    None if index == 0 => Some(location_arg(location, &mut work)?),
                    Some(_) | None => None,
                }
            }
        };
        work.publish(answer)
    }
}
fn location_arg<O: ExecutionObserver>(
    location: &PanicLocation,
    work: &mut Work<'_, '_, O>,
) -> R<Arg> {
    work.admit(2, size_of::<PanicLocation>() + size_of::<Arg>())?;
    Ok(match location {
        PanicLocation::Global(global) => Arg::Global(*global),
        PanicLocation::Value(value) => Arg::Value(*value),
    })
}
