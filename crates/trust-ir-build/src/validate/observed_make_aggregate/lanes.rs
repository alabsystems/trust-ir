// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    dead_code,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
pub(super) enum Lanes<'a> {
    Fields(&'a [FieldDef]),
    Types(&'a [Ty]),
    Repeated(&'a Ty, usize),
}
impl<'a> Lanes<'a> {
    pub(super) fn len<O: ExecutionObserver>(&self, work: &mut Work<'_, '_, O>) -> R<usize> {
        work.admit(1, size_of::<usize>())?;
        Ok(match self {
            Self::Fields(a) => a.len(),
            Self::Types(a) => a.len(),
            Self::Repeated(_, n) => *n,
        })
    }
    pub(super) fn at<O: ExecutionObserver>(
        &self,
        index: usize,
        work: &mut Work<'_, '_, O>,
    ) -> R<Option<&'a Ty>> {
        match self {
            Self::Fields(a) => Ok(work.at(a, index)?.map(|f| &f.ty)),
            Self::Types(a) => work.at(a, index),
            Self::Repeated(ty, n) => {
                work.admit(2, size_of::<Option<&Ty>>())?;
                Ok((index < *n).then_some(*ty))
            }
        }
    }
}
