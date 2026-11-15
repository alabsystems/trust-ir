// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Only original first-reason accumulation, not body-effect validation.
#![allow(
    dead_code,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::EffectPlace;
use core::{
    cmp::Ordering,
    mem::{size_of, take},
};
use trust_ir::interpret::{
    ExecutionObserver, ExecutionPhase, ExecutionProgress, ExecutionSite, ObservedSession,
    ObservedValueError,
};
mod flags;
mod retirement;
mod side;
mod storage;
#[cfg(test)]
mod tests;
use storage::Work;
type R<T = ()> = Result<T, ObservedValueError>;
pub(super) type Reason = (u32, String);
pub(super) type PlaceReason = (EffectPlace, Reason);
#[derive(Clone, Copy)]
pub(super) enum Side {
    Read,
    Write,
}
#[derive(Clone, Copy)]
pub(super) enum Flag {
    Allocates,
    Frees,
    MayUnwind,
    Io,
}
/// Borrowed exact text recipe. No candidate callback or opaque formatter.
#[derive(Clone, Copy)]
pub(super) enum Piece<'a> {
    Text(&'a str),
    U32(u32),
}
#[derive(Default)]
pub(super) struct ObservedSide {
    pub(super) everything: Option<Reason>,
    pub(super) places: Vec<PlaceReason>,
}
/// Data only. After any mutating error the enclosing original caller must
/// retain and consume this entire value under that SAME session/site. An
/// interrupted partially ordered vector is never a semantic validation result.
#[derive(Default)]
pub(super) struct ObservedNeed {
    pub(super) reads: ObservedSide,
    pub(super) writes: ObservedSide,
    pub(super) allocates: Option<Reason>,
    pub(super) frees: Option<Reason>,
    pub(super) may_unwind: Option<Reason>,
    pub(super) io: Option<Reason>,
    pub(super) detail: String,
}
impl ObservedNeed {
    pub(super) fn new_observed<O: ExecutionObserver>(
        session: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> R<Self> {
        let mut work = Work { session, site };
        work.admit(1, size_of::<Self>() + size_of::<Work<'_, '_, O>>())?;
        let answer = Self::default();
        work.publication(size_of::<Self>())?;
        Ok(answer)
    }
    fn begin<O: ExecutionObserver>(&self, work: &mut Work<'_, '_, O>) -> R {
        work.admit(1, size_of::<usize>())?;
        if self.detail.capacity() != 0 {
            return Err(ObservedValueError::InvalidRange);
        }
        Ok(())
    }
    fn render<O: ExecutionObserver>(
        &mut self,
        pieces: &[Piece<'_>],
        work: &mut Work<'_, '_, O>,
    ) -> R {
        work.admit(1, size_of::<usize>())?;
        let mut at = 0usize;
        loop {
            work.admit(1, size_of::<Option<&Piece<'_>>>())?;
            let Some(piece) = pieces.get(at) else {
                return Ok(());
            };
            work.admit(2, size_of::<Piece<'_>>())?;
            match piece {
                Piece::Text(text) => work.text(text, &mut self.detail)?,
                Piece::U32(n) => work.number(*n, &mut self.detail)?,
            }
            work.next(&mut at)?;
        }
    }
}
