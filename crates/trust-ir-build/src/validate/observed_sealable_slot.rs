// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Actual sealable handle slot type traversal under the original owner.
#![allow(
    dead_code,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
use core::mem::{size_of, take};
use trust_ir::interpret::{
    ExecutionObserver, ExecutionPhase, ExecutionProgress, ExecutionSite, ObservedSession,
    ObservedValueError,
};
use trust_ir::ty::{FieldDef, StructDef};
use trust_ir::value::StructId;
mod storage;
#[cfg(test)]
mod tests;
mod walk;
use storage::Work;
type R<T = ()> = Result<T, ObservedValueError>;
#[derive(Clone, Copy)]
enum Frame<'a> {
    Type(&'a Ty),
    Fields(&'a [FieldDef], usize, StructId),
    Tuple(&'a [Ty], usize),
}
#[derive(Default)]
struct State<'a> {
    frames: Vec<Frame<'a>>,
    visiting: Vec<StructId>,
}
/// Preserve the complete original fresh-visiting-stack predicate. Handle is
/// allowed; struct/tuple descendants are examined only when the actual original
/// nominal summary says that lane reaches a handle. All other root shapes and
/// handle-reaching cycles refuse. Declaration lookup preserves exact index+ID
/// then first physical fallback semantics with observation inside the scan.
/// The explicit heap stack changes no short circuit or recursive guard order.
/// This borrowed-input boolean is data, not layout/module/runtime authority.
/// It cannot absorb a child operational error into false or claim a prewalk as
/// actual work. The same original session/site pays frames/active IDs before
/// growth and retires all capacity before the final boolean publication.
/// Full slot shape/constructor/query/module adoption, successful input disposal
/// and physical std/allocator/panic/RSS/hard-time bounds remain OPEN.
pub(super) fn sealable_slot_type_observed<O: ExecutionObserver>(
    module: &Module,
    nominal: &trust_ir::ObservedNominalTypeReachability<'_>,
    ty: &Ty,
    session: &mut ObservedSession<'_, O>,
    site: ExecutionSite,
) -> R<bool> {
    let mut work = Work { session, site };
    work.admit(1, size_of::<State<'_>>() + size_of::<Work<'_, '_, O>>())?;
    let mut state = State::default();
    let result = state.run(module, nominal, ty, &mut work);
    state.retire(&mut work);
    match result.and_then(|answer| {
        work.publication()?;
        Ok(answer)
    }) {
        Ok(answer) => Ok(answer),
        Err(error) => Err(work.terminal(error)),
    }
}
impl State<'_> {
    fn retire<O: ExecutionObserver>(&mut self, work: &mut Work<'_, '_, O>) {
        work.rows(take(&mut self.frames));
        work.rows(take(&mut self.visiting));
    }
}
