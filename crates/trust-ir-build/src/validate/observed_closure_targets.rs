// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Local closure constructor seeds and target-preserving propagation.
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
mod build;
mod cost;
mod storage;
#[cfg(test)]
mod tests;
use storage::Work;
type R<T = ()> = Result<T, ObservedValueError>;
/// Immutable data for the exact borrowed original Function. The ordinary
/// algorithm records last constructor seed and first vacant target-preserving propagation, even
/// on malformed SSA/multi-result inputs; this establishes no uniqueness, type,
/// capture, target, reachability, source, module or proof authority. Every
/// mandatory original validator remains required by the full module caller.
/// No raw/candidate map constructor or mutable map access is exposed.
pub(super) struct ObservedLocalClosureTargets<'f> {
    _function: &'f Function,
    targets: BTreeMap<u32, FuncId>,
}
#[derive(Default)]
struct State {
    targets: BTreeMap<u32, FuncId>,
}
impl<'f> ObservedLocalClosureTargets<'f> {
    /// Execute the actual constructor pass then target-preserving fixed point, including
    /// Select and non-entry block parameters only when all known incoming
    /// targets agree; no
    /// counted prewalk or fresh owner/grant/deadline/TLS/fuel. Fixed-u32 BTree
    /// primitives receive existing core conservative logical prepayment before
    /// actual work/allocation. Full partial map remains owned until transfer or
    /// consuming retirement; physical std/allocator/hard-time bounds stay OPEN.
    pub(super) fn new_observed<O: ExecutionObserver>(
        function: &'f Function,
        session: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> R<Self> {
        let mut work = Work { session, site };
        work.admit(1, size_of::<State>() + size_of::<Work<'_, '_, O>>())?;
        let mut state = State::default();
        let result = state.build(function, &mut work);
        if let Err(error) = result.and_then(|()| work.admit(1, size_of::<Self>())) {
            state.retire(&mut work);
            return Err(work.terminal(error));
        }
        let out = Self {
            _function: function,
            targets: take(&mut state.targets),
        };
        if let Err(error) = work.publication(size_of::<Self>()) {
            out.retire_inner(&mut work);
            return Err(work.terminal(error));
        }
        Ok(out)
    }
    pub(super) fn get_observed<O: ExecutionObserver>(
        &self,
        value: ValueId,
        session: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> R<Option<FuncId>> {
        let mut work = Work { session, site };
        let out = work.read(&self.targets, value.index())?;
        work.publication(size_of::<Option<FuncId>>())?;
        Ok(out)
    }
    /// Consume all actual target rows and empty buffer despite sticky stop.
    /// Borrowed function disposal and caller input ownership remain separate.
    pub(super) fn retire_observed<O: ExecutionObserver>(
        self,
        session: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> R {
        let mut work = Work { session, site };
        self.retire_inner(&mut work);
        work.publication(0)
    }
    fn retire_inner<O: ExecutionObserver>(self, work: &mut Work<'_, '_, O>) {
        work.step(size_of::<Self>() + size_of::<State>() + 1);
        let Self {
            _function: _,
            targets,
        } = self;
        State { targets }.retire(work);
    }
}
impl State {
    fn retire<O: ExecutionObserver>(&mut self, work: &mut Work<'_, '_, O>) {
        loop {
            work.step(
                self.targets
                    .len()
                    .saturating_add(1)
                    .saturating_add(size_of::<Option<(u32, FuncId)>>()),
            );
            if self.targets.pop_first().is_none() {
                break;
            }
            work.poll();
        }
        work.step(size_of::<BTreeMap<u32, FuncId>>() + 1);
        drop(take(&mut self.targets));
        work.poll();
    }
}
