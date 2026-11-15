// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Only the original effect address-root trace and entry-parameter rule.
#![allow(
    dead_code,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::{CastOp, EffectPlace, Function, Inst, Root, ValueId};
use core::{
    cmp::Ordering as CmpOrdering,
    mem::{size_of, take},
};
use trust_ir::inst::Edge;
use trust_ir::interpret::{
    ExecutionObserver, ExecutionPhase, ExecutionProgress, ExecutionSite, ObservedSession,
    ObservedValueError,
};
mod canonical;
mod definitions;
mod entry;
mod storage;
#[cfg(test)]
mod tests;
mod trace;
use storage::Work;
type R<T = ()> = Result<T, ObservedValueError>;

/// Borrowed data only, not an observation grant or validated-body capability.
/// Callers use their original session/site for construction, queries and cleanup.
#[derive(Clone, Copy)]
pub(super) struct ObservedBody<'f> {
    function: &'f Function,
    entry: u32,
    entry_params_are_formals: bool,
}
/// Canonical complete set in the exact original Root/EffectPlace Ord order.
/// The private scalar rows are read/retired under the original supplied owner.
#[derive(Default)]
pub(super) struct ObservedRoots {
    rows: Vec<Root>,
}
#[derive(Clone, Copy)]
enum Mark {
    OnPath,
    Done,
}
#[derive(Clone, Copy)]
enum Step {
    Enter(ValueId),
    Exit(ValueId),
}
#[derive(Default)]
struct Trace {
    marks: Vec<(ValueId, Mark)>,
    stack: Vec<Step>,
    output: ObservedRoots,
}
impl ObservedBody<'_> {
    pub(super) fn roots_observed<O: ExecutionObserver>(
        &self,
        address: ValueId,
        session: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> R<ObservedRoots> {
        session.admit(ExecutionProgress {
            phase: ExecutionPhase::Validation,
            site,
            work: 1,
            copy_bytes: size_of::<Trace>() + size_of::<Work<'_, '_, O>>(),
        })?;
        let mut state = Trace::default();
        let mut work = Work { session, site };
        let result = state.walk(self, address, &mut work);
        state.finish(result, &mut work)
    }
    pub(super) fn retire_observed<O: ExecutionObserver>(
        self,
        session: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> R {
        session.retirement_step(site, size_of::<Self>().saturating_add(1));
        // Copy-bound borrowed metadata contains no owned source payload.
        let _ = self;
        Work { session, site }.publication(0, 0)
    }
}
impl ObservedRoots {
    pub(super) fn at_observed<O: ExecutionObserver>(
        &self,
        index: usize,
        session: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> R<Option<Root>> {
        let mut work = Work { session, site };
        work.admit(1, size_of::<Option<Root>>())?;
        let root = self.rows.get(index).copied();
        work.publication(1, size_of::<Option<Root>>())?;
        Ok(root)
    }
    pub(super) fn retire_observed<O: ExecutionObserver>(
        mut self,
        session: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> R {
        let mut work = Work { session, site };
        work.retire_fixed_vec(&mut self.rows);
        work.publication(0, 0)
    }
}
impl Trace {
    fn finish<O: ExecutionObserver>(
        &mut self,
        result: R,
        work: &mut Work<'_, '_, O>,
    ) -> R<ObservedRoots> {
        work.retire_fixed_vec(&mut self.stack);
        work.retire_fixed_vec(&mut self.marks);
        match result.and_then(|()| work.publication(1, size_of::<ObservedRoots>())) {
            Ok(()) => Ok(take(&mut self.output)),
            Err(error) => {
                work.retire_fixed_vec(&mut self.output.rows);
                Err(work.terminal(error))
            }
        }
    }
}
