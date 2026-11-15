// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Actual tag-read, switch-case and dominating-edge guards under one owner.
#![allow(
    dead_code,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
use core::mem::{size_of, take};
use trust_ir::InstrNode;
use trust_ir::analysis::DominatorTree;
use trust_ir::interpret::{
    ExecutionObserver, ExecutionPhase, ExecutionProgress, ExecutionSite, ObservedSession,
    ObservedValueError,
};
mod build;
mod query;
mod storage;
#[cfg(test)]
mod tests;
use storage::Work;
type R<T = ()> = Result<T, ObservedValueError>;
type Edge = (BlockId, usize, u32, i128);
#[derive(Default)]
struct State {
    tree: Option<DominatorTree>,
    tags: Vec<(u32, u32)>,
    edges: Vec<Edge>,
}
/// Private data for the exact borrowed function, not a validation capability.
/// The full module caller must preserve the original handle census, present
/// nominal summary, and observed non-tag-read predicate before construction.
/// Duplicate tag SSA definitions retain the original LAST-definition behavior;
/// their legality is still the mandatory validator's separate responsibility.
/// All actual dominator construction/query/retirement uses the supplied original
/// session/site. No resource failure becomes an absent guard or empty result.
/// Successful input/output disposal and physical allocator/stdlib/hard bounds
/// remain separate; this constituent grants no type/source/proof authority.
pub(super) struct ObservedHandleEnumGuards<'f> {
    _function: &'f Function,
    dominators: DominatorTree,
    edges: Vec<Edge>,
}
impl<'f> ObservedHandleEnumGuards<'f> {
    pub(super) fn function_reads_a_non_tag_lane_observed<O: ExecutionObserver>(
        function: &Function,
        session: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> R<bool> {
        let mut work = Work { session, site };
        work.admit(1, size_of::<Work<'_, '_, O>>() + size_of::<bool>())?;
        let result = build::reads(function, &mut work);
        match result {
            Ok(value) => {
                work.publication(size_of::<bool>())?;
                Ok(value)
            }
            Err(error) => Err(work.terminal(error)),
        }
    }
    pub(super) fn new_observed<O: ExecutionObserver>(
        function: &'f Function,
        session: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> R<Self> {
        let mut work = Work { session, site };
        work.admit(1, size_of::<State>() + size_of::<Work<'_, '_, O>>())?;
        let mut state = State::default();
        let result = state.build(function, &mut work);
        work.rows(take(&mut state.tags));
        if let Err(error) = result.and_then(|()| work.admit(1, size_of::<Self>())) {
            state.retire(&mut work);
            return Err(work.terminal(error));
        }
        let Some(dominators) = state.tree.take() else {
            state.retire(&mut work);
            return Err(work.terminal(ObservedValueError::InvalidRange));
        };
        // The complete child was already held in State before scratch retirement.
        // This complete output now remains owned across its last fallible step.
        let output = Self {
            _function: function,
            dominators,
            edges: take(&mut state.edges),
        };
        if let Err(error) = work.publication(size_of::<Self>()) {
            output.retire_inner(&mut work);
            return Err(work.terminal(error));
        }
        Ok(output)
    }
    pub(super) fn variants_selected_at_observed<O: ExecutionObserver>(
        &self,
        block: BlockId,
        aggregate: u32,
        discriminants: &[i128],
        session: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> R<Vec<usize>> {
        let mut work = Work { session, site };
        work.admit(1, size_of::<Vec<usize>>() + size_of::<Work<'_, '_, O>>())?;
        let mut output = Vec::new();
        let result = query::selected(
            self,
            block,
            aggregate,
            discriminants,
            &mut output,
            &mut work,
        );
        match result.and_then(|()| work.publication(size_of::<Vec<usize>>())) {
            Ok(()) => Ok(output),
            Err(error) => {
                work.rows(output);
                Err(work.terminal(error))
            }
        }
    }
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
        work.step(size_of::<Self>() + 1);
        let _ = self.dominators.retire_observed(work.session, work.site);
        work.rows(self.edges);
    }
}
/// Complete Copy result disposal, still under its original owner/site.
pub(super) fn retire_selected_variants_observed<O: ExecutionObserver>(
    selected: Vec<usize>,
    session: &mut ObservedSession<'_, O>,
    site: ExecutionSite,
) -> R {
    let mut work = Work { session, site };
    work.rows(selected);
    work.publication(0)
}
impl State {
    fn retire<O: ExecutionObserver>(&mut self, work: &mut Work<'_, '_, O>) {
        work.step(size_of::<Option<DominatorTree>>() + 1);
        if let Some(tree) = self.tree.take() {
            let _ = tree.retire_observed(work.session, work.site);
        }
        work.poll();
        work.rows(take(&mut self.tags));
        work.rows(take(&mut self.edges));
    }
}
