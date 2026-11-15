// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    dead_code,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
#[derive(Default)]
pub(super) struct Entry<'f> {
    pub(super) edges: Vec<Edge<'f>>,
}
impl<'f> ObservedBody<'f> {
    pub(in super::super) fn new_observed<O: ExecutionObserver>(
        function: &'f Function,
        session: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> R<Self> {
        session.admit(ExecutionProgress {
            phase: ExecutionPhase::Validation,
            site,
            work: 1,
            copy_bytes: size_of::<Entry<'_>>() + size_of::<Self>() + size_of::<Work<'_, '_, O>>(),
        })?;
        let mut state = Entry::default();
        let mut work = Work { session, site };
        let result = state.inspect(function, &mut work);
        work.retire_fixed_vec(&mut state.edges);
        let formals = result.map_err(|error| work.terminal(error))?;
        work.publication(1, size_of::<Self>())?;
        Ok(Self {
            function,
            entry: function.entry.index(),
            entry_params_are_formals: formals,
        })
    }
}
impl<'f> Entry<'f> {
    pub(super) fn inspect<O: ExecutionObserver>(
        &mut self,
        function: &'f Function,
        work: &mut Work<'_, '_, O>,
    ) -> R<bool> {
        work.admit(1, 3 * size_of::<usize>())?;
        let mut count = 0usize;
        let mut at = 0;
        while let Some(block) = work.at(&function.blocks, at)? {
            work.admit(1, 2 * size_of::<u32>())?;
            if block.id.index() == function.entry.index() {
                work.next(&mut count)?;
            }
            work.next(&mut at)?;
        }
        // The original computes incoming edges even when count != 1.
        let incoming = self.reentered(function, work)?;
        work.admit(2, size_of::<bool>())?;
        Ok(count == 1 && !incoming)
    }
    fn reentered<O: ExecutionObserver>(
        &mut self,
        function: &'f Function,
        work: &mut Work<'_, '_, O>,
    ) -> R<bool> {
        let mut at = 0;
        while let Some(block) = work.at(&function.blocks, at)? {
            let mut node_index = 0;
            while let Some(node) = work.at(&block.body, node_index)? {
                work.admit(1, size_of::<Vec<Edge<'_>>>())?;
                // Full original successor construction, then target-only scan.
                // Returned edge headers are retained before any fallible read.
                self.edges = node
                    .inst
                    .successor_edges_observed(work.session, work.site)?;
                let found = self.targets(function.entry.index(), work)?;
                work.retire_fixed_vec(&mut self.edges);
                work.admit(1, 0)?; // A cleanup stop cannot become a semantic bool.
                if found {
                    return Ok(true);
                }
                work.next(&mut node_index)?;
            }
            work.next(&mut at)?;
        }
        Ok(false)
    }
    fn targets<O: ExecutionObserver>(&self, entry: u32, work: &mut Work<'_, '_, O>) -> R<bool> {
        let mut index = 0;
        while let Some(edge) = work.at(&self.edges, index)? {
            work.admit(1, 2 * size_of::<u32>())?;
            if edge.target.index() == entry {
                return Ok(true);
            }
            work.next(&mut index)?;
        }
        Ok(false)
    }
}
