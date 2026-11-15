// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
impl<'a> Checking<'a> {
    pub(super) fn walk<O: ExecutionObserver>(
        &mut self,
        function: &'a Function,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        for block in &function.blocks {
            work.admit(1, 0)?;
            // Duplicates do not change membership. Keeping them avoids an
            // unnecessary second index and cannot alter a target verdict.
            work.push(&mut self.blocks, block.id.index())?;
        }
        for block in &function.blocks {
            work.admit(1, 0)?;
            let id = block.id.index();
            // terminator() examines only the final instruction and its fixed
            // exhaustive opcode classification; it performs no body walk.
            if let Some(term) = block.terminator() {
                if let Inst::Switch { cases, .. } = &term.inst {
                    self.switch_keys(id, cases, work)?;
                }
                self.edges = term
                    .inst
                    .successor_edges_observed(work.session, work.site)?;
                // Canonical accessor is cases then default. Preserve this
                // validator's legacy default-first diagnostic/BFS ordering
                // without an opaque rotate over all edge headers.
                if matches!(term.inst, Inst::Switch { .. }) && !self.edges.is_empty() {
                    self.edge(id, self.edges.len() - 1, work)?;
                    for index in 0..self.edges.len() - 1 {
                        self.edge(id, index, work)?;
                    }
                } else {
                    for index in 0..self.edges.len() {
                        self.edge(id, index, work)?;
                    }
                }
                self.retire_edges(work);
                work.admit(1, 0)?;
            }
            self.store_successors(id, work)?;
        }
        self.reach(function, work)
    }
    fn edge<O: ExecutionObserver>(
        &mut self,
        block: u32,
        index: usize,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        work.admit(1, 0)?;
        let target = self
            .edges
            .get(index)
            .ok_or(ObservedValueError::InvalidRange)?
            .target
            .index();
        if !work.contains(&self.blocks, target)? {
            self.fixed(
                || ValidationError::BranchTargetNotFound { block, target },
                work,
            )?;
        }
        work.push(&mut self.targets, target)
    }
    fn reach<O: ExecutionObserver>(
        &mut self,
        function: &Function,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        let entry = function.entry.index();
        if !work.contains(&self.blocks, entry)? {
            return Ok(());
        }
        work.push(&mut self.queue, entry)?;
        work.push(&mut self.reachable, entry)?;
        let mut cursor = 0usize;
        while cursor < self.queue.len() {
            work.admit(1, 0)?;
            let block = self.queue[cursor];
            cursor = cursor
                .checked_add(1)
                .ok_or(ObservedValueError::CapacityOverflow)?;
            for row in &self.successors {
                work.admit(1, 0)?;
                if row.block != block {
                    continue;
                }
                for target in &row.targets {
                    work.admit(1, 0)?;
                    if !work.contains(&self.reachable, *target)? {
                        work.push(&mut self.reachable, *target)?;
                        work.push(&mut self.queue, *target)?;
                    }
                }
                break;
            }
        }
        for block in &function.blocks {
            work.admit(1, 0)?;
            let id = block.id.index();
            if !work.contains(&self.reachable, id)? {
                self.fixed(|| ValidationError::UnreachableBlock(id), work)?;
            }
        }
        Ok(())
    }
}
