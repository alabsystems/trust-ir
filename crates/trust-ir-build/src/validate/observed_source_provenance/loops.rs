// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
impl<'f> State<'f> {
    pub(super) fn backedge<O: ExecutionObserver>(
        &mut self,
        function: &'f Function,
        header: BlockId,
        work: &mut Work<'_, '_, O>,
    ) -> R<bool> {
        let mut index = 0usize;
        loop {
            work.admit(1, size_of::<&trust_ir::Block>())?;
            let Some(latch) = function.blocks.get(index) else {
                return Ok(false);
            };
            work.admit(67, size_of::<Option<&trust_ir::InstrNode>>())?;
            if let Some(term) = latch.terminator() {
                if self.edges.capacity() != 0 {
                    return Err(ObservedValueError::InvalidRange);
                }
                self.edges = term
                    .inst
                    .successor_edges_observed(work.session, work.site)?;
                let mut edge = 0usize;
                let mut reaches = false;
                loop {
                    work.admit(2, size_of::<Option<&trust_ir::Edge<'_>>>())?;
                    let actual = if matches!(term.inst, Inst::Switch { .. }) {
                        if edge == 0 {
                            self.edges.len().checked_sub(1)
                        } else {
                            Some(edge - 1)
                        }
                    } else {
                        Some(edge)
                    };
                    let Some(candidate) = actual.and_then(|actual| self.edges.get(actual)) else {
                        break;
                    };
                    if candidate.target == header {
                        reaches = true;
                        break;
                    }
                    edge = edge
                        .checked_add(1)
                        .ok_or(ObservedValueError::CapacityOverflow)?;
                    if edge >= self.edges.len() {
                        break;
                    }
                }
                self.retire_edges(work);
                work.admit(1, 0)?;
                if reaches
                    && (latch.id == header
                        || self
                            .dominators
                            .as_ref()
                            .ok_or(ObservedValueError::InvalidRange)?
                            .strictly_dominates_observed(
                                header,
                                latch.id,
                                work.session,
                                work.site,
                            )?)
                {
                    return Ok(true);
                }
            }
            index = index
                .checked_add(1)
                .ok_or(ObservedValueError::CapacityOverflow)?;
        }
    }
}
