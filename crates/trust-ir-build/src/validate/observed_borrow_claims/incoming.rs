// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
use super::*;
impl<'f> State<'f> {
    pub(super) fn need_incoming<O: ExecutionObserver>(
        &mut self,
        function: &'f Function,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        work.admit(1, size_of::<Option<Vec<Incoming>>>())?;
        if self.incoming.is_some() {
            return Ok(());
        }
        self.incoming = Some(Vec::new());
        let mut i = 0usize;
        loop {
            work.admit(1, size_of::<&trust_ir::Block>())?;
            let Some(block) = function.blocks.get(i) else {
                return Ok(());
            };
            let mut j = 0usize;
            loop {
                work.admit(1, size_of::<&trust_ir::InstrNode>())?;
                let Some(node) = block.body.get(j) else {
                    break;
                };
                work.admit(1, size_of::<Vec<Edge<'_>>>())?;
                self.edges = node
                    .inst
                    .successor_edges_observed(work.session, work.site)?;
                work.admit(1, size_of::<bool>())?;
                let switch = matches!(node.inst, Inst::Switch { .. });
                self.incoming_edges(switch, work)?;
                self.retire_edges(work);
                work.next(&mut j)?;
            }
            work.next(&mut i)?;
        }
    }
    fn incoming_edges<O: ExecutionObserver>(
        &mut self,
        switch: bool,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        work.admit(1, size_of::<usize>())?;
        let mut position = 0usize;
        loop {
            work.admit(1, size_of::<Edge<'_>>() + size_of::<usize>())?;
            if position >= self.edges.len() {
                return Ok(());
            }
            // Index view preserves original default-first Switch order while
            // retaining the actual canonical observed edge Vec until cleanup.
            let index = if switch {
                if position == 0 {
                    self.edges.len() - 1
                } else {
                    position - 1
                }
            } else {
                position
            };
            let edge = self
                .edges
                .get(index)
                .copied()
                .ok_or(ObservedValueError::InvalidRange)?;
            if edge.kind == EdgeKind::Normal {
                self.incoming_arguments(edge, work)?;
            }
            work.next(&mut position)?;
        }
    }
    fn incoming_arguments<O: ExecutionObserver>(
        &mut self,
        edge: Edge<'f>,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        work.admit(1, size_of::<usize>())?;
        let mut index = 0usize;
        loop {
            work.admit(1, size_of::<Incoming>())?;
            let Some(&argument) = edge.args.get(index) else {
                return Ok(());
            };
            // Original incoming stores every normal argument, including extra
            // or absent-target arguments. Only an actual Param asks its key.
            work.push(
                self.incoming
                    .as_mut()
                    .ok_or(ObservedValueError::InvalidRange)?,
                (edge.target.index(), index, argument),
            )?;
            work.next(&mut index)?;
        }
    }
}
