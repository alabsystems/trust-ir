// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;

impl State {
    pub(super) fn walk<O: ExecutionObserver>(
        &mut self,
        function: &Function,
        context: Context<'_>,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        let mut block_index = 0;
        loop {
            work.admit(1, 0)?;
            let Some(block) = function.blocks.get(block_index) else {
                break;
            };
            let mut param_index = 0;
            loop {
                work.admit(1, 0)?;
                let Some((id, ty)) = block.params.get(param_index) else {
                    break;
                };
                self.pending = Some(ty.clone_observed(work.session, work.site)?);
                self.commit(id.index(), work)?;
                param_index = param_index
                    .checked_add(1)
                    .ok_or(ObservedValueError::CapacityOverflow)?;
            }
            let mut node_index = 0;
            loop {
                work.admit(1, 0)?;
                let Some(node) = block.body.get(node_index) else {
                    break;
                };
                work.admit(67, 4 * size_of::<plan::Plan<'_>>())?;
                let plan = plan::for_instruction(&node.inst, context, work)?;
                let result = self.results(node, plan, work);
                work.retire(plan);
                result?;
                work.admit(1, 0)?;
                node_index = node_index
                    .checked_add(1)
                    .ok_or(ObservedValueError::CapacityOverflow)?;
            }
            block_index = block_index
                .checked_add(1)
                .ok_or(ObservedValueError::CapacityOverflow)?;
        }
        // The concrete child resolves every chain against this complete phase-
        // one snapshot. Retain the whole owned result before any later step.
        work.admit(1, size_of::<Vec<(ValueId, Ty)>>())?;
        self.borrows = trust_ir::bridge::borrow_result_types_observed(
            function,
            &self.output.rows,
            work.session,
            work.site,
        )?;
        while !self.borrows.is_empty() {
            work.admit(1, size_of::<Option<(ValueId, Ty)>>())?;
            if let Some((value, ty)) = self.borrows.pop() {
                self.pending = Some(ty);
                self.commit(value.index(), work)?;
            }
        }
        Ok(())
    }

    fn results<O: ExecutionObserver>(
        &mut self,
        node: &trust_ir::InstrNode,
        plan: plan::Plan<'_>,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        let mut index = 0;
        loop {
            work.admit(1, 0)?;
            let Some(value) = node.results.get(index) else {
                break;
            };
            let Some(atom) = plan.at(index, work)? else {
                break;
            };
            self.pending = Some(atom.clone_type(work)?);
            self.commit(value.index(), work)?;
            index = index
                .checked_add(1)
                .ok_or(ObservedValueError::CapacityOverflow)?;
        }
        Ok(())
    }
}
