// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
impl Checking {
    pub(super) fn collect<O: ExecutionObserver>(
        &mut self,
        function: &Function,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        for block in &function.blocks {
            work.admit(1, 0)?;
            for (value, _) in &block.params {
                work.admit(1, 0)?;
                self.define(value.index(), block.id, None, work)?;
            }
            for (index, node) in block.body.iter().enumerate() {
                work.admit(1, 0)?;
                for value in &node.results {
                    work.admit(1, 0)?;
                    self.define(value.index(), block.id, Some(index), work)?;
                }
            }
        }
        Ok(())
    }
    pub(super) fn uses<O: ExecutionObserver>(
        &mut self,
        function: &Function,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        for block in &function.blocks {
            work.admit(1, 0)?;
            let tree = self
                .dominators
                .as_ref()
                .ok_or(ObservedValueError::InvalidRange)?;
            let reachable = tree.is_reachable_observed(block.id, work.session, work.site)?;
            for (index, node) in block.body.iter().enumerate() {
                work.admit(1, 0)?;
                let before = SsaUseSite::BeforeInstruction {
                    block: block.id,
                    instruction: index,
                };
                match &node.inst {
                    Inst::Invoke {
                        args, normal_args, ..
                    } => {
                        self.invocation(None, args, normal_args, before, reachable, work)?;
                    }
                    Inst::InvokeIndirect {
                        callee,
                        args,
                        normal_args,
                        ..
                    } => {
                        self.invocation(Some(*callee), args, normal_args, before, reachable, work)?;
                    }
                    _ => {
                        // Keep the fully owned fixed-ID output immediately.
                        self.operands =
                            node.inst.value_operands_observed(work.session, work.site)?;
                        for operand in 0..self.operands.len() {
                            work.admit(1, size_of::<ValueId>())?;
                            self.check(self.operands[operand], before, reachable, work)?;
                        }
                        work.retire_vec(take(&mut self.operands));
                        work.admit(1, 0)?;
                    }
                }
            }
        }
        Ok(())
    }
    fn invocation<O: ExecutionObserver>(
        &mut self,
        callee: Option<ValueId>,
        args: &[ValueId],
        normal: &[ValueId],
        before: SsaUseSite,
        reachable: bool,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        work.admit(1, 0)?;
        if let Some(callee) = callee {
            self.check(callee, before, reachable, work)?;
        }
        for argument in args {
            work.admit(1, 0)?;
            self.check(*argument, before, reachable, work)?;
        }
        let edge = SsaUseSite::InvokeNormalEdge {
            block: before.block(),
        };
        for argument in normal {
            work.admit(1, 0)?;
            self.check(*argument, edge, reachable, work)?;
        }
        Ok(())
    }
}
