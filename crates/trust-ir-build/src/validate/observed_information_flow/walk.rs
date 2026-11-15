// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

use super::*;

enum Marker {
    Seed,
    Sink,
}

fn has_marker<O: ExecutionObserver>(
    proofs: &[ProofAnnotation],
    marker: Marker,
    work: &mut Work<'_, '_, O>,
) -> R<bool> {
    work.admit(1, 0)?;
    let mut index = 0;
    while index < proofs.len() {
        work.admit(1, 0)?;
        let found = match marker {
            Marker::Seed => matches!(&proofs[index], ProofAnnotation::Tainted),
            Marker::Sink => matches!(&proofs[index], ProofAnnotation::TrustedSink),
        };
        if found {
            return Ok(true);
        }
        index += 1;
    }
    Ok(false)
}

impl Checking {
    pub(super) fn walk<O: ExecutionObserver>(
        &mut self,
        function: &Function,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        self.seed(function, work)?;
        let mut changed = true;
        while changed {
            work.admit(1, 0)?;
            changed = self.propagate(function, work)?;
        }
        self.sinks(function, work)
    }

    fn seed<O: ExecutionObserver>(&mut self, function: &Function, work: &mut Work<'_, '_, O>) -> R {
        work.admit(1, 0)?;
        let mut block_index = 0;
        while block_index < function.blocks.len() {
            work.admit(1, 0)?;
            let block = &function.blocks[block_index];
            let mut node_index = 0;
            while node_index < block.body.len() {
                work.admit(1, 0)?;
                let node = &block.body[node_index];
                if has_marker(&node.proofs, Marker::Seed, work)? {
                    let mut result_index = 0;
                    while result_index < node.results.len() {
                        work.admit(1, 0)?;
                        work.insert(&mut self.tainted, node.results[result_index].index())?;
                        result_index += 1;
                    }
                }
                node_index += 1;
            }
            block_index += 1;
        }
        Ok(())
    }

    fn collect<O: ExecutionObserver>(
        &mut self,
        instruction: &Inst,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        // Previous vectors were explicitly drained, including their buffers.
        // The returned vector is retained immediately, before any fallible step.
        work.admit(1, size_of::<Vec<ValueId>>())?;
        self.operands = instruction.value_operands_observed(work.session, work.site)?;
        Ok(())
    }

    fn propagate<O: ExecutionObserver>(
        &mut self,
        function: &Function,
        work: &mut Work<'_, '_, O>,
    ) -> R<bool> {
        work.admit(1, 0)?;
        let mut changed = false;
        let mut block_index = 0;
        while block_index < function.blocks.len() {
            work.admit(1, 0)?;
            let block = &function.blocks[block_index];
            let mut node_index = 0;
            while node_index < block.body.len() {
                work.admit(1, 0)?;
                let node = &block.body[node_index];
                self.collect(&node.inst, work)?;
                let mut consumes_tainted = false;
                let mut operand_index = 0;
                while operand_index < self.operands.len() {
                    work.admit(1, 0)?;
                    if work.contains(&self.tainted, self.operands[operand_index].index())? {
                        consumes_tainted = true;
                        break;
                    }
                    operand_index += 1;
                }
                work.retire_ids(&mut self.operands);
                // A first refusal during successful scratch retirement is also
                // terminal, before any further result/node work.
                work.admit(1, 0)?;
                if consumes_tainted {
                    let mut result_index = 0;
                    while result_index < node.results.len() {
                        work.admit(1, 0)?;
                        if work.insert(&mut self.tainted, node.results[result_index].index())? {
                            changed = true;
                        }
                        result_index += 1;
                    }
                }
                node_index += 1;
            }
            block_index += 1;
        }
        Ok(changed)
    }

    fn sinks<O: ExecutionObserver>(
        &mut self,
        function: &Function,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        work.admit(1, 0)?;
        let mut block_index = 0;
        while block_index < function.blocks.len() {
            work.admit(1, 0)?;
            let block = &function.blocks[block_index];
            let mut node_index = 0;
            while node_index < block.body.len() {
                work.admit(1, 0)?;
                let node = &block.body[node_index];
                if has_marker(&node.proofs, Marker::Sink, work)? {
                    self.collect(&node.inst, work)?;
                    let mut operand_index = 0;
                    while operand_index < self.operands.len() {
                        work.admit(1, 0)?;
                        let value = self.operands[operand_index].index();
                        if work.contains(&self.tainted, value)? {
                            self.diagnostic(block.id.index(), value, work)?;
                        }
                        operand_index += 1;
                    }
                    work.retire_ids(&mut self.operands);
                    work.admit(1, 0)?;
                }
                node_index += 1;
            }
            block_index += 1;
        }
        Ok(())
    }
}
