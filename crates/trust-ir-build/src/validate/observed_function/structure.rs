// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
impl Checking {
    pub(super) fn structure<O: ExecutionObserver>(
        &mut self,
        function: &Function,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        work.admit(2, 0)?;
        if function.blocks.is_empty() {
            if !is_bodyless_external_declaration(function) && function.summary.is_none() {
                self.fixed(|| ValidationError::EmptyFunction, work)?;
            }
            return Ok(());
        }
        let mut entry_found = false;
        for block in &function.blocks {
            work.admit(2, 0)?;
            let block_id = block.id.index();
            if work.contains(&self.blocks, block_id)? {
                self.fixed(|| ValidationError::DuplicateBlockId(block_id), work)?;
            } else {
                work.push(&mut self.blocks, block_id)?;
            }
            if block.id == function.entry {
                entry_found = true;
            }
            // The original method is a fixed last-node discriminant check.
            work.admit(1, 0)?;
            if block.terminator().is_none() {
                self.fixed(|| ValidationError::BlockMissingTerminator(block_id), work)?;
            }
            if let Some(last) = block.body.len().checked_sub(1) {
                for (index, node) in block.body.iter().enumerate() {
                    work.admit(2, 0)?;
                    if index != last && node.is_terminator() {
                        work.admit(1, size_of::<&str>())?;
                        self.detail(
                            instruction_kind(&node.inst),
                            |op| ValidationError::MidBlockTerminator {
                                block: block_id,
                                index,
                                op,
                            },
                            work,
                        )?;
                    }
                }
                work.admit(1, 0)?;
                if !block.body[last].is_terminator() {
                    self.fixed(
                        || ValidationError::MissingTerminator { block: block_id },
                        work,
                    )?;
                }
            }
        }
        if !entry_found {
            self.fixed(
                || ValidationError::EntryBlockNotFound(function.entry.index()),
                work,
            )?;
        }
        Ok(())
    }
}
