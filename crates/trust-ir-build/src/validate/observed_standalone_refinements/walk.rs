// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;

impl<'a> Checking<'a> {
    pub(super) fn walk<O: ExecutionObserver>(
        &mut self,
        function: &'a Function,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        work.admit(1, 0)?;
        let mut block_index = 0;
        while block_index < function.blocks.len() {
            work.admit(1, 0)?;
            let block = &function.blocks[block_index];
            let mut index = 0;
            while index < block.params.len() {
                work.admit(1, 0)?;
                if self.contains(&block.params[index].1, work)? {
                    self.diagnostic(
                        &function.name,
                        block.id.index(),
                        Surface::Parameter(index),
                        work,
                    )?;
                }
                index += 1;
            }
            index = 0;
            while index < block.body.len() {
                work.admit(1, size_of::<Vec<&Ty>>())?;
                // The returned borrowed-reference vector is owned immediately.
                self.types = block.body[index]
                    .inst
                    .inline_types_observed(work.session, work.site)?;
                let mut found = false;
                let mut type_index = 0;
                while type_index < self.types.len() {
                    work.admit(1, size_of::<&Ty>())?;
                    // Ordinary found |= predicate(ty) evaluates every inline
                    // type, even after a prior type contains a refinement.
                    found |= self.contains(self.types[type_index], work)?;
                    type_index += 1;
                }
                work.retire_refs(&mut self.types);
                work.admit(1, 0)?;
                if found {
                    self.diagnostic(
                        &function.name,
                        block.id.index(),
                        Surface::Instruction(index),
                        work,
                    )?;
                }
                index += 1;
            }
            block_index += 1;
        }
        Ok(())
    }
}
