// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
impl<'f, 'm> State<'f, 'm> {
    pub(super) fn collect<O: ExecutionObserver>(
        &mut self,
        function: &'f Function,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        let mut block_index = 0usize;
        loop {
            work.admit(1, size_of::<&trust_ir::Block>())?;
            let Some(block) = function.blocks.get(block_index) else {
                return Ok(());
            };
            let mut index = 0usize;
            loop {
                work.admit(1, size_of::<DefRow<'_>>())?;
                let Some((value, _)) = block.params.get(index) else {
                    break;
                };
                work.push(
                    &mut self.definitions,
                    (
                        *value,
                        Definition::Parameter {
                            block: block.id.index(),
                            index,
                        },
                    ),
                )?;
                work.next(&mut index)?;
            }
            index = 0;
            loop {
                work.admit(1, size_of::<&trust_ir::InstrNode>())?;
                let Some(node) = block.body.get(index) else {
                    break;
                };
                let mut result = 0usize;
                loop {
                    work.admit(1, size_of::<DefRow<'_>>())?;
                    let Some(value) = node.results.get(result) else {
                        break;
                    };
                    work.push(
                        &mut self.definitions,
                        (*value, Definition::Node(&node.inst)),
                    )?;
                    work.next(&mut result)?;
                }
                work.next(&mut index)?;
            }
            work.next(&mut block_index)?;
        }
    }
}
