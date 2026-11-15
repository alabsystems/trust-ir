// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
use super::*;
impl<'f> State<'f> {
    pub(super) fn need_definitions<O: ExecutionObserver>(
        &mut self,
        function: &'f Function,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        work.admit(1, size_of::<Option<Vec<DefRow<'_>>>>())?;
        if self.definitions.is_some() {
            return Ok(());
        }
        // Retain even partially built borrowed rows before any later stop.
        self.definitions = Some(Vec::new());
        let mut i = 0usize;
        loop {
            work.admit(1, size_of::<&trust_ir::Block>())?;
            let Some(block) = function.blocks.get(i) else {
                return Ok(());
            };
            let mut j = 0usize;
            loop {
                work.admit(1, size_of::<DefRow<'_>>())?;
                let Some((value, _)) = block.params.get(j) else {
                    break;
                };
                self.definition(
                    *value,
                    Definition::Parameter {
                        block: block.id.index(),
                        index: j,
                    },
                    work,
                )?;
                work.next(&mut j)?;
            }
            j = 0;
            loop {
                work.admit(1, size_of::<&trust_ir::InstrNode>())?;
                let Some(node) = block.body.get(j) else {
                    break;
                };
                let mut k = 0usize;
                loop {
                    work.admit(1, size_of::<DefRow<'_>>())?;
                    let Some(value) = node.results.get(k) else {
                        break;
                    };
                    self.definition(*value, Definition::Node(&node.inst), work)?;
                    work.next(&mut k)?;
                }
                work.next(&mut j)?;
            }
            work.next(&mut i)?;
        }
    }
    fn definition<O: ExecutionObserver>(
        &mut self,
        value: ValueId,
        definition: Definition<'f>,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        work.push(
            self.definitions
                .as_mut()
                .ok_or(ObservedValueError::InvalidRange)?,
            (value, definition),
        )
    }
    pub(super) fn is_borrow_result<O: ExecutionObserver>(
        &self,
        value: ValueId,
        work: &mut Work<'_, '_, O>,
    ) -> R<bool> {
        work.admit(1, size_of::<bool>() + size_of::<usize>())?;
        let mut found = false;
        let mut index = 0usize;
        loop {
            work.admit(3, size_of::<DefRow<'_>>())?;
            let Some(&(candidate, definition)) = self
                .definitions
                .as_ref()
                .ok_or(ObservedValueError::InvalidRange)?
                .get(index)
            else {
                return Ok(found);
            };
            if candidate == value {
                found = true;
                if !matches!(
                    definition,
                    Definition::Node(Inst::Borrow { .. } | Inst::BorrowMut { .. })
                ) {
                    return Ok(false);
                }
            }
            work.next(&mut index)?;
        }
    }
}
