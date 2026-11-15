// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
use super::*;
impl<'f> State<'f> {
    pub(super) fn borrows<O: ExecutionObserver>(
        &mut self,
        function: &'f Function,
        types: &ObservedValueTypes,
        work: &mut Work<'_, '_, O>,
    ) -> R {
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
                work.admit(2, size_of::<ValueId>())?;
                match &node.inst {
                    Inst::BorrowMut { ptr } => {
                        let ty = types.get_observed(*ptr, work.session, work.site)?;
                        work.admit(2, size_of::<bool>())?;
                        let shared = matches!(ty, Some(Ty::Ref(_) | Ty::PtrConst(_)));
                        self.need_definitions(function, work)?;
                        // Original builds both lazy structures even when the
                        // static shared type short-circuits the root query.
                        self.need_incoming(function, work)?;
                        if shared || self.shared_root(*ptr, work)? {
                            self.issue(block.id.index(), Issue::Shared, work)?;
                        }
                    }
                    Inst::EndBorrow { borrow_ptr } => {
                        self.need_definitions(function, work)?;
                        if !self.is_borrow_result(*borrow_ptr, work)? {
                            self.issue(block.id.index(), Issue::End, work)?;
                        }
                    }
                    _ => {}
                }
                work.next(&mut j)?;
            }
            work.next(&mut i)?;
        }
    }
    pub(super) fn references<O: ExecutionObserver>(
        &mut self,
        function: &Function,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        work.admit(1, 0)?;
        if !matches!(function.producer, Some(trust_ir::Producer::TRust)) {
            return Ok(());
        }
        let mut i = 0usize;
        loop {
            work.admit(1, size_of::<&trust_ir::Block>())?;
            let Some(block) = function.blocks.get(i) else {
                return Ok(());
            };
            let mut j = 0usize;
            loop {
                work.admit(67, size_of::<&trust_ir::InstrNode>())?;
                let Some(node) = block.body.get(j) else {
                    break;
                };
                // Actual fixed InstShape table, no variable payload predicate.
                if node.inst.uses_borrow_permissions() {
                    self.reference(&function.name, block.id.index(), j, work)?;
                }
                work.next(&mut j)?;
            }
            work.next(&mut i)?;
        }
    }
    fn issue<O: ExecutionObserver>(
        &mut self,
        block: u32,
        issue: Issue,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        work.reserve(&mut self.errors)?;
        work.admit(1, size_of::<ValidationError>())?;
        self.errors.push(match issue {
            Issue::Shared => ValidationError::BorrowMutThroughSharedRef { block },
            Issue::End => ValidationError::EndBorrowOfNonBorrow { block },
        });
        Ok(())
    }
    pub(super) fn reference<O: ExecutionObserver>(
        &mut self,
        name: &str,
        block: u32,
        inst_index: usize,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        work.text(name, &mut self.name)?;
        work.reserve(&mut self.errors)?;
        work.admit(1, size_of::<ValidationError>())?;
        self.errors
            .push(ValidationError::RustReferenceAsPermissionBorrow {
                function: take(&mut self.name),
                block,
                inst_index,
            });
        Ok(())
    }
}
