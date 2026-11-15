// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    dead_code,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
impl<O: ExecutionObserver> Work<'_, '_, O> {
    pub(super) fn resolve<'m>(&mut self, module: &'m Module, id: FuncId) -> R<Resolution<'m>> {
        self.admit(1, size_of::<Option<&Function>>() + size_of::<usize>())?;
        let mut found = None;
        let mut index = 0usize;
        while let Some(function) = self.at(&module.functions, index)? {
            self.admit(2, 2 * size_of::<FuncId>() + size_of::<Option<&Function>>())?;
            if function.id == id {
                if found.is_some() {
                    return self.publish_value(Resolution::Ambiguous);
                }
                found = Some(function);
            }
            self.next(&mut index)?;
        }
        self.publish_value(match found {
            Some(function) => Resolution::Unique(function),
            None => Resolution::Missing,
        })
    }
    pub(super) fn block<'f>(
        &mut self,
        function: &'f Function,
        id: BlockId,
    ) -> R<Option<&'f trust_ir::Block>> {
        let mut index = 0usize;
        while let Some(block) = self.at(&function.blocks, index)? {
            self.admit(1, 2 * size_of::<BlockId>())?;
            if block.id == id {
                return self.publish_value(Some(block));
            }
            self.next(&mut index)?;
        }
        self.publish_value(None)
    }
}
