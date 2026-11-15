// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    dead_code,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
impl<O: ExecutionObserver> Work<'_, '_, O> {
    pub(super) fn resolve<'a>(
        &mut self,
        module: &'a Module,
        id: FuncId,
    ) -> R<Option<&'a Function>> {
        self.admit(1, size_of::<Option<&Function>>())?;
        let mut found = None;
        let mut at = 0usize;
        while let Some(function) = self.at(&module.functions, at)? {
            self.admit(2, 2 * size_of::<FuncId>() + size_of::<Option<&Function>>())?;
            if function.id == id {
                if found.is_some() {
                    return self.publish_value(None);
                }
                found = Some(function);
            }
            self.next(&mut at)?;
        }
        self.publish_value(found)
    }
}
/// Every actual parameter/result definition is observed; membership is raw
/// u32 equality. No set/map construction or instruction/type inference is
/// hidden behind this query, including after an early matching definition.
pub(super) fn defined<O: ExecutionObserver>(
    function: &Function,
    value: ValueId,
    work: &mut Work<'_, '_, O>,
) -> R<bool> {
    work.admit(1, size_of::<bool>())?;
    let mut found = false;
    let mut at = 0;
    while let Some(block) = work.at(&function.blocks, at)? {
        let mut index = 0;
        while let Some((id, _)) = work.at(&block.params, index)? {
            work.admit(1, 2 * size_of::<u32>())?;
            found |= id.index() == value.index();
            work.next(&mut index)?;
        }
        let mut index = 0;
        while let Some(node) = work.at(&block.body, index)? {
            let mut result = 0;
            while let Some(id) = work.at(&node.results, result)? {
                work.admit(1, 2 * size_of::<u32>())?;
                found |= id.index() == value.index();
                work.next(&mut result)?;
            }
            work.next(&mut index)?;
        }
        work.next(&mut at)?;
    }
    work.admit(1, size_of::<bool>())?;
    Ok(found)
}
