// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    dead_code,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
impl<'m> State<'m> {
    fn definition<O: ExecutionObserver>(
        &self,
        value: ValueId,
        work: &mut Work<'_, '_, O>,
    ) -> R<Option<usize>> {
        let mut at = 0;
        while let Some((id, _)) = work.at(&self.definitions, at)? {
            work.admit(8, size_of::<bool>())?;
            if *id == value.index() {
                return Ok(Some(at));
            }
            work.next(&mut at)?;
        }
        Ok(None)
    }
    pub(super) fn build_definitions<O: ExecutionObserver>(
        &mut self,
        function: &'m Function,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        let mut b = 0;
        while let Some(block) = work.at(&function.blocks, b)? {
            let mut n = 0;
            while let Some(node) = work.at(&block.body, n)? {
                work.admit(8, size_of::<Option<ValueId>>())?;
                if let [value] = node.results.as_slice() {
                    let at = self.definition(*value, work)?;
                    if at.is_none() {
                        work.reserve(&mut self.definitions)?;
                    }
                    work.admit(3, 3 * size_of::<(u32, &Inst)>())?;
                    match at {
                        Some(at) => {
                            self.definitions
                                .get_mut(at)
                                .ok_or(ObservedValueError::InvalidRange)?
                                .1 = &node.inst
                        }
                        None => self.definitions.push((value.index(), &node.inst)),
                    }
                }
                work.next(&mut n)?;
            }
            work.next(&mut b)?;
        }
        Ok(())
    }
    pub(super) fn origin<O: ExecutionObserver>(
        &self,
        module: &'m Module,
        mut value: ValueId,
        work: &mut Work<'_, '_, O>,
    ) -> R<Option<&'m Function>> {
        work.admit(4, 2 * size_of::<usize>() + size_of::<ValueId>())?;
        let count = self
            .definitions
            .len()
            .checked_add(1)
            .ok_or(ObservedValueError::CapacityOverflow)?;
        let mut at = 0;
        while at < count {
            work.admit(8, size_of::<Option<&Inst>>())?;
            let Some(index) = self.definition(value, work)? else {
                return Ok(None);
            };
            let (_, inst) = work
                .at(&self.definitions, index)?
                .ok_or(ObservedValueError::InvalidRange)?;
            match inst {
                Inst::Copy { operand, .. } => value = *operand,
                Inst::Const {
                    value: Constant::SymbolAddr { symbol, .. },
                    ..
                } => return queries::last(module, symbol, work),
                _ => return Ok(None),
            }
            work.next(&mut at)?;
        }
        Ok(None)
    }
}
