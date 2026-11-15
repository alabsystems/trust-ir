// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    dead_code,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
impl<'f> State<'f, '_> {
    fn position<O: ExecutionObserver>(
        &self,
        id: ValueId,
        w: &mut Work<'_, '_, O>,
    ) -> R<Option<usize>> {
        let mut at = 0;
        while let Some((key, _, _)) = w.at(&self.definitions, at)? {
            w.admit(4, size_of::<bool>())?;
            if *key == id.index() {
                return Ok(Some(at));
            }
            w.next(&mut at)?;
        }
        Ok(None)
    }
    pub(super) fn unique<O: ExecutionObserver>(
        &self,
        id: ValueId,
        w: &mut Work<'_, '_, O>,
    ) -> R<Option<&'f Inst>> {
        let Some(at) = self.position(id, w)? else {
            return Ok(None);
        };
        w.admit(4, size_of::<Option<&Inst>>())?;
        let (_, count, inst) = w
            .at(&self.definitions, at)?
            .ok_or(ObservedValueError::InvalidRange)?;
        Ok((*count == 1).then_some(*inst))
    }
    pub(super) fn build_definitions<O: ExecutionObserver>(
        &mut self,
        function: &'f Function,
        w: &mut Work<'_, '_, O>,
    ) -> R {
        let mut b = 0;
        while let Some(block) = w.at(&function.blocks, b)? {
            let mut n = 0;
            while let Some(node) = w.at(&block.body, n)? {
                let mut r = 0;
                while let Some(value) = w.at(&node.results, r)? {
                    let at = self.position(*value, w)?;
                    if let Some(at) = at {
                        w.admit(4, size_of::<usize>())?;
                        let entry = self
                            .definitions
                            .get_mut(at)
                            .ok_or(ObservedValueError::InvalidRange)?;
                        entry.1 = entry
                            .1
                            .checked_add(1)
                            .ok_or(ObservedValueError::CapacityOverflow)?;
                    } else {
                        w.reserve(&mut self.definitions)?;
                        w.admit(1, size_of::<(u32, usize, &Inst)>())?;
                        self.definitions.push((value.index(), 1, &node.inst));
                    }
                    w.next(&mut r)?;
                }
                w.next(&mut n)?;
            }
            w.next(&mut b)?;
        }
        Ok(())
    }
}
