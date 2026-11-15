// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    dead_code,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
impl<'a> State<'a> {
    pub(super) fn mentions<O: ExecutionObserver>(
        &mut self,
        root: &'a Constant,
        work: &mut Work<'_, '_, O>,
    ) -> R<bool> {
        let result = self.preorder(root, work);
        self.retire_frames(work);
        result.and_then(|answer| work.publish_value(answer))
    }
    pub(super) fn preorder<O: ExecutionObserver>(
        &mut self,
        root: &'a Constant,
        work: &mut Work<'_, '_, O>,
    ) -> R<bool> {
        work.admit(1, size_of::<&Constant>())?;
        let mut current = root;
        loop {
            work.admit(1, size_of::<bool>())?;
            if matches!(current, Constant::Uninit) {
                return Ok(true);
            }
            // children() is the actual fixed three-family borrowed descriptor,
            // not an owned collection or a recursive library traversal.
            work.admit(18, size_of::<Option<ConstantChildren<'_>>>())?;
            if self.pending.is_some() {
                return Err(ObservedValueError::InvalidRange);
            }
            self.pending = Some(current.children());
            work.admit(1, size_of::<Option<&Constant>>())?;
            let first = self
                .pending
                .as_mut()
                .ok_or(ObservedValueError::InvalidRange)?
                .next();
            if let Some(first) = first {
                work.admit(1, size_of::<usize>())?;
                if self
                    .pending
                    .as_ref()
                    .ok_or(ObservedValueError::InvalidRange)?
                    .len()
                    != 0
                {
                    work.reserve(&mut self.frames)?;
                    work.admit(
                        1,
                        size_of::<ConstantChildren<'_>>()
                            + size_of::<Option<ConstantChildren<'_>>>(),
                    )?;
                    self.frames.push(
                        self.pending
                            .take()
                            .ok_or(ObservedValueError::InvalidRange)?,
                    );
                } else {
                    work.step(size_of::<Option<ConstantChildren<'_>>>().saturating_add(1));
                    self.pending.take();
                    work.admit(1, 0)?;
                }
                current = first;
                continue;
            }
            work.step(size_of::<Option<ConstantChildren<'_>>>().saturating_add(1));
            self.pending.take();
            work.admit(1, size_of::<Option<&mut ConstantChildren<'_>>>())?;
            let Some(siblings) = self.frames.last_mut() else {
                return Ok(false);
            };
            work.admit(1, size_of::<Option<&Constant>>())?;
            current = siblings.next().ok_or(ObservedValueError::InvalidRange)?;
            work.admit(1, size_of::<usize>())?;
            if siblings.len() == 0 {
                work.step(size_of::<Option<ConstantChildren<'_>>>().saturating_add(1));
                self.frames.pop();
                work.admit(1, 0)?;
            }
        }
    }
    pub(super) fn placed<O: ExecutionObserver>(
        &mut self,
        ty: &Ty,
        value: &'a Constant,
        work: &mut Work<'_, '_, O>,
    ) -> R<bool> {
        work.admit(3, size_of::<bool>())?;
        if let (Ty::Struct(_) | Ty::Tuple(_), Constant::Aggregate(lanes)) = (ty, value) {
            let mut at = 0usize;
            while let Some(lane) = work.at(lanes, at)? {
                work.admit(1, size_of::<bool>())?;
                if !matches!(lane, Constant::Uninit) && self.mentions(lane, work)? {
                    return work.publish_value(false);
                }
                work.next(&mut at)?;
            }
            work.publish_value(true)
        } else {
            let mentions = self.mentions(value, work)?;
            work.publish_value(!mentions)
        }
    }
}
