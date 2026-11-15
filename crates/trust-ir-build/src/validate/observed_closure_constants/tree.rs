// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    dead_code,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
impl<'a> State<'a> {
    pub(super) fn tree<O: ExecutionObserver>(
        &mut self,
        module: &'a Module,
        constant: &'a Constant,
        ty: &'a Ty,
        pointer_bits: u32,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        work.admit(1, size_of::<Option<Item<'_>>>())?;
        if self.current.is_some() || self.pending.capacity() != 0 {
            return Err(ObservedValueError::InvalidRange);
        }
        self.current = Some(Item {
            constant,
            ty,
            parent: None,
        });
        loop {
            work.admit(1, size_of::<Item<'_>>())?;
            let current = self.current.ok_or(ObservedValueError::InvalidRange)?;
            if let Some((id, index)) = current.parent
                && !current.constant.value_matches_ty_observed(
                    current.ty,
                    pointer_bits,
                    work.session,
                    work.site,
                )?
            {
                // Actual is_module_checked_pointer_constant is a closed
                // two-tag/at-most-two-child shape check, no name/byte walk.
                // It defers only this local error to the mandatory full
                // module-aware constant validator; it authenticates nothing.
                work.admit(32, 4 * size_of::<usize>())?;
                if !is_module_checked_pointer_constant(current.constant, current.ty) {
                    self.mismatch(current, id, index, work)?;
                }
            }
            work.admit(4, size_of::<(Option<u32>, &[Ty])>())?;
            let (closure_id, types) = match (current.constant, current.ty) {
                (Constant::Closure { captures, .. }, Ty::Closure(id)) => (
                    Some(id.index()),
                    self.single(module, captures, id.index(), work)?,
                ),
                _ => (None, &[][..]),
            };
            work.admit(
                64,
                size_of::<ConstantChildren<'_>>() + size_of::<Option<&Constant>>(),
            )?;
            let mut children = current.constant.children();
            if let Some(first) = children.next() {
                work.admit(4, size_of::<&Ty>() + size_of::<Option<(u32, usize)>>())?;
                let ty = types.first().unwrap_or(&Ty::Unit);
                if children.len() != 0 {
                    work.reserve(&mut self.pending)?;
                    work.admit(1, size_of::<Frame<'_>>())?;
                    self.pending.push(Frame {
                        children,
                        types,
                        closure_id,
                        index: 1,
                    });
                }
                self.current = Some(Item {
                    constant: first,
                    ty,
                    parent: closure_id.filter(|_| !types.is_empty()).map(|id| (id, 0)),
                });
                continue;
            }
            loop {
                work.admit(1, size_of::<Option<&mut Frame<'_>>>())?;
                let Some(frame) = self.pending.last_mut() else {
                    return Ok(());
                };
                work.admit(
                    8,
                    size_of::<Option<&Constant>>() + size_of::<Option<Item<'_>>>(),
                )?;
                if let Some(next) = frame.children.next() {
                    let ty = frame.types.get(frame.index).unwrap_or(&Ty::Unit);
                    let parent = frame
                        .closure_id
                        .filter(|_| frame.index < frame.types.len())
                        .map(|id| (id, frame.index));
                    work.admit(1, size_of::<usize>())?;
                    frame.index = frame
                        .index
                        .checked_add(1)
                        .ok_or(ObservedValueError::CapacityOverflow)?;
                    self.current = Some(Item {
                        constant: next,
                        ty,
                        parent,
                    });
                    break;
                }
                work.admit(1, size_of::<Option<Frame<'_>>>())?;
                work.retire(self.pending.pop());
                work.admit(1, 0)?;
            }
        }
    }
}
