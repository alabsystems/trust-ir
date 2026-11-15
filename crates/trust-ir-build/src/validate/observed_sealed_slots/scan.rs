// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    dead_code,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
impl State {
    pub(super) fn scan_uses<O: ExecutionObserver>(
        &mut self,
        function: &Function,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        let mut b = 0;
        while let Some(block) = work.at(&function.blocks, b)? {
            let mut n = 0;
            while let Some(node) = work.at(&block.body, n)? {
                work.admit(1, size_of::<Point>())?;
                let at = (block.id, n);
                self.instance_uses(&node.inst, at, work)?;
                work.rows(take(&mut self.operands));
                work.admit(1, 0)?;
                work.admit(1, size_of::<&Inst>())?;
                match &node.inst {
                    Inst::Store { ty, ptr, value, .. } => self.store(ty, *ptr, *value, at, work)?,
                    Inst::Load { ty, ptr, .. } => self.load(ty, *ptr, at, work)?,
                    Inst::Borrow { .. } | Inst::BorrowMut { .. } | Inst::EndBorrow { .. } => {}
                    other => self.escapes(other, at, work)?,
                }
                work.rows(take(&mut self.operands));
                work.admit(1, 0)?;
                self.apply_unsealing(work)?;
                work.next(&mut n)?;
            }
            work.next(&mut b)?;
        }
        Ok(())
    }
    fn instance_uses<O: ExecutionObserver>(
        &mut self,
        inst: &Inst,
        at: Point,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        work.admit(1, size_of::<Vec<ValueId>>())?;
        if self.operands.capacity() != 0 {
            return Err(ObservedValueError::InvalidRange);
        }
        self.operands = inst.value_operands_observed(work.session, work.site)?;
        let mut i = 0;
        while let Some(operand) = work.at(&self.operands, i)? {
            work.admit(1, size_of::<ValueId>())?;
            let operand = *operand;
            if let Some((owner, definition)) = work.read(&self.members, operand.index())? {
                let before = {
                    let tree = self
                        .dominators
                        .as_ref()
                        .ok_or(ObservedValueError::InvalidRange)?;
                    dominance::precedes(tree, definition, at, work)?
                };
                if !before {
                    work.text("its slot pointer %", &mut self.reason)?;
                    work.unsigned(u128::from(operand.index()), &mut self.reason)?;
                    work.text(" is used in bb", &mut self.reason)?;
                    work.unsigned(u128::from(at.0.index()), &mut self.reason)?;
                    work.text(
                        " where its definition does not dominate the use",
                        &mut self.reason,
                    )?;
                    self.queue_unseal(owner, work)?;
                }
            }
            work.next(&mut i)?;
        }
        Ok(())
    }
    fn escapes<O: ExecutionObserver>(
        &mut self,
        inst: &Inst,
        at: Point,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        work.admit(1, size_of::<Vec<ValueId>>())?;
        if self.operands.capacity() != 0 {
            return Err(ObservedValueError::InvalidRange);
        }
        self.operands = inst.value_operands_observed(work.session, work.site)?;
        let mut i = 0;
        while let Some(operand) = work.at(&self.operands, i)? {
            work.admit(1, size_of::<ValueId>())?;
            let operand = *operand;
            if let Some((owner, _)) = work.read(&self.members, operand.index())? {
                work.text("its slot pointer %", &mut self.reason)?;
                work.unsigned(u128::from(operand.index()), &mut self.reason)?;
                work.text(" escapes into `", &mut self.reason)?;
                work.admit(1, size_of::<trust_ir::inst::InstShape>())?;
                work.text(inst.shape().name(), &mut self.reason)?;
                work.text("` in bb", &mut self.reason)?;
                work.unsigned(u128::from(at.0.index()), &mut self.reason)?;
                self.queue_unseal(owner, work)?;
            }
            work.next(&mut i)?;
        }
        Ok(())
    }
    fn store<O: ExecutionObserver>(
        &mut self,
        ty: &Ty,
        ptr: ValueId,
        value: ValueId,
        at: Point,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        if let Some((owner, _)) = work.read(&self.members, value.index())? {
            work.text("its slot pointer %", &mut self.reason)?;
            work.unsigned(u128::from(value.index()), &mut self.reason)?;
            work.text(" is stored AS A VALUE by `Store` in bb", &mut self.reason)?;
            work.unsigned(u128::from(at.0.index()), &mut self.reason)?;
            self.queue_unseal(owner, work)?;
        }
        if let Some((owner, _)) = work.read(&self.members, ptr.index())? {
            let equal = {
                if let Some(slot) = work.slot(&self.slots, owner)? {
                    Some(ty.structural_eq_observed(&slot.ty, work.session, work.site)?)
                } else {
                    None
                }
            };
            match equal {
                Some(true) => {
                    let slot = work
                        .slot_mut(&mut self.slots, owner)?
                        .ok_or(ObservedValueError::InvalidRange)?;
                    work.push_copy(&mut slot.stores, at)?;
                }
                Some(false) => {
                    work.text("`Store` in bb", &mut self.reason)?;
                    work.unsigned(u128::from(at.0.index()), &mut self.reason)?;
                    work.text(" writes it at `", &mut self.reason)?;
                    text_type(ty, &mut self.render, &mut self.reason, work)?;
                    work.text("`, not at the slot's own type `", &mut self.reason)?;
                    let slot = work
                        .slot(&self.slots, owner)?
                        .ok_or(ObservedValueError::InvalidRange)?;
                    text_type(&slot.ty, &mut self.render, &mut self.reason, work)?;
                    work.text("`", &mut self.reason)?;
                    self.queue_unseal(owner, work)?;
                }
                None => {}
            }
        }
        Ok(())
    }
    fn load<O: ExecutionObserver>(
        &mut self,
        ty: &Ty,
        ptr: ValueId,
        at: Point,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        if let Some((owner, _)) = work.read(&self.members, ptr.index())? {
            let mismatch = {
                if let Some(slot) = work.slot(&self.slots, owner)? {
                    !ty.structural_eq_observed(&slot.ty, work.session, work.site)?
                } else {
                    false
                }
            };
            if mismatch {
                work.text("`Load` in bb", &mut self.reason)?;
                work.unsigned(u128::from(at.0.index()), &mut self.reason)?;
                work.text(" reads it at `", &mut self.reason)?;
                text_type(ty, &mut self.render, &mut self.reason, work)?;
                work.text("`, not at the slot's own type `", &mut self.reason)?;
                let slot = work
                    .slot(&self.slots, owner)?
                    .ok_or(ObservedValueError::InvalidRange)?;
                text_type(&slot.ty, &mut self.render, &mut self.reason, work)?;
                work.text("`", &mut self.reason)?;
                self.queue_unseal(owner, work)?;
            }
        }
        Ok(())
    }
}
pub(super) fn text_type<O: ExecutionObserver>(
    ty: &Ty,
    render: &mut String,
    output: &mut String,
    work: &mut Work<'_, '_, O>,
) -> R {
    work.admit(1, size_of::<String>())?;
    if render.capacity() != 0 {
        return Err(ObservedValueError::InvalidRange);
    }
    *render = ty.display_observed(work.session, work.site)?;
    work.text(render, output)?;
    work.flat(take(render));
    work.admit(1, 0)
}
