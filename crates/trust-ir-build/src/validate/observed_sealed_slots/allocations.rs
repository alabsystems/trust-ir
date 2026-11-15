// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    dead_code,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
impl State {
    pub(super) fn allocations<O: ExecutionObserver>(
        &mut self,
        layouts: &trust_ir::LayoutTable<'_>,
        function: &Function,
        nominal: &trust_ir::ObservedNominalTypeReachability<'_>,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        let mut b = 0;
        while let Some(block) = work.at(&function.blocks, b)? {
            let mut n = 0;
            while let Some(node) = work.at(&block.body, n)? {
                work.admit(1, size_of::<&Inst>())?;
                if let Inst::Alloca { ty, count, align } = &node.inst
                    && nominal.contains_handle_observed(ty, work.session, work.site)?
                {
                    work.admit(1, size_of::<usize>() + size_of::<u32>())?;
                    if let [result] = node.results.as_slice() {
                        self.allocate(
                            layouts,
                            nominal,
                            ty,
                            count.is_some(),
                            *align,
                            result.index(),
                            (block.id, n),
                            work,
                        )?;
                    }
                }
                work.next(&mut n)?;
            }
            work.next(&mut b)?;
        }
        Ok(())
    }
    fn allocate<O: ExecutionObserver>(
        &mut self,
        layouts: &trust_ir::LayoutTable<'_>,
        nominal: &trust_ir::ObservedNominalTypeReachability<'_>,
        ty: &Ty,
        count: bool,
        align: Option<u64>,
        key: u32,
        at: Point,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        work.admit(
            1,
            size_of::<Option<String>>() + size_of::<Option<Ty>>() + size_of::<Option<Slot>>(),
        )?;
        if self.pending_unsealed.is_some()
            || self.pending_natural.is_some()
            || self.pending_type.is_some()
            || self.pending_slot.is_some()
            || self.old_slot.is_some()
        {
            return Err(ObservedValueError::InvalidRange);
        }
        match slot_shape_observed(layouts, nominal, ty, count, align, work.session, work.site)? {
            Ok(natural) => self.pending_natural = Some(natural),
            Err(reason) => self.pending_unsealed = Some(reason),
        }
        self.pending_type = Some(ty.clone_observed(work.session, work.site)?);
        work.admit(
            1,
            size_of::<Slot>() + size_of::<Option<Ty>>() + size_of::<Option<String>>(),
        )?;
        let owned = self
            .pending_type
            .take()
            .ok_or(ObservedValueError::InvalidRange)?;
        self.pending_slot = Some(Slot {
            ty: owned,
            site: at,
            natural_align: self.pending_natural.take(),
            unsealed: self.pending_unsealed.take(),
            stores: Vec::new(),
        });
        // Failable prepayment happens BEFORE taking the complete owning Slot.
        work.insertion::<Slot>(self.slots.len())?;
        work.admit(1, size_of::<Option<Slot>>())?;
        let slot = self
            .pending_slot
            .take()
            .ok_or(ObservedValueError::InvalidRange)?;
        self.old_slot = self.slots.insert(key, slot);
        // A replaced value remains whole until explicit original-owner cleanup.
        self.retire_old_slot(work);
        work.admit(1, 0)?;
        let _ = work.insert_copy(&mut self.members, key, (key, at))?;
        Ok(())
    }
}
