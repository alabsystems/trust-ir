// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
impl State {
    pub(super) fn run<O: ExecutionObserver>(
        &mut self,
        module: &Module,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        work.admit(
            2,
            size_of::<trust_ir::StructPassingPolicy>() + size_of::<bool>(),
        )?;
        if !module.target_info.as_ref().is_some_and(|target| {
            target.struct_passing == trust_ir::StructPassingPolicy::AlwaysMemory
        }) {
            return Ok(());
        }
        let mut index = 0;
        while let Some(signature) = work.at(&module.func_types, index)? {
            self.slots(module, &signature.params, index, "parameter ", work)?;
            self.slots(module, &signature.returns, index, "return ", work)?;
            work.next(&mut index)?;
        }
        Ok(())
    }
    fn slots<O: ExecutionObserver>(
        &mut self,
        module: &Module,
        slots: &[Ty],
        signature: usize,
        position: &'static str,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        let mut index = 0;
        while let Some(ty) = work.at(slots, index)? {
            if module.is_by_value_aggregate_slot_observed(ty, work.session, work.site)? {
                work.admit(2, 0)?;
                if self.slot.capacity() != 0 || self.tytext.is_some() {
                    return Err(ObservedValueError::InvalidRange);
                }
                work.text(position, &mut self.slot)?;
                work.number(index as u128, &mut self.slot)?;
                self.tytext = Some(ty.display_observed(work.session, work.site)?);
                work.reserve(&mut self.errors)?;
                work.admit(2, size_of::<ValidationError>() + size_of::<u32>())?;
                let ty = self.tytext.take().ok_or(ObservedValueError::InvalidRange)?;
                self.errors
                    .push(ValidationError::AlwaysMemoryByValueAggregate {
                        func_ty: u32::try_from(signature).unwrap_or(u32::MAX),
                        slot: take(&mut self.slot),
                        ty,
                    });
            }
            work.next(&mut index)?;
        }
        Ok(())
    }
}
