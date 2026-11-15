// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
impl State {
    pub(super) fn first_pass<O: ExecutionObserver>(
        &mut self,
        function: &Function,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        let mut block = 0usize;
        loop {
            work.admit(1, size_of::<&Block>())?;
            let Some(current) = function.blocks.get(block) else {
                break;
            };
            let id = current.id.index();
            let mut parameter = 0usize;
            loop {
                work.admit(1, size_of::<&(ValueId, Ty)>())?;
                let Some((_, ty)) = current.params.get(parameter) else {
                    break;
                };
                self.vector(ty, id, work)?;
                parameter = parameter
                    .checked_add(1)
                    .ok_or(ObservedValueError::CapacityOverflow)?;
            }
            let mut node = 0usize;
            loop {
                work.admit(1, size_of::<&trust_ir::InstrNode>())?;
                let Some(current) = current.body.get(node) else {
                    break;
                };
                let mut result = 0usize;
                loop {
                    work.admit(1, size_of::<ValueId>())?;
                    let Some(value) = current.results.get(result) else {
                        break;
                    };
                    let values = self
                        .values
                        .as_ref()
                        .ok_or(ObservedValueError::InvalidRange)?;
                    if let Some(ty) = values.get_observed(*value, work.session, work.site)? {
                        // Keep the borrow in values while the owned helper result
                        // is immediately retained in the disjoint pending field.
                        self.prepare(work)?;
                        self.pending =
                            validate_vector_type_observed(ty, id, work.session, work.site)?;
                        self.append(work)?;
                    }
                    result = result
                        .checked_add(1)
                        .ok_or(ObservedValueError::CapacityOverflow)?;
                }
                work.admit(14, size_of::<(u32, i128)>())?;
                if let Inst::Const {
                    ty,
                    value: Constant::Int(value),
                } = &current.inst
                    && ty.is_integer()
                    && current.results.len() == 1
                {
                    self.constant(current.results[0].index(), *value, work)?;
                }
                node = node
                    .checked_add(1)
                    .ok_or(ObservedValueError::CapacityOverflow)?;
            }
            block = block
                .checked_add(1)
                .ok_or(ObservedValueError::CapacityOverflow)?;
        }
        Ok(())
    }
    fn constant<O: ExecutionObserver>(
        &mut self,
        id: u32,
        value: i128,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        let mut index = 0usize;
        loop {
            work.admit(1, size_of::<(u32, i128)>())?;
            let Some(row) = self.constants.get_mut(index) else {
                break;
            };
            if row.0 == id {
                row.1 = value;
                return Ok(());
            }
            index = index
                .checked_add(1)
                .ok_or(ObservedValueError::CapacityOverflow)?;
        }
        work.reserve(&mut self.constants)?;
        work.admit(1, size_of::<(u32, i128)>())?;
        self.constants.push((id, value));
        Ok(())
    }
    pub(super) fn second_pass<O: ExecutionObserver>(
        &mut self,
        function: &Function,
        context: ValidationContext<'_>,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        let mut block = 0usize;
        loop {
            work.admit(1, size_of::<&Block>())?;
            let Some(current) = function.blocks.get(block) else {
                break;
            };
            let id = current.id.index();
            let mut node = 0usize;
            loop {
                work.admit(1, size_of::<&trust_ir::InstrNode>())?;
                let Some(current) = current.body.get(node) else {
                    break;
                };
                self.instruction(id, &current.inst, context, work)?;
                node = node
                    .checked_add(1)
                    .ok_or(ObservedValueError::CapacityOverflow)?;
            }
            block = block
                .checked_add(1)
                .ok_or(ObservedValueError::CapacityOverflow)?;
        }
        Ok(())
    }
}
