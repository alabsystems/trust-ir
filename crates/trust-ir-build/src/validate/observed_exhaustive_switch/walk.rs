// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
impl<'f> State<'f> {
    pub(super) fn walk<O: ExecutionObserver>(
        &mut self,
        function: &'f Function,
        pointer_bits: u32,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        let mut index = 0usize;
        loop {
            work.admit(1, size_of::<&trust_ir::Block>())?;
            let Some(block) = function.blocks.get(index) else {
                return Ok(());
            };
            // Block::terminator only tests the actual last node's fixed shape.
            work.admit(67, size_of::<Option<&trust_ir::InstrNode>>())?;
            if let Some(node) = block.terminator()
                && let Inst::Switch {
                    value,
                    default,
                    default_args,
                    cases,
                    exhaustive_enum_unreachable: true,
                } = &node.inst
            {
                let id = block.id.index();
                if !default_args.is_empty() {
                    self.default_arguments(id, default.index(), default_args.len(), work)?;
                }
                let mut target = 0usize;
                loop {
                    work.admit(1, size_of::<&trust_ir::Block>())?;
                    let Some(candidate) = function.blocks.get(target) else {
                        break;
                    };
                    if candidate.id == *default {
                        if !candidate.params.is_empty() {
                            self.default_parameters(
                                id,
                                default.index(),
                                candidate.params.len(),
                                work,
                            )?;
                        }
                        work.admit(2, 0)?;
                        if !matches!(candidate.body.as_slice(),[only] if matches!(only.inst,Inst::Unreachable))
                        {
                            self.default_body(id, default.index(), candidate.body.len(), work)?;
                        }
                        break;
                    }
                    target = target
                        .checked_add(1)
                        .ok_or(ObservedValueError::CapacityOverflow)?;
                }
                if self.values.is_none() {
                    work.admit(1, size_of::<Option<ObservedValueTypes>>())?;
                    self.values = Some(build_function_value_types_observed(
                        function,
                        work.session,
                        work.site,
                    )?);
                }
                let ty = self
                    .values
                    .as_ref()
                    .ok_or(ObservedValueError::InvalidRange)?
                    .get_observed(*value, work.session, work.site)?;
                work.admit(13, size_of::<Option<u32>>())?;
                let width = match ty {
                    Some(ty) if ty.is_integer() || matches!(ty, Ty::Char) => {
                        ty.bit_width_with_observed(pointer_bits, work.session, work.site)?
                    }
                    _ => None,
                };
                self.cases(id, *value, cases, width, work)?;
                self.retire_seen(work);
                work.admit(1, 0)?;
            }
            index = index
                .checked_add(1)
                .ok_or(ObservedValueError::CapacityOverflow)?;
        }
    }
}
