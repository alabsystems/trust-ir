// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
impl<'m> State<'m> {
    pub(super) fn run<O: ExecutionObserver>(
        &mut self,
        module: &'m Module,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        self.table = Some(LayoutTable::new_observed(module, work.session, work.site)?);
        let mut index = 0;
        while let Some(sd) = work.at(&module.structs, index)? {
            work.admit(1, size_of::<StructRepr>())?;
            match sd.repr {
                StructRepr::Transparent => {
                    work.admit(1, size_of::<usize>())?;
                    let mut non_zst = 0usize;
                    let mut field = 0;
                    while let Some(row) = work.at(&sd.fields, field)? {
                        if !self.query(&row.ty, work)? {
                            work.admit(1, size_of::<usize>())?;
                            non_zst = non_zst
                                .checked_add(1)
                                .ok_or(ObservedValueError::CapacityOverflow)?;
                        }
                        work.next(&mut field)?;
                    }
                    work.admit(1, 0)?;
                    if non_zst > 1 {
                        work.reserve(&mut self.errors)?;
                        work.admit(1, size_of::<ValidationError>())?;
                        self.errors
                            .push(ValidationError::TransparentReprFieldCount {
                                struct_id: sd.id.index(),
                                actual_non_zst: non_zst,
                            });
                    }
                }
                StructRepr::Packed(align) => {
                    work.admit(2, size_of::<u32>())?;
                    if align == 0 || !align.is_power_of_two() {
                        work.reserve(&mut self.errors)?;
                        work.admit(1, size_of::<ValidationError>())?;
                        self.errors.push(ValidationError::PackedReprInvalidAlign {
                            struct_id: sd.id.index(),
                            align,
                        });
                    }
                }
                StructRepr::Rust | StructRepr::C => {}
            }
            work.next(&mut index)?;
        }
        Ok(())
    }
}
