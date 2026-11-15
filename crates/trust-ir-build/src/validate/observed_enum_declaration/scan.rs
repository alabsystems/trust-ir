// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
impl State {
    pub(super) fn run<O: ExecutionObserver>(
        &mut self,
        module: &Module,
        index: usize,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        let enm = work
            .at(&module.enums, index)?
            .ok_or(ObservedValueError::InvalidRange)?;
        let mut previous = 0;
        while previous < index {
            work.admit(1, 0)?;
            let row = work
                .at(&module.enums, previous)?
                .ok_or(ObservedValueError::InvalidRange)?;
            work.admit(1, 2 * size_of::<u32>())?;
            if row.id == enm.id {
                work.reserve(&mut self.errors)?;
                work.admit(1, size_of::<ValidationError>())?;
                self.errors
                    .push(ValidationError::DuplicateEnumId(enm.id.index()));
                break;
            }
            work.next(&mut previous)?;
        }
        // Retain the actual owning vector before any fallible header/use.
        let assigned = match enm.effective_discriminants_observed(work.session, work.site)? {
            Some(values) => {
                self.values = values;
                true
            }
            None => false,
        };
        work.admit(7, size_of::<bool>())?;
        self.retire_values(work);
        work.admit(1, 0)?;
        if !assigned {
            work.admit(1, size_of::<[Part<'_>; 2]>())?;
            self.message(
                enm,
                None,
                &[Part::Text(
                    "resolvable, duplicate-free discriminant assignment",
                )],
                &[Part::Text("ill-formed discriminants")],
                work,
            )?;
        } else if enm
            .canonical_tag_repr_observed(work.session, work.site)?
            .is_none()
            && !(enm.variants.is_empty()
                && enm.discriminants.is_empty()
                && enm.repr.is_none()
                && enm.layout.is_none())
        {
            work.admit(1, size_of::<[Part<'_>; 2]>())?;
            self.message(
                enm,
                None,
                &[Part::Text(
                    "a canonical tag repr (non-empty, values fit the hint and the 64-bit cap)",
                )],
                &[Part::Text("no canonical tag")],
                work,
            )?;
        }
        let mut index = 0;
        while let Some(variant) = work.at(&enm.variants, index)? {
            work.admit(3, 3 * size_of::<usize>())?;
            if !variant.field_names.is_empty() && variant.field_names.len() != variant.fields.len()
            {
                work.admit(
                    1,
                    size_of::<[Part<'_>; 5]>() + size_of::<Option<(usize, &str)>>(),
                )?;
                self.message(
                    enm,
                    Some((index, &variant.name)),
                    &[
                        Part::Text("field_names empty or exactly "),
                        Part::Number(variant.fields.len() as u128),
                        Part::Text(" entries"),
                    ],
                    &[
                        Part::Number(variant.field_names.len() as u128),
                        Part::Text(" field names"),
                    ],
                    work,
                )?;
            }
            work.next(&mut index)?;
        }
        Ok(())
    }
}
