// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
impl State<'_> {
    pub(super) fn covering_field<O: ExecutionObserver>(
        &mut self,
        enm: &EnumDef,
        layout: &EnumLayoutDescriptor,
        niche: Niche,
        end: Option<u64>,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        work.admit(1, size_of::<usize>())?;
        let Some(variant) = work.at(&enm.variants, niche.untagged as usize)? else {
            return Ok(());
        };
        let offsets = work.at(&layout.variant_field_offsets, niche.untagged as usize)?;
        work.admit(2, 2 * size_of::<usize>())?;
        let mut covered = false;
        if let Some(offsets) = offsets.filter(|offsets| offsets.len() == variant.fields.len()) {
            let mut index = 0;
            while let Some(ty) = work.at(&variant.fields, index)? {
                let offset = *work
                    .at(offsets, index)?
                    .ok_or(ObservedValueError::InvalidRange)?;
                if let Some(size) = self.size(ty, work)? {
                    work.admit(6, size_of::<bool>() + size_of::<Option<u64>>())?;
                    if size > 0
                        && offset <= niche.offset
                        && offset
                            .checked_add(size)
                            .is_some_and(|field_end| end.is_some_and(|end| field_end >= end))
                    {
                        covered = true;
                        break;
                    }
                }
                work.next(&mut index)?;
            }
        }
        work.admit(1, 0)?;
        if !covered {
            work.admit(1, size_of::<[Part<'_>; 3]>())?;
            self.message(
                enm,
                &[Part::Text(
                    "the niche lane covered by a non-ZST field of the untagged variant",
                )],
                &[
                    Part::Text("untagged_variant "),
                    Part::Number(u128::from(niche.untagged)),
                ],
                work,
            )?;
        }
        Ok(())
    }
    pub(super) fn niche_fields<O: ExecutionObserver>(
        &mut self,
        enm: &EnumDef,
        layout: &EnumLayoutDescriptor,
        niche: Niche,
        size: u64,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        let mut index = niche.start;
        loop {
            work.admit(2, size_of::<u32>())?;
            if index != niche.untagged {
                let variant = work.at(&enm.variants, index as usize)?;
                let offsets = work.at(&layout.variant_field_offsets, index as usize)?;
                if let Some((variant, offsets)) = variant.zip(offsets) {
                    work.admit(1, 2 * size_of::<usize>())?;
                    if offsets.len() == variant.fields.len() {
                        let mut field = 0;
                        while let Some(ty) = work.at(&variant.fields, field)? {
                            let offset = *work
                                .at(offsets, field)?
                                .ok_or(ObservedValueError::InvalidRange)?;
                            if let Some(field_size) = self.size(ty, work)? {
                                work.admit(12, 4 * size_of::<u64>())?;
                                if byte_ranges_overlap(niche.offset, size, offset, field_size) {
                                    work.admit(1, size_of::<[Part<'_>; 5]>())?;
                                    self.message(enm,&[Part::Text("the niche lane disjoint from non-ZST fields of niche-tagged variants")],
                                        &[Part::Text("lane overlaps variant "),Part::Number(u128::from(index)),Part::Text(" field "),Part::Number(field as u128)],work)?;
                                }
                            }
                            work.next(&mut field)?;
                        }
                    }
                }
            }
            work.admit(1, 0)?;
            if index == niche.end {
                break;
            }
            work.admit(1, size_of::<u32>())?;
            index = index
                .checked_add(1)
                .ok_or(ObservedValueError::CapacityOverflow)?;
        }
        Ok(())
    }
}
