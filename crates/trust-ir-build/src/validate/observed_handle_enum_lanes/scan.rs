// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    dead_code,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
impl State {
    pub(super) fn run<O: ExecutionObserver>(
        &mut self,
        layouts: &LayoutTable<'_>,
        nominal: &ObservedNominalTypeReachability<'_>,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        work.admit(1, size_of::<&Module>())?;
        let module = layouts.module();
        let mut en = 0usize;
        while let Some(enm) = work.at(&module.enums, en)? {
            work.admit(1, size_of::<Option<&trust_ir::ty::EnumLayoutDescriptor>>())?;
            if let Some(layout) = &enm.layout {
                work.admit(1, size_of::<&EnumTagEncoding>())?;
                if let EnumTagEncoding::Niche {
                    niche_offset,
                    niche_ty,
                    ..
                } = &layout.encoding
                {
                    work.admit(2, 2 * size_of::<u64>())?;
                    let niche_size = niche_ty.size_bytes();
                    let mut variant = 0usize;
                    while let Some(row) = work.at(&enm.variants, variant)? {
                        let Some(offsets) = work.at(&layout.variant_field_offsets, variant)? else {
                            break;
                        };
                        work.admit(1, 2 * size_of::<usize>())?;
                        if offsets.len() == row.fields.len() {
                            let mut field = 0usize;
                            while let Some(ty) = work.at(&row.fields, field)? {
                                let offset = work
                                    .at(offsets, field)?
                                    .ok_or(ObservedValueError::InvalidRange)?;
                                if nominal.contains_handle_observed(ty, work.session, work.site)? {
                                    let size = self.size(layouts, ty, work)?;
                                    work.admit(6, 4 * size_of::<u64>() + size_of::<bool>())?;
                                    let overlaps = match size {
                                        Some(size) => byte_ranges_overlap(
                                            *niche_offset,
                                            niche_size,
                                            *offset,
                                            size,
                                        ),
                                        None => true,
                                    };
                                    if overlaps {
                                        self.emit(
                                            enm,
                                            variant,
                                            field,
                                            *niche_offset,
                                            niche_size,
                                            *offset,
                                            ty,
                                            work,
                                        )?;
                                    }
                                }
                                work.next(&mut field)?;
                            }
                        }
                        work.next(&mut variant)?;
                    }
                }
            }
            work.next(&mut en)?;
        }
        Ok(())
    }
    fn emit<O: ExecutionObserver>(
        &mut self,
        enm: &EnumDef,
        variant: usize,
        field: usize,
        niche: u64,
        niche_size: u64,
        offset: u64,
        ty: &Ty,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        work.text(&enm.name, &mut self.name)?;
        work.text("niche lane at offset ", &mut self.detail)?;
        work.number(niche, &mut self.detail)?;
        work.text(" (", &mut self.detail)?;
        work.number(niche_size, &mut self.detail)?;
        work.text(" byte(s)) vs `", &mut self.detail)?;
        work.admit(1, size_of::<String>())?;
        if self.render.capacity() != 0 {
            return Err(ObservedValueError::InvalidRange);
        }
        self.render = ty.display_observed(work.session, work.site)?;
        work.text(&self.render, &mut self.detail)?;
        work.flat(take(&mut self.render));
        work.admit(1, 0)?;
        work.text("` at offset ", &mut self.detail)?;
        work.number(offset, &mut self.detail)?;
        work.reserve(&mut self.errors)?;
        work.admit(
            1,
            size_of::<ValidationError>() + 2 * size_of::<String>() + 2 * size_of::<u32>(),
        )?;
        // Preserve original diagnostic casts; other mandatory descriptor rules
        // decide index admissibility. No truncating policy acceptance added.
        self.errors.push(ValidationError::HandleLaneNiche {
            enum_name: take(&mut self.name),
            variant: variant as u32,
            field: field as u32,
            detail: take(&mut self.detail),
        });
        Ok(())
    }
}
