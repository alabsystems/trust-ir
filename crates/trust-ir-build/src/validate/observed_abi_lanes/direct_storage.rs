// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Paid full-image and packed-live-range check for the new Direct family.
use super::super::abi_lanes::{align_bytes, byte_align};
use super::*;

impl State<'_> {
    pub(super) fn retire_enum_layout<O: ExecutionObserver>(
        &mut self,
        w: &mut Work<'_, '_, O>,
    ) -> R {
        w.step(size_of::<Option<Result<Arc<EnumLayoutShape>, LayoutError>>>().saturating_add(1));
        let result = match self.enum_layout.take() {
            Some(Ok(shape)) => shape.retire_arc_observed(w.session, w.site),
            Some(Err(error)) => error.retire_observed(w.session, w.site),
            None => Ok(()),
        };
        w.poll();
        result.map_err(|error| w.terminal(error))
    }

    fn geometry<O: ExecutionObserver>(
        &mut self,
        layouts: &LayoutTable<'_>,
        ty: &Ty,
        w: &mut Work<'_, '_, O>,
    ) -> R<Option<(u64, u64)>> {
        w.admit(
            1,
            size_of::<Option<Result<Arc<TyLayoutShape>, LayoutError>>>(),
        )?;
        if self.layout.is_some() {
            return Err(ObservedValueError::InvalidRange);
        }
        self.layout = Some(layouts.ty_layout_observed(ty, w.session, w.site)?);
        w.admit(8, size_of::<Option<(u64, u64)>>())?;
        let answer = match &self.layout {
            Some(Ok(shape)) => shape.size_bytes().zip(byte_align(shape)),
            _ => None,
        };
        self.retire_layout(w)?;
        Ok(answer)
    }

    fn range<O: ExecutionObserver>(
        &mut self,
        range: (u64, u64, u64),
        w: &mut Work<'_, '_, O>,
    ) -> R {
        w.push(&mut self.ranges, range)?;
        let mut index = self.ranges.len() - 1;
        while index > 0 {
            w.admit(3, 2 * size_of::<(u64, u64, u64)>())?;
            if self.ranges[index - 1].0 <= self.ranges[index].0 {
                break;
            }
            self.ranges.swap(index - 1, index);
            index -= 1;
        }
        Ok(())
    }

    pub(super) fn direct_storage_fits<O: ExecutionObserver>(
        &mut self,
        layouts: &LayoutTable<'_>,
        def: &EnumDef,
        w: &mut Work<'_, '_, O>,
    ) -> R<bool> {
        w.admit(
            2,
            size_of::<Option<Result<Arc<EnumLayoutShape>, LayoutError>>>(),
        )?;
        if self.enum_layout.is_some() || !self.ranges.is_empty() {
            return Err(ObservedValueError::InvalidRange);
        }
        self.enum_layout = Some(layouts.enum_layout_observed(def.id, w.session, w.site)?);
        w.admit(
            4,
            size_of::<Option<(trust_ir::ty::EnumTagRepr, u64, u64)>>(),
        )?;
        let image = match &self.enum_layout {
            Some(Ok(shape)) => Some((shape.tag, shape.size_bits, shape.align_bits)),
            _ => None,
        };
        self.retire_enum_layout(w)?;
        let Some((tag, full_size, full_align)) = image else {
            return Ok(false);
        };
        let Some((tag_size, tag_align)) = self.geometry(layouts, &tag.ty(), w)? else {
            return Ok(false);
        };
        w.admit(3, size_of::<u64>())?;
        let Some(desc) = &def.layout else {
            return Ok(false);
        };
        let EnumTagEncoding::DirectWithUninhabited { tag_offset, .. } = &desc.encoding else {
            return Ok(false);
        };
        let mut live_size = 0;
        let mut live_align = tag_align;
        let mut has_live = false;
        let mut index = 0;
        while let Some(variant) = w.at(&def.variants, index)? {
            let dead = layouts.variant_is_uninhabited_observed(variant, w.session, w.site)?;
            w.admit(2, 0)?;
            if !dead {
                has_live = true;
                self.range((*tag_offset, tag_size, tag_align), w)?;
                let Some(offsets) = w.at(&desc.variant_field_offsets, index)? else {
                    return Ok(false);
                };
                let mut field_index = 0;
                while let Some(field) = w.at(&variant.fields, field_index)? {
                    let Some(offset) = w.at(offsets, field_index)? else {
                        return Ok(false);
                    };
                    let Some((size, align)) = self.geometry(layouts, field, w)? else {
                        return Ok(false);
                    };
                    w.admit(3, 0)?;
                    live_align = live_align.max(align);
                    if size != 0 {
                        self.range((*offset, size, align), w)?;
                    }
                    w.next(&mut field_index)?;
                }
                let mut end = 0;
                let mut range_index = 0;
                while let Some(&(offset, size, align)) = w.at(&self.ranges, range_index)? {
                    w.admit(6, size_of::<Option<u64>>())?;
                    if align_bytes(end, align) != Some(offset) {
                        return Ok(false);
                    }
                    let Some(next) = offset.checked_add(size) else {
                        return Ok(false);
                    };
                    end = next;
                    w.next(&mut range_index)?;
                }
                w.admit(1, 0)?;
                live_size = live_size.max(end);
                w.rows(take(&mut self.ranges));
            }
            w.next(&mut index)?;
        }
        w.admit(8, size_of::<Option<u64>>())?;
        Ok(has_live
            && align_bytes(live_size, live_align).and_then(|size| size.checked_mul(8))
                == Some(full_size)
            && live_align.checked_mul(8) == Some(full_align))
    }
}
