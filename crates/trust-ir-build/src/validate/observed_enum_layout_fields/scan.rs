// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
impl<'m> State<'m> {
    pub(super) fn run<O: ExecutionObserver>(
        &mut self,
        module: &'m Module,
        enm: &EnumDef,
        layout: &EnumLayoutDescriptor,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        work.admit(1, 0)?;
        if self.table.is_some() {
            return Err(ObservedValueError::InvalidRange);
        }
        self.table = Some(LayoutTable::new_observed(module, work.session, work.site)?);
        work.admit(2, 2 * size_of::<usize>())?;
        if layout.variant_field_offsets.len() != enm.variants.len() {
            self.begin(work)?;
            work.number(enm.variants.len() as u128, &mut self.expected)?;
            work.text(" per-variant offset lists", &mut self.expected)?;
            work.number(layout.variant_field_offsets.len() as u128, &mut self.actual)?;
            work.text(" offset lists", &mut self.actual)?;
            return self.push(enm, work);
        }
        let mut v = 0;
        while let Some(variant) = work.at(&enm.variants, v)? {
            let offsets = work
                .at(&layout.variant_field_offsets, v)?
                .ok_or(ObservedValueError::InvalidRange)?;
            work.admit(2, 2 * size_of::<usize>())?;
            if matches!(layout.encoding, trust_ir::EnumTagEncoding::SingleInhabited { variant } if usize::try_from(variant).ok() != Some(v))
            {
                if !offsets.is_empty() {
                    self.begin(work)?;
                    work.text(
                        "an empty physical offset row for an inactive single-inhabited variant",
                        &mut self.expected,
                    )?;
                    work.text("variant ", &mut self.actual)?;
                    work.number(v as u128, &mut self.actual)?;
                    work.text(": ", &mut self.actual)?;
                    work.number(offsets.len() as u128, &mut self.actual)?;
                    work.text(" offsets", &mut self.actual)?;
                    self.push(enm, work)?;
                }
                work.next(&mut v)?;
                continue;
            }
            if offsets.len() != variant.fields.len() {
                self.begin(work)?;
                work.text("variant ", &mut self.expected)?;
                work.number(v as u128, &mut self.expected)?;
                work.text(" (", &mut self.expected)?;
                work.text(&variant.name, &mut self.expected)?;
                work.text("): ", &mut self.expected)?;
                work.number(variant.fields.len() as u128, &mut self.expected)?;
                work.text(" field offsets", &mut self.expected)?;
                work.number(offsets.len() as u128, &mut self.actual)?;
                work.text(" offsets", &mut self.actual)?;
                self.push(enm, work)?;
                work.next(&mut v)?;
                continue;
            }
            let mut f = 0;
            while let Some(ty) = work.at(&variant.fields, f)? {
                work.admit(1, size_of::<u64>())?;
                let offset = *work
                    .at(offsets, f)?
                    .ok_or(ObservedValueError::InvalidRange)?;
                self.field(enm, layout, v, f, ty, offset, work)?;
                work.next(&mut f)?;
            }
            self.pairs(enm, v, variant, offsets, work)?;
            work.next(&mut v)?;
        }
        Ok(())
    }
    fn pairs<O: ExecutionObserver>(
        &mut self,
        enm: &EnumDef,
        v: usize,
        variant: &trust_ir::ty::EnumVariant,
        offsets: &[u64],
        work: &mut Work<'_, '_, O>,
    ) -> R {
        work.admit(1, 0)?;
        if self.ranges.capacity() != 0 {
            return Err(ObservedValueError::InvalidRange);
        }
        let mut f = 0;
        while let Some(ty) = work.at(&variant.fields, f)? {
            let summary = self.query(ty, work)?;
            work.admit(1, size_of::<Option<u64>>())?;
            if let Some(size) = summary.size {
                work.reserve(&mut self.ranges)?;
                work.admit(1, size_of::<(usize, u64, u64)>())?;
                let offset = *work
                    .at(offsets, f)?
                    .ok_or(ObservedValueError::InvalidRange)?;
                self.ranges.push((f, offset, size));
            }
            self.retire_query(work);
            work.admit(1, 0)?;
            work.next(&mut f)?;
        }
        let mut left = 0;
        while let Some(row) = work.at(&self.ranges, left)? {
            work.admit(1, size_of::<(usize, u64, u64)>())?;
            let (li, lo, ls) = *row;
            let mut right = left;
            work.next(&mut right)?;
            while let Some(row) = work.at(&self.ranges, right)? {
                work.admit(1, size_of::<(usize, u64, u64)>())?;
                let (ri, ro, rs) = *row;
                work.admit(16, 4 * size_of::<u64>())?;
                if byte_ranges_overlap(lo, ls, ro, rs) {
                    self.begin(work)?;
                    work.text("variant ", &mut self.expected)?;
                    work.number(v as u128, &mut self.expected)?;
                    work.text(" fields occupy disjoint byte ranges", &mut self.expected)?;
                    work.text("fields ", &mut self.actual)?;
                    work.number(li as u128, &mut self.actual)?;
                    work.text(" and ", &mut self.actual)?;
                    work.number(ri as u128, &mut self.actual)?;
                    work.text(" overlap at offsets ", &mut self.actual)?;
                    work.number(u128::from(lo), &mut self.actual)?;
                    work.text(" and ", &mut self.actual)?;
                    work.number(u128::from(ro), &mut self.actual)?;
                    self.push(enm, work)?;
                }
                work.next(&mut right)?;
            }
            work.next(&mut left)?;
        }
        self.retire_ranges(work);
        work.admit(1, 0)
    }
}
