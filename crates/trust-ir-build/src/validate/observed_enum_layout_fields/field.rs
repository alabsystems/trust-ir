// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
impl State<'_> {
    pub(super) fn field<O: ExecutionObserver>(
        &mut self,
        enm: &EnumDef,
        layout: &EnumLayoutDescriptor,
        v: usize,
        f: usize,
        ty: &Ty,
        offset: u64,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        let summary = self.query(ty, work)?;
        // Original first pass computes an error's full reason even when the
        // spelling-only zero-size exception will make the bound vacuous.
        self.error_reason(work)?;
        self.bounds(enm, layout, v, f, ty, offset, summary.size, work)?;
        work.admit(3, 0)?;
        if summary.known && summary.align.is_none() && !matches!(ty, Ty::Never) {
            self.field_prefix(v, f, work)?;
            work.text(
                " to have a byte alignment (only a direct `!` field is alignment-free)",
                &mut self.expected,
            )?;
            self.type_text(ty, work)?;
            work.text("type ", &mut self.actual)?;
            work.text(
                self.tytext
                    .as_deref()
                    .ok_or(ObservedValueError::InvalidRange)?,
                &mut self.actual,
            )?;
            work.text(" has no alignment", &mut self.actual)?;
            self.push(enm, work)?;
            retire_text_slot(&mut self.tytext, work);
            work.admit(1, 0)?;
        }
        work.admit(4, size_of::<Option<u64>>())?;
        if let Some(bits) = summary.align
            && bits >= 8
            && bits.is_multiple_of(8)
        {
            let align = bits / 8;
            work.admit(1, 0)?;
            if !offset.is_multiple_of(align) {
                self.field_prefix(v, f, work)?;
                work.text(" offset aligned to ", &mut self.expected)?;
                work.number(u128::from(align), &mut self.expected)?;
                work.text(" bytes", &mut self.expected)?;
                work.text("offset ", &mut self.actual)?;
                work.number(u128::from(offset), &mut self.actual)?;
                self.push(enm, work)?;
            }
            work.admit(1, 0)?;
            if align > layout.align {
                self.begin(work)?;
                work.text("descriptor align at least variant ", &mut self.expected)?;
                work.number(v as u128, &mut self.expected)?;
                work.text(" field ", &mut self.expected)?;
                work.number(f as u128, &mut self.expected)?;
                work.text(" alignment ", &mut self.expected)?;
                work.number(u128::from(align), &mut self.expected)?;
                work.text("align ", &mut self.actual)?;
                work.number(u128::from(layout.align), &mut self.actual)?;
                self.push(enm, work)?;
            }
        }
        self.retire_query(work);
        work.admit(1, 0)
    }
}
