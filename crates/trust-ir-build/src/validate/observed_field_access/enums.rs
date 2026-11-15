// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    dead_code,
    clippy::while_let_loop,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
impl<'m> State<'m> {
    pub(super) fn enumeration<O: ExecutionObserver>(
        &mut self,
        mode: Mode,
        block: BlockId,
        aggregate: &Ty,
        def: &'m EnumDef,
        field: u32,
        declared: &Ty,
        values: &ObservedValueTypes,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        let Some(repr) = def.canonical_tag_repr_observed(work.session, work.site)? else {
            work.text("enum ", &mut self.reason)?;
            render::ty(aggregate, &mut self.render, &mut self.reason, work)?;
            work.text(" has no canonical tag repr (uninhabited or unrepresentable), so no lane of it can be projected",&mut self.reason)?;
            return self.invalid(mode, block, work);
        };
        if field == 0 {
            if matches!(mode, Mode::Insert(_)) {
                work.text("insert_field cannot rewrite an enum discriminant; construct the variant with Const (lane 0 is the tag, and a re-tag would leave the old variant's payload lanes in place under the new tag)",&mut self.reason)?;
                return self.invalid(mode, block, work);
            }
            work.admit(16, size_of::<Option<Ty>>() + size_of::<Ty>())?;
            self.tag = Some(repr.ty());
            let expected = self.tag.as_ref().ok_or(ObservedValueError::InvalidRange)?;
            if !expected.structural_eq_observed(declared, work.session, work.site)? {
                work.admit(3, size_of::<bool>())?;
                if !(expected.is_refine() || declared.is_refine()) {
                    self.expected = expected.display_observed(work.session, work.site)?;
                    return self.enum_mismatch(mode, block, "field", declared, work);
                }
            }
            return Ok(());
        }
        work.admit(4, 2 * size_of::<usize>())?;
        let lane = (field - 1) as usize;
        let mut widest = 0;
        let mut at = 0;
        loop {
            let Some(variant) = work.at(&def.variants, at)? else {
                break;
            };
            work.admit(1, size_of::<usize>())?;
            widest = widest.max(variant.fields.len());
            if let Some(ty) = work.at(&variant.fields, lane)? {
                work.reserve(&mut self.lanes)?;
                work.admit(1, size_of::<(&str, &Ty)>())?;
                self.lanes.push((&variant.name, ty));
            }
            work.next(&mut at)?;
        }
        if self.lanes.is_empty() {
            work.text("field ", &mut self.reason)?;
            work.number(field as usize, &mut self.reason)?;
            work.text(" is out of range for every variant of ", &mut self.reason)?;
            render::ty(aggregate, &mut self.render, &mut self.reason, work)?;
            work.text(" (the widest variant has ", &mut self.reason)?;
            work.number(widest, &mut self.reason)?;
            work.text(
                " field(s), so an enum value has lanes 0..=",
                &mut self.reason,
            )?;
            work.number(widest, &mut self.reason)?;
            work.text(")", &mut self.reason)?;
            return self.invalid(mode, block, work);
        }
        let actual = match mode {
            Mode::Extract => Some(declared),
            Mode::Insert(value) => values.get_observed(value, work.session, work.site)?,
        };
        let Some(actual) = actual else { return Ok(()) };
        let mut at = 0;
        loop {
            let Some((_, expected)) = work.at(&self.lanes, at)? else {
                break;
            };
            if expected.structural_eq_observed(actual, work.session, work.site)? {
                return Ok(());
            }
            work.admit(3, size_of::<bool>())?;
            if expected.is_refine() || actual.is_refine() {
                return Ok(());
            }
            work.next(&mut at)?;
        }
        work.text("one of {", &mut self.expected)?;
        let mut at = 0;
        loop {
            let Some((name, ty)) = work.at(&self.lanes, at)? else {
                break;
            };
            if at != 0 {
                work.text(", ", &mut self.expected)?;
            }
            work.text(name, &mut self.expected)?;
            work.text(": ", &mut self.expected)?;
            render::ty(ty, &mut self.render, &mut self.expected, work)?;
            work.next(&mut at)?;
        }
        work.text("}", &mut self.expected)?;
        self.enum_mismatch(
            mode,
            block,
            match mode {
                Mode::Extract => "field",
                Mode::Insert(_) => "value",
            },
            actual,
            work,
        )
    }
}
