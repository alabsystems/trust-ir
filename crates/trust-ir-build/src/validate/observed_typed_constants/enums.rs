// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
impl<'a> State<'a> {
    pub(super) fn enumeration<'m: 'a, O: ExecutionObserver>(
        &mut self,
        symbols: &ObservedConstantSymbols<'_, 'm>,
        values: &[Constant],
        id: EnumId,
        work: &mut Work<'_, '_, O>,
    ) -> R<Option<&'a [Ty]>> {
        let Some(def) = lookup::enumeration(symbols.module(), id, work)? else {
            self.missing("enum.", id.index(), work)?;
            return Ok(None);
        };
        self.discriminants = def.effective_discriminants_observed(work.session, work.site)?;
        if self.discriminants.is_none() {
            work.text("enum ", &mut self.expected)?;
            work.text(&def.name, &mut self.expected)?;
            work.text(" with resolvable discriminants", &mut self.expected)?;
            work.text("ill-formed discriminant assignment", &mut self.actual)?;
            self.mismatch_ready(work)?;
            return Ok(None);
        }
        let Some((head, payload)) = values.split_first() else {
            work.text(
                "enum constant with a leading discriminant element",
                &mut self.expected,
            )?;
            work.text("empty aggregate", &mut self.actual)?;
            self.mismatch_ready(work)?;
            return Ok(None);
        };
        work.admit(2, size_of::<i128>())?;
        let Constant::Int(discriminant) = head else {
            work.text("integer discriminant at element 0", &mut self.expected)?;
            self.actual = head.shape_label_observed(work.session, work.site)?;
            self.mismatch_ready(work)?;
            return Ok(None);
        };
        let mut at = 0;
        let index = loop {
            let values = self
                .discriminants
                .as_ref()
                .ok_or(ObservedValueError::InvalidRange)?;
            let Some(n) = work.at(values, at)? else {
                break None;
            };
            work.admit(1, size_of::<bool>())?;
            if n == discriminant {
                break Some(at);
            }
            work.next(&mut at)?;
        };
        let Some(index) = index else {
            work.text("a discriminant of enum ", &mut self.expected)?;
            work.text(&def.name, &mut self.expected)?;
            work.signed(*discriminant, &mut self.actual)?;
            self.mismatch_ready(work)?;
            return Ok(None);
        };
        let variant = work
            .at(&def.variants, index)?
            .ok_or(ObservedValueError::InvalidRange)?;
        if symbols
            .layouts()
            .variant_is_uninhabited_observed(variant, work.session, work.site)?
        {
            self.here(work)?;
            work.text(&def.name, &mut self.enum_name)?;
            work.text(&variant.name, &mut self.variant_name)?;
            work.reserve(&mut self.errors)?;
            work.admit(1, size_of::<ValidationError>() + 3 * size_of::<String>())?;
            self.errors
                .push(ValidationError::UninhabitedVariantConstructed {
                    location: take(&mut self.location),
                    enum_name: take(&mut self.enum_name),
                    variant: u32::try_from(index).unwrap_or(u32::MAX),
                    variant_name: take(&mut self.variant_name),
                });
            return Ok(None);
        }
        work.admit(1, size_of::<bool>())?;
        if payload.len() != variant.fields.len() {
            work.unsigned(variant.fields.len() as u128, &mut self.expected)?;
            work.text(" payload field(s) for variant ", &mut self.expected)?;
            work.text(&variant.name, &mut self.expected)?;
            work.unsigned(payload.len() as u128, &mut self.actual)?;
            work.text(" field(s)", &mut self.actual)?;
            self.mismatch_ready(work)?;
            return Ok(None);
        }
        Ok(Some(&variant.fields))
    }
}
