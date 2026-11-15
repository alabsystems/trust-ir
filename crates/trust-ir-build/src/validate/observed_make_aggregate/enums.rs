// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    dead_code,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
impl State {
    pub(super) fn enumeration<O: ExecutionObserver>(
        &mut self,
        layouts: &trust_ir::LayoutTable<'_>,
        block: BlockId,
        ty: &Ty,
        id: EnumId,
        variant: Option<u32>,
        fields: &[ValueId],
        values: &ObservedValueTypes,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        let Some(def) = lookup::enumeration(layouts.module(), id, work)? else {
            return self.because(block, ty, "references an undefined enum definition", work);
        };
        work.admit(1, size_of::<Option<u32>>())?;
        let Some(variant) = variant else {
            return self.because(block, ty, "an enum construction needs a `variant` index (the tag is `discriminants[variant]`, never a lane operand)", work);
        };
        let Some(row) = work.at(&def.variants, variant as usize)? else {
            work.text("variant index ", &mut self.reason)?;
            work.unsigned(u128::from(variant), &mut self.reason)?;
            work.text(" is out of range (", &mut self.reason)?;
            work.unsigned(def.variants.len() as u128, &mut self.reason)?;
            work.text(" variant(s))", &mut self.reason)?;
            return self.invalid(block, ty, work);
        };
        // Preserve original short-circuit: no second assignment if tag is None.
        let canonical = def
            .canonical_tag_repr_observed(work.session, work.site)?
            .is_some();
        let mut resolvable = false;
        if canonical {
            work.admit(1, size_of::<Option<Vec<i128>>>())?;
            if let Some(discriminants) =
                def.effective_discriminants_observed(work.session, work.site)?
            {
                self.discriminants = discriminants;
                resolvable = true;
            }
        }
        work.admit(2, size_of::<bool>())?;
        if !(canonical && resolvable) {
            return self.because(block, ty, "the enum has no canonical tag repr or no resolvable discriminants, so no value of it can be built", work);
        }
        // Child-owned assignment result stays in State during the full actual
        // fixpoint query and all later diagnostics, including after refusal.
        if layouts.variant_is_uninhabited_observed(row, work.session, work.site)? {
            self.location(block, ty, work)?;
            work.text(&def.name, &mut self.enum_name)?;
            work.text(&row.name, &mut self.variant_name)?;
            work.reserve(&mut self.errors)?;
            work.admit(1, size_of::<ValidationError>() + 3 * size_of::<String>())?;
            self.errors
                .push(ValidationError::UninhabitedVariantConstructed {
                    location: take(&mut self.location),
                    enum_name: take(&mut self.enum_name),
                    variant,
                    variant_name: take(&mut self.variant_name),
                });
            return Ok(());
        }
        self.check(
            block,
            ty,
            fields,
            lanes::Lanes::Types(&row.fields),
            values,
            work,
        )
    }
}
