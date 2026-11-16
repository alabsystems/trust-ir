// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

impl Work {
    pub(super) fn native_enum<O: ExecutionObserver>(
        &mut self,
        fact: &NativeAdtLayoutFact,
        layout: &NativeEnumLayoutFact,
        definition: &EnumDef,
        session: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> R {
        let reference = NativeCompilerFactRef::AdtLayout(fact.id);
        admit(session, site, 2, 0)?;
        if matches!(
            definition.layout.as_ref().map(|layout| &layout.encoding),
            Some(crate::EnumTagEncoding::SingleInhabited { .. })
        ) && layout.tag_encoding != NativeEnumTagEncoding::Untagged
        {
            self.invalid(reference, "enum_layout.tag_encoding", session, site)?;
        }
        self.profile_binding(fact, layout, definition, session, site)?;
        let mut index = 0;
        while index < layout.variants.len() {
            admit(session, site, 1, 0)?;
            let variant = &layout.variants[index];
            if !set_insert(
                &mut self.seen_variants,
                variant.variant_index,
                session,
                site,
            )? {
                self.invalid(reference, "enum_layout.variant_index", session, site)?;
            }
            admit(session, site, 1, 0)?;
            let Some(expected) = definition.variants.get(variant.variant_index as usize) else {
                self.invalid(reference, "enum_layout.variant", session, site)?;
                index += 1;
                continue;
            };
            if !text_equal(&expected.name, &variant.name, session, site)? {
                self.invalid(reference, "enum_layout.variant", session, site)?;
            }
            let profiled_direct = matches!(
                definition.layout.as_ref().map(|layout| &layout.encoding),
                Some(crate::EnumTagEncoding::DirectWithUninhabited { .. })
            );
            if let Some(crate::EnumTagEncoding::DirectWithUninhabited { variants, .. }) =
                definition.layout.as_ref().map(|layout| &layout.encoding)
            {
                admit(
                    session,
                    site,
                    crate::layout_table::direct_storage::profile_lookup_work(variants.len()),
                    size_of::<Option<&crate::UninhabitedVariantLayout>>(),
                )?;
                if let Some(profile) = crate::layout_table::direct_storage::profile(
                    definition,
                    variant.variant_index as usize,
                ) {
                    admit(session, site, 4, 0)?;
                    if profile.size.checked_mul(8) != Some(variant.size_bits) {
                        self.invalid(reference, "enum_layout.variant.size_bits", session, site)?;
                    }
                    if profile.align.checked_mul(8) != variant.align_bits {
                        self.invalid(reference, "enum_layout.variant.align_bits", session, site)?;
                    }
                }
            }
            admit(session, site, 1, 0)?;
            let inactive = matches!(definition.layout.as_ref().map(|layout| &layout.encoding),
                Some(crate::EnumTagEncoding::SingleInhabited { variant: selected }) if variant.variant_index != *selected);
            admit(session, site, 3, 0)?;
            if inactive {
                if !variant.fields.is_empty() {
                    self.invalid(reference, "enum_layout.variant.fields", session, site)?;
                }
                if variant.size_bits != 0 {
                    self.invalid(reference, "layout.size_bits", session, site)?;
                }
            } else if variant.fields.len() != expected.fields.len() {
                self.invalid(reference, "enum_layout.variant.fields", session, site)?;
            }
            let mut field_index = 0;
            while field_index < variant.fields.len() {
                admit(session, site, 2, 0)?;
                let field = &variant.fields[field_index];
                if let Some(expected) = expected.fields.get(field_index) {
                    if u32::try_from(field_index) != Ok(field.field) {
                        self.invalid(reference, "enum_layout.variant.fields", session, site)?;
                    }
                    // Ty::shape is a fixed discriminant classification, not a
                    // recursive type walk or equality over a variable payload.
                    admit(session, site, 4, size_of::<crate::TyShape>())?;
                    if field.ty_shape != expected.shape() {
                        self.invalid(
                            reference,
                            "enum_layout.variant.fields.ty_shape",
                            session,
                            site,
                        )?;
                    }
                    if profiled_direct {
                        admit(session, site, 4, 0)?;
                        let offset = definition
                            .layout
                            .as_ref()
                            .and_then(|layout| {
                                layout
                                    .variant_field_offsets
                                    .get(variant.variant_index as usize)
                            })
                            .and_then(|offsets| offsets.get(field_index))
                            .and_then(|offset| offset.checked_mul(8));
                        if offset != field.offset_bits {
                            self.invalid(
                                reference,
                                "enum_layout.variant.fields.offset_bits",
                                session,
                                site,
                            )?;
                        }
                    }
                }
                field_index += 1;
            }
            admit(session, site, 1, 0)?;
            if variant.size_bits > fact.layout.size_bits {
                self.invalid(reference, "layout.size_bits", session, site)?;
            }
            admit(session, site, 4, 0)?;
            match (fact.layout.align_bits, variant.align_bits) {
                (_, Some(0)) => {
                    self.invalid(reference, "enum_layout.variant.align_bits", session, site)?
                }
                (Some(outer), Some(inner))
                    if outer == 0 || outer < inner || !outer.is_multiple_of(inner) =>
                {
                    self.invalid(reference, "layout.align_bits", session, site)?;
                }
                _ => {}
            }
            index += 1;
        }
        admit(session, site, 1, 0)?;
        match &layout.tag_encoding {
            NativeEnumTagEncoding::Direct | NativeEnumTagEncoding::DirectWithUninhabited { .. } => {
                self.direct(fact, layout, session, site)
            }
            NativeEnumTagEncoding::Niche => self.niche(fact, layout, definition, session, site),
            NativeEnumTagEncoding::Untagged => self.untagged(fact, layout, session, site),
        }
    }

    fn profile_binding<O: ExecutionObserver>(
        &mut self,
        fact: &NativeAdtLayoutFact,
        layout: &NativeEnumLayoutFact,
        definition: &EnumDef,
        session: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> R {
        let reference = NativeCompilerFactRef::AdtLayout(fact.id);
        admit(session, site, 2, 0)?;
        match (
            definition.layout.as_ref().map(|layout| &layout.encoding),
            &layout.tag_encoding,
        ) {
            (
                Some(crate::EnumTagEncoding::DirectWithUninhabited {
                    tag_offset,
                    variants,
                }),
                NativeEnumTagEncoding::DirectWithUninhabited { variants: native },
            ) => {
                if !profiles_equal(variants, native, session, site)? {
                    self.invalid(reference, "enum_layout.tag_encoding", session, site)?;
                }
                admit(session, site, 2, 0)?;
                if tag_offset.checked_mul(8) != layout.discriminant_offset_bits {
                    self.invalid(
                        reference,
                        "enum_layout.discriminant_offset_bits",
                        session,
                        site,
                    )?;
                }
                let tag = definition.canonical_tag_repr_observed(session, site)?;
                admit(session, site, 2, 0)?;
                if tag.map(|repr| repr.size_bytes() as u32 * 8) != layout.tag_bits {
                    self.invalid(reference, "enum_layout.tag_bits", session, site)?;
                }
            }
            (Some(crate::EnumTagEncoding::DirectWithUninhabited { .. }), _)
            | (_, NativeEnumTagEncoding::DirectWithUninhabited { .. }) => {
                self.invalid(reference, "enum_layout.tag_encoding", session, site)?;
            }
            _ => {}
        }
        Ok(())
    }

    fn direct<O: ExecutionObserver>(
        &mut self,
        fact: &NativeAdtLayoutFact,
        layout: &NativeEnumLayoutFact,
        session: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> R {
        let reference = NativeCompilerFactRef::AdtLayout(fact.id);
        admit(session, site, 1, 0)?;
        if layout.niche.is_some() {
            self.invalid(reference, "enum_layout.niche", session, site)?;
        }
        admit(session, site, 4, 0)?;
        match (layout.tag_bits, layout.discriminant_offset_bits) {
            (Some(bits), Some(offset)) => {
                if bits == 0 {
                    return self.invalid(reference, "enum_layout.tag_bits", session, site);
                }
                if offset
                    .checked_add(u64::from(bits))
                    .is_none_or(|end| end > fact.layout.size_bits)
                {
                    self.invalid(
                        reference,
                        "enum_layout.discriminant_offset_bits",
                        session,
                        site,
                    )?;
                }
            }
            (None, _) => self.invalid(reference, "enum_layout.tag_bits", session, site)?,
            (_, None) => self.invalid(
                reference,
                "enum_layout.discriminant_offset_bits",
                session,
                site,
            )?,
        }
        let mut index = 0;
        while index < layout.variants.len() {
            admit(session, site, 1, 0)?;
            match layout.variants[index].discriminant {
                None => {
                    self.invalid(reference, "enum_layout.variant.discriminant", session, site)?
                }
                Some(value) => {
                    if !set_insert(&mut self.discriminants, value, session, site)? {
                        self.invalid(reference, "enum_layout.variant.discriminant", session, site)?;
                    }
                }
            }
            index += 1;
        }
        Ok(())
    }

    fn niche<O: ExecutionObserver>(
        &mut self,
        fact: &NativeAdtLayoutFact,
        layout: &NativeEnumLayoutFact,
        definition: &EnumDef,
        session: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> R {
        let reference = NativeCompilerFactRef::AdtLayout(fact.id);
        admit(session, site, 1, 0)?;
        if layout.tag_bits.is_some() {
            self.invalid(reference, "enum_layout.tag_bits", session, site)?;
        }
        admit(session, site, 1, 0)?;
        if layout.discriminant_offset_bits.is_some() {
            self.invalid(
                reference,
                "enum_layout.discriminant_offset_bits",
                session,
                site,
            )?;
        }
        admit(session, site, 1, 0)?;
        let Some(niche) = &layout.niche else {
            return self.invalid(reference, "enum_layout.niche", session, site);
        };
        admit(session, site, 1, 0)?;
        if niche.valid_range.start > niche.valid_range.end {
            self.invalid(reference, "enum_layout.niche.valid_range", session, site)?;
        }
        admit(session, site, 1, 0)?;
        let Some(variant) = definition.variants.get(niche.variant_index as usize) else {
            return self.invalid(reference, "enum_layout.niche.variant_index", session, site);
        };
        admit(session, site, 2, 0)?;
        if let Some(field) = niche.field
            && variant.fields.get(field as usize).is_none()
        {
            self.invalid(reference, "enum_layout.niche.field", session, site)?;
        }
        Ok(())
    }

    fn untagged<O: ExecutionObserver>(
        &mut self,
        fact: &NativeAdtLayoutFact,
        layout: &NativeEnumLayoutFact,
        session: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> R {
        let reference = NativeCompilerFactRef::AdtLayout(fact.id);
        admit(session, site, 1, 0)?;
        if layout.tag_bits.is_some() {
            self.invalid(reference, "enum_layout.tag_bits", session, site)?;
        }
        admit(session, site, 1, 0)?;
        if layout.discriminant_offset_bits.is_some() {
            self.invalid(
                reference,
                "enum_layout.discriminant_offset_bits",
                session,
                site,
            )?;
        }
        admit(session, site, 1, 0)?;
        if layout.niche.is_some() {
            self.invalid(reference, "enum_layout.niche", session, site)?;
        }
        let mut index = 0;
        while index < layout.variants.len() {
            admit(session, site, 1, 0)?;
            if layout.variants[index].discriminant.is_some() {
                self.invalid(reference, "enum_layout.variant.discriminant", session, site)?;
                break;
            }
            index += 1;
        }
        Ok(())
    }
}

fn profiles_equal<O: ExecutionObserver>(
    left: &[crate::UninhabitedVariantLayout],
    right: &[crate::UninhabitedVariantLayout],
    session: &mut ObservedSession<'_, O>,
    site: ExecutionSite,
) -> R<bool> {
    admit(session, site, 1, 0)?;
    if left.len() != right.len() {
        return Ok(false);
    }
    for (left, right) in left.iter().zip(right) {
        admit(session, site, 4, 0)?;
        if left.variant != right.variant
            || left.size != right.size
            || left.align != right.align
            || left.fields.len() != right.fields.len()
        {
            return Ok(false);
        }
        for (left, right) in left.fields.iter().zip(&right.fields) {
            admit(session, site, 2, 0)?;
            if left.size != right.size || left.align != right.align {
                return Ok(false);
            }
        }
    }
    Ok(true)
}
