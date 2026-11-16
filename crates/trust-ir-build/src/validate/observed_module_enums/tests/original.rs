// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Original complete ordinary enum block; with the separately qualified diagnostic and v67 Direct-profile corrections.
use super::*;
pub(super) fn run(module: &Module) -> Vec<ValidationError> {
    let layouts = module.layout_table();
    let mut errors = Vec::new();
    // Check for duplicate enum IDs
    let mut seen_enum_ids = BTreeSet::new();
    for enm in &module.enums {
        if !seen_enum_ids.insert(enm.id.index()) {
            errors.push(ValidationError::DuplicateEnumId(enm.id.index()));
        }
        // Trust (B3-1): EnumDef WELL-FORMEDNESS — every def must resolve its
        // effective discriminants (rejects duplicate values and implicit-
        // increment overflow) and admit a canonical tag repr (rejects empty/
        // uninhabited defs, a repr hint too narrow for the values, and
        // discriminants beyond the 64-bit tag cap) in one shot. Before this
        // check a malformed def validated fine and failed only when a value
        // of the type was first sized/decoded mid-execution.
        if enm.effective_discriminants().is_none() {
            errors.push(ValidationError::ConstTypeMismatch {
                location: format!("enum.{} ({})", enm.id.index(), enm.name),
                expected: "resolvable, duplicate-free discriminant assignment".to_string(),
                actual: "ill-formed discriminants".to_string(),
            });
        } else if enm.canonical_tag_repr().is_none()
            && !(enm.variants.is_empty()
                && enm.discriminants.is_empty()
                && enm.repr.is_none()
                && enm.layout.is_none())
        {
            errors.push(ValidationError::ConstTypeMismatch {
                location: format!("enum.{} ({})", enm.id.index(), enm.name),
                expected:
                    "a canonical tag repr (non-empty, values fit the hint and the 64-bit cap)"
                        .to_string(),
                actual: "no canonical tag".to_string(),
            });
        }
        for (variant_index, variant) in enm.variants.iter().enumerate() {
            if !variant.field_names.is_empty() && variant.field_names.len() != variant.fields.len()
            {
                errors.push(ValidationError::ConstTypeMismatch {
                    location: format!(
                        "enum.{} ({}) variant {} ({})",
                        enm.id.index(),
                        enm.name,
                        variant_index,
                        variant.name
                    ),
                    expected: format!(
                        "field_names empty or exactly {} entries",
                        variant.fields.len()
                    ),
                    actual: format!("{} field names", variant.field_names.len()),
                });
            }
        }
        let Some(layout) = &enm.layout else { continue };
        let location = || format!("enum.{} ({}) layout", enm.id.index(), enm.name);
        if matches!(
            &layout.encoding,
            trust_ir::EnumTagEncoding::DirectWithUninhabited { .. }
        ) {
            let bound = module
                .enums
                .iter()
                .find(|row| row.id == enm.id)
                .is_some_and(|row| core::ptr::eq(row, enm));
            if !bound || layouts.enum_layout(enm.id).is_err() {
                errors.push(ValidationError::ConstTypeMismatch {
                    location: location(),
                    expected: "a valid Direct storage profile for exactly the uninhabited variants"
                        .into(),
                    actual: "invalid Direct uninhabited storage".into(),
                });
            }
            continue;
        }
        // WS2.22: the tag lane's SIZE is the repr's own width
        // (`EnumTagRepr::size_bytes`); its ALIGNMENT is the TARGET's, and the
        // two are different facts — an ABI may align an integer below its
        // width. Ask the layout authority for the alignment before any
        // placement clause is judged, exactly as the interpreter already does
        // (`byte_align_in`). A target with no scalar table has no answer, so
        // the descriptor is REFUSED rather than measured against the byte
        // count; the alignment clauses below are then skipped, the enum having
        // already drawn its error.
        let lane_repr = match &layout.encoding {
            trust_ir::EnumTagEncoding::Direct { .. }
            | trust_ir::EnumTagEncoding::DirectWithUninhabited { .. } => enm.canonical_tag_repr(),
            trust_ir::EnumTagEncoding::Niche { niche_ty, .. } => Some(*niche_ty),
            trust_ir::EnumTagEncoding::Untagged
            | trust_ir::EnumTagEncoding::SingleInhabited { .. } => None,
        };
        let lane_align = match lane_repr.map(|repr| module.enum_tag_repr_align(repr)) {
            None => None,
            Some(Ok(align)) => Some(align),
            Some(Err(trust_ir::LayoutError::TargetScalarLayoutUnavailable { triple })) => {
                errors.push(ValidationError::EnumTagTargetScalarLayoutUnavailable {
                    enum_id: enm.id.index(),
                    triple,
                });
                None
            }
            Some(Err(err)) => {
                errors.push(ValidationError::ConstTypeMismatch {
                    location: location(),
                    expected: "a resolvable alignment for the tag lane's integer type".to_string(),
                    actual: err.to_string(),
                });
                None
            }
        };
        let mut push_layout_error = |expected: String, actual: String| {
            errors.push(ValidationError::ConstTypeMismatch {
                location: location(),
                expected,
                actual,
            });
        };
        if layout.align == 0 || !layout.align.is_power_of_two() {
            push_layout_error(
                "a non-zero power-of-two alignment".to_string(),
                format!("align {}", layout.align),
            );
        } else if !layout.size.is_multiple_of(layout.align) {
            push_layout_error(
                format!("size a multiple of align {}", layout.align),
                format!("size {}", layout.size),
            );
        }
        if layout.variant_field_offsets.len() != enm.variants.len() {
            push_layout_error(
                format!("{} per-variant offset lists", enm.variants.len()),
                format!("{} offset lists", layout.variant_field_offsets.len()),
            );
        } else {
            for (variant_index, (variant, offsets)) in enm
                .variants
                .iter()
                .zip(&layout.variant_field_offsets)
                .enumerate()
            {
                if matches!(layout.encoding, trust_ir::EnumTagEncoding::SingleInhabited { variant } if usize::try_from(variant).ok() != Some(variant_index))
                {
                    if !offsets.is_empty() {
                        push_layout_error(
                            "an empty physical offset row for an inactive single-inhabited variant"
                                .into(),
                            format!("variant {variant_index}: {} offsets", offsets.len()),
                        );
                    }
                    continue;
                }
                if offsets.len() != variant.fields.len() {
                    push_layout_error(
                        format!(
                            "variant {variant_index} ({}): {} field offsets",
                            variant.name,
                            variant.fields.len()
                        ),
                        format!("{} offsets", offsets.len()),
                    );
                    continue;
                }
                for (field_index, (field_ty, offset)) in
                    variant.fields.iter().zip(offsets).enumerate()
                {
                    // KEEP the LayoutError rather than `.ok()`-ing it away. The
                    // two failures below are different defects with different
                    // owners -- a field that genuinely overflows the variant is
                    // a LAYOUT bug, while a field whose layout will not resolve
                    // is a SPELLING bug in whoever produced the type -- and the
                    // message has to say which. Measured 2026-08-27: reporting
                    // both as "entirely within size 32 / offset 16" sent a
                    // reader hunting an offset bug that did not exist, when the
                    // arithmetic (16 + 16 = 32) fit perfectly and the real
                    // cause was `ty_layout_shape` having no rule for a
                    // non-empty tuple. The reason was in hand at this line and
                    // thrown away.
                    let layout_result = layouts.ty_layout(field_ty);
                    let layout_err = layout_result.as_ref().err().map(|e| e.to_string());
                    let known_layout = layout_result.ok();
                    let known_size = known_layout.as_ref().and_then(|shape| shape.size_bytes());
                    let outside = match known_size {
                        Some(field_size) => offset
                            .checked_add(field_size)
                            .is_none_or(|end| end > layout.size),
                        // An unavailable layout provides no upper bound for a
                        // non-ZST field. Fail closed instead of treating every
                        // offset below `size` as evidence that the field fits.
                        None => !ty_is_zero_sized(field_ty) || *offset > layout.size,
                    };
                    if outside {
                        match known_size {
                            Some(field_size) => push_layout_error(
                                format!(
                                    "variant {variant_index} field {field_index} entirely within size {}",
                                    layout.size
                                ),
                                format!("offset {offset}, field size {field_size}"),
                            ),
                            // Say what actually went wrong: the bound could not
                            // be COMPUTED. Naming the type and the underlying
                            // LayoutError points at the producer that signed an
                            // unresolvable spelling.
                            None => push_layout_error(
                                format!(
                                    "variant {variant_index} field {field_index} to have a \
                                     resolvable layout (needed to bound it within size {})",
                                    layout.size
                                ),
                                match &layout_err {
                                    Some(why) => format!(
                                        "offset {offset}, layout UNRESOLVABLE for type {field_ty}: {why}"
                                    ),
                                    None => format!("offset {offset}, no size for type {field_ty}"),
                                },
                            ),
                        }
                    }
                    // WS3.14: a resolved field layout with NO alignment is a
                    // `!`-derived type (`[!; 2]`, a struct holding `!`). Only a
                    // DIRECT `Ty::Never` field has a descriptor rule (size 0,
                    // align 1 — rustc's `B(!)`); `shape` and the interpreter
                    // refuse every other alignment-less field, so the validator
                    // must too, or an uninhabited variant exempt from niche
                    // coverage would validate a layout no consumer can compute.
                    if known_layout
                        .as_ref()
                        .is_some_and(|shape| shape.align_bits.is_none())
                        && !matches!(field_ty, Ty::Never)
                    {
                        push_layout_error(
                            format!(
                                "variant {variant_index} field {field_index} to have a byte \
                                 alignment (only a direct `!` field is alignment-free)"
                            ),
                            format!("type {field_ty} has no alignment"),
                        );
                    }
                    if let Some(field_align) = known_layout
                        .and_then(|shape| shape.align_bits)
                        .filter(|bits| *bits >= 8 && bits.is_multiple_of(8))
                        .map(|bits| bits / 8)
                    {
                        if !offset.is_multiple_of(field_align) {
                            push_layout_error(
                                format!(
                                    "variant {variant_index} field {field_index} offset aligned to {field_align} bytes"
                                ),
                                format!("offset {offset}"),
                            );
                        }
                        if field_align > layout.align {
                            push_layout_error(
                                format!(
                                    "descriptor align at least variant {variant_index} field {field_index} alignment {field_align}"
                                ),
                                format!("align {}", layout.align),
                            );
                        }
                    }
                }
                // Every overlapping pair of sized fields, reported in
                // `(left, right)` order: each field's size asked once, the
                // pairs found by a sweep, O(f log f + pairs) rather than a
                // pairwise loop.
                let mut sized: Vec<usize> = Vec::with_capacity(variant.fields.len());
                let mut ranges: Vec<(u64, u64)> = Vec::with_capacity(variant.fields.len());
                for (field_index, field_ty) in variant.fields.iter().enumerate() {
                    if let Some(size) = layouts
                        .ty_layout(field_ty)
                        .ok()
                        .and_then(|shape| shape.size_bytes())
                    {
                        sized.push(field_index);
                        ranges.push((offsets[field_index], size));
                    }
                }
                for (left, right) in trust_ir::shape::overlapping_byte_range_pairs(&ranges) {
                    let (left, right) = (sized[left], sized[right]);
                    push_layout_error(
                        format!("variant {variant_index} fields occupy disjoint byte ranges"),
                        format!(
                            "fields {left} and {right} overlap at offsets {} and {}",
                            offsets[left], offsets[right]
                        ),
                    );
                }
            }
        }
        match &layout.encoding {
            // v37 `Untagged`: no tag lane exists, so every tag-placement and
            // tag/field-disjointness check above is vacuous. The one claim that
            // still has content is that a variant can be RECOVERED without
            // reading anything — which holds exactly when there is one variant.
            // A multi-variant untagged descriptor is undiscriminable, so reject
            // it here rather than let a consumer pick a variant arbitrarily.
            trust_ir::EnumTagEncoding::Untagged => {
                if enm.variants.len() != 1 {
                    push_layout_error(
                        "exactly one variant under the untagged encoding".to_string(),
                        format!("{} variants", enm.variants.len()),
                    );
                }
            }
            trust_ir::EnumTagEncoding::SingleInhabited { variant } => {
                let active = usize::try_from(*variant).ok();
                if active
                    .and_then(|index| enm.variants.get(index))
                    .is_none_or(|item| layouts.variant_is_uninhabited(item))
                    || enm.variants.iter().enumerate().any(|(index, item)| {
                        Some(index) != active && !layouts.variant_is_uninhabited(item)
                    })
                {
                    push_layout_error("one selected inhabited variant and only structurally uninhabited inactive variants".into(), format!("single-inhabited selector {variant}"));
                }
            }
            trust_ir::EnumTagEncoding::Direct { tag_offset }
            | trust_ir::EnumTagEncoding::DirectWithUninhabited { tag_offset, .. } => {
                if let Some(repr) = enm.canonical_tag_repr() {
                    let tag_size = repr.size_bytes();
                    if let Some(tag_align) = lane_align {
                        if !tag_offset.is_multiple_of(tag_align) {
                            push_layout_error(
                                format!("a direct tag aligned to {tag_align} bytes"),
                                format!("tag_offset {tag_offset}"),
                            );
                        }
                        if tag_align > layout.align {
                            push_layout_error(
                                format!(
                                    "descriptor align at least direct-tag alignment {tag_align}"
                                ),
                                format!("align {}", layout.align),
                            );
                        }
                    }
                    let tag_in_bounds = tag_offset
                        .checked_add(tag_size)
                        .is_some_and(|end| end <= layout.size);
                    if !tag_in_bounds {
                        push_layout_error(
                            format!(
                                "a direct tag ({tag_size} bytes) within size {}",
                                layout.size
                            ),
                            format!("tag_offset {tag_offset}"),
                        );
                    }
                    for (variant_index, (variant, offsets)) in enm
                        .variants
                        .iter()
                        .zip(&layout.variant_field_offsets)
                        .enumerate()
                    {
                        if offsets.len() != variant.fields.len() {
                            continue;
                        }
                        for (field_index, (field_ty, field_offset)) in
                            variant.fields.iter().zip(offsets).enumerate()
                        {
                            let Some(field_size) = layouts
                                .ty_layout(field_ty)
                                .ok()
                                .and_then(|shape| shape.size_bytes())
                            else {
                                continue;
                            };
                            if byte_ranges_overlap(*tag_offset, tag_size, *field_offset, field_size)
                            {
                                push_layout_error(
                                    "a direct tag disjoint from every non-ZST field".to_string(),
                                    format!(
                                        "tag overlaps variant {variant_index} field {field_index}"
                                    ),
                                );
                            }
                        }
                    }
                }
            }
            trust_ir::EnumTagEncoding::Niche {
                untagged_variant,
                niche_variants_start,
                niche_variants_end,
                niche_start,
                niche_offset,
                niche_ty,
            } => {
                let variant_count = u32::try_from(enm.variants.len()).ok();
                if variant_count.is_none()
                    || variant_count.is_some_and(|count| *untagged_variant >= count)
                {
                    push_layout_error(
                        "an in-range untagged variant".to_string(),
                        format!("untagged_variant {untagged_variant}"),
                    );
                }
                let niche_interval_in_range = niche_variants_start <= niche_variants_end
                    && variant_count.is_some_and(|count| *niche_variants_end < count);
                if !niche_interval_in_range {
                    push_layout_error(
                        "an ordered, in-range niche variant interval".to_string(),
                        format!("{niche_variants_start}..={niche_variants_end}"),
                    );
                }
                // WS3.14 (F-056): every INHABITED variant is the untagged
                // variant or lies in the niche interval. An uninhabited variant
                // (`Module::variant_is_uninhabited` — rustc's `B(!)`) has no
                // value and therefore needs no encoding: it may lie in either
                // place or in neither, exactly as rustc lays it out. The same
                // rule, through the same helper, as `shape` and the
                // interpreter. Constructing such a variant is refused
                // separately (`UninhabitedVariantConstructed`). The pass's
                // table decides each node's inhabitedness once.
                if variant_count.is_some()
                    && let Some(unencoded) = layouts.niche_unencoded_inhabited_variant(
                        enm,
                        *untagged_variant,
                        *niche_variants_start,
                        *niche_variants_end,
                    )
                {
                    push_layout_error(
                        "the niche interval plus the untagged variant to cover every inhabited variant"
                            .to_string(),
                        format!(
                            "inhabited variant {unencoded} ({}) is neither untagged {untagged_variant} \
                             nor in niche interval {niche_variants_start}..={niche_variants_end}",
                            enm.variants[unencoded].name
                        ),
                    );
                }
                let niche_size = niche_ty.size_bytes();
                if let Some(niche_align) = lane_align {
                    if !niche_offset.is_multiple_of(niche_align) {
                        push_layout_error(
                            format!("a niche lane aligned to {niche_align} bytes"),
                            format!("niche_offset {niche_offset}"),
                        );
                    }
                    if niche_align > layout.align {
                        push_layout_error(
                            format!("descriptor align at least niche alignment {niche_align}"),
                            format!("align {}", layout.align),
                        );
                    }
                }
                let niche_end = niche_offset.checked_add(niche_size);
                if niche_end.is_none_or(|end| end > layout.size) {
                    push_layout_error(
                        format!(
                            "a niche lane ({niche_size} bytes) within size {}",
                            layout.size
                        ),
                        format!("niche_offset {niche_offset}"),
                    );
                }
                if let Some(untagged) = enm.variants.get(*untagged_variant as usize) {
                    let offsets = layout
                        .variant_field_offsets
                        .get(*untagged_variant as usize)
                        .filter(|offsets| offsets.len() == untagged.fields.len());
                    let lane_is_covered = offsets.is_some_and(|offsets| {
                        untagged
                            .fields
                            .iter()
                            .zip(offsets)
                            .any(|(field_ty, field_offset)| {
                                layouts
                                    .ty_layout(field_ty)
                                    .ok()
                                    .and_then(|shape| shape.size_bytes())
                                    .is_some_and(|field_size| {
                                        field_size > 0
                                            && *field_offset <= *niche_offset
                                            && field_offset.checked_add(field_size).is_some_and(
                                                |field_end| {
                                                    niche_end.is_some_and(|niche_end| {
                                                        field_end >= niche_end
                                                    })
                                                },
                                            )
                                    })
                            })
                    });
                    if !lane_is_covered {
                        push_layout_error(
                            "the niche lane covered by a non-ZST field of the untagged variant"
                                .to_string(),
                            format!("untagged_variant {untagged_variant}"),
                        );
                    }
                }
                if niche_interval_in_range {
                    for variant_index in *niche_variants_start..=*niche_variants_end {
                        if variant_index == *untagged_variant {
                            continue;
                        }
                        let Some((variant, offsets)) = enm
                            .variants
                            .get(variant_index as usize)
                            .zip(layout.variant_field_offsets.get(variant_index as usize))
                        else {
                            continue;
                        };
                        if offsets.len() != variant.fields.len() {
                            continue;
                        }
                        for (field_index, (field_ty, field_offset)) in
                            variant.fields.iter().zip(offsets).enumerate()
                        {
                            let Some(field_size) = layouts
                                .ty_layout(field_ty)
                                .ok()
                                .and_then(|shape| shape.size_bytes())
                            else {
                                continue;
                            };
                            if byte_ranges_overlap(
                                *niche_offset,
                                niche_size,
                                *field_offset,
                                field_size,
                            ) {
                                push_layout_error(
                                    "the niche lane disjoint from non-ZST fields of niche-tagged variants"
                                        .to_string(),
                                    format!(
                                        "lane overlaps variant {variant_index} field {field_index}"
                                    ),
                                );
                            }
                        }
                    }
                }
                let niche_bits = (niche_size * 8) as u32;
                let max_value = if niche_bits == 128 {
                    u128::MAX
                } else {
                    (1u128 << niche_bits) - 1
                };
                if *niche_start > max_value {
                    push_layout_error(
                        format!("niche_start representable in {niche_bits} bits"),
                        format!("niche_start {niche_start}"),
                    );
                }
                let niche_span = niche_variants_end
                    .checked_sub(*niche_variants_start)
                    .map(u128::from);
                if niche_span.is_none_or(|span| span > max_value) {
                    // A reversed interval is still rejected when the lane is
                    // 128 bits; its capacity is 2^128, not representable in
                    // u128. Constructing this diagnostic must not overflow.
                    let expected = match max_value.checked_add(1) {
                        Some(capacity) => format!("at most {capacity} distinct niche variants"),
                        None => "at most 340282366920938463463374607431768211456 distinct niche variants".to_string(),
                    };
                    push_layout_error(
                        expected,
                        format!("niche interval {niche_variants_start}..={niche_variants_end}"),
                    );
                }
            }
        }
    }

    errors
}
