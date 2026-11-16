// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Exact original ordinary stage bodies, including corrected 128-bit message.
use super::*;
pub(super) fn prelude(
    module: &Module,
    enm: &EnumDef,
    layout: &EnumLayoutDescriptor,
) -> (Vec<ValidationError>, Option<u64>) {
    if matches!(
        &layout.encoding,
        EnumTagEncoding::DirectWithUninhabited { .. }
    ) {
        return (vec![], None);
    }
    let mut errors = Vec::new();
    let location = || format!("enum.{} ({}) layout", enm.id.index(), enm.name);
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
        trust_ir::EnumTagEncoding::Untagged | trust_ir::EnumTagEncoding::SingleInhabited { .. } => {
            None
        }
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
    (errors, lane_align)
}
pub(super) fn encoding(
    module: &Module,
    enm: &EnumDef,
    layout: &EnumLayoutDescriptor,
    lane_align: Option<u64>,
) -> Vec<ValidationError> {
    let layouts = module.layout_table();
    let mut errors = Vec::new();
    let location = || format!("enum.{} ({}) layout", enm.id.index(), enm.name);
    let mut push_layout_error = |expected: String, actual: String| {
        errors.push(ValidationError::ConstTypeMismatch {
            location: location(),
            expected,
            actual,
        });
    };
    match &layout.encoding {
        trust_ir::EnumTagEncoding::DirectWithUninhabited { .. } => {}
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
        trust_ir::EnumTagEncoding::Direct { tag_offset } => {
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
                            format!("descriptor align at least direct-tag alignment {tag_align}"),
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
                        if byte_ranges_overlap(*tag_offset, tag_size, *field_offset, field_size) {
                            push_layout_error(
                                "a direct tag disjoint from every non-ZST field".to_string(),
                                format!("tag overlaps variant {variant_index} field {field_index}"),
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
                                                niche_end
                                                    .is_some_and(|niche_end| field_end >= niche_end)
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
                        if byte_ranges_overlap(*niche_offset, niche_size, *field_offset, field_size)
                        {
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
                    None => {
                        "at most 340282366920938463463374607431768211456 distinct niche variants"
                            .to_string()
                    }
                };
                push_layout_error(
                    expected,
                    format!("niche interval {niche_variants_start}..={niche_variants_end}"),
                );
            }
        }
    }
    errors
}
