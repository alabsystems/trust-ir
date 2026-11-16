// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Retained ordinary field block with explicit version66 profile validation;
//! scoped as a diagnostic-only oracle.
use super::*;
pub(super) fn run(
    module: &Module,
    enm: &EnumDef,
    layout: &EnumLayoutDescriptor,
) -> Vec<ValidationError> {
    let layouts = module.layout_table();
    let mut errors = Vec::new();
    let location = || format!("enum.{} ({}) layout", enm.id.index(), enm.name);
    if matches!(
        &layout.encoding,
        trust_ir::EnumTagEncoding::DirectWithUninhabited { .. }
    ) {
        let bound = module
            .enums
            .iter()
            .find(|row| row.id == enm.id)
            .is_some_and(|row| core::ptr::eq(row, enm))
            && enm
                .layout
                .as_ref()
                .is_some_and(|actual| core::ptr::eq(actual, layout));
        if !bound || layouts.enum_layout(enm.id).is_err() {
            errors.push(ValidationError::ConstTypeMismatch {
                location: location(),
                expected: "a valid Direct storage profile for exactly the uninhabited variants"
                    .into(),
                actual: "invalid Direct uninhabited storage".into(),
            });
        }
        return errors;
    }
    let mut push_layout_error = |expected: String, actual: String| {
        errors.push(ValidationError::ConstTypeMismatch {
            location: location(),
            expected,
            actual,
        })
    };
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
            for (field_index, (field_ty, offset)) in variant.fields.iter().zip(offsets).enumerate()
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

    errors
}
