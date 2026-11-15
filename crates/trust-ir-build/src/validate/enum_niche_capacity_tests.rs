// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Authored UNRUN regressions for the actual ordinary validator diagnostic.
use super::*;
use trust_ir::ty::{EnumDef, EnumLayoutDescriptor, EnumTagEncoding, EnumTagRepr, EnumVariant};
use trust_ir::value::EnumId;
fn fixture(repr: EnumTagRepr, reversed: bool) -> Module {
    let mut module = Module::new("niche-capacity");
    module.target_info = Some(trust_ir::TargetInfo {
        triple: "aarch64-unknown-linux-gnu".into(),
        pointer_size: 8,
        endianness: trust_ir::Endianness::Little,
        abi: None,
        struct_passing: Default::default(),
    });
    let mut enm = EnumDef::new(
        EnumId::new(0),
        "E",
        vec![
            EnumVariant {
                name: "Data".into(),
                fields: vec![repr.ty()],
                field_names: vec![],
            },
            EnumVariant {
                name: "Empty".into(),
                fields: vec![],
                field_names: vec![],
            },
        ],
    );
    enm.repr = Some(repr);
    enm.layout = Some(EnumLayoutDescriptor {
        encoding: EnumTagEncoding::Niche {
            untagged_variant: 0,
            niche_variants_start: 1,
            niche_variants_end: if reversed { 0 } else { 1 },
            niche_start: 0,
            niche_offset: 0,
            niche_ty: repr,
        },
        size: repr.size_bytes(),
        align: repr.size_bytes(),
        variant_field_offsets: vec![vec![0], vec![]],
    });
    module.enums.push(enm);
    module
}
fn capacity_error(errors: &[ValidationError], expected: &str) -> bool {
    errors.iter().any(|e| matches!(e, ValidationError::ConstTypeMismatch {
        location, expected: actual_expected, actual,
    } if location == "enum.0 (E) layout" && actual_expected == expected && actual == "niche interval 1..=0"))
}
#[test]
fn reversed_unsigned_128_niche_is_a_full_rejection_instead_of_a_formatting_panic() {
    let errors = validate_module(&fixture(EnumTagRepr::U128, true));
    assert!(capacity_error(
        &errors,
        "at most 340282366920938463463374607431768211456 distinct niche variants"
    ));
    assert!(errors.iter().any(
        |e| matches!(e, ValidationError::ConstTypeMismatch {expected,..}
        if expected == "an ordered, in-range niche variant interval")
    ));
    assert!(errors.iter().any(|e| matches!(e, ValidationError::ConstTypeMismatch {expected,..}
        if expected == "the niche interval plus the untagged variant to cover every inhabited variant")));
}
#[test]
fn reversed_signed_128_niche_keeps_the_same_mathematical_capacity_and_refusal() {
    let errors = validate_module(&fixture(EnumTagRepr::I128, true));
    assert!(capacity_error(
        &errors,
        "at most 340282366920938463463374607431768211456 distinct niche variants"
    ));
}
#[test]
fn smaller_lane_rejection_messages_are_byte_identical_for_both_signednesses() {
    for (repr, expected) in [
        (EnumTagRepr::U8, "at most 256 distinct niche variants"),
        (EnumTagRepr::I8, "at most 256 distinct niche variants"),
        (EnumTagRepr::U16, "at most 65536 distinct niche variants"),
        (EnumTagRepr::I16, "at most 65536 distinct niche variants"),
        (
            EnumTagRepr::U32,
            "at most 4294967296 distinct niche variants",
        ),
        (
            EnumTagRepr::I32,
            "at most 4294967296 distinct niche variants",
        ),
        (
            EnumTagRepr::U64,
            "at most 18446744073709551616 distinct niche variants",
        ),
        (
            EnumTagRepr::I64,
            "at most 18446744073709551616 distinct niche variants",
        ),
    ] {
        let errors = validate_module(&fixture(repr, true));
        assert!(capacity_error(&errors, expected));
    }
}
#[test]
fn ordered_valid_niche_twins_still_validate_for_every_lane_width_and_signedness() {
    for repr in [
        EnumTagRepr::U8,
        EnumTagRepr::I8,
        EnumTagRepr::U16,
        EnumTagRepr::I16,
        EnumTagRepr::U32,
        EnumTagRepr::I32,
        EnumTagRepr::U64,
        EnumTagRepr::I64,
        EnumTagRepr::U128,
        EnumTagRepr::I128,
    ] {
        assert!(validate_module(&fixture(repr, false)).is_empty());
    }
}
