// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
#[test]
fn empty_and_valid_descriptor_modules_match_the_full_original_block() {
    assert!(run(&Module::new("empty")).0.is_empty());
    assert!(run(&fixture()).0.is_empty());
}
#[test]
fn every_rows_declaration_prelude_fields_encoding_precede_the_next_duplicate_id() {
    let m = invalid();
    let out = run(&m).0;
    let duplicate = out
        .iter()
        .position(|e| matches!(e, ValidationError::DuplicateEnumId(7)))
        .unwrap();
    assert_eq!(duplicate, 4);
    assert_eq!(out.len(), 9);
    assert!(
        matches!(&out[0],ValidationError::ConstTypeMismatch {expected,..} if expected=="field_names empty or exactly 1 entries")
    );
    assert!(
        matches!(&out[1],ValidationError::ConstTypeMismatch {expected,..} if expected=="a non-zero power-of-two alignment")
    );
    assert!(
        matches!(&out[2],ValidationError::ConstTypeMismatch {expected,..} if expected=="variant 0 (Data): 1 field offsets")
    );
    assert!(
        matches!(&out[3],ValidationError::ConstTypeMismatch {expected,..} if expected=="exactly one variant under the untagged encoding")
    );
}
#[test]
fn absent_descriptor_keeps_declaration_errors_and_never_runs_a_layout_stage() {
    let mut m = invalid();
    for e in &mut m.enums {
        e.layout = None;
    }
    let out = run(&m).0;
    assert_eq!(out.len(), 3);
    assert!(matches!(out[1], ValidationError::DuplicateEnumId(7)));
}
#[test]
fn actual_field_errors_stay_between_lane_global_errors_and_direct_tag_overlap() {
    let mut m = fixture();
    let e = &mut m.enums[0];
    e.variants[0].fields = vec![Ty::U16, Ty::U16];
    let l = e.layout.as_mut().unwrap();
    l.encoding = EnumTagEncoding::Direct { tag_offset: 0 };
    l.variant_field_offsets[0] = vec![0, 0];
    l.align = 0;
    l.size = 1;
    run(&m);
}
#[test]
fn corrected_wide_niche_diagnostics_and_full_raw_names_survive_connected_composition() {
    let mut m = fixture();
    m.target_info = Some(trust_ir::TargetInfo {
        triple: "aarch64-unknown-linux-gnu".into(),
        pointer_size: 8,
        endianness: trust_ir::Endianness::Little,
        abi: None,
        struct_passing: Default::default(),
    });
    let e = &mut m.enums[0];
    e.name = "λ\n'".repeat(1000) + "TAIL";
    e.repr = Some(EnumTagRepr::U128);
    e.variants[0].fields = vec![Ty::U128];
    let l = e.layout.as_mut().unwrap();
    l.size = 16;
    l.align = 16;
    if let EnumTagEncoding::Niche {
        niche_ty,
        niche_variants_end,
        ..
    } = &mut l.encoding
    {
        *niche_ty = EnumTagRepr::U128;
        *niche_variants_end = 0;
    }
    let out = run(&m).0;
    assert_eq!(out.len(), 3);
    assert!(out.iter().all(|e|matches!(e,ValidationError::ConstTypeMismatch {location,..} if location.contains("TAIL"))));
}
#[test]
fn all_semantic_diagnostics_are_independent_of_later_input_mutation() {
    let mut m = invalid();
    let out = run(&m).0;
    let old = out.clone();
    m.enums.clear();
    assert_eq!(out, old);
}
