// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
#[test]
fn exact_overlap_disjoint_offsets_and_raw_diagnostic_fields_match_original_rule() {
    let mut m = fixture();
    let out = run(&m).0;
    assert!(
        matches!(&out[..],[ValidationError::HandleLaneNiche{enum_name,variant:0,field:1,detail}] if enum_name=="raw enum λ'\0" && detail.starts_with("niche lane at offset 0 (1 byte(s)) vs `handle<")&&detail.ends_with("` at offset 0"))
    );
    m.enums[0].layout.as_mut().unwrap().variant_field_offsets[0][1] = 8;
    assert!(run(&m).0.is_empty());
}
#[test]
fn all_tag_widths_u64_offsets_overflow_and_zero_extent_keep_exact_range_predicate() {
    let mut m = fixture();
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
        if let EnumTagEncoding::Niche { niche_ty, .. } =
            &mut m.enums[0].layout.as_mut().unwrap().encoding
        {
            *niche_ty = repr;
        }
        assert_eq!(run(&m).0.len(), 1);
    }
    m.enums[0].layout.as_mut().unwrap().variant_field_offsets[0][1] = u64::MAX;
    assert_eq!(run(&m).0.len(), 1);
    m.types = vec![handle()];
    m.enums[0].variants[0].fields[1] = Ty::Array(TyId::new(0), 0);
    assert!(run(&m).0.is_empty());
}
#[test]
fn absent_direct_untagged_and_mismatched_zipped_descriptor_rows_keep_original_skips() {
    let mut m = fixture();
    m.enums[0].layout = None;
    assert!(run(&m).0.is_empty());
    let mut e = fixture().enums.remove(0);
    e.layout.as_mut().unwrap().encoding = EnumTagEncoding::Direct { tag_offset: 0 };
    m.enums = vec![e.clone()];
    assert!(run(&m).0.is_empty());
    e.layout.as_mut().unwrap().encoding = EnumTagEncoding::Untagged;
    m.enums = vec![e];
    assert!(run(&m).0.is_empty());
    m = fixture();
    m.enums[0].layout.as_mut().unwrap().variant_field_offsets[0].pop();
    assert!(run(&m).0.is_empty());
    m.enums[0]
        .layout
        .as_mut()
        .unwrap()
        .variant_field_offsets
        .clear();
    assert!(run(&m).0.is_empty());
}
#[test]
fn semantic_unavailable_handle_reaching_field_remains_conservatively_refused_not_silently_skipped()
{
    let mut m = fixture();
    m.enums[0].variants[0].fields[1] = semantic_ty();
    let old = LayoutTable::new(&m);
    assert!(old.ty_layout(&semantic_ty()).is_err());
    assert_eq!(run(&m).0.len(), 1);
}
#[test]
fn repeated_off_index_enum_definitions_and_variants_are_all_reported_in_physical_order() {
    let mut m = fixture();
    let mut e = m.enums[0].clone();
    e.name = "second raw\0尾".into();
    e.variants.push(e.variants[0].clone());
    e.layout
        .as_mut()
        .unwrap()
        .variant_field_offsets
        .push(vec![16, 0]);
    m.enums.push(e);
    let out = run(&m).0;
    assert_eq!(out.len(), 3);
    assert!(
        matches!(&out[1],ValidationError::HandleLaneNiche{enum_name,variant:0,field:1,..}if enum_name=="second raw\0尾")
    );
    assert!(matches!(
        out[2],
        ValidationError::HandleLaneNiche {
            variant: 1,
            field: 1,
            ..
        }
    ));
}
#[test]
fn actual_target_pointer_extent_changes_overlap_without_assuming_a_host_width() {
    let mut m = fixture();
    if let EnumTagEncoding::Niche { niche_offset, .. } =
        &mut m.enums[0].layout.as_mut().unwrap().encoding
    {
        *niche_offset = 4;
    }
    for (triple, pointer_size, count) in [
        ("wasm32-unknown-unknown", 4, 0),
        ("aarch64-unknown-linux-gnu", 8, 1),
    ] {
        m.target_info = Some(trust_ir::TargetInfo {
            triple: triple.into(),
            pointer_size,
            endianness: trust_ir::Endianness::Little,
            abi: None,
            struct_passing: Default::default(),
        });
        assert_eq!(run(&m).0.len(), count);
    }
}
#[test]
fn skipped_rows_do_not_read_names_variant_metadata_offsets_or_unrelated_input_payloads() {
    let mut m = fixture();
    m.enums[0].layout = None;
    let (_, a, begin, end) = run(&m);
    m.enums[0].name = "unread λ\0".repeat(4096);
    m.enums[0].variants[0].name = "unread variant".repeat(4096);
    m.enums[0].variants[0].field_names = vec!["unread field".repeat(4096); 2];
    let (_, b, start, stop) = run(&m);
    assert_eq!(&a.events[begin..end], &b.events[start..stop]);
}
