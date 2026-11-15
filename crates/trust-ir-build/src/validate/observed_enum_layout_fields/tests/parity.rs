// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;

#[test]
fn valid_fields_and_empty_lists_preserve_exact_empty_component_result() {
    let (m, mut e, mut d) = fixture();
    assert!(run(&m, &e, &d).0.is_empty());
    e.variants.clear();
    d.variant_field_offsets.clear();
    assert!(run(&m, &e, &d).0.is_empty());
    e.variants.push(variant("empty", vec![]));
    d.variant_field_offsets.push(vec![]);
    assert!(run(&m, &e, &d).0.is_empty());
}
#[test]
fn outer_count_is_single_error_before_any_field_or_pair_check() {
    let (m, mut e, mut d) = compact();
    d.variant_field_offsets.clear();
    let out = run(&m, &e, &d).0;
    assert_eq!(out.len(), 1);
    assert_eq!(parts(&out[0]).1, "1 per-variant offset lists");
    assert_eq!(parts(&out[0]).2, "0 offset lists");
    e.variants.clear();
    d.variant_field_offsets = vec![vec![], vec![]];
    assert_eq!(parts(&run(&m, &e, &d).0[0]).1, "0 per-variant offset lists");
}
#[test]
fn variant_count_keeps_full_name_and_continues_with_later_variant_checks() {
    let (m, mut e, mut d) = fixture();
    e.variants[0].name = "V\nλ'\"".into();
    e.variants.push(variant("later", vec![Ty::U64]));
    d.variant_field_offsets = vec![vec![], vec![1]];
    d.size = 0;
    d.align = 0;
    let out = run(&m, &e, &d).0;
    assert_eq!(out.len(), 4);
    assert_eq!(parts(&out[0]).1, "variant 0 (V\nλ'\"): 3 field offsets");
    assert!(parts(&out[1]).1.starts_with("variant 1 field 0 entirely"));
    assert!(parts(&out[2]).1.contains("offset aligned to 8"));
    assert!(
        parts(&out[3])
            .1
            .starts_with("descriptor align at least variant 1")
    );
}
#[test]
fn bounds_then_offset_alignment_then_descriptor_alignment_keep_original_order() {
    let (m, mut e, mut d) = compact();
    e.variants[0].fields = vec![Ty::U64];
    d.size = 2;
    d.align = 1;
    let out = run(&m, &e, &d).0;
    assert_eq!(out.len(), 3);
    assert_eq!(parts(&out[0]).1, "variant 0 field 0 entirely within size 2");
    assert_eq!(parts(&out[0]).2, "offset 1, field size 8");
    assert_eq!(
        parts(&out[1]).1,
        "variant 0 field 0 offset aligned to 8 bytes"
    );
    assert_eq!(
        parts(&out[2]).1,
        "descriptor align at least variant 0 field 0 alignment 8"
    );
}
#[test]
fn checked_field_end_overflow_is_outside_even_with_maximum_descriptor_size() {
    let (m, mut e, mut d) = compact();
    e.variants[0].fields = vec![Ty::U64];
    d.size = u64::MAX;
    d.align = 8;
    d.variant_field_offsets[0][0] = u64::MAX;
    let out = run(&m, &e, &d).0;
    assert_eq!(out.len(), 2);
    assert_eq!(
        parts(&out[0]).2,
        format!("offset {}, field size 8", u64::MAX)
    );
    assert!(parts(&out[1]).1.contains("offset aligned to 8"));
}
#[test]
fn spelling_only_zero_fields_at_end_are_allowed_but_past_end_are_not() {
    let (m, mut e, mut d) = fixture();
    e.variants[0].fields = vec![Ty::Unit, Ty::Tuple(vec![]), Ty::Array(TyId::new(99), 0)];
    d.size = 4;
    d.align = 1;
    d.variant_field_offsets = vec![vec![4, 4, 4]];
    assert!(run(&m, &e, &d).0.is_empty());
    d.variant_field_offsets[0] = vec![5, 5, 5];
    let out = run(&m, &e, &d).0;
    assert_eq!(out.len(), 3);
    assert!(parts(&out[2]).2.contains("layout UNRESOLVABLE"));
    assert!(parts(&out[2]).2.contains("ty.99"));
}
#[test]
fn missing_layout_is_reported_as_unresolvable_with_exact_type_and_reason() {
    let (m, mut e, mut d) = fixture();
    e.variants[0].fields = vec![
        Ty::Struct(StructId::new(99)),
        Ty::Tuple(vec![Ty::U64, Ty::U8]),
        Ty::Error,
    ];
    d.variant_field_offsets = vec![vec![0, 0, 0]];
    let out = run(&m, &e, &d).0;
    assert_eq!(out.len(), 3);
    for error in &out {
        assert!(parts(error).1.contains("resolvable layout"));
        assert!(parts(error).2.contains("layout UNRESOLVABLE"));
    }
    assert!(
        parts(&out[0])
            .2
            .ends_with("struct layout entry struct.99 is missing")
    );
}
#[test]
fn direct_never_is_alignment_free_but_never_derived_array_is_diagnosed() {
    let (mut m, mut e, mut d) = fixture();
    m.types = vec![Ty::Never];
    e.variants[0].fields = vec![Ty::Never, Ty::Array(TyId::new(0), 2)];
    d.variant_field_offsets = vec![vec![0, 0]];
    let out = run(&m, &e, &d).0;
    assert_eq!(out.len(), 1);
    assert_eq!(
        parts(&out[0]).1,
        "variant 0 field 1 to have a byte alignment (only a direct `!` field is alignment-free)"
    );
}
#[test]
fn zero_struct_resolution_never_broadens_the_missing_size_spelling_exception() {
    let (mut m, mut e, mut d) = compact();
    m.structs = vec![strukt(9, Some(0), Some(1), vec![])];
    let ty = Ty::Struct(StructId::new(9));
    e.variants[0].fields = vec![ty.clone()];
    d.variant_field_offsets[0][0] = 0;
    d.size = 0;
    d.align = 1;
    assert!(run(&m, &e, &d).0.is_empty());
    let mut observer = Observer::default();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    let mut work = Work {
        session: &mut session,
        site: site(),
    };
    assert!(!query::spelling_zero(&ty, &mut work).unwrap());
    assert!(!ty_is_zero_sized(&ty));
    m.structs[0].size = None;
    let out = run(&m, &e, &d).0;
    assert_eq!(out.len(), 1);
    assert!(parts(&out[0]).2.contains("UNRESOLVABLE"));
}
#[test]
fn every_pair_uses_physical_indices_and_canonical_left_right_order() {
    let (m, mut e, mut d) = fixture();
    e.variants[0].fields = vec![Ty::U64, Ty::Struct(StructId::new(99)), Ty::U64, Ty::U64];
    d.variant_field_offsets = vec![vec![0, 0, 0, 0]];
    let out = run(&m, &e, &d).0;
    assert_eq!(out.len(), 4);
    assert!(parts(&out[0]).2.contains("UNRESOLVABLE"));
    assert_eq!(
        parts(&out[1]).2,
        "fields 0 and 2 overlap at offsets 0 and 0"
    );
    assert_eq!(
        parts(&out[2]).2,
        "fields 0 and 3 overlap at offsets 0 and 0"
    );
    assert_eq!(
        parts(&out[3]).2,
        "fields 2 and 3 overlap at offsets 0 and 0"
    );
}
#[test]
fn pair_predicate_keeps_zero_and_overflow_rules_and_end_touch_is_disjoint() {
    let (m, mut e, mut d) = fixture();
    e.variants[0].fields = vec![Ty::U8, Ty::U8, Ty::Unit, Ty::U8];
    d.size = u64::MAX;
    d.align = 1;
    d.variant_field_offsets = vec![vec![0, 1, u64::MAX, u64::MAX]];
    let out = run(&m, &e, &d).0;
    assert_eq!(out.len(), 3); // overflowing final field, then (0,3) and (1,3).
    assert!(parts(&out[0]).1.contains("entirely within"));
    assert_eq!(
        parts(&out[1]).2,
        format!("fields 0 and 3 overlap at offsets 0 and {}", u64::MAX)
    );
    assert_eq!(
        parts(&out[2]).2,
        format!("fields 1 and 3 overlap at offsets 1 and {}", u64::MAX)
    );
    assert!(!byte_ranges_overlap(u64::MAX, 0, u64::MAX, 1));
    assert!(!byte_ranges_overlap(0, 1, 1, 1));
}
#[test]
fn declaration_encoding_and_global_layout_checks_are_outside_this_constituent() {
    let (m, mut e, mut d) = fixture();
    e.name.clear();
    e.discriminants = vec![Some(1), Some(1)];
    e.variants[0].name.clear();
    d.size = 17;
    d.align = 3;
    e.variants[0].fields = vec![];
    d.variant_field_offsets = vec![vec![]];
    for encoding in [
        EnumTagEncoding::Direct {
            tag_offset: u64::MAX,
        },
        EnumTagEncoding::Niche {
            untagged_variant: 99,
            niche_variants_start: 9,
            niche_variants_end: 0,
            niche_start: u128::MAX,
            niche_offset: u64::MAX,
            niche_ty: EnumTagRepr::I8,
        },
        EnumTagEncoding::Untagged,
    ] {
        d.encoding = encoding;
        assert!(run(&m, &e, &d).0.is_empty());
    }
}
#[test]
fn raw_unicode_names_and_full_unresolved_type_text_are_never_truncated_or_quoted() {
    let (m, mut e, mut d) = compact();
    e.name = "λ'\"\n".repeat(400);
    e.variants[0].fields = vec![Ty::Tuple(vec![Ty::U64; 400])];
    d.variant_field_offsets[0][0] = 0;
    let out = run(&m, &e, &d).0;
    assert_eq!(out.len(), 1);
    assert_eq!(parts(&out[0]).0, format!("enum.7 ({}) layout", e.name));
    assert!(
        parts(&out[0])
            .2
            .contains(&e.variants[0].fields[0].to_string())
    );
    assert!(parts(&out[0]).2.len() > 1600);
}
#[test]
fn unsupported_target_reason_keeps_entire_owned_triple_for_each_physical_field() {
    let (mut m, mut e, mut d) = compact();
    let triple = "unknown-λ'\"\n".repeat(400);
    m.target_info = Some(target(triple.clone()));
    e.variants[0].fields = vec![Ty::U64, Ty::U64];
    d.variant_field_offsets = vec![vec![0, 0]];
    let out = run(&m, &e, &d).0;
    assert_eq!(out.len(), 2);
    for error in out {
        assert!(parts(&error).2.contains(&format!("{triple:?}")));
    }
}
