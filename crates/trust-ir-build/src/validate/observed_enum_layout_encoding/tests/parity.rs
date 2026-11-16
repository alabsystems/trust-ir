// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
#[test]
fn all_ten_lane_sizes_and_target_alignments_match_original_valid_niche_stages() {
    for repr in reprs() {
        let m = fixture(repr);
        assert!(run(&m, Stage::Prelude).0.is_empty());
        assert!(run(&m, Stage::Encoding).0.is_empty());
    }
}
#[test]
fn full_off_table_target_error_precedes_the_independent_global_alignment_error() {
    let mut m = fixture(EnumTagRepr::U128);
    let triple = "unsupported-λ".repeat(2000) + "TAIL";
    m.target_info = Some(target(&triple));
    m.enums[0].layout.as_mut().unwrap().align = 0;
    let out = run(&m, Stage::Prelude).0;
    assert_eq!(out.len(), 2);
    assert!(
        matches!(&out[0],ValidationError::EnumTagTargetScalarLayoutUnavailable {enum_id:9,triple:actual} if actual==&triple)
    );
    run(&m, Stage::Encoding);
}
#[test]
fn global_align_zero_nonpower_and_size_modulo_preserve_original_else_if() {
    let mut m = fixture(EnumTagRepr::U8);
    for (size, align) in [(0, 0), (31, 3), (31, 16), (32, 16)] {
        let l = m.enums[0].layout.as_mut().unwrap();
        l.size = size;
        l.align = align;
        let out = run(&m, Stage::Prelude).0;
        assert_eq!(
            out.len(),
            usize::from(align == 0 || !align.is_power_of_two() || !size.is_multiple_of(align))
        );
    }
}
#[test]
fn direct_alignment_bounds_and_field_overlap_keep_the_original_order_and_zip_prefix() {
    let mut m = fixture(EnumTagRepr::U16);
    m.enums[0].variants[0].fields.push(Ty::U8);
    let l = m.enums[0].layout.as_mut().unwrap();
    l.encoding = EnumTagEncoding::Direct { tag_offset: 1 };
    l.size = 2;
    l.align = 1;
    l.variant_field_offsets[0] = vec![0, 1];
    let out = run(&m, Stage::Encoding).0;
    assert_eq!(out.len(), 5);
    m.enums[0]
        .layout
        .as_mut()
        .unwrap()
        .variant_field_offsets
        .truncate(1);
    run(&m, Stage::Encoding);
    m.enums[0].layout.as_mut().unwrap().variant_field_offsets[0].pop();
    run(&m, Stage::Encoding);
}
#[test]
fn invalid_canonical_direct_repr_skips_lane_checks_without_turning_declaration_clean() {
    let mut m = fixture(EnumTagRepr::U8);
    m.enums[0].discriminants = vec![Some(256), Some(257)];
    m.enums[0].layout.as_mut().unwrap().encoding = EnumTagEncoding::Direct {
        tag_offset: u64::MAX,
    };
    assert!(run(&m, Stage::Prelude).0.is_empty());
    assert!(run(&m, Stage::Encoding).0.is_empty());
    assert!(m.enums[0].canonical_tag_repr().is_none());
}
#[test]
fn untagged_is_exactly_one_physical_variant_without_a_lane_authority_query() {
    let mut m = fixture(EnumTagRepr::U8);
    m.enums[0].layout.as_mut().unwrap().encoding = EnumTagEncoding::Untagged;
    m.target_info = Some(target("unsupported"));
    run(&m, Stage::Prelude);
    assert_eq!(run(&m, Stage::Encoding).0.len(), 1);
    m.enums[0].variants.truncate(1);
    assert!(run(&m, Stage::Encoding).0.is_empty());
    m.enums[0].variants.clear();
    assert_eq!(run(&m, Stage::Encoding).0.len(), 1);
}
#[test]
fn niche_coverage_uses_actual_least_fixpoint_and_reports_only_the_first_unencoded_variant() {
    let mut m = fixture(EnumTagRepr::U8);
    m.enums[0].variants.extend([
        variant("dead", vec![Ty::Never]),
        variant("firstλ", vec![]),
        variant("later", vec![]),
    ]);
    let out = run(&m, Stage::Encoding).0;
    assert_eq!(out.len(), 1);
    assert!(
        matches!(&out[0],ValidationError::ConstTypeMismatch {actual,..} if actual=="inhabited variant 3 (firstλ) is neither untagged 0 nor in niche interval 1..=1")
    );
    m.enums[0].variants[2].fields = vec![Ty::Enum(EnumId::new(9))];
    run(&m, Stage::Encoding);
}
#[test]
fn reversed_128_intervals_keep_all_refusals_and_exact_nonoverflowing_capacity() {
    for repr in [EnumTagRepr::U128, EnumTagRepr::I128] {
        let mut m = fixture(repr);
        if let EnumTagEncoding::Niche {
            niche_variants_end, ..
        } = &mut m.enums[0].layout.as_mut().unwrap().encoding
        {
            *niche_variants_end = 0;
        }
        let out = run(&m, Stage::Encoding).0;
        assert_eq!(out.len(), 3);
        assert!(
            matches!(&out[2],ValidationError::ConstTypeMismatch {expected,..} if expected=="at most 340282366920938463463374607431768211456 distinct niche variants")
        );
    }
}
#[test]
fn niche_lane_must_be_wholly_covered_and_disjoint_from_each_niched_non_zst_field() {
    let mut m = fixture(EnumTagRepr::U16);
    m.enums[0].variants[0].fields = vec![Ty::U8];
    m.enums[0].variants[1].fields = vec![Ty::U8, Ty::Unit];
    m.enums[0].layout.as_mut().unwrap().variant_field_offsets[1] = vec![0, 0];
    let out = run(&m, Stage::Encoding).0;
    assert_eq!(out.len(), 2);
    m.enums[0].layout.as_mut().unwrap().variant_field_offsets[0].clear();
    run(&m, Stage::Encoding);
}
#[test]
fn scalar_start_span_and_full_u128_decimal_keep_unsigned_niche_capacity_rules() {
    let mut m = fixture(EnumTagRepr::U8);
    m.enums[0]
        .variants
        .extend((2..258).map(|i| variant(&format!("N{i}"), vec![])));
    m.enums[0]
        .layout
        .as_mut()
        .unwrap()
        .variant_field_offsets
        .resize(258, vec![]);
    if let EnumTagEncoding::Niche {
        niche_variants_end,
        niche_start,
        ..
    } = &mut m.enums[0].layout.as_mut().unwrap().encoding
    {
        *niche_variants_end = 257;
        *niche_start = u128::MAX;
    }
    let out = run(&m, Stage::Encoding).0;
    assert_eq!(out.len(), 2);
    assert!(
        matches!(&out[0],ValidationError::ConstTypeMismatch {actual,..} if actual==&format!("niche_start {}",u128::MAX))
    );
}
#[test]
fn unresolved_field_sizes_and_overflowing_ranges_keep_original_noninvented_bounds() {
    let mut m = fixture(EnumTagRepr::U8);
    m.enums[0].variants[0].fields = vec![Ty::Struct(StructId::new(999)), Ty::Unit];
    let l = m.enums[0].layout.as_mut().unwrap();
    l.encoding = EnumTagEncoding::Direct {
        tag_offset: u64::MAX,
    };
    l.variant_field_offsets[0] = vec![u64::MAX, u64::MAX];
    let out = run(&m, Stage::Encoding).0;
    assert_eq!(out.len(), 1);
    m.enums[0].variants[0].fields[0] = Ty::U8;
    assert_eq!(run(&m, Stage::Encoding).0.len(), 2);
}
#[test]
fn raw_enum_variant_names_and_opaque_metadata_are_not_normalized_or_newly_walked() {
    let mut m = fixture(EnumTagRepr::U8);
    m.enums[0]
        .variants
        .push(variant("λ\n'".repeat(1000).as_str(), vec![]));
    let (_, before) = run(&m, Stage::Encoding);
    m.enums[0].variants[0].field_names = vec!["opaque".repeat(10000)];
    m.enums[0]
        .discriminants
        .extend([None, None, Some(i128::MAX)]);
    let (_, after) = run(&m, Stage::Encoding);
    assert_eq!(before.events, after.events);
}

#[test]
fn actual_observed_prelude_alignment_matches_all_reprs_and_drives_encoding_checks() {
    for repr in reprs() {
        for off in [false, true] {
            let mut m = fixture(repr);
            if off {
                m.target_info = Some(target("unsupported-actual-alignment"));
            }
            // Actual malformed lane offset makes the returned alignment's use
            // observable for every multi-byte repr; scalar size remains fixed.
            if let EnumTagEncoding::Niche { niche_offset, .. } =
                &mut m.enums[0].layout.as_mut().unwrap().encoding
            {
                *niche_offset = 1;
            }
            let e = &m.enums[0];
            let l = e.layout.as_ref().unwrap();
            let (expected, expected_align) = original::prelude(&m, e, l);
            let mut o = Observer::default();
            let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
            let (pre, actual_align) =
                validate_enum_layout_prelude_observed(&m, e, l, &mut s, site()).unwrap();
            assert_eq!(pre, expected);
            assert_eq!(actual_align, expected_align);
            assert_eq!(
                actual_align,
                if off { None } else { Some(repr.size_bytes()) }
            );
            let encoded =
                validate_enum_layout_encoding_observed(&m, e, l, actual_align, &mut s, site())
                    .unwrap();
            assert_eq!(encoded, original::encoding(&m, e, l, expected_align));
            let lane_error=encoded.iter().any(|error|matches!(error,ValidationError::ConstTypeMismatch {expected,..} if expected.starts_with("a niche lane aligned to ")));
            assert_eq!(lane_error, !off && repr.size_bytes() > 1);
            assert!(s.first_refusal().is_none());
            assert_eq!(s.remaining_fuel(), InterpretOptions::default().fuel);
            assert!(o.events.iter().all(|event| event.site == site()));
        }
    }
}

#[test]
fn single_encoding_current_policy_and_semantic_refusals_match_the_ordinary_oracle() {
    let m = strict_single_fixture();
    assert!(m.layout_table().enum_layout(EnumId::new(9)).is_ok());
    assert!(run(&m, Stage::Prelude).0.is_empty());
    assert!(run(&m, Stage::Encoding).0.is_empty());

    // Root's affirmed policy permits one declared inhabited row as well.
    let mut one = strict_single_fixture();
    one.enums[0].variants.remove(0);
    one.enums[0].discriminants = vec![Some(17)];
    let layout = one.enums[0].layout.as_mut().unwrap();
    layout.encoding = EnumTagEncoding::SingleInhabited { variant: 0 };
    layout.variant_field_offsets = vec![vec![0]];
    assert!(one.layout_table().enum_layout(EnumId::new(9)).is_ok());
    assert!(run(&one, Stage::Encoding).0.is_empty());

    for which in 0..4 {
        let mut bad = strict_single_fixture();
        match which {
            0 => {
                bad.enums[0].layout.as_mut().unwrap().encoding =
                    EnumTagEncoding::SingleInhabited { variant: 2 }
            }
            1 => bad.enums[0].variants[0].fields = vec![Ty::U8],
            2 => bad.enums[0].variants[1].fields = vec![Ty::Never],
            3 => bad.enums[0].variants[0].fields = vec![Ty::Struct(StructId::new(999))],
            _ => unreachable!(),
        }
        assert!(bad.layout_table().enum_layout(EnumId::new(9)).is_err());
        let errors = run(&bad, Stage::Encoding).0;
        assert!(matches!(
            &errors[..],
            [ValidationError::ConstTypeMismatch { expected, actual, .. }]
                if expected == "one selected inhabited variant and only structurally uninhabited inactive variants"
                    && actual == if which == 0 { "single-inhabited selector 2" }
                        else { "single-inhabited selector 1" }
        ));
    }
}
