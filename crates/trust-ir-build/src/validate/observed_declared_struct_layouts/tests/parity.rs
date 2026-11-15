// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
#[test]
fn valid_reordered_fields_and_trailing_scalar_and_struct_zsts_match_original() {
    let mut m = fixtures::valid();
    assert!(run(&m, &[]).0.is_empty());
    m.structs[0].fields.swap(0, 1);
    assert!(run(&m, &[]).0.is_empty());
    m.structs[0].fields[2].ty = Ty::Struct(StructId::new(1));
    assert!(run(&m, &[]).0.is_empty());
}
#[test]
fn scalar_alignment_size_offset_and_overlap_reasons_keep_original_stage_order() {
    let m = fixtures::invalid();
    let out = run(&m, &[]).0;
    assert_eq!(
        out,
        vec![
            ValidationError::StructLayoutInconsistent {
                struct_id: 0,
                reason: STRUCT_FIELDS_OVERLAP_REASON
            },
            ValidationError::StructLayoutInconsistent {
                struct_id: 1,
                reason: "align must be a non-zero power of two"
            }
        ]
    );
    for case in 0..5 {
        let mut m = fixtures::valid();
        match case {
            0 => m.structs[0].align = Some(3),
            1 => m.structs[0].size = Some(15),
            2 => m.structs[0].fields[0].offset = Some(17),
            3 => m.structs[0].fields[0].offset = Some(3),
            4 => m.structs[0].fields[0].offset = Some(16),
            _ => unreachable!(),
        }
        assert!(!run(&m, &[]).0.is_empty());
    }
}
#[test]
fn partial_missing_offsets_or_size_and_align_keep_original_nontightening() {
    let mut m = fixtures::valid();
    m.structs[0].fields[0].offset = None;
    assert!(run(&m, &[]).0.is_empty());
    for (size, align) in [(None, None), (None, Some(8)), (Some(16), None)] {
        m.structs[0].size = size;
        m.structs[0].align = align;
        run(&m, &[]);
    }
}
#[test]
fn generic_containment_and_transparent_defects_have_exact_prior_suppression() {
    let mut m = Module::new("generic");
    m.structs.push(fixtures::strukt(
        0,
        Some(8),
        Some(8),
        vec![fixtures::field("wide", Ty::U128, Some(0))],
    ));
    assert_eq!(
        run(&m, &[]).0,
        vec![ValidationError::StructLayoutInconsistent {
            struct_id: 0,
            reason: STRUCT_LAYOUT_INCOHERENT_REASON
        }]
    );
    m = fixtures::valid();
    m.structs[0].repr = trust_ir::StructRepr::Transparent;
    assert!(!run(&m, &[]).0.is_empty());
    let prior = vec![ValidationError::TransparentReprFieldCount {
        struct_id: 0,
        actual_non_zst: 2,
    }];
    assert!(run(&m, &prior).0.is_empty());
}
#[test]
fn packed_clamps_and_invalid_clamp_prior_follow_original_independent_rules() {
    for clamp in [0, 1, 2, 3, 8, 16] {
        let mut m = fixtures::valid();
        m.structs[0].repr = trust_ir::StructRepr::Packed(clamp);
        run(&m, &[]);
        run(
            &m,
            &[ValidationError::PackedReprInvalidAlign {
                struct_id: 0,
                align: clamp,
            }],
        );
    }
    let mut m = fixtures::valid();
    m.structs[0].repr = trust_ir::StructRepr::Packed(2);
    assert_eq!(
        run(&m, &[]).0,
        vec![ValidationError::StructLayoutInconsistent {
            struct_id: 0,
            reason: "struct alignment exceeds the repr(packed) clamp"
        }]
    );
}
#[test]
fn same_id_generic_rows_are_not_suppressed_by_newly_added_generic_errors() {
    let mut m = Module::new("duplicate");
    let row = fixtures::strukt(
        0,
        Some(8),
        Some(8),
        vec![fixtures::field("wide", Ty::U128, Some(0))],
    );
    m.structs = vec![row.clone(), row];
    let out = run(&m, &[]).0;
    assert_eq!(out.len(), 2);
    assert!(out.iter().all(|e| matches!(
        e,
        ValidationError::StructLayoutInconsistent {
            struct_id: 0,
            reason: STRUCT_LAYOUT_INCOHERENT_REASON
        }
    )));
}
#[test]
fn offcanonical_target_owned_triple_is_full_and_missing_defs_remain_original_refusals() {
    let mut m = fixtures::valid();
    let triple = "custom-'λ\n".repeat(1000);
    m.target_info = Some(fixtures::target(triple.clone()));
    let out = run(&m, &[]).0;
    assert!(out.iter().any(|e|matches!(e,ValidationError::TargetScalarLayoutUnavailable{triple:actual,..} if actual==&triple)));
    m.target_info = None;
    m.structs[0].fields[0].ty = Ty::Struct(StructId::new(999));
    run(&m, &[]);
}
#[test]
fn overflow_and_zero_byte_ranges_use_exact_shared_pair_predicate() {
    for second in [false, true] {
        let mut m = Module::new("overflow");
        let mut fields = vec![
            fixtures::field("overflow", Ty::U64, Some(u64::MAX - 7)),
            fixtures::field("zero", Ty::Unit, Some(0)),
        ];
        if second {
            fields.push(fixtures::field("other", Ty::U8, Some(0)));
        }
        m.structs = vec![fixtures::strukt(0, Some(u64::MAX), Some(1), fields)];
        let out = run(&m, &[]).0;
        if second {
            assert!(out.iter().any(|e| matches!(
                e,
                ValidationError::StructLayoutInconsistent {
                    reason: STRUCT_FIELDS_OVERLAP_REASON,
                    ..
                }
            )));
        }
    }
}
#[test]
fn suppression_uses_only_original_four_scoped_errors_and_ignores_owned_text_payloads() {
    let mut m = Module::new("prior");
    m.structs.push(fixtures::strukt(
        0,
        Some(8),
        Some(8),
        vec![fixtures::field("wide", Ty::U128, Some(0))],
    ));
    for prior in [
        ValidationError::StructLayoutInconsistent {
            struct_id: 0,
            reason: "old",
        },
        ValidationError::TargetScalarLayoutUnavailable {
            struct_id: 0,
            triple: "opaque".repeat(10000),
        },
        ValidationError::PackedReprInvalidAlign {
            struct_id: 0,
            align: 3,
        },
        ValidationError::TransparentReprFieldCount {
            struct_id: 0,
            actual_non_zst: 2,
        },
    ] {
        assert!(run(&m, &[prior]).0.is_empty());
    }
    assert_eq!(run(&m, &[ValidationError::DuplicateStructId(0)]).0.len(), 1);
}
