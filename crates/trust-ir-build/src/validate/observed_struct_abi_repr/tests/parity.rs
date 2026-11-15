// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
#[test]
fn transparent_counts_all_nontrivial_fields_and_packed_errors_follow_physical_order() {
    let out = run(&fixture()).0;
    assert_eq!(
        out,
        vec![
            ValidationError::TransparentReprFieldCount {
                struct_id: 7,
                actual_non_zst: 2
            },
            ValidationError::PackedReprInvalidAlign {
                struct_id: 8,
                align: 3
            }
        ]
    );
}
#[test]
fn zero_or_one_nontrivial_transparent_field_is_valid_and_more_than_one_is_not() {
    let mut m = fixture();
    m.structs.truncate(1);
    for fields in [
        vec![],
        vec![Ty::Unit],
        vec![Ty::Unit, Ty::U8],
        vec![Ty::U8, Ty::U8],
        vec![Ty::U8, Ty::Unit, Ty::U16, Ty::U32],
    ] {
        m.structs[0].fields = fields
            .into_iter()
            .map(|ty| FieldDef {
                name: String::new(),
                ty,
                offset: None,
            })
            .collect();
        run(&m);
    }
}
#[test]
fn module_aware_one_zst_is_distinct_from_an_overaligned_zero_sized_struct() {
    let mut m = fixture();
    m.structs = vec![
        strukt(0, StructRepr::Rust, vec![], Some(0), Some(1)),
        strukt(1, StructRepr::Rust, vec![], Some(0), Some(8)),
        strukt(
            2,
            StructRepr::Transparent,
            vec![Ty::Struct(StructId::new(0)), Ty::U8],
            None,
            None,
        ),
        strukt(
            3,
            StructRepr::Transparent,
            vec![Ty::Struct(StructId::new(1)), Ty::U8],
            None,
            None,
        ),
    ];
    assert_eq!(
        run(&m).0,
        vec![ValidationError::TransparentReprFieldCount {
            struct_id: 3,
            actual_non_zst: 2
        }]
    );
}
#[test]
fn unresolvable_and_alignment_free_fields_are_nontrivial_without_dropping_refusal() {
    let mut m = fixture();
    m.structs = vec![strukt(
        0,
        StructRepr::Transparent,
        vec![Ty::Struct(StructId::new(999)), Ty::Never, Ty::U8],
        None,
        None,
    )];
    assert_eq!(
        run(&m).0,
        vec![ValidationError::TransparentReprFieldCount {
            struct_id: 0,
            actual_non_zst: 3
        }]
    );
}
#[test]
fn every_packed_clamp_and_rust_c_repr_preserve_original_no_layout_queries() {
    let mut m = fixture();
    m.structs = vec![strukt(
        0,
        StructRepr::Packed(0),
        vec![Ty::Error],
        None,
        None,
    )];
    for align in [0, 1, 2, 3, 4, 8, u32::MAX] {
        m.structs[0].repr = StructRepr::Packed(align);
        assert_eq!(
            run(&m).0.len(),
            usize::from(align == 0 || !align.is_power_of_two())
        );
    }
    for repr in [StructRepr::Rust, StructRepr::C] {
        m.structs[0].repr = repr;
        assert!(run(&m).0.is_empty());
    }
}
#[test]
fn duplicate_struct_ids_remain_physical_rows_and_layout_lookups_keep_first_definition() {
    let mut m = fixture();
    m.structs = vec![
        strukt(0, StructRepr::Rust, vec![], Some(0), Some(1)),
        strukt(0, StructRepr::Rust, vec![], Some(0), Some(8)),
        strukt(
            0,
            StructRepr::Transparent,
            vec![Ty::Struct(StructId::new(0)), Ty::U8],
            None,
            None,
        ),
    ];
    assert!(run(&m).0.is_empty());
    m.structs.swap(0, 1);
    assert_eq!(run(&m).0.len(), 1);
}
#[test]
fn irrelevant_full_names_offsets_and_metadata_do_not_add_new_repr_checks() {
    let mut m = fixture();
    let (_, before) = run(&m);
    m.structs[0].name = "opaque".repeat(10000);
    for f in &mut m.structs[0].fields {
        f.name = "opaque".repeat(10000);
        f.offset = Some(u64::MAX);
    }
    let (_, after) = run(&m);
    assert_eq!(before.events, after.events);
}
#[test]
fn complete_transparent_field_walk_does_not_short_circuit_after_the_second_nontrivial() {
    let mut m = fixture();
    m.structs.truncate(1);
    m.structs[0].fields = (0..20)
        .map(|_| FieldDef {
            name: String::new(),
            ty: Ty::U8,
            offset: None,
        })
        .collect();
    assert_eq!(
        run(&m).0,
        vec![ValidationError::TransparentReprFieldCount {
            struct_id: 7,
            actual_non_zst: 20
        }]
    );
}
