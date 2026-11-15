// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
#[test]
fn actual_struct_record_tuple_and_closure_register_fields_match_without_layout_claim() {
    let m = fixture();
    for value in 0..4 {
        assert!(run(&m, &extract(value, 0, Ty::Bool)).0.is_empty());
        assert!(run(&m, &extract(value, 1, Ty::U64)).0.is_empty());
    }
}
#[test]
fn every_register_carrier_checks_exact_inserted_value_and_declared_extracted_type() {
    let m = fixture();
    for (value, ty) in [
        (0, Ty::Struct(StructId::new(0))),
        (1, Ty::Record(RecordId::new(0))),
        (2, Ty::Tuple(vec![Ty::Bool, Ty::U64])),
        (3, Ty::Closure(ClosureTyId::new(0))),
    ] {
        assert!(run(&m, &insert(value, 0, ty.clone(), 5)).0.is_empty());
        assert!(
            matches!(&run(&m,&insert(value,0,ty,6)).0[..],[ValidationError::OperandTypeMismatch {role,..}]if role=="value")
        );
        assert!(
            matches!(&run(&m,&extract(value,0,Ty::U64)).0[..],[ValidationError::OperandTypeMismatch {role,..}]if role=="field")
        );
    }
}
#[test]
fn wrong_insert_result_is_reported_before_out_of_range_and_unsupported_carrier() {
    let m = fixture();
    for inst in [insert(0, u32::MAX, Ty::U64, 5), insert(5, 0, Ty::U64, 5)] {
        let e = run(&m, &inst).0;
        assert_eq!(e.len(), 2);
        assert!(matches!(&e[0],ValidationError::OperandTypeMismatch {role,..}if role=="result"));
        assert!(matches!(e[1], ValidationError::FieldAccessInvalid { .. }));
    }
}
#[test]
fn missing_nominal_definitions_and_closure_ids_refuse_but_unknown_aggregate_skips() {
    let mut m = fixture();
    m.structs.clear();
    m.records.clear();
    m.enums.clear();
    m.closure_types.clear();
    for aggregate in [0, 1, 3, 4] {
        assert!(matches!(
            &run(&m, &extract(aggregate, 0, Ty::Bool)).0[..],
            [ValidationError::FieldAccessInvalid { .. }]
        ));
    }
    assert!(run(&m, &extract(999, 0, Ty::Bool)).0.is_empty());
}
#[test]
fn struct_fast_index_beats_earlier_duplicate_and_off_index_fallback_is_first_physical() {
    let mut m = fixture();
    m.structs = vec![structure(1, vec![Ty::U64]), structure(1, vec![Ty::Bool])];
    m.functions[0].blocks[0].params[0].1 = Ty::Struct(StructId::new(1));
    assert!(run(&m, &extract(0, 0, Ty::Bool)).0.is_empty());
    m.structs[0].id = StructId::new(77);
    m.structs[1].id = StructId::new(77);
    m.functions[0].blocks[0].params[0].1 = Ty::Struct(StructId::new(77));
    assert!(run(&m, &extract(0, 0, Ty::U64)).0.is_empty());
}
#[test]
fn record_and_enum_off_index_declared_ids_preserve_actual_fallback_semantics() {
    let mut m = fixture();
    m.records[0].id = RecordId::new(77);
    m.enums[0].id = EnumId::new(88);
    m.functions[0].blocks[0].params[1].1 = Ty::Record(RecordId::new(77));
    m.functions[0].blocks[0].params[4].1 = Ty::Enum(EnumId::new(88));
    assert!(run(&m, &extract(1, 0, Ty::Bool)).0.is_empty());
    assert!(run(&m, &extract(4, 1, Ty::U64)).0.is_empty());
}
#[test]
fn top_refinement_defers_lane_reads_writes_but_never_the_insert_result_contract() {
    let m = fixture();
    assert!(
        run(&m, &extract(0, 0, Ty::Refine(TyId::new(0), PredId::new(0))))
            .0
            .is_empty()
    );
    assert!(
        run(&m, &insert(0, 0, Ty::Struct(StructId::new(0)), 7))
            .0
            .is_empty()
    );
    let e = run(
        &m,
        &insert(0, 0, Ty::Refine(TyId::new(0), PredId::new(0)), 5),
    )
    .0;
    assert!(matches!(&e[..],[ValidationError::OperandTypeMismatch {role,..}]if role=="result"));
}
#[test]
fn enum_tag_reads_exact_canonical_type_and_tag_write_is_always_refused() {
    let m = fixture();
    assert!(run(&m, &extract(4, 0, Ty::U8)).0.is_empty());
    assert!(matches!(
        &run(&m, &extract(4, 0, Ty::U64)).0[..],
        [ValidationError::OperandTypeMismatch { .. }]
    ));
    assert!(matches!(
        &run(&m, &insert(4, 0, Ty::Enum(EnumId::new(0)), 5)).0[..],
        [ValidationError::FieldAccessInvalid { .. }]
    ));
}
#[test]
fn enum_later_candidate_can_match_but_complete_mismatch_lists_all_original_lanes() {
    let m = fixture();
    assert!(run(&m, &extract(4, 1, Ty::U64)).0.is_empty());
    let e = run(&m, &extract(4, 1, Ty::Ptr)).0;
    let ValidationError::OperandTypeMismatch { expected, .. } = &e[0] else {
        panic!()
    };
    assert_eq!(expected, "one of {A: bool, B: u64}");
}
#[test]
fn empty_or_malformed_enum_has_no_tag_and_no_projection_permission() {
    for malformed in [false, true] {
        let mut m = fixture();
        if malformed {
            m.enums[0].discriminants = vec![Some(1), Some(1)]
        } else {
            m.enums[0].variants.clear()
        };
        let e = run(&m, &extract(4, 1, Ty::Bool)).0;
        assert!(
            matches!(&e[..],[ValidationError::FieldAccessInvalid {reason,..}]if reason.contains("no canonical tag repr"))
        );
    }
}
#[test]
fn missing_enum_payload_lane_reports_actual_widest_without_materializing_field_index() {
    let m = fixture();
    let e = run(&m, &extract(4, u32::MAX, Ty::Bool)).0;
    assert!(
        matches!(&e[..],[ValidationError::FieldAccessInvalid {reason,..}]if reason.contains("4294967295")&&reason.contains("widest variant has 1 field(s)"))
    );
}
#[test]
fn enum_any_refinement_candidate_uses_original_consumption_defer() {
    let mut m = fixture();
    m.enums[0].variants[0].fields[0] = Ty::Refine(TyId::new(0), PredId::new(0));
    assert!(run(&m, &extract(4, 1, Ty::Ptr)).0.is_empty());
    assert!(
        run(&m, &insert(4, 1, Ty::Enum(EnumId::new(0)), 8))
            .0
            .is_empty()
    );
}
#[test]
fn explicit_wide_signed_tag_uses_actual_repr_without_layout_or_machine_claim() {
    let mut m = fixture();
    m.enums[0].repr = Some(EnumTagRepr::I128);
    m.enums[0].discriminants = vec![Some(-1), Some(2)];
    assert!(run(&m, &extract(4, 0, Ty::I128)).0.is_empty());
}
#[test]
fn empty_tuple_unknown_insert_value_and_long_variant_names_preserve_original_rules() {
    let mut m = fixture();
    m.functions[0].blocks[0].params[2].1 = Ty::Tuple(vec![]);
    assert!(matches!(
        &run(&m, &extract(2, 0, Ty::Bool)).0[..],
        [ValidationError::FieldAccessInvalid { .. }]
    ));
    assert!(
        run(&m, &insert(0, 0, Ty::Struct(StructId::new(0)), 999))
            .0
            .is_empty()
    );
    let e = run(&long_enum(), &extract(4, 1, Ty::Ptr)).0;
    assert!(
        matches!(&e[..],[ValidationError::OperandTypeMismatch {expected,..}]if expected.contains("é🦀variant")&&expected.contains("rt::long"))
    );
}
