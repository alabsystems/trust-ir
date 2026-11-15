// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
#[test]
fn actual_struct_record_tuple_and_enum_success_match_without_redundant_type_copies() {
    let m = fixture();
    for inst in [
        make(Ty::Struct(StructId::new(0)), None, &[0, 1]),
        make(Ty::Record(RecordId::new(0)), None, &[0, 1]),
        make(Ty::Tuple(vec![Ty::Bool, Ty::U64]), None, &[0, 1]),
        make(Ty::Enum(EnumId::new(0)), Some(0), &[0, 1]),
    ] {
        assert!(run(&m, &inst).0.is_empty());
    }
}
#[test]
fn every_nonenum_variant_is_refused_before_missing_definition_or_arity() {
    let m = fixture();
    for ty in [
        Ty::Struct(StructId::new(999)),
        Ty::Record(RecordId::new(999)),
        Ty::Tuple(vec![]),
        Ty::Array(TyId::new(999), 8),
        Ty::Bool,
    ] {
        assert!(matches!(&run(&m, &make(ty, Some(0), &[0])).0[..],
            [ValidationError::InvalidMakeAggregate { reason, .. }] if reason.contains("only meaningful")));
    }
}
#[test]
fn missing_struct_record_enum_and_array_element_refuse_exact_original_reason() {
    let m = fixture();
    for ty in [
        Ty::Struct(StructId::new(999)),
        Ty::Record(RecordId::new(999)),
        Ty::Enum(EnumId::new(999)),
        Ty::Array(TyId::new(999), 0),
    ] {
        assert!(
            matches!(&run(&m, &make(ty, None, &[])).0[..], [ValidationError::InvalidMakeAggregate { reason, .. }] if reason.contains("undefined"))
        );
    }
}
#[test]
fn unsupported_scalar_refined_closure_sequence_handle_and_dialect_carriers_are_refused() {
    let m = fixture();
    for ty in [
        Ty::Bool,
        Ty::Refine(TyId::new(0), PredId::new(0)),
        Ty::Closure(trust_ir::value::ClosureTyId::new(0)),
        Ty::Sequence(TyId::new(0)),
        Ty::handle("H", "rt::H"),
        Ty::Dialect(Box::new(trust_ir::DialectTy::new("n", "D", 1))),
    ] {
        assert!(matches!(
            &run(&m, &make(ty, None, &[])).0[..],
            [ValidationError::InvalidMakeAggregate { .. }]
        ));
    }
}
#[test]
fn ordinary_nominal_index_priority_and_first_fallback_are_preserved_for_all_families() {
    let mut m = fixture();
    m.structs = vec![structure(1, vec![Ty::U64]), structure(1, vec![Ty::Bool])];
    assert!(
        run(&m, &make(Ty::Struct(StructId::new(1)), None, &[0]))
            .0
            .is_empty()
    );
    for d in &mut m.structs {
        d.id = StructId::new(77);
    }
    assert!(
        run(&m, &make(Ty::Struct(StructId::new(77)), None, &[1]))
            .0
            .is_empty()
    );
    m.records[0].id = RecordId::new(88);
    m.enums[0].id = EnumId::new(99);
    assert!(
        run(&m, &make(Ty::Record(RecordId::new(88)), None, &[0, 1]))
            .0
            .is_empty()
    );
    assert!(
        run(&m, &make(Ty::Enum(EnumId::new(99)), Some(0), &[0, 1]))
            .0
            .is_empty()
    );
}
#[test]
fn declared_arity_refuses_before_any_unknown_or_wrong_lane_types() {
    let m = fixture();
    for ty in [
        Ty::Struct(StructId::new(0)),
        Ty::Record(RecordId::new(0)),
        Ty::Tuple(vec![Ty::Bool, Ty::U64]),
    ] {
        assert!(
            matches!(&run(&m, &make(ty, None, &[3, 3, 999])).0[..], [ValidationError::InvalidMakeAggregate { reason, .. }] if reason=="3 lane operand(s) supplied, but the type declares 2 lane(s)")
        );
    }
}
#[test]
fn exact_lanes_unknown_skip_and_only_top_refinement_defer_match_original() {
    let m = fixture();
    let e = run(&m, &make(Ty::Tuple(vec![Ty::Bool, Ty::U64]), None, &[1, 0])).0;
    assert!(
        matches!(&e[..], [ValidationError::OperandTypeMismatch { role: a, .. }, ValidationError::OperandTypeMismatch { role: b, .. }] if a=="lane 0"&&b=="lane 1")
    );
    assert!(
        run(
            &m,
            &make(Ty::Tuple(vec![Ty::Bool, Ty::U64]), None, &[4, 999])
        )
        .0
        .is_empty()
    );
    assert!(
        run(
            &m,
            &make(
                Ty::Tuple(vec![Ty::Refine(TyId::new(0), PredId::new(0))]),
                None,
                &[3]
            )
        )
        .0
        .is_empty()
    );
    assert!(matches!(
        &run(
            &m,
            &make(Ty::Tuple(vec![Ty::Rc(Box::new(Ty::Bool))]), None, &[7])
        )
        .0[..],
        [ValidationError::OperandTypeMismatch { .. }]
    ));
}
#[test]
fn enum_requires_actual_variant_index_and_preserves_out_of_range_text() {
    let m = fixture();
    assert!(
        matches!(&run(&m, &make(Ty::Enum(EnumId::new(0)), None, &[])).0[..], [ValidationError::InvalidMakeAggregate { reason, .. }] if reason.contains("needs a `variant` index"))
    );
    assert!(
        matches!(&run(&m, &make(Ty::Enum(EnumId::new(0)), Some(u32::MAX), &[])).0[..], [ValidationError::InvalidMakeAggregate { reason, .. }] if reason=="variant index 4294967295 is out of range (3 variant(s))")
    );
}
#[test]
fn duplicate_or_unrepresentable_enum_discriminants_refuse_before_lane_validation() {
    for overflow in [false, true] {
        let mut m = fixture();
        if overflow {
            m.enums[0].discriminants = vec![Some(i128::MAX), None];
        } else {
            m.enums[0].discriminants = vec![Some(1), Some(1)];
        }
        assert!(
            matches!(&run(&m, &make(Ty::Enum(EnumId::new(0)), Some(0), &[3])).0[..], [ValidationError::InvalidMakeAggregate { reason, .. }] if reason.contains("no canonical tag repr"))
        );
    }
    let mut wide = fixture();
    wide.enums[0].repr = Some(EnumTagRepr::I128);
    wide.enums[0].discriminants = vec![Some(i128::MIN), Some(i128::MIN + 1), Some(i128::MIN + 2)];
    assert!(
        run(&wide, &make(Ty::Enum(EnumId::new(0)), Some(1), &[]))
            .0
            .is_empty()
    );
    wide.enums[0].repr = Some(EnumTagRepr::U8);
    assert!(matches!(
        &run(&wide, &make(Ty::Enum(EnumId::new(0)), Some(1), &[])).0[..],
        [ValidationError::InvalidMakeAggregate { .. }]
    ));
}
#[test]
fn real_enum_inhabitedness_precedes_arity_and_retains_complete_names() {
    let m = long_void();
    let e = run(&m, &make(Ty::Enum(EnumId::new(0)), Some(2), &[])).0;
    assert!(
        matches!(&e[..], [ValidationError::UninhabitedVariantConstructed { enum_name, variant: 2, variant_name, location }] if enum_name==&m.enums[0].name && variant_name==&m.enums[0].variants[2].name && location=="block 1: make_aggregate enum.0")
    );
    assert!(
        run(&m, &make(Ty::Enum(EnumId::new(0)), Some(1), &[]))
            .0
            .is_empty()
    );
}
#[test]
fn array_arity_first_does_not_materialize_impossible_length_and_empty_is_not_uniform() {
    let m = fixture();
    assert!(
        matches!(&run(&m, &make(Ty::Array(TyId::new(0), u64::MAX), None, &[1])).0[..], [ValidationError::InvalidMakeAggregate { reason, .. }] if reason.contains("18446744073709551615 element(s)"))
    );
    assert!(
        run(&m, &make(Ty::Array(TyId::new(0), 0), None, &[]))
            .0
            .is_empty()
    );
}
#[test]
fn array_uniform_including_one_lane_reports_before_exact_lane_mismatches() {
    let m = fixture();
    for fields in [&[1][..], &[1, 1][..]] {
        let e = run(
            &m,
            &make(Ty::Array(TyId::new(0), fields.len() as u64), None, fields),
        )
        .0;
        assert!(
            matches!(&e[0], ValidationError::NonCanonicalUniformArray { spelling, .. } if spelling.contains("array_splat"))
        );
        assert_eq!(e.len(), fields.len() + 1);
        assert!(
            e[1..]
                .iter()
                .all(|e| matches!(e, ValidationError::OperandTypeMismatch { .. }))
        );
    }
    assert!(
        run(&m, &make(Ty::Array(TyId::new(0), 2), None, &[0, 4]))
            .0
            .is_empty()
    );
}
