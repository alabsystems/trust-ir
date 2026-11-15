// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
#[test]
fn bare_empty_declaration_is_retained_but_empty_physical_metadata_refuses() {
    let mut m = fixture();
    assert!(run(&m, 0).0.is_empty());
    m.enums[0].variants.clear();
    assert!(run(&m, 0).0.is_empty(), "bare empty nominal declaration");
    m.enums[0].repr = Some(EnumTagRepr::U8);
    assert!(
        matches!(&run(&m,0).0[..],[ValidationError::ConstTypeMismatch {actual,..}] if actual=="no canonical tag")
    );
    m.enums[0].repr = None;
    m.enums[0].discriminants.push(Some(0));
    assert!(
        matches!(&run(&m,0).0[..],[ValidationError::ConstTypeMismatch {actual,..}] if actual=="no canonical tag")
    );
    m.enums[0].discriminants.clear();
    m.enums[0].layout = Some(trust_ir::ty::EnumLayoutDescriptor {
        encoding: trust_ir::ty::EnumTagEncoding::Direct { tag_offset: 0 },
        size: 1,
        align: 1,
        variant_field_offsets: Vec::new(),
    });
    assert!(
        matches!(&run(&m,0).0[..],[ValidationError::ConstTypeMismatch {actual,..}] if actual=="no canonical tag")
    );
}
#[test]
fn each_later_duplicate_physical_row_reports_once_before_its_own_other_errors() {
    let mut m = fixture();
    let mut row = m.enums[0].clone();
    row.variants.clear();
    row.repr = Some(EnumTagRepr::U8);
    m.enums.extend([row.clone(), row]);
    assert!(run(&m, 0).0.is_empty());
    for index in [1, 2] {
        let out = run(&m, index).0;
        assert_eq!(out.len(), 2);
        assert!(matches!(out[0], ValidationError::DuplicateEnumId(7)));
    }
}
#[test]
fn assignment_failure_precedes_canonical_check_and_keeps_full_field_name_diagnostics() {
    let mut m = fixture();
    m.enums[0].discriminants = vec![Some(1), Some(1)];
    m.enums[0].variants[0].field_names = vec!["extra".into()];
    m.enums[0].variants[1].field_names = vec!["x".into(), "y".into()];
    let out = run(&m, 0).0;
    assert_eq!(out.len(), 3);
    assert!(
        matches!(&out[0],ValidationError::ConstTypeMismatch {actual,..} if actual=="ill-formed discriminants")
    );
}
#[test]
fn full_raw_enum_and_variant_names_are_preserved_without_debug_or_normalization() {
    let mut m = fixture();
    m.enums[0].name = "λ\n'\"".repeat(2000) + "TAIL";
    m.enums[0].variants[1].name = "中\n'".repeat(1000) + "END";
    m.enums[0].variants[1].field_names = vec!["x".into(), "y".into()];
    let out = run(&m, 0).0;
    assert!(
        matches!(&out[0],ValidationError::ConstTypeMismatch {location,..} if location.contains("TAIL")&&location.ends_with("END)"))
    );
}
#[test]
fn explicit_repr_boundaries_and_required_implicit_overflow_keep_original_error_order() {
    let mut m = fixture();
    for (repr, value) in [
        (EnumTagRepr::U8, 256),
        (EnumTagRepr::I8, -129),
        (EnumTagRepr::U64, u64::MAX as i128 + 1),
        (EnumTagRepr::U128, i128::MAX),
        (EnumTagRepr::I128, i128::MIN),
    ] {
        m.enums[0].repr = Some(repr);
        m.enums[0].discriminants = vec![Some(value), Some(0)];
        run(&m, 0);
    }
    m.enums[0].discriminants = vec![Some(i128::MAX), None];
    assert!(
        matches!(&run(&m,0).0[0],ValidationError::ConstTypeMismatch {actual,..} if actual=="ill-formed discriminants")
    );
}
#[test]
fn field_name_payloads_and_ignored_discriminant_tail_do_not_become_new_checks() {
    let mut m = fixture();
    let (_, before) = run(&m, 0);
    m.enums[0].variants[1].field_names[0] = "opaque".repeat(10000);
    m.enums[0].discriminants = vec![None, None, Some(i128::MAX), Some(i128::MAX)];
    let (_, after) = run(&m, 0);
    assert_eq!(before.events, after.events);
}
#[test]
fn invalid_physical_index_is_typed_refusal_instead_of_a_clean_declaration() {
    let m = fixture();
    let mut o = Observer::default();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    assert_eq!(
        validate_enum_declaration_observed(&m, 1, &mut s, site()),
        Err(ObservedValueError::InvalidRange)
    );
    assert!(s.first_refusal().is_none());
}
#[test]
fn returned_full_diagnostics_are_independent_of_subsequent_input_mutation() {
    let mut m = fixture();
    m.enums[0].variants[0].field_names.push("x".into());
    let out = run(&m, 0).0;
    let expected = out.clone();
    m.enums[0].name.clear();
    m.enums[0].variants.clear();
    assert_eq!(out, expected);
}
