// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
#[test]
fn positive_declared_length_is_never_materialized_and_maximum_has_identical_work() {
    let m = fixture(Ty::Bool);
    let (a, first, _, _) = run(&m, &array(1));
    let (b, last, _, _) = run(&m, &array(u64::MAX));
    assert!(a.is_empty() && b.is_empty());
    assert_eq!(first.events, last.events);
}
#[test]
fn zero_length_stays_noncanonical_after_element_mismatch_and_unknown_value_skip() {
    let m = fixture(Ty::U64);
    let e = run(&m, &array(0)).0;
    assert!(matches!(e[0], ValidationError::OperandTypeMismatch { .. }));
    assert!(matches!(
        e[1],
        ValidationError::NonCanonicalUniformArray { .. }
    ));
    let unknown = Inst::ArraySplat {
        ty: Ty::Array(TyId::new(0), 0),
        value: v(999),
    };
    assert!(matches!(
        &run(&m, &unknown).0[..],
        [ValidationError::NonCanonicalUniformArray { .. }]
    ));
}
#[test]
fn wrong_outer_type_and_undefined_element_are_exact_single_diagnostics() {
    let m = fixture(Ty::Bool);
    for ty in [
        Ty::Bool,
        Ty::Refine(TyId::new(0), PredId::new(0)),
        Ty::Array(TyId::new(u32::MAX), 0),
    ] {
        let e = run(&m, &Inst::ArraySplat { ty, value: v(0) }).0;
        assert!(matches!(
            &e[..],
            [ValidationError::InvalidArraySplat { .. }]
        ));
    }
}
#[test]
fn known_exact_unknown_and_top_refinement_element_cases_keep_original_local_rules() {
    assert!(run(&fixture(Ty::Bool), &array(2)).0.is_empty());
    let unknown = Inst::ArraySplat {
        ty: Ty::Array(TyId::new(0), 2),
        value: v(999),
    };
    assert!(run(&fixture(Ty::U64), &unknown).0.is_empty());
    assert!(
        run(
            &fixture(Ty::Refine(TyId::new(0), PredId::new(0))),
            &array(2)
        )
        .0
        .is_empty()
    );
    let refined = Inst::ArraySplat {
        ty: Ty::Array(TyId::new(2), 2),
        value: v(0),
    };
    assert!(run(&fixture(Ty::U64), &refined).0.is_empty());
}
#[test]
fn rich_expected_actual_types_and_maximum_ids_preserve_complete_diagnostic_text() {
    let mut m = fixture(Ty::Tuple(vec![Ty::handle("é", "rt::中"), Ty::Bool]));
    m.types[0] = Ty::Tuple(vec![Ty::U64, Ty::Ptr]);
    assert!(matches!(
        &run(&m, &array(2)).0[..],
        [ValidationError::OperandTypeMismatch { .. }]
    ));
    let e = run_block(&m, &array(0), BlockId::new(u32::MAX)).0;
    let ValidationError::NonCanonicalUniformArray { location, spelling } = &e[1] else {
        panic!()
    };
    assert!(location.starts_with("block 4294967295: array_splat "));
    assert!(spelling.starts_with("zero copies are the empty array `const "));
}
#[test]
fn unrelated_instruction_skips_without_reading_large_unrelated_type_payload() {
    let m = fixture(Ty::Bool);
    let inst = Inst::Drop {
        ty: Ty::Tuple(vec![Ty::Bool; 1000]),
        ptr: v(0),
    };
    assert!(run(&m, &inst).0.is_empty());
}
