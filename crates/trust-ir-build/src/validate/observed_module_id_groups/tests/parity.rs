// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
#[test]
fn empty_and_unique_ids_are_clean_in_both_original_groups() {
    for g in [Group::Structs, Group::Functions] {
        assert!(run(&module(&[]), g).0.is_empty());
        assert!(run(&module(&[9, 0, u32::MAX]), g).0.is_empty());
    }
}
#[test]
fn struct_id_is_reported_once_for_every_repeated_physical_row() {
    assert_eq!(
        run(&module(&[8, 8, 8, 8]), Group::Structs).0,
        vec![ValidationError::DuplicateStructId(8); 3]
    );
}
#[test]
fn struct_duplicate_order_is_physical_not_numeric() {
    assert_eq!(
        run(&module(&[9, 1, 9, 1, 9]), Group::Structs).0,
        vec![
            ValidationError::DuplicateStructId(9),
            ValidationError::DuplicateStructId(1),
            ValidationError::DuplicateStructId(9)
        ]
    );
}
#[test]
fn sparse_maximum_ids_are_not_used_as_allocation_indices() {
    let m = module(&[u32::MAX, 0, u32::MAX, 0]);
    for g in [Group::Structs, Group::Functions] {
        assert_eq!(run(&m, g).0.len(), 2);
    }
}
#[test]
fn catalog_function_duplicates_are_unique_numeric_order_despite_repetition() {
    assert_eq!(
        run(&module(&[9, 1, 9, 1, 9]), Group::Functions).0,
        vec![
            ValidationError::DuplicateFuncId(1),
            ValidationError::DuplicateFuncId(9)
        ]
    );
}
#[test]
fn labels_and_unrelated_fields_never_substitute_for_raw_id_identity() {
    let mut m = module(&[0, 1, 2]);
    for s in &mut m.structs {
        s.name = "same".into();
    }
    for f in &mut m.functions {
        f.name = "same".into();
    }
    assert!(run(&m, Group::Structs).0.is_empty());
    assert!(run(&m, Group::Functions).0.is_empty());
}
#[test]
fn mismatched_physical_coordinates_do_not_hide_late_duplicates() {
    let m = module(&[40, 2, 13, 99, 40, 13]);
    assert_eq!(
        run(&m, Group::Structs).0,
        vec![
            ValidationError::DuplicateStructId(40),
            ValidationError::DuplicateStructId(13)
        ]
    );
    assert_eq!(
        run(&m, Group::Functions).0,
        vec![
            ValidationError::DuplicateFuncId(13),
            ValidationError::DuplicateFuncId(40)
        ]
    );
}
#[test]
fn successful_full_diagnostics_are_owned_after_source_and_catalog_disposal() {
    let mut m = module(&[3, 3, 1, 1, 3]);
    let expected = expected(&m, Group::Functions);
    let errors = run(&m, Group::Functions).0;
    m.functions.clear();
    m.structs.clear();
    assert_eq!(errors, expected);
}
