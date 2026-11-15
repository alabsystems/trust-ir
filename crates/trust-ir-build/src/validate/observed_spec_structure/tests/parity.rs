// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
#[test]
fn empty_and_valid_structural_inputs_preserve_exact_wrapping_without_other_module_checks() {
    let m = Module::new("");
    assert!(run(&m).0.is_empty());
    let mut m = Module::new("");
    let mut spec = SpecModule::new("M");
    spec.actions = vec!["a".into()];
    m.spec_modules.push(spec);
    assert!(run(&m).0.is_empty());
}
#[test]
fn full_original_structural_order_and_duplicate_normalization_are_mapped_without_reordering() {
    let mut m = input();
    m.spec_modules[0].actions = vec!["".into(), "a".into(), "a".into()];
    m.spec_modules[0].vars = vec![SpecVar::new("", "")];
    let duplicate = m.spec_modules[0].clone();
    m.spec_modules.push(duplicate);
    let (out, _) = run(&m);
    assert!(out.len() >= 4);
    assert!(
        out.iter()
            .all(|e| matches!(e, ValidationError::InvalidSpecStructure { .. }))
    );
}
#[test]
fn linked_text_and_full_module_claims_remain_outside_the_structural_mapping_scope() {
    let mut m = input();
    m.name.clear();
    let spec = &mut m.spec_modules[0];
    spec.actions = vec!["a".into()];
    spec.enforcement = SpecEnforcementMode::Linked;
    spec.vars = vec![SpecVar::new("unreadable name", "unreadable type")];
    assert!(run(&m).0.is_empty());
    assert!(!super::super::super::validate_spec_module_semantics(&m).is_empty());
}
#[test]
fn returned_full_owned_diagnostics_survive_disposal_of_the_borrowed_input() {
    let mut m = input();
    m.spec_modules[0].name = "λ'\n".repeat(2000) + "TAIL";
    let out = run(&m).0;
    let expected = wrapped(&m);
    m.spec_modules.clear();
    assert_eq!(out, expected);
    assert!(
        matches!(&out[0],ValidationError::InvalidSpecStructure {violation:SpecLinkViolation::BlankSemanticValue {container,..}} if container.ends_with("TAIL"))
    );
}
