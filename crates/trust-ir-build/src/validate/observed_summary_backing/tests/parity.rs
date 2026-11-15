// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
#[test]
fn absent_or_entity_only_citation_cannot_gain_proof_bearing_standing() {
    let (m, f, mut summary) = fixture();
    summary.backed_by = None;
    assert_eq!(
        run(&m, &f, &summary, ImportPolicy::Refuse).0,
        (vec![], SummaryCitation::Absent)
    );
    summary.backed_by = Some(ExternRef::new(ImportId::new(0), "entity"));
    assert_eq!(
        run(&m, &f, &summary, ImportPolicy::Refuse).0,
        (vec![], SummaryCitation::Absent)
    );
}
#[test]
fn missing_import_reports_only_dangling_citation_and_preserves_false_flag() {
    let (mut m, f, mut summary) = fixture();
    m.imports.clear();
    summary.backed_by.as_mut().unwrap().module = ImportId::new(u32::MAX);
    for policy in [ImportPolicy::Structural, ImportPolicy::Refuse] {
        let (out, claim) = run(&m, &f, &summary, policy).0;
        assert_eq!(claim, SummaryCitation::Absent);
        assert_eq!(out.len(), 1);
        assert!(
            matches!(&out[0],ValidationError::DanglingExternRef {detail} if detail.contains("4294967295") && !detail.contains("symbol"))
        );
    }
}
#[test]
fn structural_floor_and_unproved_citation_keep_the_original_flag_without_new_authentication() {
    let (m, f, mut summary) = fixture();
    assert_eq!(
        run(&m, &f, &summary, ImportPolicy::Structural).0,
        (vec![], SummaryCitation::ProofBearing)
    );
    summary.proved = false;
    assert_eq!(
        run(&m, &f, &summary, ImportPolicy::Refuse).0,
        (vec![], SummaryCitation::ProofBearing)
    );
}
#[test]
fn refuse_policy_keeps_complete_symbol_debug_unsigned_ids_and_one_named_refusal() {
    let (m, f, mut summary) = fixture();
    summary.backed_by.as_mut().unwrap().symbol = "λ'\"\n\0".repeat(2000) + "TAIL";
    let (out, claim) = run(&m, &f, &summary, ImportPolicy::Refuse).0;
    assert_eq!(claim, SummaryCitation::ProofBearing);
    assert_eq!(out.len(), 1);
    assert!(
        matches!(&out[0],ValidationError::UnauthenticatedImport {import:0,site:"backed_by",detail} if detail.contains("TAIL") && detail.contains("4294967295") && detail.contains("\\0"))
    );
}
#[test]
fn default_authenticated_map_fails_closed_instead_of_assuming_an_unexamined_citation() {
    let (m, f, summary) = fixture();
    let auth = crate::linked::AuthenticatedImports::default();
    let (out, claim) = run(&m, &f, &summary, ImportPolicy::Authenticated(&auth)).0;
    assert_eq!(claim, SummaryCitation::ProofBearing);
    assert!(
        matches!(&out[..],[ValidationError::UnauthenticatedImport {detail,..}] if detail.ends_with("'s citation was not examined by the linked validator"))
    );
}
#[test]
fn nonproof_and_unproved_paths_do_not_read_the_opaque_symbol_or_authentication_outcomes() {
    let (m, f, mut summary) = fixture();
    summary.proved = false;
    let auth = crate::linked::AuthenticatedImports::default();
    let (_, before) = run(&m, &f, &summary, ImportPolicy::Authenticated(&auth));
    summary.backed_by.as_mut().unwrap().symbol = "opaque".repeat(10000);
    let (_, after) = run(&m, &f, &summary, ImportPolicy::Authenticated(&auth));
    assert_eq!(before.events, after.events);
}
