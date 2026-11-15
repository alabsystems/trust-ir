// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
#[test]
fn complete_ordered_actual_four_postcheck_oracles_match_empty_and_rich_inputs() {
    run(&fixture());
    run(&Input {
        module: Module::new(""),
        tv: vec![],
        islands: vec![],
        rows: vec![],
    });
}
#[test]
fn actual_acyclic_calls_island_bridges_and_one_claim_have_no_post_replay_error() {
    let mut i = fixture();
    i.rows.clear();
    let catalog = ModuleFunctionCatalog::new(&i.module);
    assert!(oracle(&i, &catalog).is_empty());
    run(&i);
}
#[test]
fn duplicate_rechecked_ids_ground_nothing_even_when_only_one_has_the_callee_function() {
    let mut i = fixture();
    i.tv.push(tv(11, 9, &[], None));
    let out = oracle(&i, &ModuleFunctionCatalog::new(&i.module));
    assert!(out.iter().any(|e|matches!(e,ValidationError::CertifiedCleanCicKernelRecheckFailed{reason,..} if reason.contains("cites obligation #11"))));
    run(&i);
}
#[test]
fn called_duplicate_rows_and_uncalled_rows_preserve_first_naming_and_full_error_order() {
    let mut i = fixture();
    i.module.proof_certificates.insert(1, inherited(10, 7, 11));
    i.module.proof_certificates.insert(0, inherited(10, 55, 12));
    i.tv[0].callees.push(FuncId::new(55));
    i.tv[0].callees.push(FuncId::new(55));
    i.module.proof_certificates.insert(0, inherited(10, 99, 12));
    let out = oracle(&i, &ModuleFunctionCatalog::new(&i.module));
    assert!(out.iter().any(|e|matches!(e,ValidationError::CertifiedCleanCicKernelRecheckFailed{reason,..} if reason.contains("one row per call edge"))));
    run(&i);
}
#[test]
fn external_rows_never_mark_a_local_callee_named_and_missing_duplicate_calls_repeat() {
    let mut i = fixture();
    if let ProofEvidence::InheritedFromCallee { external, .. } =
        &mut i.module.proof_certificates[0].evidence
    {
        *external = Some(
            trust_ir::ExternRef::new(trust_ir::value::ImportId::new(0), "callee")
                .relying_on(ProofId::new(11)),
        );
    }
    i.tv[0].callees.push(FuncId::new(7));
    run(&i);
}
#[test]
fn per_start_bfs_keeps_first_shortest_cycle_tie_and_self_loop_spelling() {
    let i = cycle_fixture();
    let out = oracle(&i, &ModuleFunctionCatalog::new(&i.module));
    assert!(out.iter().any(|e|matches!(e,ValidationError::CertifiedCleanCicKernelRecheckFailed{reason,..} if reason.contains("calleré🦀 → calleeé🦀 → calleré🦀"))));
    run(&i);
    let mut i = fixture();
    i.tv[0].callees = vec![FuncId::new(3)];
    i.module.proof_certificates = vec![inherited(10, 3, 10)];
    run(&i);
}
#[test]
fn ambiguous_missing_and_sparse_function_ids_use_actual_unique_catalog_diagnostic_names() {
    let mut i = cycle_fixture();
    i.module.functions.push(i.module.functions[0].clone());
    i.module.functions.retain(|f| f.id != FuncId::new(7));
    run(&i);
}
#[test]
fn island_bridge_requires_exact_digest_and_source_name_in_btree_citation_order() {
    let mut i = fixture();
    i.islands[0].cited = ["Z", "A", "B"].into_iter().map(String::from).collect();
    i.tv[0].island.as_mut().unwrap().0 = digest(4);
    i.tv[1].island.as_mut().unwrap().1 = "different".into();
    run(&i);
}
#[test]
fn theorem_first_name_stays_first_across_same_claim_and_both_conflict_kinds() {
    let mut i = fixture();
    i.islands.extend([
        theorem(21, "claimé", 3, 5, &[]),
        theorem(22, "claimé", 3, 6, &[]),
        theorem(23, "claimé", 4, 5, &[]),
        theorem(24, "other", 7, 5, &[]),
    ]);
    run(&i);
}
#[test]
fn duplicate_content_group_and_ids_order_match_btree_key_order_and_sort_unstable_oracle() {
    let mut i = fixture();
    i.rows = vec![
        row(99, None, "z"),
        row(42, None, "z"),
        row(7, Some(3), "b"),
        row(7, Some(3), "b"),
        row(3, Some(3), "a"),
        row(2, Some(3), "a"),
        row(1, Some(7), "a"),
    ];
    run(&i);
}
#[test]
fn v8_renumbering_unknown_and_ambiguous_owners_preserve_semantic_none_and_scope_identity() {
    let mut i = fixture();
    i.rows.push(row(91, Some(777), "same"));
    i.rows.push(row(92, Some(7), "same"));
    i.rows.push(row(93, Some(7), "same"));
    i.module.functions.push(i.module.functions[1].clone());
    run(&i);
}
#[test]
fn full_unicode_nul_names_and_long_v8_preimages_survive_diagnostics_and_exact_ordering() {
    let mut i = cycle_fixture();
    i.module.functions[0].name = "é🦀\0".repeat(400);
    i.islands = vec![
        theorem(20, &"é🦀".repeat(400), 3, 5, &["missing\0é"]),
        theorem(21, &"é🦀".repeat(400), 4, 5, &[]),
    ];
    i.rows = vec![
        row(8, Some(3), &"é🦀\0".repeat(600)),
        row(7, Some(3), &"é🦀\0".repeat(600)),
    ];
    run(&i);
}
