// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
#[test]
fn actual_scope_then_inline_node_and_sidecar_span_order_is_exact() {
    let m = fixture();
    assert_eq!(
        run(&m, Component::Spans).0,
        [3, 4, 5, 6, 7].map(|file| ValidationError::SpanFileIndexOutOfRange {
            file,
            file_count: 2
        })
    );
}
#[test]
fn empty_file_table_retains_original_skip_and_valid_last_index_is_in_range() {
    let mut m = fixture();
    m.files.clear();
    let (out, o) = run(&m, Component::Spans);
    assert!(out.is_empty());
    assert_eq!(
        o.events
            .iter()
            .filter(|e| e.phase == ExecutionPhase::Validation)
            .count(),
        2
    );
    m.files = vec![String::new(); 8];
    assert!(run(&m, Component::Spans).0.is_empty());
}
#[test]
fn all_physical_duplicate_external_unreachable_rows_are_checked_without_filter() {
    let mut m = fixture();
    let mut f = m.functions[0].clone();
    f.linkage = Linkage::External;
    f.entry = BlockId::new(999);
    m.functions.push(f);
    assert_eq!(run(&m, Component::Spans).0.len(), 9);
    assert_eq!(run(&m, Component::Weights).0.len(), 10);
}
#[test]
fn function_placement_precedes_all_node_weights_with_original_reason_spelling() {
    let m = fixture();
    let out = run(&m, Component::Weights).0;
    assert_eq!(out.len(), 5);
    assert_eq!(
        out[0],
        ValidationError::BranchWeightsMismatch {
            reason: "branch_weights may not be attached at function scope; it belongs on a CondBr/Switch terminator node"
        }
    );
    assert_eq!(
        out[2],
        ValidationError::BranchWeightsMismatch {
            reason: "CondBr requires exactly 2 weights [taken, not_taken]"
        }
    );
    assert_eq!(
        out[3],
        ValidationError::BranchWeightsMismatch {
            reason: "Switch requires cases+1 weights (per-case then default)"
        }
    );
    assert_eq!(
        out[4],
        ValidationError::BranchWeightsMismatch {
            reason: "only CondBr/Switch nodes may carry branch_weights"
        }
    );
}
#[test]
fn condbr_two_and_switch_case_plus_default_are_exact_positive_twins() {
    let mut m = fixture();
    let f = &mut m.functions[0];
    f.proofs.clear();
    f.blocks[0].body.truncate(2);
    for n in &mut f.blocks[0].body {
        n.proofs = vec![trust_ir::ProofAnnotation::BranchWeights(vec![u32::MAX, 0])];
    }
    assert!(run(&m, Component::Weights).0.is_empty());
}
#[test]
fn duplicate_obligation_ids_and_duplicate_missing_diagnostics_keep_original_semantics() {
    let mut m = fixture();
    assert_eq!(
        run(&m, Component::Diagnostics).0,
        vec![ValidationError::DanglingDiagnosticObligation { obligation: 8 }; 2]
    );
    m.proof_obligations.push(obligation(8));
    assert!(run(&m, Component::Diagnostics).0.is_empty());
    m.proof_obligations.clear();
    assert_eq!(run(&m, Component::Diagnostics).0.len(), 4);
}
#[test]
fn empty_diagnostics_skip_all_obligations_and_unrelated_payloads_are_not_walked() {
    let mut m = fixture();
    m.obligation_diagnostics.clear();
    m.proof_obligations[0].description = "opaque".repeat(10000);
    let (out, o) = run(&m, Component::Diagnostics);
    assert!(out.is_empty());
    assert_eq!(
        o.events
            .iter()
            .filter(|e| e.phase == ExecutionPhase::Validation)
            .count(),
        2
    );
}
#[test]
fn scalar_reference_rules_do_not_scan_weight_text_span_coordinates_or_claim_payloads() {
    let mut m = fixture();
    let (_, before) = run(&m, Component::Diagnostics);
    for o in &mut m.proof_obligations {
        o.description = "untrusted".repeat(10000);
    }
    for d in &mut m.obligation_diagnostics {
        d.message = "untrusted".repeat(10000);
        d.detail = Some("untrusted".repeat(10000));
    }
    let (_, after) = run(&m, Component::Diagnostics);
    assert_eq!(before.events, after.events);
    let (_, before) = run(&m, Component::Weights);
    for proof in &mut m.functions[0].proofs {
        *proof = trust_ir::ProofAnnotation::BranchWeights(vec![0; 10000]);
    }
    let (_, after) = run(&m, Component::Weights);
    assert_eq!(before.events, after.events);
}
