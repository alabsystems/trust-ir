// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
#[test]
fn all_four_empty_leaves_preserve_the_entire_original_result() {
    for r in rules() {
        assert!(run(&Module::new("empty"), r).0.is_empty());
    }
}
#[test]
fn exact_evidence_authority_reports_each_physical_bodied_function() {
    let out = run(&fixture(), Rule::GateEvidence).0;
    assert_eq!(
        out,
        vec![
            ValidationError::UnevidencedGate {
                function: 9,
                authority: "clean-kernel-tv".into()
            },
            ValidationError::UnevidencedGate {
                function: 1,
                authority: "clean-kernel-tv".into()
            },
            ValidationError::UnevidencedGate {
                function: 9,
                authority: "clean-kernel-tv".into()
            }
        ]
    );
}
#[test]
fn declarations_skip_only_the_original_gate_evidence_leaf() {
    let mut m = fixture();
    m.functions[0].blocks.clear();
    assert_eq!(run(&m, Rule::GateEvidence).0.len(), 2);
    assert_eq!(run(&m, Rule::PanicKinds).0.len(), 4);
}
#[test]
fn present_unchecked_gate_evidence_is_not_treated_as_absent() {
    let mut m = fixture();
    m.functions[0].body_gate = Some(trust_ir::BodyGate::Gated {
        authority: "clean-kernel-tv".into(),
        evidence: Some(trust_ir::GateEvidence {
            obligation: trust_ir::ProofId::new(999),
            body_digest: trust_ir::proof::ProofDigest::sha256([99; 32]),
        }),
    });
    assert_eq!(run(&m, Rule::GateEvidence).0.len(), 2);
}
#[test]
fn evidence_authority_membership_is_exact_without_case_padding_or_unicode_normalization() {
    for name in [
        "Clean-Kernel-TV",
        "clean-kernel-tv ",
        " clean-kernel-tv",
        "clean-kernel-tν",
        "unknown",
        "",
    ] {
        let mut m = fixture();
        for f in &mut m.functions {
            f.body_gate = Some(trust_ir::BodyGate::gated(name));
        }
        assert!(run(&m, Rule::GateEvidence).0.is_empty());
    }
}
#[test]
fn absent_or_ungated_body_claim_does_not_gain_an_evidence_diagnostic_or_license() {
    let mut m = fixture();
    m.functions[0].body_gate = None;
    m.functions[1].body_gate = Some(trust_ir::BodyGate::Ungated);
    assert_eq!(run(&m, Rule::GateEvidence).0.len(), 1);
}
#[test]
fn global_asm_is_one_complete_count_diagnostic_for_all_raw_blocks() {
    let mut m = fixture();
    m.global_asm.push("".into());
    assert_eq!(
        run(&m, Rule::GlobalAsm).0,
        vec![ValidationError::GlobalAsmNotConsumable { blocks: 3 }]
    );
}
#[test]
fn global_asm_refusal_does_not_parse_or_normalize_any_assembly_text() {
    let mut m = fixture();
    m.global_asm = vec!["\0\nλ\"".repeat(1024)];
    assert_eq!(
        run(&m, Rule::GlobalAsm).0,
        vec![ValidationError::GlobalAsmNotConsumable { blocks: 1 }]
    );
}
#[test]
fn unspecified_kinds_keep_physical_duplicate_function_block_and_raw_node_positions() {
    let out = run(&fixture(), Rule::PanicKinds).0;
    assert_eq!(out.len(), 6);
    for (i, error) in out.iter().enumerate() {
        assert_eq!(
            error,
            &ValidationError::AssertPanicKindUnspecified {
                function: format!("whole λ {}", [9, 1, 9][i / 2]),
                block: [7, 0][i % 2],
                inst_index: 1
            }
        );
    }
}
#[test]
fn ordinary_known_kind_with_no_site_is_only_a_missing_site_diagnostic() {
    let mut m = fixture();
    for f in &mut m.functions {
        for b in &mut f.blocks {
            b.body = vec![InstrNode::new(Inst::Assert {
                cond: ValueId::new(0),
                kind: AssertKind::NullPtr,
                site: None,
            })];
        }
    }
    assert!(run(&m, Rule::PanicKinds).0.is_empty());
    assert_eq!(run(&m, Rule::PanicSites).0.len(), 6);
}
#[test]
fn present_site_does_not_hide_the_independent_unspecified_kind() {
    let mut m = fixture();
    for f in &mut m.functions {
        for b in &mut f.blocks {
            if let Inst::Assert { site, .. } = &mut b.body[1].inst {
                *site = Some(PanicSite {
                    entry: FuncId::new(0),
                    location: PanicLocation::Value(ValueId::new(0)),
                });
            }
        }
    }
    assert_eq!(run(&m, Rule::PanicKinds).0.len(), 6);
    assert!(run(&m, Rule::PanicSites).0.is_empty());
}
#[test]
fn whole_owned_names_and_prior_rows_survive_original_source_disposal() {
    let actual = {
        let mut m = fixture();
        for f in &mut m.functions {
            f.name = "complete λ function".repeat(200);
        }
        run(&m, Rule::PanicSites).0
    };
    assert_eq!(actual.len(), 6);
    assert!(actual.iter().all(|e| matches!(e,ValidationError::AssertPanicSiteMissing {function,..} if function==&"complete λ function".repeat(200))));
}
