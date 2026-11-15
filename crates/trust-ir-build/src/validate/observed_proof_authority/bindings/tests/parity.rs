// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
#[test]
fn complete_actual_binding_oracle_matches_all_equal_and_all_four_independent_mismatches() {
    let i = fixture();
    assert!(oracle(&i).is_empty());
    run(&i);
    let i = bad();
    let out = oracle(&i);
    assert_eq!(out.len(), 4);
    assert_eq!(
        out.iter()
            .map(|e| match e {
                ValidationError::CertificateBindingMismatch { field, .. } => field.as_str(),
                _ => "wrong",
            })
            .collect::<Vec<_>>(),
        vec![
            "environment_digest",
            "statement_digest",
            "origin_module",
            "callees"
        ]
    );
    run(&i);
}
#[test]
fn both_digest_algorithms_and_every_digest_byte_render_exact_lowercase_hex() {
    for algorithm in [
        ProofDigestAlgorithm::Sha256,
        ProofDigestAlgorithm::TrustIrStableV1,
    ] {
        for at in 0..32 {
            let mut i = fixture();
            i.binding.environment_digest.algorithm = algorithm;
            i.binding.environment_digest.bytes[at] ^= 0xf3;
            i.binding.statement_digest.algorithm = algorithm;
            i.binding.statement_digest.bytes[31 - at] ^= 0x7a;
            run(&i);
        }
    }
}
#[test]
fn absent_expected_digest_and_origin_presence_follow_original_distinct_diagnostics() {
    for env in [None, Some(digest(1))] {
        for statement in [None, Some(digest(2))] {
            for origin in [None, Some(digest(3)), Some(digest(9))] {
                let mut i = fixture();
                i.env = env;
                i.statement = statement;
                i.binding.origin_module = origin;
                run(&i);
            }
        }
    }
}
#[test]
fn full_import_table_any_exact_digest_match_ignores_names_and_duplicate_rows() {
    let mut i = fixture();
    i.module.imports = vec![
        trust_ir::ModuleImport::new("wrong", digest(8)),
        trust_ir::ModuleImport::new("other", digest(3)),
        trust_ir::ModuleImport::new("duplicate", digest(3)),
    ];
    run(&i);
    i.binding.origin_module.as_mut().unwrap().algorithm = ProofDigestAlgorithm::TrustIrStableV1;
    run(&i);
}
#[test]
fn ordered_callee_equality_and_full_debug_lists_keep_duplicates_controls_and_unicode() {
    for case in 0..4 {
        let mut i = fixture();
        i.binding.callees = vec![
            "a".into(),
            "a".into(),
            "'\"\\\r\n\t\0\u{1}\u{1248}é🦀\u{200d}".repeat(130),
        ];
        i.callees = i.binding.callees.clone();
        match case {
            0 => {}
            1 => i.callees.reverse(),
            2 => {
                i.callees.pop();
            }
            _ => i.callees[2].push('x'),
        };
        run(&i);
    }
}
#[test]
fn unrelated_opaque_island_payload_remains_outside_this_data_comparison_rule() {
    let mut i = fixture();
    i.binding.environment = Some(IslandEnvironment::new(vec![255, 0, 9, 9]));
    run(&i);
    i.row.status = ProofStatus::Pending;
    i.row.description = "unrelated".into();
    run(&i);
}
