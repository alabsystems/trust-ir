// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
#[test]
fn empty_and_absent_source_or_public_fields_keep_their_original_no_claim_boundary() {
    assert!(run(&Module::new("")).0.is_empty());
    let mut m = Module::new("");
    m.proof_obligations.push(row(3, None));
    m.proof_obligations.push(row(
        4,
        Some(ProofObligationSourceIdentity::new("source", "assertion")),
    ));
    assert!(run(&m).0.is_empty());
}
#[test]
fn source_ids_preserve_internal_unicode_spaces_and_noncontrol_format_characters() {
    for text in [
        "a",
        "source λ internal",
        "a\u{200b}b",
        "a\u{2028}b",
        "尾",
        "a b",
    ] {
        assert!(trust_ir::proof::is_valid_proof_obligation_source_text_id(
            text
        ));
        let mut m = Module::new("");
        m.proof_obligations
            .push(row(3, Some(ProofObligationSourceIdentity::new(text, text))));
        assert!(run(&m).0.is_empty());
    }
}
#[test]
fn source_endpoint_whitespace_and_every_control_scalar_have_the_exact_original_refusal() {
    for ch in (0..=255).filter_map(char::from_u32) {
        for text in [
            ch.to_string(),
            format!("a{ch}b"),
            format!("{ch}a"),
            format!("a{ch}"),
        ] {
            let mut m = Module::new("");
            m.proof_obligations.push(row(
                3,
                Some(ProofObligationSourceIdentity::new(&text, "valid")),
            ));
            let errors = run(&m).0;
            assert_eq!(
                errors.is_empty(),
                trust_ir::proof::is_valid_proof_obligation_source_text_id(&text)
            );
        }
    }
}
#[test]
fn semantic_id_limit_counts_utf8_bytes_and_preserves_the_exact1024_byte_boundary() {
    for text in [
        "a".repeat(1023),
        "a".repeat(1024),
        "a".repeat(1025),
        "λ".repeat(512),
        "λ".repeat(513),
        String::new(),
    ] {
        let mut m = Module::new("");
        m.proof_obligations.push(row(
            3,
            Some(ProofObligationSourceIdentity::new(&text, &text)),
        ));
        let errors = run(&m).0;
        assert_eq!(
            errors.len(),
            if trust_ir::proof::is_valid_proof_obligation_source_text_id(&text) {
                0
            } else {
                2
            }
        );
    }
}
#[test]
fn public_id_byte_vocabulary_is_visible_ascii_except_question_and_hash_without_normalization() {
    for ch in (0..=255).filter_map(char::from_u32) {
        let text = ch.to_string();
        let mut m = Module::new("");
        m.proof_obligations.push(row(3, Some(source(&text))));
        let errors = run(&m).0;
        assert_eq!(
            errors.is_empty(),
            trust_ir::proof::is_canonical_public_obligation_id(&text)
        );
    }
    for text in [
        "a?b", "a#b", " public", "public ", "λ", "a/b:c@d", "Public", "public",
    ] {
        let mut m = Module::new("");
        m.proof_obligations.push(row(3, Some(source(text))));
        run(&m);
    }
}
#[test]
fn source_range_file_zero_line_and_reversed_position_errors_remain_separate_and_ordered() {
    let mut m = Module::new("");
    m.proof_obligations.push(row(
        3,
        Some(
            ProofObligationSourceIdentity::new("s", "a").with_range(ProofObligationSourceRange {
                file: u32::MAX,
                start_line: 1,
                start_col: 4,
                end_line: 0,
                end_col: 1,
            }),
        ),
    ));
    assert_eq!(
        run(&m).0,
        vec![
            ValidationError::ProofObligationSourceRangeFileOutOfRange {
                obligation: 3,
                file: u32::MAX,
                file_count: 0
            },
            ValidationError::InvalidProofObligationSourceRange {
                obligation: 3,
                reason: "start_line and end_line must be nonzero"
            },
            ValidationError::InvalidProofObligationSourceRange {
                obligation: 3,
                reason: "end position precedes start position"
            }
        ]
    );
}
#[test]
fn same_position_column_zero_and_unsigned_extremes_keep_ordinary_valid_range_rules() {
    for range in [
        ProofObligationSourceRange {
            file: 0,
            start_line: 1,
            start_col: 0,
            end_line: 1,
            end_col: 0,
        },
        ProofObligationSourceRange {
            file: 0,
            start_line: u32::MAX,
            start_col: u32::MAX,
            end_line: u32::MAX,
            end_col: u32::MAX,
        },
    ] {
        let mut m = Module::new("");
        m.files.push("unused".into());
        m.proof_obligations.push(row(
            3,
            Some(ProofObligationSourceIdentity::new("s", "a").with_range(range)),
        ));
        assert!(run(&m).0.is_empty());
    }
}
#[test]
fn sha256_algorithm_and_zero_digest_checks_are_independent_and_do_not_hash_any_payload() {
    for algorithm in [
        ProofDigestAlgorithm::Sha256,
        ProofDigestAlgorithm::TrustIrStableV1,
    ] {
        for bytes in [[0; 32], [1; 32]] {
            let mut s = source("id");
            s.public.as_mut().unwrap().semantic_digest = ProofDigest { algorithm, bytes };
            let mut m = Module::new("");
            m.proof_obligations.push(row(3, Some(s)));
            assert_eq!(
                run(&m).0.len(),
                usize::from(algorithm != ProofDigestAlgorithm::Sha256)
                    + usize::from(bytes == [0; 32])
            );
        }
    }
    for at in 0..32 {
        let mut bytes = [0; 32];
        bytes[at] = 1;
        let mut s = source("id");
        s.public.as_mut().unwrap().semantic_digest.bytes = bytes;
        let mut m = Module::new("");
        m.proof_obligations.push(row(3, Some(s)));
        assert!(run(&m).0.is_empty());
    }
}
#[test]
fn earliest_physical_public_identity_wins_even_if_its_source_and_digest_are_invalid() {
    let mut m = Module::new("");
    let mut first = bad_source();
    first.public.as_mut().unwrap().obligation_id = "same".into();
    m.proof_obligations = vec![
        row(5, None),
        row(17, Some(first)),
        row(29, Some(source("same"))),
        row(41, Some(source("same"))),
    ];
    let errors = run(&m).0;
    let duplicates = errors
        .iter()
        .filter_map(|e| match e {
            ValidationError::DuplicatePublicObligationId {
                first_obligation,
                duplicate_obligation,
                ..
            } => Some((*first_obligation, *duplicate_obligation)),
            _ => None,
        })
        .collect::<Vec<_>>();
    assert_eq!(duplicates, vec![(17, 29), (17, 41)]);
}
#[test]
fn invalid_oversized_duplicate_public_id_is_not_clipped_or_exempted_from_full_raw_diagnostics() {
    let id = "invalid?λ\0FULLTAIL".repeat(500);
    let mut m = fixture();
    for p in &mut m.proof_obligations {
        p.source
            .as_mut()
            .unwrap()
            .public
            .as_mut()
            .unwrap()
            .obligation_id = id.clone();
    }
    let errors = run(&m).0;
    assert_eq!(errors.len(), 3);
    assert_eq!(
        errors[2],
        ValidationError::DuplicatePublicObligationId {
            obligation_id: id,
            first_obligation: 5,
            duplicate_obligation: 7
        }
    );
}
#[test]
fn source_fields_then_range_then_public_spelling_algorithm_zero_and_duplicate_keep_full_order() {
    let mut m = Module::new("");
    m.proof_obligations = vec![row(5, Some(bad_source())), row(7, Some(bad_source()))];
    let errors = run(&m).0;
    assert_eq!(errors.len(), 17);
    assert!(matches!(
        errors[0],
        ValidationError::InvalidProofObligationSourceTextId {
            field: "source_id",
            ..
        }
    ));
    assert!(matches!(
        errors[1],
        ValidationError::InvalidProofObligationSourceTextId {
            field: "assertion_id",
            ..
        }
    ));
    assert!(matches!(
        errors[5],
        ValidationError::InvalidPublicObligationId { .. }
    ));
    assert!(matches!(
        errors[6],
        ValidationError::PublicObligationDigestNotSha256 { .. }
    ));
    assert!(matches!(
        errors[7],
        ValidationError::PublicObligationDigestZero { .. }
    ));
    assert_eq!(
        errors[16],
        ValidationError::DuplicatePublicObligationId {
            obligation_id: "?bad".into(),
            first_obligation: 5,
            duplicate_obligation: 7
        }
    );
}
#[test]
fn unrelated_obligation_description_and_file_payloads_do_not_enter_identity_validation() {
    let m = fixture();
    let (_, a, cut_a) = run(&m);
    let mut huge = m.clone();
    huge.name = "unused".repeat(100_000);
    huge.files[0] = "unused".repeat(100_000);
    for p in &mut huge.proof_obligations {
        p.description = "unused".repeat(100_000);
    }
    let (_, b, cut_b) = run(&huge);
    assert_eq!(cut_a, cut_b);
    assert_eq!(a.events, b.events);
}
