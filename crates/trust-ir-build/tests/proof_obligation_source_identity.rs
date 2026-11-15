// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use trust_ir::value::ProofId;
use trust_ir::{
    Module, ObligationKind, ProofDigest, ProofObligation, ProofObligationSourceIdentity,
    ProofObligationSourceRange, ProofStatus, PublicObligationIdentity,
};
use trust_ir_build::{ValidationError, validate_module};

fn obligation(id: u32) -> ProofObligation {
    ProofObligation::new(
        ProofId::new(id),
        ObligationKind::Precondition,
        ProofStatus::Pending,
        "x is nonnegative",
    )
}

fn valid_source() -> ProofObligationSourceIdentity {
    ProofObligationSourceIdentity::new("Rust + Lean::módulo α", "assertión exacta 7")
        .with_range(ProofObligationSourceRange {
            file: 0,
            start_line: 17,
            start_col: 3,
            end_line: 19,
            end_col: 11,
        })
        .with_public(PublicObligationIdentity {
            obligation_id: "vc:crate::checked_add:7".to_string(),
            semantic_digest: ProofDigest::sha256([7; 32]),
        })
}

fn module_with(source: Option<ProofObligationSourceIdentity>) -> Module {
    let mut module = Module::new("source_validation");
    module
        .intern_file("src/módulo.rs")
        .expect("Module::intern_file: test fixture");
    let mut proof = obligation(0);
    proof.source = source;
    module.proof_obligations.push(proof);
    module
}

#[test]
fn valid_exact_utf8_identity_and_range_are_accepted() {
    let module = module_with(Some(valid_source()));
    assert!(
        validate_module(&module).is_empty(),
        "{:?}",
        validate_module(&module)
    );
}

#[test]
fn generic_obligations_may_omit_source_or_public_identity() {
    let without_source = module_with(None);
    assert!(validate_module(&without_source).is_empty());

    let without_public = module_with(Some(ProofObligationSourceIdentity::new(
        "Lean::módulo α",
        "assertion with internal spaces",
    )));
    assert!(validate_module(&without_public).is_empty());
}

#[test]
fn source_and_assertion_ids_are_bounded_trimmed_and_control_free() {
    for (field, value) in [
        ("source_id", "".to_string()),
        ("source_id", " leading".to_string()),
        ("source_id", "trailing ".to_string()),
        ("source_id", "line\nbreak".to_string()),
        ("source_id", "x".repeat(1025)),
        ("assertion_id", "\tassertion".to_string()),
    ] {
        let mut source = ProofObligationSourceIdentity::new("valid source", "valid assertion");
        match field {
            "source_id" => source.source_id = value,
            "assertion_id" => source.assertion_id = value,
            _ => unreachable!(),
        }
        let errors = validate_module(&module_with(Some(source)));
        assert!(
            errors.iter().any(|error| matches!(
                error,
                ValidationError::InvalidProofObligationSourceTextId {
                    obligation: 0,
                    field: actual,
                } if *actual == field
            )),
            "missing {field} rejection: {errors:?}"
        );
    }
}

#[test]
fn public_id_uses_strict_canonical_transport_spelling() {
    for invalid in [
        "".to_string(),
        "has space".to_string(),
        "unicode-α".to_string(),
        "query?x".to_string(),
        "fragment#x".to_string(),
        "x".repeat(1025),
    ] {
        let mut source = valid_source();
        source.public.as_mut().unwrap().obligation_id = invalid;
        let errors = validate_module(&module_with(Some(source)));
        assert!(
            errors.iter().any(|error| matches!(
                error,
                ValidationError::InvalidPublicObligationId { obligation: 0 }
            )),
            "missing public-id rejection: {errors:?}"
        );
    }
}

#[test]
fn public_digest_must_be_nonzero_sha256() {
    let mut wrong_algorithm = valid_source();
    wrong_algorithm.public.as_mut().unwrap().semantic_digest =
        ProofDigest::trust_ir_stable("test", b"claim");
    let errors = validate_module(&module_with(Some(wrong_algorithm)));
    assert!(errors.iter().any(|error| matches!(
        error,
        ValidationError::PublicObligationDigestNotSha256 { obligation: 0 }
    )));

    let mut zero = valid_source();
    zero.public.as_mut().unwrap().semantic_digest = ProofDigest::zero();
    let errors = validate_module(&module_with(Some(zero)));
    assert!(errors.iter().any(|error| matches!(
        error,
        ValidationError::PublicObligationDigestZero { obligation: 0 }
    )));
}

#[test]
fn range_requires_real_file_nonzero_lines_and_ordered_exact_end() {
    let mut bad_file = valid_source();
    bad_file.range.as_mut().unwrap().file = 1;
    let errors = validate_module(&module_with(Some(bad_file)));
    assert!(errors.iter().any(|error| matches!(
        error,
        ValidationError::ProofObligationSourceRangeFileOutOfRange {
            obligation: 0,
            file: 1,
            file_count: 1,
        }
    )));

    for mutate in [
        (0, 3, 19, 11),
        (17, 3, 0, 11),
        (19, 3, 18, 11),
        (17, 12, 17, 11),
    ] {
        let mut source = valid_source();
        let range = source.range.as_mut().unwrap();
        (
            range.start_line,
            range.start_col,
            range.end_line,
            range.end_col,
        ) = mutate;
        let errors = validate_module(&module_with(Some(source)));
        assert!(
            errors.iter().any(|error| matches!(
                error,
                ValidationError::InvalidProofObligationSourceRange { obligation: 0, .. }
            )),
            "missing range rejection for {mutate:?}: {errors:?}"
        );
    }

    let mut exact_multiline_end = valid_source();
    let range = exact_multiline_end.range.as_mut().unwrap();
    range.start_line = 17;
    range.start_col = 99;
    range.end_line = 18;
    range.end_col = 0;
    assert!(validate_module(&module_with(Some(exact_multiline_end))).is_empty());
}

#[test]
fn duplicate_public_ids_are_rejected_module_wide() {
    let mut module = Module::new("duplicate_public_ids");
    let source = ProofObligationSourceIdentity::new("rust:crate::f", "assertion").with_public(
        PublicObligationIdentity {
            obligation_id: "vc:crate::f:0".to_string(),
            semantic_digest: ProofDigest::sha256([7; 32]),
        },
    );
    module
        .proof_obligations
        .push(obligation(2).with_source(source.clone()));
    module
        .proof_obligations
        .push(obligation(9).with_source(source));

    let errors = validate_module(&module);
    assert!(
        errors.iter().any(|error| matches!(
            error,
            ValidationError::DuplicatePublicObligationId {
                obligation_id,
                first_obligation: 2,
                duplicate_obligation: 9,
            } if obligation_id == "vc:crate::f:0"
        )),
        "missing duplicate rejection: {errors:?}"
    );
}
