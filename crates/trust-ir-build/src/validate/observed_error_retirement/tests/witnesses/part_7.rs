// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

use super::*;
pub(super) fn cases() -> Vec<(ValidationError, usize)> {
    vec![
        (
            ValidationError::EntryParamsMismatch {
                func_name: String::from("owned λ\0"),
                expected: String::from("owned λ\0"),
                actual: String::from("owned λ\0"),
            },
            3,
        ),
        (
            ValidationError::DanglingTypeReference {
                location: String::from("owned λ\0"),
                kind: "borrowed static",
                id: 17u32,
            },
            1,
        ),
        (ValidationError::DuplicateProofObligationId(17u32), 0),
        (
            ValidationError::InvalidProofObligationSourceTextId {
                obligation: 17u32,
                field: "borrowed static",
            },
            0,
        ),
        (
            ValidationError::ProofObligationSourceRangeFileOutOfRange {
                obligation: 17u32,
                file: 17u32,
                file_count: 19usize,
            },
            0,
        ),
        (
            ValidationError::ObligationSiteFunctionMismatch {
                obligation: 17u32,
                site_function: 17u32,
                scope_function: 17u32,
            },
            0,
        ),
        (
            ValidationError::ObligationSiteOutOfRange {
                obligation: 17u32,
                function: 17u32,
                block: 17u32,
                inst_index: 17u32,
                reason: "borrowed static",
            },
            0,
        ),
        (
            ValidationError::InvalidObligationBinding {
                obligation: 17u32,
                detail: String::from("owned λ\0"),
            },
            1,
        ),
        (
            ValidationError::FormulaTextsDisagree {
                site: trust_ir::proof::FormulaSite::SpecTemporal {
                    machine: "machine".into(),
                    property: "property".into(),
                },
            },
            2,
        ),
        (
            ValidationError::UnresolvedObligationSpecRef {
                obligation: 17u32,
                machine: String::from("owned λ\0"),
                temporal: String::from("owned λ\0"),
                reason: "borrowed static",
            },
            2,
        ),
        (
            ValidationError::ObligationFunctionScopeUnresolved {
                obligation: 17u32,
                function: 17u32,
                reason: "borrowed static",
            },
            0,
        ),
        (
            ValidationError::InvalidProofObligationSourceRange {
                obligation: 17u32,
                reason: "borrowed static",
            },
            0,
        ),
        (
            ValidationError::InvalidPublicObligationId { obligation: 17u32 },
            0,
        ),
        (
            ValidationError::PublicObligationDigestNotSha256 { obligation: 17u32 },
            0,
        ),
        (
            ValidationError::PublicObligationDigestZero { obligation: 17u32 },
            0,
        ),
        (
            ValidationError::DuplicatePublicObligationId {
                obligation_id: String::from("owned λ\0"),
                first_obligation: 17u32,
                duplicate_obligation: 17u32,
            },
            1,
        ),
        (
            ValidationError::DischargedWithoutCertificate { obligation: 17u32 },
            0,
        ),
        (
            ValidationError::DanglingProofCertificate { obligation: 17u32 },
            0,
        ),
        (
            ValidationError::SpanFileIndexOutOfRange {
                file: 17u32,
                file_count: 19usize,
            },
            0,
        ),
        (
            ValidationError::TransparentReprFieldCount {
                struct_id: 17u32,
                actual_non_zst: 19usize,
            },
            0,
        ),
        (
            ValidationError::PackedReprInvalidAlign {
                struct_id: 17u32,
                align: 17u32,
            },
            0,
        ),
        (
            ValidationError::AccessAlignInvalid {
                inst: "borrowed static",
                align: 23u64,
            },
            0,
        ),
        (
            ValidationError::GlobalAlignInvalid {
                global: String::from("owned λ\0"),
                align: 17u32,
            },
            1,
        ),
        (
            ValidationError::WrappingConflictsWithNoOverflow { block: 17u32 },
            0,
        ),
    ]
}
