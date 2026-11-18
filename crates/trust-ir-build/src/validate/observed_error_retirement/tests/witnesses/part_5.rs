// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

use super::*;
pub(super) fn cases() -> Vec<(ValidationError, usize)> {
    vec![
        (
            ValidationError::ProofContextOnNonCallNode { block: 17u32 },
            0,
        ),
        (
            ValidationError::ProofContextUnknownObligation {
                block: 17u32,
                obligation: 17u32,
            },
            0,
        ),
        (
            ValidationError::ProofContextAssumeNotAuthoritative {
                block: 17u32,
                obligation: 17u32,
            },
            0,
        ),
        (
            ValidationError::ProofContextAssumeScopeMismatch {
                block: 17u32,
                obligation: 17u32,
                callee: 17u32,
                actual_owner: 17u32,
            },
            0,
        ),
        (
            ValidationError::ProofContextEstablishScopeMismatch {
                block: 17u32,
                obligation: 17u32,
                callee: 17u32,
                actual_owner: 17u32,
            },
            0,
        ),
        (
            ValidationError::ProofRefUnresolved {
                function: 17u32,
                obligation: 17u32,
                missing: true,
            },
            0,
        ),
        (
            ValidationError::ProofRefWithoutClaim {
                function: 17u32,
                obligation: 17u32,
            },
            0,
        ),
        (
            ValidationError::ProofRefKindMismatch {
                function: 17u32,
                obligation: 17u32,
                kind: "borrowed static",
            },
            0,
        ),
        (
            ValidationError::ProofRefScopeMismatch {
                function: 17u32,
                obligation: 17u32,
                owner: 17u32,
            },
            0,
        ),
        (
            ValidationError::ProofRefSiteMismatch {
                function: 17u32,
                obligation: 17u32,
            },
            0,
        ),
        (
            ValidationError::ValueRangeInverted {
                function: 17u32,
                lo: -29i128,
                hi: -29i128,
            },
            0,
        ),
        (
            ValidationError::KnownBitsContradiction {
                function: 17u32,
                overlap: 31u128,
            },
            0,
        ),
        (
            ValidationError::CertifiedWithoutCleanCic { obligation: 17u32 },
            0,
        ),
        (
            ValidationError::CertifiedCleanCicLineageMismatch { obligation: 17u32 },
            0,
        ),
        (
            ValidationError::GroundCertificateStatusInconsistent {
                obligation: 17u32,
                status: "borrowed static",
            },
            0,
        ),
        (
            ValidationError::TrustedWithoutJustification { obligation: 17u32 },
            0,
        ),
        (
            ValidationError::ObligationSiteKindMismatch {
                obligation: 17u32,
                kind: "borrowed static",
                op: "borrowed static",
            },
            0,
        ),
        (
            ValidationError::EvidenceKindMismatch {
                obligation: 17u32,
                kind: "borrowed static",
                evidence: "borrowed static",
            },
            0,
        ),
        (
            ValidationError::UnbackedClaimOnCheck {
                function: String::from("owned λ\0"),
                block: 17u32,
                inst_index: 17u32,
                claim: "borrowed static",
            },
            1,
        ),
        (
            ValidationError::BoxDerefTypeMismatch {
                function: String::from("owned λ\0"),
                block: 17u32,
                inst_index: 17u32,
                detail: String::from("owned λ\0"),
            },
            2,
        ),
        (
            ValidationError::BoxDerefPointeeOutOfScope {
                function: String::from("owned λ\0"),
                block: 17u32,
                inst_index: 17u32,
                reason: "borrowed static",
            },
            1,
        ),
        (
            ValidationError::BoxDerefConjunctCover {
                function: String::from("owned λ\0"),
                block: 17u32,
                inst_index: 17u32,
                detail: String::from("owned λ\0"),
            },
            2,
        ),
        (
            ValidationError::BoxDerefPremiseNotPinned {
                function: String::from("owned λ\0"),
                block: 17u32,
                inst_index: 17u32,
                conjunct: "borrowed static",
            },
            1,
        ),
        (
            ValidationError::BoxDerefSessionRefused {
                function: String::from("owned λ\0"),
                block: 17u32,
                inst_index: 17u32,
                reason: "borrowed static",
            },
            1,
        ),
        (
            ValidationError::BoxDerefDominatingCheckInvalid {
                function: String::from("owned λ\0"),
                block: 17u32,
                inst_index: 17u32,
                conjunct: "borrowed static",
                reason: "borrowed static",
            },
            1,
        ),
        (
            ValidationError::BoxDerefConjunctUnestablished {
                function: String::from("owned λ\0"),
                block: 17u32,
                inst_index: 17u32,
                conjunct: "borrowed static",
            },
            1,
        ),
        (
            ValidationError::BoxDerefObligationUnbound {
                function: String::from("owned λ\0"),
                block: 17u32,
                inst_index: 17u32,
                obligation: 17u32,
                reason: "borrowed static",
            },
            1,
        ),
        (
            ValidationError::BoxDerefNonClaimsNotPinned {
                function: String::from("owned λ\0"),
                block: 17u32,
                inst_index: 17u32,
            },
            1,
        ),
        (
            ValidationError::BoxDerefPremiseContradicted {
                function: String::from("owned λ\0"),
                block: 17u32,
                inst_index: 17u32,
                reason: "borrowed static",
            },
            1,
        ),
        (
            ValidationError::BoxValidityEvidenceBelowFloor {
                function: String::from("owned λ\0"),
                block: 17u32,
                inst_index: 17u32,
                conjunct: "borrowed static",
                tier: "borrowed static",
                floor: "borrowed static",
            },
            1,
        ),
        (
            ValidationError::AssertPanicKindUnspecified {
                function: String::from("owned λ\0"),
                block: 17u32,
                inst_index: 17u32,
            },
            1,
        ),
        (
            ValidationError::AssertPanicSiteMissing {
                function: String::from("owned λ\0"),
                block: 17u32,
                inst_index: 17u32,
            },
            1,
        ),
        (
            ValidationError::PanicEntrySignatureMismatch {
                function: String::from("owned λ\0"),
                block: 17u32,
                inst_index: 17u32,
                entry: 17u32,
                expected: String::from("owned λ\0"),
                found: String::from("owned λ\0"),
            },
            3,
        ),
        (
            ValidationError::PanicLocationGlobalInvalid {
                function: String::from("owned λ\0"),
                block: 17u32,
                inst_index: 17u32,
                global: 17u32,
                reason: "borrowed static",
            },
            1,
        ),
        (
            ValidationError::NonCanonicalPanicLocation {
                function: String::from("owned λ\0"),
                block: 17u32,
                inst_index: 17u32,
            },
            1,
        ),
    ]
}
