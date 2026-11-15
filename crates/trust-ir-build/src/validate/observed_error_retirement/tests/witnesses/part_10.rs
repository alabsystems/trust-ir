// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

use super::*;
pub(super) fn cases() -> Vec<(ValidationError, usize)> {
    vec![
        (
            ValidationError::CoverageAssuranceRequestUnknown {
                obligation: 17u32,
                recorded: trust_ir::proof::ProofDigest {
                    algorithm: trust_ir::proof::ProofDigestAlgorithm::Sha256,
                    bytes: [17; 32],
                },
                bundle_requests: 19usize,
            },
            0,
        ),
        (
            ValidationError::CoverageAssuranceObligationNotRequested {
                obligation: 17u32,
                request: 17u32,
                request_obligations: vec![0, 1, u32::MAX],
            },
            1,
        ),
        (
            ValidationError::CoverageAssuranceBoundMismatch {
                obligation: 17u32,
                recorded: String::from("owned λ\0"),
                derived: String::from("owned λ\0"),
            },
            2,
        ),
        (
            ValidationError::CoverageAttestationSchemaUnsupported {
                detail: String::from("owned λ\0"),
            },
            1,
        ),
        (
            ValidationError::CoverageAttestationRowDuplicate {
                obligation: 17u32,
                solved_bundle: trust_ir::proof::ProofDigest {
                    algorithm: trust_ir::proof::ProofDigestAlgorithm::Sha256,
                    bytes: [17; 32],
                },
                request: trust_ir::proof::ProofDigest {
                    algorithm: trust_ir::proof::ProofDigestAlgorithm::Sha256,
                    bytes: [17; 32],
                },
            },
            0,
        ),
        (
            ValidationError::CoverageSolvedBundleMissing {
                obligation: 17u32,
                recorded: trust_ir::proof::ProofDigest {
                    algorithm: trust_ir::proof::ProofDigestAlgorithm::Sha256,
                    bytes: [17; 32],
                },
                supplied: 19usize,
            },
            0,
        ),
        (
            ValidationError::CoverageSolvedBundleInvalid {
                obligation: 17u32,
                detail: String::from("owned λ\0"),
            },
            1,
        ),
        (
            ValidationError::CoverageSolvedBundleDigestMismatch {
                obligation: 17u32,
                field: "borrowed static",
                recorded: trust_ir::proof::ProofDigest {
                    algorithm: trust_ir::proof::ProofDigestAlgorithm::Sha256,
                    bytes: [17; 32],
                },
                actual: trust_ir::proof::ProofDigest {
                    algorithm: trust_ir::proof::ProofDigestAlgorithm::Sha256,
                    bytes: [17; 32],
                },
            },
            0,
        ),
        (
            ValidationError::CoverageEvidenceMissing {
                obligation: 17u32,
                request: 17u32,
            },
            0,
        ),
        (
            ValidationError::CoverageEvidenceDigestMismatch {
                obligation: 17u32,
                request: 17u32,
                recorded: trust_ir::proof::ProofDigest {
                    algorithm: trust_ir::proof::ProofDigestAlgorithm::Sha256,
                    bytes: [17; 32],
                },
            },
            0,
        ),
        (
            ValidationError::CoverageResultArtifactUnresolved {
                obligation: 17u32,
                artifact: String::from("owned λ\0"),
                reason: String::from("owned λ\0"),
            },
            2,
        ),
        (
            ValidationError::CoverageResultReplayInvalid {
                obligation: 17u32,
                detail: String::from("owned λ\0"),
            },
            1,
        ),
        (
            ValidationError::CoverageModeStrengthMismatch {
                obligation: 17u32,
                request: 17u32,
                mode: String::from("owned λ\0"),
                strength: String::from("owned λ\0"),
            },
            2,
        ),
        (
            ValidationError::CoverageSubjectCodeDrift {
                obligation: 17u32,
                solved: trust_ir::proof::ProofDigest {
                    algorithm: trust_ir::proof::ProofDigestAlgorithm::Sha256,
                    bytes: [17; 32],
                },
                admitted: trust_ir::proof::ProofDigest {
                    algorithm: trust_ir::proof::ProofDigestAlgorithm::Sha256,
                    bytes: [17; 32],
                },
            },
            0,
        ),
        (
            ValidationError::CoverageClaimDrift {
                obligation: 17u32,
                detail: String::from("owned λ\0"),
            },
            1,
        ),
        (
            ValidationError::CoverageContradicted {
                obligation: 17u32,
                detail: String::from("owned λ\0"),
            },
            1,
        ),
        (
            ValidationError::CoverageRowExceedsEstablished {
                obligation: 17u32,
                recorded: String::from("owned λ\0"),
                established: String::from("owned λ\0"),
            },
            2,
        ),
        (
            ValidationError::ImportCoverageBelowClaim {
                import: 17u32,
                site: "borrowed static",
                obligation: 17u32,
                needs: String::from("owned λ\0"),
                far: vec![String::from("first"), String::from("second")],
            },
            4,
        ),
    ]
}
