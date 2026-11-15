// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

use super::*;
pub(super) fn cases() -> Vec<(ValidationError, usize)> {
    vec![
        (
            ValidationError::BindingFrameNotOpen {
                block: 17u32,
                frame_value: 17u32,
            },
            0,
        ),
        (
            ValidationError::BindingSlotOutOfRange {
                block: 17u32,
                frame_id: 17u32,
                slot: 17u32,
                arity: 17u32,
            },
            0,
        ),
        (
            ValidationError::BindingSlotTypeMismatch {
                block: 17u32,
                frame_id: 17u32,
                slot: 17u32,
                expected: String::from("owned λ\0"),
                actual: String::from("owned λ\0"),
            },
            2,
        ),
        (
            ValidationError::BindingBindTypeMismatch {
                block: 17u32,
                frame_id: 17u32,
                slot: 17u32,
                expected: String::from("owned λ\0"),
                actual: String::from("owned λ\0"),
            },
            2,
        ),
        (
            ValidationError::BindingUseAfterClose {
                block: 17u32,
                frame_value: 17u32,
            },
            0,
        ),
        (
            ValidationError::BindingFrameUnclosed {
                block: 17u32,
                frame_id: 17u32,
            },
            0,
        ),
        (
            ValidationError::BindingFrameUnopened {
                block: 17u32,
                frame_value: 17u32,
            },
            0,
        ),
        (
            ValidationError::BindingFrameAnalysisFailed {
                reason: String::from("owned λ\0"),
            },
            1,
        ),
        (
            ValidationError::ConflictingMemoryRoles {
                block: 17u32,
                value: Some(37u32),
                roles: vec![String::from("first"), String::from("second")],
            },
            3,
        ),
        (
            ValidationError::ConflictingFunctionMemoryRoles {
                func_name: String::from("owned λ\0"),
                roles: vec![String::from("first"), String::from("second")],
            },
            4,
        ),
        (
            ValidationError::TaintedValueReachesTrustedSink {
                block: 17u32,
                value: 17u32,
            },
            0,
        ),
        (
            ValidationError::ClosurePureWithStatefulCapture {
                block: 17u32,
                value: Some(37u32),
                closure_ty_id: 17u32,
                capture_index: 17u32,
                capture_ty: String::from("owned λ\0"),
            },
            1,
        ),
        (
            ValidationError::FunctionPureWithStatefulClosureSignature {
                func_name: String::from("owned λ\0"),
                closure_ty_id: 17u32,
                capture_index: 17u32,
                capture_ty: String::from("owned λ\0"),
            },
            2,
        ),
        (
            ValidationError::ClosureTypeNotFound {
                location: String::from("owned λ\0"),
                closure_ty_id: 17u32,
            },
            1,
        ),
        (
            ValidationError::ClosureCaptureArityMismatch {
                location: String::from("owned λ\0"),
                closure_ty_id: 17u32,
                expected: 19usize,
                actual: 19usize,
            },
            1,
        ),
        (
            ValidationError::ClosureCaptureTypeMismatch {
                location: String::from("owned λ\0"),
                closure_ty_id: 17u32,
                capture_index: 19usize,
                expected: String::from("owned λ\0"),
                actual: String::from("owned λ\0"),
            },
            3,
        ),
        (
            ValidationError::InheritedProofCalleeNotFound {
                obligation: 17u32,
                callee: 17u32,
            },
            0,
        ),
        (
            ValidationError::InheritedProofNotDischarged {
                obligation: 17u32,
                callee: 17u32,
                inherited_obligation: 17u32,
            },
            0,
        ),
        (
            ValidationError::InheritedProofCalleeScopeMismatch {
                obligation: 17u32,
                named_callee: 17u32,
                actual_owner: 17u32,
            },
            0,
        ),
        (
            ValidationError::LocalInheritanceRestatementMismatch {
                certificate_obligation: 17u32,
                detail: String::from("owned λ\0"),
            },
            1,
        ),
        (
            ValidationError::CertificateBindingMismatch {
                obligation: 17u32,
                field: String::from("owned λ\0"),
                detail: String::from("owned λ\0"),
            },
            2,
        ),
        (ValidationError::UnboundCertificate { obligation: 17u32 }, 0),
        (
            ValidationError::GatedEvidenceMismatch {
                function: 17u32,
                detail: String::from("owned λ\0"),
            },
            1,
        ),
        (
            ValidationError::UnevidencedGate {
                function: 17u32,
                authority: String::from("owned λ\0"),
            },
            1,
        ),
        (
            ValidationError::DuplicateObligationContent {
                function: 17u32,
                obligations: vec![0, 1, u32::MAX],
            },
            1,
        ),
    ]
}
