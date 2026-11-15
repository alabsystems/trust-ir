// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

use super::*;
pub(super) fn cases() -> Vec<(ValidationError, usize)> {
    vec![
        (
            ValidationError::TargetPointerSizeInvalid {
                pointer_size: 17u32,
            },
            0,
        ),
        (ValidationError::TargetTripleEmpty, 0),
        (
            ValidationError::TargetScalarLayoutUnavailable {
                struct_id: 17u32,
                triple: String::from("owned λ\0"),
            },
            1,
        ),
        (
            ValidationError::EnumTagTargetScalarLayoutUnavailable {
                enum_id: 17u32,
                triple: String::from("owned λ\0"),
            },
            1,
        ),
        (
            ValidationError::BranchWeightsMismatch {
                reason: "borrowed static",
            },
            0,
        ),
        (
            ValidationError::HavocMarkerMisplaced {
                location: String::from("owned λ\0"),
                marker: "borrowed static",
            },
            1,
        ),
        (
            ValidationError::DanglingDiagnosticObligation { obligation: 17u32 },
            0,
        ),
        (
            ValidationError::TupleLayoutInconsistent {
                reason: String::from("owned λ\0"),
            },
            1,
        ),
        (
            ValidationError::InlineAggregateCycle {
                ty: String::from("owned λ\0"),
            },
            1,
        ),
        (
            ValidationError::StructLayoutInconsistent {
                struct_id: 17u32,
                reason: "borrowed static",
            },
            0,
        ),
        (
            ValidationError::FfiStructReprUnpinned {
                func_name: String::from("owned λ\0"),
                struct_id: 17u32,
                position: "borrowed static",
            },
            1,
        ),
        (
            ValidationError::TargetInfoRequired {
                boundary: String::from("owned λ\0"),
            },
            1,
        ),
        (
            ValidationError::CallEdgeConvMismatch {
                block: 17u32,
                callee: String::from("owned λ\0"),
                declared: String::from("owned λ\0"),
                actual: String::from("owned λ\0"),
            },
            3,
        ),
        (
            ValidationError::CallEdgeSignatureMismatch {
                block: 17u32,
                callee: String::from("owned λ\0"),
                declared: String::from("owned λ\0"),
                actual: String::from("owned λ\0"),
            },
            3,
        ),
        (
            ValidationError::ParamAbiAttrInvalid {
                func_name: String::from("owned λ\0"),
                param_index: 19usize,
                reason: "borrowed static",
            },
            1,
        ),
        (
            ValidationError::PredicateTableMalformed {
                location: String::from("owned λ\0"),
                detail: String::from("owned λ\0"),
            },
            2,
        ),
        (
            ValidationError::PredicateTableNotInterned {
                kind: "borrowed static",
                first: 17u32,
                duplicate: 17u32,
                content: String::from("owned λ\0"),
            },
            1,
        ),
        (
            ValidationError::DanglingPredicateRef {
                location: String::from("owned λ\0"),
                kind: "borrowed static",
                id: 17u32,
            },
            1,
        ),
        (
            ValidationError::RefinementTypeInvalid {
                location: String::from("owned λ\0"),
                detail: String::from("owned λ\0"),
            },
            2,
        ),
        (
            ValidationError::InvalidDialectType {
                location: String::from("owned λ\0"),
                detail: String::from("owned λ\0"),
            },
            2,
        ),
        (
            ValidationError::InvalidHandleType {
                location: String::from("owned λ\0"),
                detail: String::from("owned λ\0"),
            },
            2,
        ),
        (
            ValidationError::UntrustedHandleRuntime {
                location: String::from("owned λ\0"),
                name: String::from("owned λ\0"),
                runtime: String::from("owned λ\0"),
            },
            3,
        ),
        (
            ValidationError::HandleEntryPointSignatureMismatch {
                function: 17u32,
                symbol: String::from("owned λ\0"),
                expected: String::from("owned λ\0"),
                actual: String::from("owned λ\0"),
            },
            3,
        ),
        (
            ValidationError::HandleEntryPointDefinedLocally {
                function: 17u32,
                symbol: String::from("owned λ\0"),
            },
            1,
        ),
    ]
}
