// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

use super::*;
pub(super) fn cases() -> Vec<(ValidationError, usize)> {
    vec![
        (
            ValidationError::InvalidInlinedScope {
                function: 17u32,
                scope: 17u32,
                detail: String::from("owned λ\0"),
            },
            1,
        ),
        (
            ValidationError::DuplicateValueDef {
                value: 17u32,
                block: 17u32,
            },
            0,
        ),
        (
            ValidationError::UseBeforeDef {
                value: 17u32,
                block: 17u32,
            },
            0,
        ),
        (
            ValidationError::BinOpTypeMismatch {
                block: 17u32,
                op: String::from("owned λ\0"),
                lhs_ty: String::from("owned λ\0"),
                rhs_ty: String::from("owned λ\0"),
            },
            3,
        ),
        (
            ValidationError::BinOpRequiresInteger {
                block: 17u32,
                op: String::from("owned λ\0"),
                ty: String::from("owned λ\0"),
            },
            2,
        ),
        (
            ValidationError::BinOpRequiresFloat {
                block: 17u32,
                op: String::from("owned λ\0"),
                ty: String::from("owned λ\0"),
            },
            2,
        ),
        (
            ValidationError::BinOpRequiresBool {
                block: 17u32,
                op: String::from("owned λ\0"),
                ty: String::from("owned λ\0"),
            },
            2,
        ),
        (ValidationError::UnOpNotOnScalarBool { block: 17u32 }, 0),
        (
            ValidationError::ICmpRequiresIntegerOrPtr {
                block: 17u32,
                ty: String::from("owned λ\0"),
            },
            1,
        ),
        (
            ValidationError::FCmpRequiresFloat {
                block: 17u32,
                ty: String::from("owned λ\0"),
            },
            1,
        ),
        (
            ValidationError::CastIncompatible {
                block: 17u32,
                op: String::from("owned λ\0"),
                src: String::from("owned λ\0"),
                dst: String::from("owned λ\0"),
            },
            3,
        ),
        (
            ValidationError::CastLayoutUnsupported {
                block: 17u32,
                op: String::from("owned λ\0"),
                src: String::from("owned λ\0"),
                dst: String::from("owned λ\0"),
                reason: String::from("owned λ\0"),
            },
            4,
        ),
        (
            ValidationError::PointerOpInvalid {
                block: 17u32,
                op: String::from("owned λ\0"),
                ptr_ty: String::from("owned λ\0"),
                reason: String::from("owned λ\0"),
            },
            3,
        ),
        (
            ValidationError::PointerMetadataTypeMismatch {
                block: 17u32,
                op: String::from("owned λ\0"),
                ptr_ty: String::from("owned λ\0"),
                expected: String::from("owned λ\0"),
                actual: String::from("owned λ\0"),
            },
            4,
        ),
        (
            ValidationError::CondBrRequiresBool {
                block: 17u32,
                cond_ty: String::from("owned λ\0"),
            },
            1,
        ),
        (
            ValidationError::PredicateRequiresBool {
                block: 17u32,
                op: String::from("owned λ\0"),
                cond_ty: String::from("owned λ\0"),
            },
            2,
        ),
        (
            ValidationError::SelectConditionTypeMismatch {
                block: 17u32,
                expected: String::from("owned λ\0"),
                actual: String::from("owned λ\0"),
            },
            2,
        ),
        (
            ValidationError::InvalidVectorType {
                block: 17u32,
                ty: String::from("owned λ\0"),
                reason: String::from("owned λ\0"),
            },
            2,
        ),
        (
            ValidationError::InvalidModuleVectorType {
                location: String::from("owned λ\0"),
                ty: String::from("owned λ\0"),
                reason: String::from("owned λ\0"),
            },
            3,
        ),
        (
            ValidationError::InvalidVectorDialectOp {
                block: 17u32,
                op: String::from("owned λ\0"),
                reason: String::from("owned λ\0"),
            },
            2,
        ),
        (
            ValidationError::InvalidDialectSchema {
                block: 17u32,
                op: String::from("owned λ\0"),
                reason: String::from("owned λ\0"),
            },
            2,
        ),
        (
            ValidationError::InvalidVectorElementOp {
                block: 17u32,
                op: String::from("owned λ\0"),
                reason: String::from("owned λ\0"),
            },
            2,
        ),
        (
            ValidationError::BranchTargetNotFound {
                block: 17u32,
                target: 17u32,
            },
            0,
        ),
        (
            ValidationError::DuplicateSwitchCase {
                block: 17u32,
                value: String::from("owned λ\0"),
            },
            1,
        ),
    ]
}
