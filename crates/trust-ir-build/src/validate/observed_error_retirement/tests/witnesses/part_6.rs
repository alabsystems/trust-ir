// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

use super::*;
pub(super) fn cases() -> Vec<(ValidationError, usize)> {
    vec![
        (
            ValidationError::CertifiedCleanCicKernelRecheckFailed {
                obligation: 17u32,
                reason: String::from("owned λ\0"),
            },
            1,
        ),
        (
            ValidationError::OperandNotPointer {
                block: 17u32,
                op: String::from("owned λ\0"),
                ty: String::from("owned λ\0"),
            },
            2,
        ),
        (
            ValidationError::GepIndexNotInteger {
                block: 17u32,
                ty: String::from("owned λ\0"),
            },
            1,
        ),
        (
            ValidationError::OperandNotInteger {
                block: 17u32,
                op: String::from("owned λ\0"),
                ty: String::from("owned λ\0"),
            },
            2,
        ),
        (
            ValidationError::OperandTypeMismatch {
                block: 17u32,
                op: String::from("owned λ\0"),
                role: String::from("owned λ\0"),
                expected: String::from("owned λ\0"),
                actual: String::from("owned λ\0"),
            },
            4,
        ),
        (
            ValidationError::FieldAccessInvalid {
                block: 17u32,
                op: String::from("owned λ\0"),
                reason: String::from("owned λ\0"),
            },
            2,
        ),
        (
            ValidationError::IllegalAtomicOrdering {
                block: 17u32,
                op: "borrowed static",
                role: "borrowed static",
                ordering: String::from("owned λ\0"),
                legal: "borrowed static",
            },
            1,
        ),
        (
            ValidationError::BranchArgTypeMismatch {
                block: 17u32,
                target: 17u32,
                arg_index: 19usize,
                expected: String::from("owned λ\0"),
                actual: String::from("owned λ\0"),
            },
            2,
        ),
        (
            ValidationError::UseBeforeDefInBlock {
                value: 17u32,
                block: 17u32,
            },
            0,
        ),
        (
            ValidationError::MidBlockTerminator {
                block: 17u32,
                index: 19usize,
                op: String::from("owned λ\0"),
            },
            1,
        ),
        (ValidationError::MissingTerminator { block: 17u32 }, 0),
        (
            ValidationError::UnwindDestWithoutLandingPad {
                block: 17u32,
                target: 17u32,
            },
            0,
        ),
        (
            ValidationError::MisplacedLandingPad {
                block: 17u32,
                reason: String::from("owned λ\0"),
            },
            1,
        ),
        (
            ValidationError::InvalidDropGlue {
                entry: 19usize,
                glue: 17u32,
                reason: String::from("owned λ\0"),
            },
            1,
        ),
        (
            ValidationError::NonCanonicalDrop {
                function: String::from("owned λ\0"),
                block: 17u32,
                reason: String::from("owned λ\0"),
            },
            2,
        ),
        (
            ValidationError::ExhaustiveSwitchDefaultReachable {
                block: 17u32,
                reason: String::from("owned λ\0"),
            },
            1,
        ),
        (
            ValidationError::ExhaustiveSwitchCasesIncomplete {
                block: 17u32,
                enum_ty: String::from("owned λ\0"),
                reason: String::from("owned λ\0"),
            },
            2,
        ),
        (
            ValidationError::FuncAttrClaimViolated {
                function: String::from("owned λ\0"),
                attr: "borrowed static",
                block: 17u32,
                inst: String::from("owned λ\0"),
            },
            2,
        ),
        (
            ValidationError::EffectSummaryViolated {
                function: String::from("owned λ\0"),
                effect: "borrowed static",
                block: 17u32,
                inst: String::from("owned λ\0"),
            },
            2,
        ),
        (
            ValidationError::BorrowMutThroughSharedRef { block: 17u32 },
            0,
        ),
        (ValidationError::EndBorrowOfNonBorrow { block: 17u32 }, 0),
        (
            ValidationError::RustReferenceAsPermissionBorrow {
                function: String::from("owned λ\0"),
                block: 17u32,
                inst_index: 19usize,
            },
            1,
        ),
        (
            ValidationError::CastOperandTypeMismatch {
                block: 17u32,
                op: String::from("owned λ\0"),
                declared_src: String::from("owned λ\0"),
                actual: String::from("owned λ\0"),
            },
            3,
        ),
        (
            ValidationError::CastWidthDirectionInvalid {
                block: 17u32,
                op: String::from("owned λ\0"),
                src: String::from("owned λ\0"),
                dst: String::from("owned λ\0"),
                reason: String::from("owned λ\0"),
            },
            4,
        ),
    ]
}
