// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

use super::*;
pub(super) fn cases() -> Vec<(ValidationError, usize)> {
    vec![
        (ValidationError::UnreachableBlock(17u32), 0),
        (
            ValidationError::BranchArgCountMismatch {
                block: 17u32,
                target: 17u32,
                expected: 19usize,
                actual: 19usize,
            },
            0,
        ),
        (
            ValidationError::ReturnTypeMismatch {
                block: 17u32,
                expected: String::from("owned λ\0"),
                actual: String::from("owned λ\0"),
            },
            2,
        ),
        (
            ValidationError::ReturnArityMismatch {
                block: 17u32,
                expected: 19usize,
                actual: 19usize,
            },
            0,
        ),
        (
            ValidationError::CallArgCountMismatch {
                block: 17u32,
                callee: String::from("owned λ\0"),
                expected: 19usize,
                actual: 19usize,
                caller_producer: Some(String::from("optional owned")),
                callee_producer: Some(String::from("optional owned")),
            },
            3,
        ),
        (
            ValidationError::CallArgTypeMismatch {
                block: 17u32,
                callee: String::from("owned λ\0"),
                arg_index: 19usize,
                expected: String::from("owned λ\0"),
                actual: String::from("owned λ\0"),
                caller_producer: Some(String::from("optional owned")),
                callee_producer: Some(String::from("optional owned")),
            },
            5,
        ),
        (
            ValidationError::CalleeNotFound {
                block: 17u32,
                callee_id: 17u32,
            },
            0,
        ),
        (
            ValidationError::SeqMapFwdNotFound {
                block: 17u32,
                fwd_id: 17u32,
            },
            0,
        ),
        (
            ValidationError::SeqMapTypeNotSequence {
                block: 17u32,
                ty: String::from("owned λ\0"),
            },
            1,
        ),
        (
            ValidationError::SeqMapFwdSignatureMismatch {
                block: 17u32,
                fwd: String::from("owned λ\0"),
                expected: String::from("owned λ\0"),
                actual: String::from("owned λ\0"),
            },
            3,
        ),
        (
            ValidationError::GlobalNotFound {
                block: 17u32,
                global_id: 17u32,
            },
            0,
        ),
        (
            ValidationError::CallIndirectSigNotFound {
                block: 17u32,
                sig_id: 17u32,
            },
            0,
        ),
        (
            ValidationError::CallIndirectArgCountMismatch {
                block: 17u32,
                sig_id: 17u32,
                expected: 19usize,
                actual: 19usize,
            },
            0,
        ),
        (
            ValidationError::CallIndirectArgTypeMismatch {
                block: 17u32,
                sig_id: 17u32,
                arg_index: 19usize,
                expected: String::from("owned λ\0"),
                actual: String::from("owned λ\0"),
            },
            2,
        ),
        (
            ValidationError::CallIndirectClosureSigMismatch {
                block: 17u32,
                closure_ty_id: 17u32,
                declared_sig_id: 17u32,
                apparent_sig_id: 17u32,
            },
            0,
        ),
        (
            ValidationError::CallIndirectClosureTargetMismatch {
                block: 17u32,
                closure_ty_id: 17u32,
                target: String::from("owned λ\0"),
                expected: String::from("owned λ\0"),
                actual: String::from("owned λ\0"),
            },
            3,
        ),
        (
            ValidationError::FuncTypeNotFound {
                func_name: String::from("owned λ\0"),
                func_ty_id: 17u32,
            },
            1,
        ),
        (
            ValidationError::InstrResultArityMismatch {
                block: 17u32,
                op: String::from("owned λ\0"),
                expected: 19usize,
                actual: 19usize,
            },
            1,
        ),
        (
            ValidationError::ConstTypeMismatch {
                location: String::from("owned λ\0"),
                expected: String::from("owned λ\0"),
                actual: String::from("owned λ\0"),
            },
            3,
        ),
        (
            ValidationError::ConstTypeReferenceNotFound {
                location: String::from("owned λ\0"),
                type_ref: String::from("owned λ\0"),
            },
            2,
        ),
        (ValidationError::DuplicateStructId(17u32), 0),
        (ValidationError::DuplicateEnumId(17u32), 0),
        (ValidationError::DuplicateFuncId(17u32), 0),
        (
            ValidationError::BindingFrameIdReused {
                block: 17u32,
                frame_id: 17u32,
            },
            0,
        ),
    ]
}
