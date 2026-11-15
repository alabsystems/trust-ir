// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

use super::*;
pub(super) fn cases() -> Vec<(ValidationError, usize)> {
    vec![
        (
            ValidationError::HandleEntryPointShadowedByGlobal {
                global: String::from("owned λ\0"),
                symbol: String::from("owned λ\0"),
            },
            2,
        ),
        (
            ValidationError::HandleEntryPointAddressTaken {
                location: String::from("owned λ\0"),
                symbol: String::from("owned λ\0"),
            },
            2,
        ),
        (
            ValidationError::RcEntryPointSignatureMismatch {
                function: 17u32,
                symbol: String::from("owned λ\0"),
                expected: String::from("owned λ\0"),
                actual: String::from("owned λ\0"),
            },
            3,
        ),
        (
            ValidationError::RcEntryPointDefinedLocally {
                function: 17u32,
                symbol: String::from("owned λ\0"),
            },
            1,
        ),
        (
            ValidationError::RcEntryPointShadowedByGlobal {
                global: String::from("owned λ\0"),
                symbol: String::from("owned λ\0"),
            },
            2,
        ),
        (
            ValidationError::RcEntryPointAddressTaken {
                location: String::from("owned λ\0"),
                symbol: String::from("owned λ\0"),
            },
            2,
        ),
        (
            ValidationError::DirectCallToWeakDeclaration {
                location: String::from("owned λ\0"),
                callee: 17u32,
                name: String::from("owned λ\0"),
            },
            2,
        ),
        (
            ValidationError::WeakDeclarationAsFnDef {
                location: String::from("owned λ\0"),
                function: 17u32,
                name: String::from("owned λ\0"),
            },
            2,
        ),
        (
            ValidationError::WeakDeclarationAddressNotNullable {
                location: String::from("owned λ\0"),
                symbol: String::from("owned λ\0"),
                detail: String::from("owned λ\0"),
            },
            3,
        ),
        (
            ValidationError::HandleForeignDeclaration {
                function: 17u32,
                name: String::from("owned λ\0"),
                handle: String::from("owned λ\0"),
                detail: String::from("owned λ\0"),
            },
            3,
        ),
        (
            ValidationError::InvalidHandleUse {
                location: String::from("owned λ\0"),
                detail: String::from("owned λ\0"),
            },
            2,
        ),
        (
            ValidationError::HandleRuntimeSpelledStructurally {
                def: String::from("owned λ\0"),
                runtime: String::from("owned λ\0"),
            },
            2,
        ),
        (
            ValidationError::HandleLaneNiche {
                enum_name: String::from("owned λ\0"),
                variant: 17u32,
                field: 17u32,
                detail: String::from("owned λ\0"),
            },
            2,
        ),
        (
            ValidationError::UninhabitedVariantConstructed {
                location: String::from("owned λ\0"),
                enum_name: String::from("owned λ\0"),
                variant: 17u32,
                variant_name: String::from("owned λ\0"),
            },
            3,
        ),
        (
            ValidationError::InvalidMakeAggregate {
                block: 17u32,
                ty: String::from("owned λ\0"),
                reason: String::from("owned λ\0"),
            },
            2,
        ),
        (
            ValidationError::InvalidArraySplat {
                block: 17u32,
                ty: String::from("owned λ\0"),
                reason: String::from("owned λ\0"),
            },
            2,
        ),
        (
            ValidationError::NonCanonicalUniformArray {
                location: String::from("owned λ\0"),
                spelling: String::from("owned λ\0"),
            },
            2,
        ),
        (
            ValidationError::PointerConstantRefused {
                location: String::from("owned λ\0"),
                symbol: String::from("owned λ\0"),
                ty: String::from("owned λ\0"),
                reason: PointerConstantRefusal::PointeeTypeMismatch {
                    global_ty: "pointer type".into(),
                },
            },
            4,
        ),
        (
            ValidationError::RefinementNotImplied {
                location: String::from("owned λ\0"),
                actual: String::from("owned λ\0"),
                required: String::from("owned λ\0"),
            },
            3,
        ),
        (
            ValidationError::RefinementContradicted {
                location: String::from("owned λ\0"),
                declared: String::from("owned λ\0"),
                derived: String::from("owned λ\0"),
            },
            3,
        ),
        (
            ValidationError::GlobalAsmNotConsumable { blocks: 19usize },
            0,
        ),
        (
            ValidationError::UnpinnedCustomObligationNamespace {
                obligation: 17u32,
                namespace: String::from("owned λ\0"),
                name: String::from("owned λ\0"),
            },
            2,
        ),
        (
            ValidationError::NativeBundleNotForThisModule {
                expected: trust_ir::proof::ProofDigest {
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
            ValidationError::ModuleHasNoWireIdentity {
                location: String::from("owned λ\0"),
                construct: String::from("owned λ\0"),
            },
            2,
        ),
    ]
}
