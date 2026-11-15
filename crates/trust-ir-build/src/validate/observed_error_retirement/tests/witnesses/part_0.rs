// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

use super::*;
pub(super) fn cases() -> Vec<(ValidationError, usize)> {
    vec![
        (ValidationError::EmptyFunction, 0),
        (
            ValidationError::InvalidSpecAnchorFunction {
                machine: String::from("owned λ\0"),
                action: String::from("owned λ\0"),
                function: 17u32,
                detail: String::from("owned λ\0"),
            },
            3,
        ),
        (
            ValidationError::InvalidSpecProjectionFunction {
                machine: String::from("owned λ\0"),
                action: String::from("owned λ\0"),
                function: 17u32,
                detail: String::from("owned λ\0"),
            },
            3,
        ),
        (ValidationError::BlankModuleName, 0),
        (
            ValidationError::InvalidSpecStructure {
                violation: trust_ir::SpecLinkViolation::SpecTypedBindingInvalid {
                    machine: "machine".into(),
                    subject: "subject",
                    name: "name".into(),
                    binding: "binding".into(),
                    detail: "detail".into(),
                },
            },
            4,
        ),
        (
            ValidationError::SpecLinkedFormulaUnparsed {
                module: String::from("owned λ\0"),
                invariant: String::from("owned λ\0"),
                detail: String::from("owned λ\0"),
            },
            3,
        ),
        (
            ValidationError::SpecLinkedVariableUnparsed {
                module: String::from("owned λ\0"),
                variable: String::from("owned λ\0"),
                detail: String::from("owned λ\0"),
            },
            3,
        ),
        (
            ValidationError::InvalidFunctionSummary {
                function: 17u32,
                detail: String::from("owned λ\0"),
            },
            1,
        ),
        (
            ValidationError::InvalidSourceProvenance {
                function: 17u32,
                detail: String::from("owned λ\0"),
            },
            1,
        ),
        (
            ValidationError::InvalidBodyGate {
                function: 17u32,
                detail: String::from("owned λ\0"),
            },
            1,
        ),
        (
            ValidationError::InvalidDisplayPath {
                function: 17u32,
                detail: String::from("owned λ\0"),
            },
            1,
        ),
        (
            ValidationError::InvalidFunctionSection {
                function: 17u32,
                detail: String::from("owned λ\0"),
            },
            1,
        ),
        (
            ValidationError::InvalidAbiSlotFact {
                function: 17u32,
                slot: String::from("owned λ\0"),
                detail: String::from("owned λ\0"),
            },
            2,
        ),
        (
            ValidationError::InvalidSignatureAbi {
                signature: 17u32,
                detail: String::from("owned λ\0"),
            },
            1,
        ),
        (
            ValidationError::AlwaysMemoryByValueAggregate {
                func_ty: 17u32,
                slot: String::from("owned λ\0"),
                ty: String::from("owned λ\0"),
            },
            2,
        ),
        (
            ValidationError::ContradictoryFunctionVisibility {
                function: 17u32,
                linkage: trust_ir::Linkage::External,
                visibility: trust_ir::Visibility::Hidden,
            },
            0,
        ),
        (
            ValidationError::UngatedBodyForCodegen {
                function: 17u32,
                name: String::from("owned λ\0"),
            },
            1,
        ),
        (
            ValidationError::UnlicensedBodyForCodegen {
                function: 17u32,
                name: String::from("owned λ\0"),
            },
            1,
        ),
        (
            ValidationError::ProducerOmittedBodyGate {
                function: 17u32,
                name: String::from("owned λ\0"),
                wire_version: 17u32,
            },
            1,
        ),
        (
            ValidationError::GatedWithoutEvidence {
                function: 17u32,
                authority: String::from("owned λ\0"),
                detail: String::from("owned λ\0"),
            },
            2,
        ),
        (
            ValidationError::GatedFunctionRefuted {
                function: 17u32,
                obligation: 17u32,
            },
            0,
        ),
        (
            ValidationError::UnrecognizedGateAuthority {
                function: 17u32,
                authority: String::from("owned λ\0"),
            },
            1,
        ),
        (
            ValidationError::UnlowerableForCodegen {
                function: 17u32,
                name: String::from("owned λ\0"),
                block: 17u32,
                inst: "borrowed static",
                detail: String::from("owned λ\0"),
            },
            2,
        ),
        (
            ValidationError::ReservedSpecModuleName {
                name: String::from("owned λ\0"),
                detail: String::from("owned λ\0"),
            },
            2,
        ),
    ]
}
