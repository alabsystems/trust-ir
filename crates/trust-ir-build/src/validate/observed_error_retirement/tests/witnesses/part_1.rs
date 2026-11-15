// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

use super::*;
pub(super) fn cases() -> Vec<(ValidationError, usize)> {
    vec![
        (
            ValidationError::DanglingExternRef {
                detail: String::from("owned λ\0"),
            },
            1,
        ),
        (
            ValidationError::DuplicateFunctionSymbol {
                name: String::from("owned λ\0"),
                first: 17u32,
                second: 17u32,
                first_producer: Some(trust_ir::Producer::Other(String::from("foreign producer"))),
                second_producer: Some(trust_ir::Producer::Other(String::from("foreign producer"))),
                first_display_path: Some(String::from("optional owned")),
                second_display_path: Some(String::from("optional owned")),
            },
            5,
        ),
        (
            ValidationError::SyntheticSymbolName {
                function: 17u32,
                name: String::from("owned λ\0"),
            },
            1,
        ),
        (
            ValidationError::UnloweredRowNamesDefinition {
                symbol: String::from("owned λ\0"),
                function: 17u32,
            },
            1,
        ),
        (
            ValidationError::DuplicateUnloweredRow {
                symbol: String::from("owned λ\0"),
            },
            1,
        ),
        (ValidationError::EmptyPartialClaim, 0),
        (
            ValidationError::UnauthenticatedImport {
                import: 17u32,
                site: "borrowed static",
                detail: String::from("owned λ\0"),
            },
            1,
        ),
        (
            ValidationError::ImportTableNotInterned {
                first: 17u32,
                duplicate: 17u32,
                name: String::from("owned λ\0"),
            },
            1,
        ),
        (
            ValidationError::ImportIdentityConflict {
                first: 17u32,
                conflicting: 17u32,
                first_name: String::from("owned λ\0"),
                conflicting_name: String::from("owned λ\0"),
            },
            2,
        ),
        (
            ValidationError::TypeOriginConflict {
                origin: String::from("owned λ\0"),
                first_module: Some(String::from("optional owned")),
                first_table: "borrowed static",
                first: String::from("owned λ\0"),
                second_module: Some(String::from("optional owned")),
                second_table: "borrowed static",
                second: String::from("owned λ\0"),
            },
            5,
        ),
        (
            ValidationError::AmbiguousImportedSymbol {
                symbol: String::from("owned λ\0"),
                imports: vec![0, 1, u32::MAX],
            },
            2,
        ),
        (
            ValidationError::ImportUnavailable {
                import: 17u32,
                name: String::from("owned λ\0"),
            },
            1,
        ),
        (
            ValidationError::ImportedModuleInvalid {
                import: 17u32,
                errors: 19usize,
                first: String::from("owned λ\0"),
            },
            1,
        ),
        (
            ValidationError::ImportIncomplete {
                import: 17u32,
                site: "borrowed static",
                unlowered: vec![String::from("first"), String::from("second")],
            },
            3,
        ),
        (
            ValidationError::ImportCycle {
                import: 17u32,
                path: vec![String::from("first"), String::from("second")],
            },
            3,
        ),
        (
            ValidationError::ImportClosureTooDeep {
                import: 17u32,
                depth: 19usize,
            },
            0,
        ),
        (
            ValidationError::ExternInheritanceRestatementMismatch {
                certificate_obligation: 17u32,
                evidence_obligation: 17u32,
            },
            0,
        ),
        (
            ValidationError::RustAbiVararg {
                function: 17u32,
                detail: String::from("owned λ\0"),
            },
            1,
        ),
        (ValidationError::BlockMissingTerminator(17u32), 0),
        (ValidationError::DuplicateBlockId(17u32), 0),
        (ValidationError::EntryBlockNotFound(17u32), 0),
        (
            ValidationError::InvalidValueName {
                function: 17u32,
                value: 17u32,
                detail: String::from("owned λ\0"),
            },
            1,
        ),
        (
            ValidationError::InvalidScopeTree {
                function: 17u32,
                scope: 17u32,
                detail: String::from("owned λ\0"),
            },
            1,
        ),
        (
            ValidationError::InvalidInstructionScope {
                function: 17u32,
                block: 17u32,
                instruction: 19usize,
                scope: 17u32,
                scope_count: 19usize,
            },
            0,
        ),
    ]
}
