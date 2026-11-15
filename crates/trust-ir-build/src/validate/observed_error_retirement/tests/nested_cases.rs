// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
pub(super) fn specs() -> Vec<(ValidationError, usize)> {
    vec![
        (
            ValidationError::InvalidSpecStructure {
                violation: trust_ir::SpecLinkViolation::DuplicateMachineIdentity {
                    machine: String::from("nested owned λ"),
                },
            },
            1,
        ),
        (
            ValidationError::InvalidSpecStructure {
                violation: trust_ir::SpecLinkViolation::DuplicateMemberIdentity {
                    machine: String::from("nested owned λ"),
                    member: "static borrowed",
                    name: String::from("nested owned λ"),
                },
            },
            2,
        ),
        (
            ValidationError::InvalidSpecStructure {
                violation: trust_ir::SpecLinkViolation::BlankSemanticValue {
                    container: String::from("nested owned λ"),
                    subject: "static borrowed",
                    field: "static borrowed",
                },
            },
            1,
        ),
        (
            ValidationError::InvalidSpecStructure {
                violation: trust_ir::SpecLinkViolation::DuplicateBindingIdentity {
                    machine: String::from("nested owned λ"),
                    binding: "static borrowed",
                    identity: String::from("nested owned λ"),
                },
            },
            2,
        ),
        (
            ValidationError::InvalidSpecStructure {
                violation: trust_ir::SpecLinkViolation::AnchorWaiverConflict {
                    machine: String::from("nested owned λ"),
                    action: String::from("nested owned λ"),
                },
            },
            2,
        ),
        (
            ValidationError::InvalidSpecStructure {
                violation: trust_ir::SpecLinkViolation::ReferenceContainerMismatch {
                    container: String::from("nested owned λ"),
                    machine: String::from("nested owned λ"),
                    action: String::from("nested owned λ"),
                    from: "static borrowed",
                },
            },
            3,
        ),
        (
            ValidationError::InvalidSpecStructure {
                violation: trust_ir::SpecLinkViolation::TypedTargetRequired {
                    machine: String::from("nested owned λ"),
                    action: String::from("nested owned λ"),
                    target: "static borrowed",
                },
            },
            2,
        ),
        (
            ValidationError::InvalidSpecStructure {
                violation: trust_ir::SpecLinkViolation::ProjectionTargetIncompatible {
                    machine: String::from("nested owned λ"),
                    action: String::from("nested owned λ"),
                    detail: String::from("nested owned λ"),
                },
            },
            3,
        ),
        (
            ValidationError::InvalidSpecStructure {
                violation: trust_ir::SpecLinkViolation::ExecutableTargetInvalid {
                    machine: String::from("nested owned λ"),
                    action: String::from("nested owned λ"),
                    target: "static borrowed",
                    function: 7,
                    detail: String::from("nested owned λ"),
                },
            },
            3,
        ),
        (
            ValidationError::InvalidSpecStructure {
                violation: trust_ir::SpecLinkViolation::ActionMissing {
                    machine: String::from("nested owned λ"),
                    action: String::from("nested owned λ"),
                    from: "static borrowed",
                    detail: String::from("nested owned λ"),
                },
            },
            3,
        ),
        (
            ValidationError::InvalidSpecStructure {
                violation: trust_ir::SpecLinkViolation::MachineMissing {
                    machine: String::from("nested owned λ"),
                    action: String::from("nested owned λ"),
                    from: "static borrowed",
                    detail: String::from("nested owned λ"),
                },
            },
            3,
        ),
        (
            ValidationError::InvalidSpecStructure {
                violation: trust_ir::SpecLinkViolation::ActionUncovered {
                    machine: String::from("nested owned λ"),
                    action: String::from("nested owned λ"),
                },
            },
            2,
        ),
        (
            ValidationError::InvalidSpecStructure {
                violation: trust_ir::SpecLinkViolation::ProjectionMissing {
                    machine: String::from("nested owned λ"),
                    action: String::from("nested owned λ"),
                },
            },
            2,
        ),
        (
            ValidationError::InvalidSpecStructure {
                violation: trust_ir::SpecLinkViolation::ProofUnresolved {
                    machine: String::from("nested owned λ"),
                    action: String::from("nested owned λ"),
                    proof_name: String::from("nested owned λ"),
                },
            },
            3,
        ),
        (
            ValidationError::InvalidSpecStructure {
                violation: trust_ir::SpecLinkViolation::ProofManifestRequired {
                    machine: String::from("nested owned λ"),
                },
            },
            1,
        ),
        (
            ValidationError::InvalidSpecStructure {
                violation: trust_ir::SpecLinkViolation::LinkedFormulaUnparsed {
                    machine: String::from("nested owned λ"),
                    invariant: String::from("nested owned λ"),
                    detail: String::from("nested owned λ"),
                },
            },
            3,
        ),
        (
            ValidationError::InvalidSpecStructure {
                violation: trust_ir::SpecLinkViolation::LinkedVariableUnparsed {
                    machine: String::from("nested owned λ"),
                    variable: String::from("nested owned λ"),
                    detail: String::from("nested owned λ"),
                },
            },
            3,
        ),
        (
            ValidationError::InvalidSpecStructure {
                violation: trust_ir::SpecLinkViolation::LinkedTypedCarrierUnparsed {
                    machine: String::from("nested owned λ"),
                    subject: "static borrowed",
                    name: String::from("nested owned λ"),
                    detail: String::from("nested owned λ"),
                },
            },
            3,
        ),
        (
            ValidationError::InvalidSpecStructure {
                violation: trust_ir::SpecLinkViolation::LinkedTypedCarrierDisagrees {
                    machine: String::from("nested owned λ"),
                    invariant: String::from("nested owned λ"),
                    detail: String::from("nested owned λ"),
                },
            },
            3,
        ),
        (
            ValidationError::InvalidSpecStructure {
                violation: trust_ir::SpecLinkViolation::SpecTypedBindingInvalid {
                    machine: String::from("nested owned λ"),
                    subject: "static borrowed",
                    name: String::from("nested owned λ"),
                    binding: String::from("nested owned λ"),
                    detail: String::from("nested owned λ"),
                },
            },
            4,
        ),
        (
            ValidationError::InvalidSpecStructure {
                violation: trust_ir::SpecLinkViolation::SpecVariableSortMismatch {
                    machine: String::from("nested owned λ"),
                    variable: String::from("nested owned λ"),
                    detail: String::from("nested owned λ"),
                },
            },
            3,
        ),
        (
            ValidationError::InvalidSpecStructure {
                violation: trust_ir::SpecLinkViolation::CleanTheoremUnresolved {
                    machine: String::from("nested owned λ"),
                    action: String::from("nested owned λ"),
                    theorem: String::from("nested owned λ"),
                    detail: String::from("nested owned λ"),
                },
            },
            4,
        ),
    ]
}
pub(super) fn pointers() -> Vec<(ValidationError, usize)> {
    vec![
        (
            ValidationError::PointerConstantRefused {
                location: "location".into(),
                symbol: "symbol".into(),
                ty: "ty".into(),
                reason: PointerConstantRefusal::NotAModuleGlobal,
            },
            3,
        ),
        (
            ValidationError::PointerConstantRefused {
                location: "location".into(),
                symbol: "symbol".into(),
                ty: "ty".into(),
                reason: PointerConstantRefusal::AmbiguousSymbol {
                    globals: 11,
                    functions: 11,
                },
            },
            3,
        ),
        (
            ValidationError::PointerConstantRefused {
                location: "location".into(),
                symbol: "symbol".into(),
                ty: "ty".into(),
                reason: PointerConstantRefusal::GlobalNotDefined,
            },
            3,
        ),
        (
            ValidationError::PointerConstantRefused {
                location: "location".into(),
                symbol: "symbol".into(),
                ty: "ty".into(),
                reason: PointerConstantRefusal::ThreadLocal,
            },
            3,
        ),
        (
            ValidationError::PointerConstantRefused {
                location: "location".into(),
                symbol: "symbol".into(),
                ty: "ty".into(),
                reason: PointerConstantRefusal::InterposableLinkage {
                    linkage: trust_ir::Linkage::Weak,
                },
            },
            3,
        ),
        (
            ValidationError::PointerConstantRefused {
                location: "location".into(),
                symbol: "symbol".into(),
                ty: "ty".into(),
                reason: PointerConstantRefusal::NonzeroAddend { addend: -17 },
            },
            3,
        ),
        (
            ValidationError::PointerConstantRefused {
                location: "location".into(),
                symbol: "symbol".into(),
                ty: "ty".into(),
                reason: PointerConstantRefusal::PointeeTypeMismatch {
                    global_ty: String::from("nested owned λ"),
                },
            },
            4,
        ),
        (
            ValidationError::PointerConstantRefused {
                location: "location".into(),
                symbol: "symbol".into(),
                ty: "ty".into(),
                reason: PointerConstantRefusal::MutabilityMismatch {
                    global_mutable: true,
                },
            },
            3,
        ),
        (
            ValidationError::PointerConstantRefused {
                location: "location".into(),
                symbol: "symbol".into(),
                ty: "ty".into(),
                reason: PointerConstantRefusal::ArrayTypeMismatch {
                    global_ty: String::from("nested owned λ"),
                },
            },
            4,
        ),
        (
            ValidationError::PointerConstantRefused {
                location: "location".into(),
                symbol: "symbol".into(),
                ty: "ty".into(),
                reason: PointerConstantRefusal::InvalidLength {
                    length: String::from("nested owned λ"),
                },
            },
            4,
        ),
        (
            ValidationError::PointerConstantRefused {
                location: "location".into(),
                symbol: "symbol".into(),
                ty: "ty".into(),
                reason: PointerConstantRefusal::WindowOutOfBounds {
                    offset: -17,
                    length: 13,
                    capacity: 13,
                },
            },
            3,
        ),
        (
            ValidationError::PointerConstantRefused {
                location: "location".into(),
                symbol: "symbol".into(),
                ty: "ty".into(),
                reason: PointerConstantRefusal::MisalignedOffset {
                    offset: -17,
                    element_size: 13,
                },
            },
            3,
        ),
        (
            ValidationError::PointerConstantRefused {
                location: "location".into(),
                symbol: "symbol".into(),
                ty: "ty".into(),
                reason: PointerConstantRefusal::ElementLayoutUnknown,
            },
            3,
        ),
        (
            ValidationError::PointerConstantRefused {
                location: "location".into(),
                symbol: "symbol".into(),
                ty: "ty".into(),
                reason: PointerConstantRefusal::NotUtf8Bytes,
            },
            3,
        ),
        (
            ValidationError::PointerConstantRefused {
                location: "location".into(),
                symbol: "symbol".into(),
                ty: "ty".into(),
                reason: PointerConstantRefusal::NotOnCharBoundary,
            },
            3,
        ),
    ]
}
pub(super) fn formulas() -> Vec<(ValidationError, usize)> {
    vec![
        (
            ValidationError::FormulaTextsDisagree {
                site: trust_ir::proof::FormulaSite::Obligation(trust_ir::value::ProofId::new(7)),
            },
            0,
        ),
        (
            ValidationError::FormulaTextsDisagree {
                site: trust_ir::proof::FormulaSite::SummaryClause {
                    function: trust_ir::value::FuncId::new(11),
                    clause: "static borrowed",
                    index: 11,
                },
            },
            0,
        ),
        (
            ValidationError::FormulaTextsDisagree {
                site: trust_ir::proof::FormulaSite::SpecInvariant {
                    machine: String::from("nested owned λ"),
                    invariant: String::from("nested owned λ"),
                },
            },
            2,
        ),
        (
            ValidationError::FormulaTextsDisagree {
                site: trust_ir::proof::FormulaSite::SpecTemporal {
                    machine: String::from("nested owned λ"),
                    property: String::from("nested owned λ"),
                },
            },
            2,
        ),
    ]
}
