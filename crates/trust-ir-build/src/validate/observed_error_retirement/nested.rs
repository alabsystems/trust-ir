// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

use super::*;
use trust_ir::proof::{FormulaSite, ProofDigest};
use trust_ir::{Producer, SpecLinkViolation};
impl<O: ExecutionObserver> Work<'_, '_, O> {
    pub(super) fn violation(&mut self, value: SpecLinkViolation) {
        self.step(22);
        match value {
            SpecLinkViolation::DuplicateMachineIdentity { machine } => {
                self.string(machine);
            }
            SpecLinkViolation::DuplicateMemberIdentity {
                machine,
                member,
                name,
            } => {
                self.string(machine);
                self.fixed(member);
                self.string(name);
            }
            SpecLinkViolation::BlankSemanticValue {
                container,
                subject,
                field,
            } => {
                self.string(container);
                self.fixed(subject);
                self.fixed(field);
            }
            SpecLinkViolation::DuplicateBindingIdentity {
                machine,
                binding,
                identity,
            } => {
                self.string(machine);
                self.fixed(binding);
                self.string(identity);
            }
            SpecLinkViolation::AnchorWaiverConflict { machine, action } => {
                self.string(machine);
                self.string(action);
            }
            SpecLinkViolation::ReferenceContainerMismatch {
                container,
                machine,
                action,
                from,
            } => {
                self.string(container);
                self.string(machine);
                self.string(action);
                self.fixed(from);
            }
            SpecLinkViolation::TypedTargetRequired {
                machine,
                action,
                target,
            } => {
                self.string(machine);
                self.string(action);
                self.fixed(target);
            }
            SpecLinkViolation::ProjectionTargetIncompatible {
                machine,
                action,
                detail,
            } => {
                self.string(machine);
                self.string(action);
                self.string(detail);
            }
            SpecLinkViolation::ExecutableTargetInvalid {
                machine,
                action,
                target,
                function,
                detail,
            } => {
                self.string(machine);
                self.string(action);
                self.fixed(target);
                self.fixed(function);
                self.string(detail);
            }
            SpecLinkViolation::ActionMissing {
                machine,
                action,
                from,
                detail,
            } => {
                self.string(machine);
                self.string(action);
                self.fixed(from);
                self.string(detail);
            }
            SpecLinkViolation::MachineMissing {
                machine,
                action,
                from,
                detail,
            } => {
                self.string(machine);
                self.string(action);
                self.fixed(from);
                self.string(detail);
            }
            SpecLinkViolation::ActionUncovered { machine, action } => {
                self.string(machine);
                self.string(action);
            }
            SpecLinkViolation::ProjectionMissing { machine, action } => {
                self.string(machine);
                self.string(action);
            }
            SpecLinkViolation::ProofUnresolved {
                machine,
                action,
                proof_name,
            } => {
                self.string(machine);
                self.string(action);
                self.string(proof_name);
            }
            SpecLinkViolation::ProofManifestRequired { machine } => {
                self.string(machine);
            }
            SpecLinkViolation::LinkedFormulaUnparsed {
                machine,
                invariant,
                detail,
            } => {
                self.string(machine);
                self.string(invariant);
                self.string(detail);
            }
            SpecLinkViolation::LinkedVariableUnparsed {
                machine,
                variable,
                detail,
            } => {
                self.string(machine);
                self.string(variable);
                self.string(detail);
            }
            SpecLinkViolation::LinkedTypedCarrierUnparsed {
                machine,
                subject,
                name,
                detail,
            } => {
                self.string(machine);
                self.fixed(subject);
                self.string(name);
                self.string(detail);
            }
            SpecLinkViolation::LinkedTypedCarrierDisagrees {
                machine,
                invariant,
                detail,
            } => {
                self.string(machine);
                self.string(invariant);
                self.string(detail);
            }
            SpecLinkViolation::SpecTypedBindingInvalid {
                machine,
                subject,
                name,
                binding,
                detail,
            } => {
                self.string(machine);
                self.fixed(subject);
                self.string(name);
                self.string(binding);
                self.string(detail);
            }
            SpecLinkViolation::SpecVariableSortMismatch {
                machine,
                variable,
                detail,
            } => {
                self.string(machine);
                self.string(variable);
                self.string(detail);
            }
            SpecLinkViolation::CleanTheoremUnresolved {
                machine,
                action,
                theorem,
                detail,
            } => {
                self.string(machine);
                self.string(action);
                self.string(theorem);
                self.string(detail);
            }
        }
    }
    pub(super) fn refusal(&mut self, value: PointerConstantRefusal) {
        self.step(15);
        match value {
            PointerConstantRefusal::NotAModuleGlobal => {
                self.fixed(());
            }
            PointerConstantRefusal::AmbiguousSymbol { globals, functions } => {
                self.fixed(globals);
                self.fixed(functions);
            }
            PointerConstantRefusal::GlobalNotDefined => {
                self.fixed(());
            }
            PointerConstantRefusal::ThreadLocal => {
                self.fixed(());
            }
            PointerConstantRefusal::InterposableLinkage { linkage } => {
                self.fixed(linkage);
            }
            PointerConstantRefusal::NonzeroAddend { addend } => {
                self.fixed(addend);
            }
            PointerConstantRefusal::PointeeTypeMismatch { global_ty } => {
                self.string(global_ty);
            }
            PointerConstantRefusal::MutabilityMismatch { global_mutable } => {
                self.fixed(global_mutable);
            }
            PointerConstantRefusal::ArrayTypeMismatch { global_ty } => {
                self.string(global_ty);
            }
            PointerConstantRefusal::InvalidLength { length } => {
                self.string(length);
            }
            PointerConstantRefusal::WindowOutOfBounds {
                offset,
                length,
                capacity,
            } => {
                self.fixed(offset);
                self.fixed(length);
                self.fixed(capacity);
            }
            PointerConstantRefusal::MisalignedOffset {
                offset,
                element_size,
            } => {
                self.fixed(offset);
                self.fixed(element_size);
            }
            PointerConstantRefusal::ElementLayoutUnknown => {
                self.fixed(());
            }
            PointerConstantRefusal::NotUtf8Bytes => {
                self.fixed(());
            }
            PointerConstantRefusal::NotOnCharBoundary => {
                self.fixed(());
            }
        }
    }
    pub(super) fn formula_site(&mut self, value: FormulaSite) {
        self.step(4);
        match value {
            FormulaSite::Obligation(field0) => {
                self.fixed(field0);
            }
            FormulaSite::SummaryClause {
                function,
                clause,
                index,
            } => {
                self.fixed(function);
                self.fixed(clause);
                self.fixed(index);
            }
            FormulaSite::SpecInvariant { machine, invariant } => {
                self.string(machine);
                self.string(invariant);
            }
            FormulaSite::SpecTemporal { machine, property } => {
                self.string(machine);
                self.string(property);
            }
        }
    }
    pub(super) fn optional_producer(&mut self, value: Option<Producer>) {
        self.step(2);
        match value {
            Some(value) => self.producer(value),
            None => self.fixed(()),
        }
    }
    pub(super) fn producer(&mut self, value: Producer) {
        self.step(6);
        match value {
            Producer::TRust
            | Producer::Clean
            | Producer::TrustIr
            | Producer::TSwift
            | Producer::TC => self.fixed(()),
            Producer::Other(text) => self.string(text),
        }
    }
    pub(super) fn digest(&mut self, value: ProofDigest) {
        self.step(1);
        let ProofDigest { algorithm, bytes } = value;
        self.fixed(algorithm);
        self.fixed(bytes);
    }
}
