// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Exhaustive current enum fields; no wildcard or field-rest patterns.
use super::*;
impl<O: ExecutionObserver> Work<'_, '_, O> {
    pub(super) fn error(&mut self, value: ValidationError) {
        self.step(270);
        match value {
            ValidationError::InvalidStorageUse { location, detail } => {
                self.string(location);
                self.string(detail);
            }
            ValidationError::EmptyFunction => {
                self.fixed(());
            }
            ValidationError::InvalidSpecAnchorFunction {
                machine,
                action,
                function,
                detail,
            } => {
                self.string(machine);
                self.string(action);
                self.fixed(function);
                self.string(detail);
            }
            ValidationError::InvalidSpecProjectionFunction {
                machine,
                action,
                function,
                detail,
            } => {
                self.string(machine);
                self.string(action);
                self.fixed(function);
                self.string(detail);
            }
            ValidationError::BlankModuleName => {
                self.fixed(());
            }
            ValidationError::InvalidSpecStructure { violation } => {
                self.violation(violation);
            }
            ValidationError::SpecLinkedFormulaUnparsed {
                module,
                invariant,
                detail,
            } => {
                self.string(module);
                self.string(invariant);
                self.string(detail);
            }
            ValidationError::SpecLinkedVariableUnparsed {
                module,
                variable,
                detail,
            } => {
                self.string(module);
                self.string(variable);
                self.string(detail);
            }
            ValidationError::InvalidFunctionSummary { function, detail } => {
                self.fixed(function);
                self.string(detail);
            }
            ValidationError::InvalidSourceProvenance { function, detail } => {
                self.fixed(function);
                self.string(detail);
            }
            ValidationError::InvalidBodyGate { function, detail } => {
                self.fixed(function);
                self.string(detail);
            }
            ValidationError::InvalidDisplayPath { function, detail } => {
                self.fixed(function);
                self.string(detail);
            }
            ValidationError::InvalidFunctionSection { function, detail } => {
                self.fixed(function);
                self.string(detail);
            }
            ValidationError::InvalidAbiSlotFact {
                function,
                slot,
                detail,
            } => {
                self.fixed(function);
                self.string(slot);
                self.string(detail);
            }
            ValidationError::InvalidSignatureAbi { signature, detail } => {
                self.fixed(signature);
                self.string(detail);
            }
            ValidationError::AlwaysMemoryByValueAggregate { func_ty, slot, ty } => {
                self.fixed(func_ty);
                self.string(slot);
                self.string(ty);
            }
            ValidationError::ContradictoryFunctionVisibility {
                function,
                linkage,
                visibility,
            } => {
                self.fixed(function);
                self.fixed(linkage);
                self.fixed(visibility);
            }
            ValidationError::UngatedBodyForCodegen { function, name } => {
                self.fixed(function);
                self.string(name);
            }
            ValidationError::UnlicensedBodyForCodegen { function, name } => {
                self.fixed(function);
                self.string(name);
            }
            ValidationError::ProducerOmittedBodyGate {
                function,
                name,
                wire_version,
            } => {
                self.fixed(function);
                self.string(name);
                self.fixed(wire_version);
            }
            ValidationError::GatedWithoutEvidence {
                function,
                authority,
                detail,
            } => {
                self.fixed(function);
                self.string(authority);
                self.string(detail);
            }
            ValidationError::GatedFunctionRefuted {
                function,
                obligation,
            } => {
                self.fixed(function);
                self.fixed(obligation);
            }
            ValidationError::UnrecognizedGateAuthority {
                function,
                authority,
            } => {
                self.fixed(function);
                self.string(authority);
            }
            ValidationError::UnlowerableForCodegen {
                function,
                name,
                block,
                inst,
                detail,
            } => {
                self.fixed(function);
                self.string(name);
                self.fixed(block);
                self.fixed(inst);
                self.string(detail);
            }
            ValidationError::ReservedSpecModuleName { name, detail } => {
                self.string(name);
                self.string(detail);
            }
            ValidationError::DanglingExternRef { detail } => {
                self.string(detail);
            }
            ValidationError::DuplicateFunctionSymbol {
                name,
                first,
                second,
                first_producer,
                second_producer,
                first_display_path,
                second_display_path,
            } => {
                self.string(name);
                self.fixed(first);
                self.fixed(second);
                self.optional_producer(first_producer);
                self.optional_producer(second_producer);
                self.optional_string(first_display_path);
                self.optional_string(second_display_path);
            }
            ValidationError::SyntheticSymbolName { function, name } => {
                self.fixed(function);
                self.string(name);
            }
            ValidationError::UnloweredRowNamesDefinition { symbol, function } => {
                self.string(symbol);
                self.fixed(function);
            }
            ValidationError::DuplicateUnloweredRow { symbol } => {
                self.string(symbol);
            }
            ValidationError::EmptyPartialClaim => {
                self.fixed(());
            }
            ValidationError::UnauthenticatedImport {
                import,
                site,
                detail,
            } => {
                self.fixed(import);
                self.fixed(site);
                self.string(detail);
            }
            ValidationError::ImportTableNotInterned {
                first,
                duplicate,
                name,
            } => {
                self.fixed(first);
                self.fixed(duplicate);
                self.string(name);
            }
            ValidationError::ImportIdentityConflict {
                first,
                conflicting,
                first_name,
                conflicting_name,
            } => {
                self.fixed(first);
                self.fixed(conflicting);
                self.string(first_name);
                self.string(conflicting_name);
            }
            ValidationError::TypeOriginConflict {
                origin,
                first_module,
                first_table,
                first,
                second_module,
                second_table,
                second,
            } => {
                self.string(origin);
                self.optional_string(first_module);
                self.fixed(first_table);
                self.string(first);
                self.optional_string(second_module);
                self.fixed(second_table);
                self.string(second);
            }
            ValidationError::AmbiguousImportedSymbol { symbol, imports } => {
                self.string(symbol);
                self.numbers(imports);
            }
            ValidationError::ImportUnavailable { import, name } => {
                self.fixed(import);
                self.string(name);
            }
            ValidationError::ImportedModuleInvalid {
                import,
                errors,
                first,
            } => {
                self.fixed(import);
                self.fixed(errors);
                self.string(first);
            }
            ValidationError::ImportIncomplete {
                import,
                site,
                unlowered,
            } => {
                self.fixed(import);
                self.fixed(site);
                self.strings(unlowered);
            }
            ValidationError::ImportCycle { import, path } => {
                self.fixed(import);
                self.strings(path);
            }
            ValidationError::ImportClosureTooDeep { import, depth } => {
                self.fixed(import);
                self.fixed(depth);
            }
            ValidationError::ExternInheritanceRestatementMismatch {
                certificate_obligation,
                evidence_obligation,
            } => {
                self.fixed(certificate_obligation);
                self.fixed(evidence_obligation);
            }
            ValidationError::RustAbiVararg { function, detail } => {
                self.fixed(function);
                self.string(detail);
            }
            ValidationError::BlockMissingTerminator(field0) => {
                self.fixed(field0);
            }
            ValidationError::DuplicateBlockId(field0) => {
                self.fixed(field0);
            }
            ValidationError::EntryBlockNotFound(field0) => {
                self.fixed(field0);
            }
            ValidationError::InvalidValueName {
                function,
                value,
                detail,
            } => {
                self.fixed(function);
                self.fixed(value);
                self.string(detail);
            }
            ValidationError::InvalidScopeTree {
                function,
                scope,
                detail,
            } => {
                self.fixed(function);
                self.fixed(scope);
                self.string(detail);
            }
            ValidationError::InvalidInstructionScope {
                function,
                block,
                instruction,
                scope,
                scope_count,
            } => {
                self.fixed(function);
                self.fixed(block);
                self.fixed(instruction);
                self.fixed(scope);
                self.fixed(scope_count);
            }
            ValidationError::InvalidInlinedScope {
                function,
                scope,
                detail,
            } => {
                self.fixed(function);
                self.fixed(scope);
                self.string(detail);
            }
            ValidationError::DuplicateValueDef { value, block } => {
                self.fixed(value);
                self.fixed(block);
            }
            ValidationError::UseBeforeDef { value, block } => {
                self.fixed(value);
                self.fixed(block);
            }
            ValidationError::BinOpTypeMismatch {
                block,
                op,
                lhs_ty,
                rhs_ty,
            } => {
                self.fixed(block);
                self.string(op);
                self.string(lhs_ty);
                self.string(rhs_ty);
            }
            ValidationError::BinOpRequiresInteger { block, op, ty } => {
                self.fixed(block);
                self.string(op);
                self.string(ty);
            }
            ValidationError::BinOpRequiresFloat { block, op, ty } => {
                self.fixed(block);
                self.string(op);
                self.string(ty);
            }
            ValidationError::BinOpRequiresBool { block, op, ty } => {
                self.fixed(block);
                self.string(op);
                self.string(ty);
            }
            ValidationError::UnOpNotOnScalarBool { block } => {
                self.fixed(block);
            }
            ValidationError::ICmpRequiresIntegerOrPtr { block, ty } => {
                self.fixed(block);
                self.string(ty);
            }
            ValidationError::FCmpRequiresFloat { block, ty } => {
                self.fixed(block);
                self.string(ty);
            }
            ValidationError::CastIncompatible {
                block,
                op,
                src,
                dst,
            } => {
                self.fixed(block);
                self.string(op);
                self.string(src);
                self.string(dst);
            }
            ValidationError::CastLayoutUnsupported {
                block,
                op,
                src,
                dst,
                reason,
            } => {
                self.fixed(block);
                self.string(op);
                self.string(src);
                self.string(dst);
                self.string(reason);
            }
            ValidationError::PointerOpInvalid {
                block,
                op,
                ptr_ty,
                reason,
            } => {
                self.fixed(block);
                self.string(op);
                self.string(ptr_ty);
                self.string(reason);
            }
            ValidationError::PointerMetadataTypeMismatch {
                block,
                op,
                ptr_ty,
                expected,
                actual,
            } => {
                self.fixed(block);
                self.string(op);
                self.string(ptr_ty);
                self.string(expected);
                self.string(actual);
            }
            ValidationError::CondBrRequiresBool { block, cond_ty } => {
                self.fixed(block);
                self.string(cond_ty);
            }
            ValidationError::PredicateRequiresBool { block, op, cond_ty } => {
                self.fixed(block);
                self.string(op);
                self.string(cond_ty);
            }
            ValidationError::SelectConditionTypeMismatch {
                block,
                expected,
                actual,
            } => {
                self.fixed(block);
                self.string(expected);
                self.string(actual);
            }
            ValidationError::InvalidVectorType { block, ty, reason } => {
                self.fixed(block);
                self.string(ty);
                self.string(reason);
            }
            ValidationError::InvalidModuleVectorType {
                location,
                ty,
                reason,
            } => {
                self.string(location);
                self.string(ty);
                self.string(reason);
            }
            ValidationError::InvalidVectorDialectOp { block, op, reason } => {
                self.fixed(block);
                self.string(op);
                self.string(reason);
            }
            ValidationError::InvalidDialectSchema { block, op, reason } => {
                self.fixed(block);
                self.string(op);
                self.string(reason);
            }
            ValidationError::InvalidVectorElementOp { block, op, reason } => {
                self.fixed(block);
                self.string(op);
                self.string(reason);
            }
            ValidationError::BranchTargetNotFound { block, target } => {
                self.fixed(block);
                self.fixed(target);
            }
            ValidationError::DuplicateSwitchCase { block, value } => {
                self.fixed(block);
                self.string(value);
            }
            ValidationError::UnreachableBlock(field0) => {
                self.fixed(field0);
            }
            ValidationError::BranchArgCountMismatch {
                block,
                target,
                expected,
                actual,
            } => {
                self.fixed(block);
                self.fixed(target);
                self.fixed(expected);
                self.fixed(actual);
            }
            ValidationError::ReturnTypeMismatch {
                block,
                expected,
                actual,
            } => {
                self.fixed(block);
                self.string(expected);
                self.string(actual);
            }
            ValidationError::ReturnArityMismatch {
                block,
                expected,
                actual,
            } => {
                self.fixed(block);
                self.fixed(expected);
                self.fixed(actual);
            }
            ValidationError::CallArgCountMismatch {
                block,
                callee,
                expected,
                actual,
                caller_producer,
                callee_producer,
            } => {
                self.fixed(block);
                self.string(callee);
                self.fixed(expected);
                self.fixed(actual);
                self.optional_string(caller_producer);
                self.optional_string(callee_producer);
            }
            ValidationError::CallArgTypeMismatch {
                block,
                callee,
                arg_index,
                expected,
                actual,
                caller_producer,
                callee_producer,
            } => {
                self.fixed(block);
                self.string(callee);
                self.fixed(arg_index);
                self.string(expected);
                self.string(actual);
                self.optional_string(caller_producer);
                self.optional_string(callee_producer);
            }
            ValidationError::CalleeNotFound { block, callee_id } => {
                self.fixed(block);
                self.fixed(callee_id);
            }
            ValidationError::SeqMapFwdNotFound { block, fwd_id } => {
                self.fixed(block);
                self.fixed(fwd_id);
            }
            ValidationError::SeqMapTypeNotSequence { block, ty } => {
                self.fixed(block);
                self.string(ty);
            }
            ValidationError::SeqMapFwdSignatureMismatch {
                block,
                fwd,
                expected,
                actual,
            } => {
                self.fixed(block);
                self.string(fwd);
                self.string(expected);
                self.string(actual);
            }
            ValidationError::GlobalNotFound { block, global_id } => {
                self.fixed(block);
                self.fixed(global_id);
            }
            ValidationError::CallIndirectSigNotFound { block, sig_id } => {
                self.fixed(block);
                self.fixed(sig_id);
            }
            ValidationError::CallIndirectArgCountMismatch {
                block,
                sig_id,
                expected,
                actual,
            } => {
                self.fixed(block);
                self.fixed(sig_id);
                self.fixed(expected);
                self.fixed(actual);
            }
            ValidationError::CallIndirectArgTypeMismatch {
                block,
                sig_id,
                arg_index,
                expected,
                actual,
            } => {
                self.fixed(block);
                self.fixed(sig_id);
                self.fixed(arg_index);
                self.string(expected);
                self.string(actual);
            }
            ValidationError::CallIndirectClosureSigMismatch {
                block,
                closure_ty_id,
                declared_sig_id,
                apparent_sig_id,
            } => {
                self.fixed(block);
                self.fixed(closure_ty_id);
                self.fixed(declared_sig_id);
                self.fixed(apparent_sig_id);
            }
            ValidationError::CallIndirectClosureTargetMismatch {
                block,
                closure_ty_id,
                target,
                expected,
                actual,
            } => {
                self.fixed(block);
                self.fixed(closure_ty_id);
                self.string(target);
                self.string(expected);
                self.string(actual);
            }
            ValidationError::FuncTypeNotFound {
                func_name,
                func_ty_id,
            } => {
                self.string(func_name);
                self.fixed(func_ty_id);
            }
            ValidationError::InstrResultArityMismatch {
                block,
                op,
                expected,
                actual,
            } => {
                self.fixed(block);
                self.string(op);
                self.fixed(expected);
                self.fixed(actual);
            }
            ValidationError::ConstTypeMismatch {
                location,
                expected,
                actual,
            } => {
                self.string(location);
                self.string(expected);
                self.string(actual);
            }
            ValidationError::ConstTypeReferenceNotFound { location, type_ref } => {
                self.string(location);
                self.string(type_ref);
            }
            ValidationError::DuplicateStructId(field0) => {
                self.fixed(field0);
            }
            ValidationError::DuplicateEnumId(field0) => {
                self.fixed(field0);
            }
            ValidationError::DuplicateFuncId(field0) => {
                self.fixed(field0);
            }
            ValidationError::BindingFrameIdReused { block, frame_id } => {
                self.fixed(block);
                self.fixed(frame_id);
            }
            ValidationError::BindingFrameNotOpen { block, frame_value } => {
                self.fixed(block);
                self.fixed(frame_value);
            }
            ValidationError::BindingSlotOutOfRange {
                block,
                frame_id,
                slot,
                arity,
            } => {
                self.fixed(block);
                self.fixed(frame_id);
                self.fixed(slot);
                self.fixed(arity);
            }
            ValidationError::BindingSlotTypeMismatch {
                block,
                frame_id,
                slot,
                expected,
                actual,
            } => {
                self.fixed(block);
                self.fixed(frame_id);
                self.fixed(slot);
                self.string(expected);
                self.string(actual);
            }
            ValidationError::BindingBindTypeMismatch {
                block,
                frame_id,
                slot,
                expected,
                actual,
            } => {
                self.fixed(block);
                self.fixed(frame_id);
                self.fixed(slot);
                self.string(expected);
                self.string(actual);
            }
            ValidationError::BindingUseAfterClose { block, frame_value } => {
                self.fixed(block);
                self.fixed(frame_value);
            }
            ValidationError::BindingFrameUnclosed { block, frame_id } => {
                self.fixed(block);
                self.fixed(frame_id);
            }
            ValidationError::BindingFrameUnopened { block, frame_value } => {
                self.fixed(block);
                self.fixed(frame_value);
            }
            ValidationError::BindingFrameAnalysisFailed { reason } => {
                self.string(reason);
            }
            ValidationError::ConflictingMemoryRoles {
                block,
                value,
                roles,
            } => {
                self.fixed(block);
                self.fixed(value);
                self.strings(roles);
            }
            ValidationError::ConflictingFunctionMemoryRoles { func_name, roles } => {
                self.string(func_name);
                self.strings(roles);
            }
            ValidationError::TaintedValueReachesTrustedSink { block, value } => {
                self.fixed(block);
                self.fixed(value);
            }
            ValidationError::ClosurePureWithStatefulCapture {
                block,
                value,
                closure_ty_id,
                capture_index,
                capture_ty,
            } => {
                self.fixed(block);
                self.fixed(value);
                self.fixed(closure_ty_id);
                self.fixed(capture_index);
                self.string(capture_ty);
            }
            ValidationError::FunctionPureWithStatefulClosureSignature {
                func_name,
                closure_ty_id,
                capture_index,
                capture_ty,
            } => {
                self.string(func_name);
                self.fixed(closure_ty_id);
                self.fixed(capture_index);
                self.string(capture_ty);
            }
            ValidationError::ClosureTypeNotFound {
                location,
                closure_ty_id,
            } => {
                self.string(location);
                self.fixed(closure_ty_id);
            }
            ValidationError::ClosureCaptureArityMismatch {
                location,
                closure_ty_id,
                expected,
                actual,
            } => {
                self.string(location);
                self.fixed(closure_ty_id);
                self.fixed(expected);
                self.fixed(actual);
            }
            ValidationError::ClosureCaptureTypeMismatch {
                location,
                closure_ty_id,
                capture_index,
                expected,
                actual,
            } => {
                self.string(location);
                self.fixed(closure_ty_id);
                self.fixed(capture_index);
                self.string(expected);
                self.string(actual);
            }
            ValidationError::InheritedProofCalleeNotFound { obligation, callee } => {
                self.fixed(obligation);
                self.fixed(callee);
            }
            ValidationError::InheritedProofNotDischarged {
                obligation,
                callee,
                inherited_obligation,
            } => {
                self.fixed(obligation);
                self.fixed(callee);
                self.fixed(inherited_obligation);
            }
            ValidationError::InheritedProofCalleeScopeMismatch {
                obligation,
                named_callee,
                actual_owner,
            } => {
                self.fixed(obligation);
                self.fixed(named_callee);
                self.fixed(actual_owner);
            }
            ValidationError::LocalInheritanceRestatementMismatch {
                certificate_obligation,
                detail,
            } => {
                self.fixed(certificate_obligation);
                self.string(detail);
            }
            ValidationError::CertificateBindingMismatch {
                obligation,
                field,
                detail,
            } => {
                self.fixed(obligation);
                self.string(field);
                self.string(detail);
            }
            ValidationError::UnboundCertificate { obligation } => {
                self.fixed(obligation);
            }
            ValidationError::GatedEvidenceMismatch { function, detail } => {
                self.fixed(function);
                self.string(detail);
            }
            ValidationError::UnevidencedGate {
                function,
                authority,
            } => {
                self.fixed(function);
                self.string(authority);
            }
            ValidationError::DuplicateObligationContent {
                function,
                obligations,
            } => {
                self.fixed(function);
                self.numbers(obligations);
            }
            ValidationError::ProofContextOnNonCallNode { block } => {
                self.fixed(block);
            }
            ValidationError::ProofContextUnknownObligation { block, obligation } => {
                self.fixed(block);
                self.fixed(obligation);
            }
            ValidationError::ProofContextAssumeNotAuthoritative { block, obligation } => {
                self.fixed(block);
                self.fixed(obligation);
            }
            ValidationError::ProofContextAssumeScopeMismatch {
                block,
                obligation,
                callee,
                actual_owner,
            } => {
                self.fixed(block);
                self.fixed(obligation);
                self.fixed(callee);
                self.fixed(actual_owner);
            }
            ValidationError::ProofContextEstablishScopeMismatch {
                block,
                obligation,
                callee,
                actual_owner,
            } => {
                self.fixed(block);
                self.fixed(obligation);
                self.fixed(callee);
                self.fixed(actual_owner);
            }
            ValidationError::ProofRefUnresolved {
                function,
                obligation,
                missing,
            } => {
                self.fixed(function);
                self.fixed(obligation);
                self.fixed(missing);
            }
            ValidationError::ProofRefWithoutClaim {
                function,
                obligation,
            } => {
                self.fixed(function);
                self.fixed(obligation);
            }
            ValidationError::ProofRefKindMismatch {
                function,
                obligation,
                kind,
            } => {
                self.fixed(function);
                self.fixed(obligation);
                self.fixed(kind);
            }
            ValidationError::ProofRefScopeMismatch {
                function,
                obligation,
                owner,
            } => {
                self.fixed(function);
                self.fixed(obligation);
                self.fixed(owner);
            }
            ValidationError::ProofRefSiteMismatch {
                function,
                obligation,
            } => {
                self.fixed(function);
                self.fixed(obligation);
            }
            ValidationError::ValueRangeInverted { function, lo, hi } => {
                self.fixed(function);
                self.fixed(lo);
                self.fixed(hi);
            }
            ValidationError::KnownBitsContradiction { function, overlap } => {
                self.fixed(function);
                self.fixed(overlap);
            }
            ValidationError::CertifiedWithoutCleanCic { obligation } => {
                self.fixed(obligation);
            }
            ValidationError::CertifiedCleanCicLineageMismatch { obligation } => {
                self.fixed(obligation);
            }
            ValidationError::GroundCertificateStatusInconsistent { obligation, status } => {
                self.fixed(obligation);
                self.fixed(status);
            }
            ValidationError::TrustedWithoutJustification { obligation } => {
                self.fixed(obligation);
            }
            ValidationError::ObligationSiteKindMismatch {
                obligation,
                kind,
                op,
            } => {
                self.fixed(obligation);
                self.fixed(kind);
                self.fixed(op);
            }
            ValidationError::EvidenceKindMismatch {
                obligation,
                kind,
                evidence,
            } => {
                self.fixed(obligation);
                self.fixed(kind);
                self.fixed(evidence);
            }
            ValidationError::UnbackedClaimOnCheck {
                function,
                block,
                inst_index,
                claim,
            } => {
                self.string(function);
                self.fixed(block);
                self.fixed(inst_index);
                self.fixed(claim);
            }
            ValidationError::BoxDerefTypeMismatch {
                function,
                block,
                inst_index,
                detail,
            } => {
                self.string(function);
                self.fixed(block);
                self.fixed(inst_index);
                self.string(detail);
            }
            ValidationError::BoxDerefPointeeOutOfScope {
                function,
                block,
                inst_index,
                reason,
            } => {
                self.string(function);
                self.fixed(block);
                self.fixed(inst_index);
                self.fixed(reason);
            }
            ValidationError::BoxDerefConjunctCover {
                function,
                block,
                inst_index,
                detail,
            } => {
                self.string(function);
                self.fixed(block);
                self.fixed(inst_index);
                self.string(detail);
            }
            ValidationError::BoxDerefPremiseNotPinned {
                function,
                block,
                inst_index,
                conjunct,
            } => {
                self.string(function);
                self.fixed(block);
                self.fixed(inst_index);
                self.fixed(conjunct);
            }
            ValidationError::BoxDerefSessionRefused {
                function,
                block,
                inst_index,
                reason,
            } => {
                self.string(function);
                self.fixed(block);
                self.fixed(inst_index);
                self.fixed(reason);
            }
            ValidationError::BoxDerefDominatingCheckInvalid {
                function,
                block,
                inst_index,
                conjunct,
                reason,
            } => {
                self.string(function);
                self.fixed(block);
                self.fixed(inst_index);
                self.fixed(conjunct);
                self.fixed(reason);
            }
            ValidationError::BoxDerefConjunctUnestablished {
                function,
                block,
                inst_index,
                conjunct,
            } => {
                self.string(function);
                self.fixed(block);
                self.fixed(inst_index);
                self.fixed(conjunct);
            }
            ValidationError::BoxDerefObligationUnbound {
                function,
                block,
                inst_index,
                obligation,
                reason,
            } => {
                self.string(function);
                self.fixed(block);
                self.fixed(inst_index);
                self.fixed(obligation);
                self.fixed(reason);
            }
            ValidationError::BoxDerefNonClaimsNotPinned {
                function,
                block,
                inst_index,
            } => {
                self.string(function);
                self.fixed(block);
                self.fixed(inst_index);
            }
            ValidationError::BoxDerefPremiseContradicted {
                function,
                block,
                inst_index,
                reason,
            } => {
                self.string(function);
                self.fixed(block);
                self.fixed(inst_index);
                self.fixed(reason);
            }
            ValidationError::BoxValidityEvidenceBelowFloor {
                function,
                block,
                inst_index,
                conjunct,
                tier,
                floor,
            } => {
                self.string(function);
                self.fixed(block);
                self.fixed(inst_index);
                self.fixed(conjunct);
                self.fixed(tier);
                self.fixed(floor);
            }
            ValidationError::AssertPanicKindUnspecified {
                function,
                block,
                inst_index,
            } => {
                self.string(function);
                self.fixed(block);
                self.fixed(inst_index);
            }
            ValidationError::AssertPanicSiteMissing {
                function,
                block,
                inst_index,
            } => {
                self.string(function);
                self.fixed(block);
                self.fixed(inst_index);
            }
            ValidationError::PanicEntrySignatureMismatch {
                function,
                block,
                inst_index,
                entry,
                expected,
                found,
            } => {
                self.string(function);
                self.fixed(block);
                self.fixed(inst_index);
                self.fixed(entry);
                self.string(expected);
                self.string(found);
            }
            ValidationError::PanicLocationGlobalInvalid {
                function,
                block,
                inst_index,
                global,
                reason,
            } => {
                self.string(function);
                self.fixed(block);
                self.fixed(inst_index);
                self.fixed(global);
                self.fixed(reason);
            }
            ValidationError::NonCanonicalPanicLocation {
                function,
                block,
                inst_index,
            } => {
                self.string(function);
                self.fixed(block);
                self.fixed(inst_index);
            }
            ValidationError::CertifiedCleanCicKernelRecheckFailed { obligation, reason } => {
                self.fixed(obligation);
                self.string(reason);
            }
            ValidationError::OperandNotPointer { block, op, ty } => {
                self.fixed(block);
                self.string(op);
                self.string(ty);
            }
            ValidationError::GepIndexNotInteger { block, ty } => {
                self.fixed(block);
                self.string(ty);
            }
            ValidationError::OperandNotInteger { block, op, ty } => {
                self.fixed(block);
                self.string(op);
                self.string(ty);
            }
            ValidationError::OperandTypeMismatch {
                block,
                op,
                role,
                expected,
                actual,
            } => {
                self.fixed(block);
                self.string(op);
                self.string(role);
                self.string(expected);
                self.string(actual);
            }
            ValidationError::FieldAccessInvalid { block, op, reason } => {
                self.fixed(block);
                self.string(op);
                self.string(reason);
            }
            ValidationError::IllegalAtomicOrdering {
                block,
                op,
                role,
                ordering,
                legal,
            } => {
                self.fixed(block);
                self.fixed(op);
                self.fixed(role);
                self.string(ordering);
                self.fixed(legal);
            }
            ValidationError::BranchArgTypeMismatch {
                block,
                target,
                arg_index,
                expected,
                actual,
            } => {
                self.fixed(block);
                self.fixed(target);
                self.fixed(arg_index);
                self.string(expected);
                self.string(actual);
            }
            ValidationError::UseBeforeDefInBlock { value, block } => {
                self.fixed(value);
                self.fixed(block);
            }
            ValidationError::MidBlockTerminator { block, index, op } => {
                self.fixed(block);
                self.fixed(index);
                self.string(op);
            }
            ValidationError::MissingTerminator { block } => {
                self.fixed(block);
            }
            ValidationError::UnwindDestWithoutLandingPad { block, target } => {
                self.fixed(block);
                self.fixed(target);
            }
            ValidationError::MisplacedLandingPad { block, reason } => {
                self.fixed(block);
                self.string(reason);
            }
            ValidationError::InvalidDropGlue {
                entry,
                glue,
                reason,
            } => {
                self.fixed(entry);
                self.fixed(glue);
                self.string(reason);
            }
            ValidationError::NonCanonicalDrop {
                function,
                block,
                reason,
            } => {
                self.string(function);
                self.fixed(block);
                self.string(reason);
            }
            ValidationError::ExhaustiveSwitchDefaultReachable { block, reason } => {
                self.fixed(block);
                self.string(reason);
            }
            ValidationError::ExhaustiveSwitchCasesIncomplete {
                block,
                enum_ty,
                reason,
            } => {
                self.fixed(block);
                self.string(enum_ty);
                self.string(reason);
            }
            ValidationError::FuncAttrClaimViolated {
                function,
                attr,
                block,
                inst,
            } => {
                self.string(function);
                self.fixed(attr);
                self.fixed(block);
                self.string(inst);
            }
            ValidationError::EffectSummaryViolated {
                function,
                effect,
                block,
                inst,
            } => {
                self.string(function);
                self.fixed(effect);
                self.fixed(block);
                self.string(inst);
            }
            ValidationError::BorrowMutThroughSharedRef { block } => {
                self.fixed(block);
            }
            ValidationError::EndBorrowOfNonBorrow { block } => {
                self.fixed(block);
            }
            ValidationError::RustReferenceAsPermissionBorrow {
                function,
                block,
                inst_index,
            } => {
                self.string(function);
                self.fixed(block);
                self.fixed(inst_index);
            }
            ValidationError::CastOperandTypeMismatch {
                block,
                op,
                declared_src,
                actual,
            } => {
                self.fixed(block);
                self.string(op);
                self.string(declared_src);
                self.string(actual);
            }
            ValidationError::CastWidthDirectionInvalid {
                block,
                op,
                src,
                dst,
                reason,
            } => {
                self.fixed(block);
                self.string(op);
                self.string(src);
                self.string(dst);
                self.string(reason);
            }
            ValidationError::EntryParamsMismatch {
                func_name,
                expected,
                actual,
            } => {
                self.string(func_name);
                self.string(expected);
                self.string(actual);
            }
            ValidationError::DanglingTypeReference { location, kind, id } => {
                self.string(location);
                self.fixed(kind);
                self.fixed(id);
            }
            ValidationError::DuplicateProofObligationId(field0) => {
                self.fixed(field0);
            }
            ValidationError::InvalidProofObligationSourceTextId { obligation, field } => {
                self.fixed(obligation);
                self.fixed(field);
            }
            ValidationError::ProofObligationSourceRangeFileOutOfRange {
                obligation,
                file,
                file_count,
            } => {
                self.fixed(obligation);
                self.fixed(file);
                self.fixed(file_count);
            }
            ValidationError::ObligationSiteFunctionMismatch {
                obligation,
                site_function,
                scope_function,
            } => {
                self.fixed(obligation);
                self.fixed(site_function);
                self.fixed(scope_function);
            }
            ValidationError::ObligationSiteOutOfRange {
                obligation,
                function,
                block,
                inst_index,
                reason,
            } => {
                self.fixed(obligation);
                self.fixed(function);
                self.fixed(block);
                self.fixed(inst_index);
                self.fixed(reason);
            }
            ValidationError::InvalidObligationBinding { obligation, detail } => {
                self.fixed(obligation);
                self.string(detail);
            }
            ValidationError::FormulaTextsDisagree { site } => {
                self.formula_site(site);
            }
            ValidationError::UnresolvedObligationSpecRef {
                obligation,
                machine,
                temporal,
                reason,
            } => {
                self.fixed(obligation);
                self.string(machine);
                self.string(temporal);
                self.fixed(reason);
            }
            ValidationError::ObligationFunctionScopeUnresolved {
                obligation,
                function,
                reason,
            } => {
                self.fixed(obligation);
                self.fixed(function);
                self.fixed(reason);
            }
            ValidationError::InvalidProofObligationSourceRange { obligation, reason } => {
                self.fixed(obligation);
                self.fixed(reason);
            }
            ValidationError::InvalidPublicObligationId { obligation } => {
                self.fixed(obligation);
            }
            ValidationError::PublicObligationDigestNotSha256 { obligation } => {
                self.fixed(obligation);
            }
            ValidationError::PublicObligationDigestZero { obligation } => {
                self.fixed(obligation);
            }
            ValidationError::DuplicatePublicObligationId {
                obligation_id,
                first_obligation,
                duplicate_obligation,
            } => {
                self.string(obligation_id);
                self.fixed(first_obligation);
                self.fixed(duplicate_obligation);
            }
            ValidationError::DischargedWithoutCertificate { obligation } => {
                self.fixed(obligation);
            }
            ValidationError::DanglingProofCertificate { obligation } => {
                self.fixed(obligation);
            }
            ValidationError::SpanFileIndexOutOfRange { file, file_count } => {
                self.fixed(file);
                self.fixed(file_count);
            }
            ValidationError::TransparentReprFieldCount {
                struct_id,
                actual_non_zst,
            } => {
                self.fixed(struct_id);
                self.fixed(actual_non_zst);
            }
            ValidationError::PackedReprInvalidAlign { struct_id, align } => {
                self.fixed(struct_id);
                self.fixed(align);
            }
            ValidationError::AccessAlignInvalid { inst, align } => {
                self.fixed(inst);
                self.fixed(align);
            }
            ValidationError::GlobalAlignInvalid { global, align } => {
                self.string(global);
                self.fixed(align);
            }
            ValidationError::WrappingConflictsWithNoOverflow { block } => {
                self.fixed(block);
            }
            ValidationError::TargetPointerSizeInvalid { pointer_size } => {
                self.fixed(pointer_size);
            }
            ValidationError::TargetTripleEmpty => {
                self.fixed(());
            }
            ValidationError::TargetScalarLayoutUnavailable { struct_id, triple } => {
                self.fixed(struct_id);
                self.string(triple);
            }
            ValidationError::EnumTagTargetScalarLayoutUnavailable { enum_id, triple } => {
                self.fixed(enum_id);
                self.string(triple);
            }
            ValidationError::BranchWeightsMismatch { reason } => {
                self.fixed(reason);
            }
            ValidationError::HavocMarkerMisplaced { location, marker } => {
                self.string(location);
                self.fixed(marker);
            }
            ValidationError::DanglingDiagnosticObligation { obligation } => {
                self.fixed(obligation);
            }
            ValidationError::TupleLayoutInconsistent { reason } => {
                self.string(reason);
            }
            ValidationError::InlineAggregateCycle { ty } => {
                self.string(ty);
            }
            ValidationError::StructLayoutInconsistent { struct_id, reason } => {
                self.fixed(struct_id);
                self.fixed(reason);
            }
            ValidationError::FfiStructReprUnpinned {
                func_name,
                struct_id,
                position,
            } => {
                self.string(func_name);
                self.fixed(struct_id);
                self.fixed(position);
            }
            ValidationError::TargetInfoRequired { boundary } => {
                self.string(boundary);
            }
            ValidationError::CallEdgeConvMismatch {
                block,
                callee,
                declared,
                actual,
            } => {
                self.fixed(block);
                self.string(callee);
                self.string(declared);
                self.string(actual);
            }
            ValidationError::CallEdgeSignatureMismatch {
                block,
                callee,
                declared,
                actual,
            } => {
                self.fixed(block);
                self.string(callee);
                self.string(declared);
                self.string(actual);
            }
            ValidationError::ParamAbiAttrInvalid {
                func_name,
                param_index,
                reason,
            } => {
                self.string(func_name);
                self.fixed(param_index);
                self.fixed(reason);
            }
            ValidationError::PredicateTableMalformed { location, detail } => {
                self.string(location);
                self.string(detail);
            }
            ValidationError::PredicateTableNotInterned {
                kind,
                first,
                duplicate,
                content,
            } => {
                self.fixed(kind);
                self.fixed(first);
                self.fixed(duplicate);
                self.string(content);
            }
            ValidationError::DanglingPredicateRef { location, kind, id } => {
                self.string(location);
                self.fixed(kind);
                self.fixed(id);
            }
            ValidationError::RefinementTypeInvalid { location, detail } => {
                self.string(location);
                self.string(detail);
            }
            ValidationError::InvalidDialectType { location, detail } => {
                self.string(location);
                self.string(detail);
            }
            ValidationError::InvalidHandleType { location, detail } => {
                self.string(location);
                self.string(detail);
            }
            ValidationError::UntrustedHandleRuntime {
                location,
                name,
                runtime,
            } => {
                self.string(location);
                self.string(name);
                self.string(runtime);
            }
            ValidationError::HandleEntryPointSignatureMismatch {
                function,
                symbol,
                expected,
                actual,
            } => {
                self.fixed(function);
                self.string(symbol);
                self.string(expected);
                self.string(actual);
            }
            ValidationError::HandleEntryPointDefinedLocally { function, symbol } => {
                self.fixed(function);
                self.string(symbol);
            }
            ValidationError::HandleEntryPointShadowedByGlobal { global, symbol } => {
                self.string(global);
                self.string(symbol);
            }
            ValidationError::HandleEntryPointAddressTaken { location, symbol } => {
                self.string(location);
                self.string(symbol);
            }
            ValidationError::RcEntryPointSignatureMismatch {
                function,
                symbol,
                expected,
                actual,
            } => {
                self.fixed(function);
                self.string(symbol);
                self.string(expected);
                self.string(actual);
            }
            ValidationError::RcEntryPointDefinedLocally { function, symbol } => {
                self.fixed(function);
                self.string(symbol);
            }
            ValidationError::RcEntryPointShadowedByGlobal { global, symbol } => {
                self.string(global);
                self.string(symbol);
            }
            ValidationError::RcEntryPointAddressTaken { location, symbol } => {
                self.string(location);
                self.string(symbol);
            }
            ValidationError::DirectCallToWeakDeclaration {
                location,
                callee,
                name,
            } => {
                self.string(location);
                self.fixed(callee);
                self.string(name);
            }
            ValidationError::WeakDeclarationAsFnDef {
                location,
                function,
                name,
            } => {
                self.string(location);
                self.fixed(function);
                self.string(name);
            }
            ValidationError::WeakDeclarationAddressNotNullable {
                location,
                symbol,
                detail,
            } => {
                self.string(location);
                self.string(symbol);
                self.string(detail);
            }
            ValidationError::HandleForeignDeclaration {
                function,
                name,
                handle,
                detail,
            } => {
                self.fixed(function);
                self.string(name);
                self.string(handle);
                self.string(detail);
            }
            ValidationError::InvalidHandleUse { location, detail } => {
                self.string(location);
                self.string(detail);
            }
            ValidationError::HandleRuntimeSpelledStructurally { def, runtime } => {
                self.string(def);
                self.string(runtime);
            }
            ValidationError::HandleLaneNiche {
                enum_name,
                variant,
                field,
                detail,
            } => {
                self.string(enum_name);
                self.fixed(variant);
                self.fixed(field);
                self.string(detail);
            }
            ValidationError::UninhabitedVariantConstructed {
                location,
                enum_name,
                variant,
                variant_name,
            } => {
                self.string(location);
                self.string(enum_name);
                self.fixed(variant);
                self.string(variant_name);
            }
            ValidationError::InvalidMakeClosure {
                block,
                closure_ty_id,
                reason,
            } => {
                self.fixed(block);
                self.fixed(closure_ty_id);
                self.string(reason);
            }
            ValidationError::InvalidMakeAggregate { block, ty, reason } => {
                self.fixed(block);
                self.string(ty);
                self.string(reason);
            }
            ValidationError::InvalidArraySplat { block, ty, reason } => {
                self.fixed(block);
                self.string(ty);
                self.string(reason);
            }
            ValidationError::NonCanonicalUniformArray { location, spelling } => {
                self.string(location);
                self.string(spelling);
            }
            ValidationError::PointerConstantRefused {
                location,
                symbol,
                ty,
                reason,
            } => {
                self.string(location);
                self.string(symbol);
                self.string(ty);
                self.refusal(reason);
            }
            ValidationError::RefinementNotImplied {
                location,
                actual,
                required,
            } => {
                self.string(location);
                self.string(actual);
                self.string(required);
            }
            ValidationError::RefinementContradicted {
                location,
                declared,
                derived,
            } => {
                self.string(location);
                self.string(declared);
                self.string(derived);
            }
            ValidationError::GlobalAsmNotConsumable { blocks } => {
                self.fixed(blocks);
            }
            ValidationError::UnpinnedCustomObligationNamespace {
                obligation,
                namespace,
                name,
            } => {
                self.fixed(obligation);
                self.string(namespace);
                self.string(name);
            }
            ValidationError::NativeBundleNotForThisModule { expected, actual } => {
                self.digest(expected);
                self.digest(actual);
            }
            ValidationError::ModuleHasNoWireIdentity {
                location,
                construct,
            } => {
                self.string(location);
                self.string(construct);
            }
            ValidationError::CoverageAssuranceRequestUnknown {
                obligation,
                recorded,
                bundle_requests,
            } => {
                self.fixed(obligation);
                self.digest(recorded);
                self.fixed(bundle_requests);
            }
            ValidationError::CoverageAssuranceObligationNotRequested {
                obligation,
                request,
                request_obligations,
            } => {
                self.fixed(obligation);
                self.fixed(request);
                self.numbers(request_obligations);
            }
            ValidationError::CoverageAssuranceBoundMismatch {
                obligation,
                recorded,
                derived,
            } => {
                self.fixed(obligation);
                self.string(recorded);
                self.string(derived);
            }
            ValidationError::CoverageAttestationSchemaUnsupported { detail } => {
                self.string(detail);
            }
            ValidationError::CoverageAttestationRowDuplicate {
                obligation,
                solved_bundle,
                request,
            } => {
                self.fixed(obligation);
                self.digest(solved_bundle);
                self.digest(request);
            }
            ValidationError::CoverageSolvedBundleMissing {
                obligation,
                recorded,
                supplied,
            } => {
                self.fixed(obligation);
                self.digest(recorded);
                self.fixed(supplied);
            }
            ValidationError::CoverageSolvedBundleInvalid { obligation, detail } => {
                self.fixed(obligation);
                self.string(detail);
            }
            ValidationError::CoverageSolvedBundleDigestMismatch {
                obligation,
                field,
                recorded,
                actual,
            } => {
                self.fixed(obligation);
                self.fixed(field);
                self.digest(recorded);
                self.digest(actual);
            }
            ValidationError::CoverageEvidenceMissing {
                obligation,
                request,
            } => {
                self.fixed(obligation);
                self.fixed(request);
            }
            ValidationError::CoverageEvidenceDigestMismatch {
                obligation,
                request,
                recorded,
            } => {
                self.fixed(obligation);
                self.fixed(request);
                self.digest(recorded);
            }
            ValidationError::CoverageResultArtifactUnresolved {
                obligation,
                artifact,
                reason,
            } => {
                self.fixed(obligation);
                self.string(artifact);
                self.string(reason);
            }
            ValidationError::CoverageResultReplayInvalid { obligation, detail } => {
                self.fixed(obligation);
                self.string(detail);
            }
            ValidationError::CoverageModeStrengthMismatch {
                obligation,
                request,
                mode,
                strength,
            } => {
                self.fixed(obligation);
                self.fixed(request);
                self.string(mode);
                self.string(strength);
            }
            ValidationError::CoverageSubjectCodeDrift {
                obligation,
                solved,
                admitted,
            } => {
                self.fixed(obligation);
                self.digest(solved);
                self.digest(admitted);
            }
            ValidationError::CoverageClaimDrift { obligation, detail } => {
                self.fixed(obligation);
                self.string(detail);
            }
            ValidationError::CoverageContradicted { obligation, detail } => {
                self.fixed(obligation);
                self.string(detail);
            }
            ValidationError::CoverageRowExceedsEstablished {
                obligation,
                recorded,
                established,
            } => {
                self.fixed(obligation);
                self.string(recorded);
                self.string(established);
            }
            ValidationError::ImportCoverageBelowClaim {
                import,
                site,
                obligation,
                needs,
                far,
            } => {
                self.fixed(import);
                self.fixed(site);
                self.fixed(obligation);
                self.string(needs);
                self.strings(far);
            }
            ValidationError::InvalidTensorType { location, detail } => {
                self.string(location);
                self.string(detail);
            }
            ValidationError::InvalidTensorContract { block, ty, reason }
            | ValidationError::InvalidTensorMap { block, ty, reason }
            | ValidationError::InvalidTensorReduce { block, ty, reason }
            | ValidationError::InvalidTensorView { block, ty, reason }
            | ValidationError::InvalidTensorGather { block, ty, reason }
            | ValidationError::InvalidTensorScatter { block, ty, reason } => {
                self.fixed(block);
                self.string(ty);
                self.string(reason);
            }
            ValidationError::InvalidBlobTable { row, reason } => {
                self.fixed(row);
                self.string(reason);
            }
            ValidationError::MissingBlob { location, digest } => {
                self.string(location);
                self.string(digest);
            }
            ValidationError::InvalidTensorBlob { location, reason } => {
                self.string(location);
                self.string(reason);
            }
        }
    }
}
