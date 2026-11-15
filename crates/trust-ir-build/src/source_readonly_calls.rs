// Copyright 2026 Andrew Yates | Apache-2.0
//! A distinct admitted source/body family for readonly pointer calls. The
//! certificate states WHOLE effect-function equality, not equality at one word.
//! Execution, physical input permissions, frontend/source-text authentication
//! and native installation remain separate consuming owners.

use crate::{ModuleValidationReport, codegen_license_errors_with};
use trust_ir::proof::{KERNEL_ANCHOR_CLEAN_BACKEND_READONLY_CALLS_V1, SourceDefinitionRef};
use trust_ir::{BodyGate, FuncId, Inst, Module};

/// Sealed custody of the SAME original module/report and both source-bearing
/// readonly-family certificates actually replayed by its pinned validator.
/// This is a format body-license prerequisite, not an executable capability.
pub struct CheckedReadonlySourceFamily<'m> {
    report: &'m ModuleValidationReport<'m>,
    module: &'m Module,
    caller: FuncId,
    callee: FuncId,
    caller_source: SourceDefinitionRef,
    callee_source: SourceDefinitionRef,
    island: trust_ir::proof::IslandEnvironment,
}
impl<'m> CheckedReadonlySourceFamily<'m> {
    pub(crate) fn source_island(&self) -> &trust_ir::proof::IslandEnvironment {
        &self.island
    }
    pub fn module(&self) -> &'m Module {
        self.module
    }
    pub fn validation_report(&self) -> &'m ModuleValidationReport<'m> {
        self.report
    }
    pub fn functions_in(&self, module: &Module) -> Result<(FuncId, FuncId), String> {
        if !std::ptr::eq(module, self.module) {
            return Err("readonly source family belongs to another original module".into());
        }
        Ok((self.caller, self.callee))
    }
    pub fn source(&self, function: FuncId) -> Result<&SourceDefinitionRef, String> {
        if function == self.caller {
            Ok(&self.caller_source)
        } else if function == self.callee {
            Ok(&self.callee_source)
        } else {
            Err("function is not in this checked readonly source family".into())
        }
    }
}

/// Consume the actual successful pinned validation pass. A label, hash, DTO,
/// island by itself or a pointwise source-entry owner cannot call this factory.
/// The default codegen license evidence layer is checked against this SAME
/// pass's replayed set; CG must still apply its default authority policy.
pub fn check_readonly_source_family<'m>(
    report: &'m ModuleValidationReport<'m>,
) -> Result<CheckedReadonlySourceFamily<'m>, String> {
    let module = report
        .validated_module()
        .ok_or("readonly source family needs a successful original-module validation")?;
    if !report.handle_registry_is_pinned() {
        return Err("readonly source family requires pinned validation".into());
    }
    let replayed = report
        .replayed_certificate_refs()
        .ok_or("readonly source family lost replayed certificate authority")?;
    if module.functions.len() != 2
        || !module.imports.is_empty()
        || !codegen_license_errors_with(report).is_empty()
    {
        return Err("readonly source family requires both original definitions and current default license evidence".into());
    }
    let mut selected = Vec::new();
    let mut original_island = None;
    let mut caller = None;
    let mut callee = None;
    for function in &module.functions {
        if !matches!(&function.body_gate,Some(BodyGate::Gated{authority,..}) if authority=="clean-kernel-tv")
        {
            return Err(
                "readonly source family requires the actual recognized source body gate".into(),
            );
        }
        let matches = module
            .proof_certificates
            .iter()
            .filter(|certificate| {
                replayed.contains(&certificate.lineage_ref())
                    && certificate
                        .evidence
                        .clean_cic_kernel_recheck()
                        .is_some_and(|r| r.anchor == KERNEL_ANCHOR_CLEAN_BACKEND_READONLY_CALLS_V1)
                    && module
                        .proof_obligations
                        .iter()
                        .any(|o| o.id == certificate.obligation && o.function == Some(function.id))
            })
            .collect::<Vec<_>>();
        let [certificate] = matches.as_slice() else {
            return Err("readonly source family needs one actual replayed readonly certificate per definition".into());
        };
        let source = certificate
            .evidence
            .clean_cic_kernel_recheck()
            .and_then(|r| r.binding.as_deref())
            .and_then(|b| b.source.as_ref())
            .ok_or("readonly certificate lost its source binding")?
            .clone();
        let island = certificate
            .evidence
            .clean_cic_kernel_recheck()
            .and_then(|r| r.binding.as_deref())
            .and_then(|b| b.environment.as_ref())
            .ok_or("readonly source family lost its actual replayed source island")?;
        if let Some(existing) = &original_island {
            if existing != island {
                return Err("readonly source family uses different actual source islands".into());
            }
        } else {
            original_island = Some(island.clone());
        }
        match function
            .blocks
            .first()
            .and_then(|b| b.body.first())
            .map(|n| &n.inst)
        {
            Some(Inst::Call { .. }) if caller.is_none() => caller = Some(function.id),
            Some(Inst::Load { .. }) if callee.is_none() => callee = Some(function.id),
            _ => return Err("readonly source family actual original body roles differ".into()),
        }
        selected.push((function.id, source));
    }
    let caller = caller.ok_or("readonly source caller absent")?;
    let callee = callee.ok_or("readonly source load leaf absent")?;
    let source = |id| {
        selected
            .iter()
            .find(|(f, _)| *f == id)
            .map(|(_, s)| s.clone())
            .ok_or_else(|| "readonly source selection absent".to_owned())
    };
    Ok(CheckedReadonlySourceFamily {
        report,
        module,
        caller,
        callee,
        caller_source: source(caller)?,
        callee_source: source(callee)?,
        island: original_island.ok_or("readonly source family island absent")?,
    })
}

/// Retain all original proof fields and module identity. Raw reflection still
/// refuses annotated modules; only the actual admitted source family supplies
/// the existing checked-report interpretation for this distinct entry point.
pub fn reflect_readonly_source_core_module_v1<'m>(
    family: &'m CheckedReadonlySourceFamily<'m>,
    addresses: &[(FuncId, u64)],
) -> Result<crate::core_reflection::ReflectedCoreModuleV1<'m>, String> {
    crate::core_reflection::reflect_validated_source_module_v1(
        family.validation_report(),
        addresses,
    )
    .map_err(|error| error.to_string())
}
