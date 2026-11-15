// Copyright 2026 Andrew Yates | Licensed under the Apache License, Version 2.0
//! Checked SOURCE_CALL island to the complete original ByteV1 entry.
//! No native, provider, source-text authentication or body license is minted.
use crate::core_execution::{CheckedDefinedConstantCallEntry, CheckedDefinedWordForwardCallEntry};
use crate::{ModuleValidationReport, SourceValueOperationalError};
use clean_kernel::{Environment, Expr};
use clean_verify::eval_ir::{EvalIrVocabulary, shared_specification_with_stack};
use trust_ir::proof::{
    IslandEnvironment, KERNEL_ANCHOR_CLEAN_BACKEND_SOURCE_CALLS_V1, SourceDefinitionRef,
};
use trust_ir::{FuncId, Module, Ty};

type Result<T> = core::result::Result<T, SourceValueOperationalError>;

/// An independently replayed source-named initializer/run-four/halt judgment.
/// The source is the actual admitted island Definition, not a supplied word.
pub struct CheckedSourceCallOperational<'module> {
    module: &'module Module,
    caller: FuncId,
    callee: FuncId,
    source: SourceDefinitionRef,
    environment: Environment,
    judgment: Expr,
    proof: Expr,
}
impl CheckedSourceCallOperational<'_> {
    pub fn functions_in(&self, module: &Module) -> Result<(FuncId, FuncId)> {
        if !std::ptr::eq(module, self.module) {
            return Err(SourceValueOperationalError(
                "source-call operational owner belongs to another immutable module".into(),
            ));
        }
        Ok((self.caller, self.callee))
    }
    pub fn source(&self) -> &SourceDefinitionRef {
        &self.source
    }
    pub fn environment(&self) -> &Environment {
        &self.environment
    }
    pub fn judgment(&self) -> &Expr {
        &self.judgment
    }
    pub fn proof(&self) -> &Expr {
        &self.proof
    }
}

/// Reflect the SAME source-bearing original module after its complete pinned
/// report replayed a SOURCE_CALL certificate for every definition. This is a
/// data catalog, not an execution, body license or source correspondence. Raw
/// reflection still refuses these proof tables. No certificate is stripped.
pub fn reflect_source_call_core_module_v1<'m>(
    report: &'m ModuleValidationReport<'m>,
    addresses: &[(FuncId, u64)],
) -> Result<crate::core_reflection::ReflectedCoreModuleV1<'m>> {
    let checked = || -> core::result::Result<_, String> {
        let module = report
            .validated_module()
            .ok_or("source reflection requires a successful original-module report")?;
        if !report.handle_registry_is_pinned() {
            return Err("source reflection requires pinned validation".into());
        }
        let replayed = report
            .replayed_certificate_refs()
            .ok_or("source reflection lost replayed certificate authority")?;
        for function in &module.functions {
            let count = module
                .proof_certificates
                .iter()
                .filter(|certificate| {
                    replayed.contains(&certificate.lineage_ref())
                        && certificate.evidence.clean_cic_kernel_recheck().is_some_and(
                            |directive| {
                                directive.anchor == KERNEL_ANCHOR_CLEAN_BACKEND_SOURCE_CALLS_V1
                            },
                        )
                        && module.proof_obligations.iter().any(|obligation| {
                            obligation.id == certificate.obligation
                                && obligation.function == Some(function.id)
                        })
                })
                .count();
            if count != 1 {
                return Err("source reflection requires one replayed SOURCE_CALL certificate for every original definition".into());
            }
        }
        crate::core_reflection::reflect_validated_source_module_v1(report, addresses)
            .map_err(|error| error.to_string())
    };
    checked().map_err(SourceValueOperationalError)
}

/// The report must retain BOTH actual SOURCE_CALL certificates replayed for
/// the original module. `island` and the two source selectors are independently
/// chosen consumer inputs, and must equal those exact replayed bindings.
/// First profile: the ordinary attribute-free zero-argument U64 caller/leaf.
/// The source constant itself enters the complete return judgment, and its
/// body is checked in the original island loader, admitted with unchanged
/// checked dependency closure, and replayed in the actual canonical kernel.
/// There is no Rust comparison of source and IR result numbers.
pub fn check_source_bound_defined_constant_call_entry<'module>(
    report: &ModuleValidationReport<'module>,
    core: &CheckedDefinedConstantCallEntry<'module>,
    island: &IslandEnvironment,
    caller_source: &SourceDefinitionRef,
    callee_source: &SourceDefinitionRef,
) -> Result<CheckedSourceCallOperational<'module>> {
    check(report, core, island, caller_source, callee_source, None)
        .map_err(SourceValueOperationalError)
}
/// Join a pointwise one-word original call with both independent checked
/// SOURCE_CALL lambda Definitions. The captured argument is applied to source;
/// only strict canonical replay can discharge its connection to the actual
/// initializer/run-three/halt proof. No other argument/native authority follows.
pub fn check_source_bound_defined_word_forward_call_entry<'module>(
    report: &ModuleValidationReport<'module>,
    core: &CheckedDefinedWordForwardCallEntry<'module>,
    island: &IslandEnvironment,
    caller_source: &SourceDefinitionRef,
    callee_source: &SourceDefinitionRef,
) -> Result<CheckedSourceCallOperational<'module>> {
    check(
        report,
        core.common(),
        island,
        caller_source,
        callee_source,
        Some(core.argument()),
    )
    .map_err(SourceValueOperationalError)
}

fn check<'module>(
    report: &ModuleValidationReport<'module>,
    core: &CheckedDefinedConstantCallEntry<'module>,
    island: &IslandEnvironment,
    caller_source: &SourceDefinitionRef,
    callee_source: &SourceDefinitionRef,
    argument: Option<u64>,
) -> core::result::Result<CheckedSourceCallOperational<'module>, String> {
    let module = report
        .validated_module()
        .ok_or("source-call operational join requires a successful original-module report")?;
    if !report.handle_registry_is_pinned() {
        return Err("source-call operational join requires the pinned validation owner".into());
    }
    let (caller, callee) = core.functions_in(module)?;
    if core.captured_argument() != argument {
        return Err("source-call captured argument profile differs".into());
    }
    for function in &module.functions {
        let signature = module
            .func_type(function.ty)
            .ok_or("missing original source-call signature")?;
        if signature.params
            != if argument.is_some() {
                vec![Ty::U64]
            } else {
                vec![]
            }
            || signature.returns != [Ty::U64]
        {
            return Err(
                "source-call operational join supports the zero-argument U64 profile only".into(),
            );
        }
    }
    let specification = shared_specification_with_stack(EvalIrVocabulary::ByteV1)
        .map_err(|e| format!("source-call canonical specification: {e:?}"))?;
    let environment = source_call_environment(
        report,
        caller,
        callee,
        island,
        caller_source,
        callee_source,
        specification.env().clone(),
    )?;
    let caller_name = clean_kernel::Name::from_string(&caller_source.decl);
    let mut source = Expr::const_(caller_name, vec![]);
    if let Some(argument) = argument {
        source = Expr::app(source, Expr::nat_lit(argument));
    }
    // The actual original source constant, with all its checked definitions,
    // replaces the result term of the independently reconstructed whole query.
    // Only kernel replay can discharge the resulting source/Core connection.
    let judgment = core.entry_claim_with_word(source);
    let proof = core.proof().clone();
    crate::source_value_operational::strict_replay(&environment, &judgment, &proof)?;
    Ok(CheckedSourceCallOperational {
        module,
        caller,
        callee,
        source: caller_source.clone(),
        environment,
        judgment,
        proof,
    })
}

/// Reuse exactly the original SOURCE_CALL binding/closure admission for another
/// independently selected maintained canonical environment. A changed or
/// colliding original declaration still refuses before correspondence replay.
pub(crate) fn source_call_environment(
    report: &ModuleValidationReport<'_>,
    caller: FuncId,
    callee: FuncId,
    island: &IslandEnvironment,
    caller_source: &SourceDefinitionRef,
    callee_source: &SourceDefinitionRef,
    mut environment: Environment,
) -> core::result::Result<Environment, String> {
    let module = report
        .validated_module()
        .ok_or("source-call environment needs original valid report")?;
    if !report.handle_registry_is_pinned() {
        return Err("source-call environment requires pinned report".into());
    }
    let replayed = report
        .replayed_certificate_refs()
        .ok_or("source-call report lost replayed authority")?;
    for (function, selected) in [(caller, caller_source), (callee, callee_source)] {
        let mut matches = module.proof_certificates.iter().filter(|certificate| {
            certificate
                .evidence
                .clean_cic_kernel_recheck()
                .is_some_and(|directive| {
                    directive.anchor == KERNEL_ANCHOR_CLEAN_BACKEND_SOURCE_CALLS_V1
                        && module.proof_obligations.iter().any(|obligation| {
                            obligation.id == certificate.obligation
                                && obligation.function == Some(function)
                        })
                })
        });
        let certificate = matches
            .next()
            .ok_or("missing original SOURCE_CALL certificate")?;
        if matches.next().is_some() || !replayed.contains(&certificate.lineage_ref()) {
            return Err(
                "SOURCE_CALL certificate is ambiguous or lacks replayed kernel authority".into(),
            );
        }
        let binding = certificate
            .evidence
            .clean_cic_kernel_recheck()
            .and_then(|directive| directive.binding.as_deref())
            .ok_or("missing SOURCE_CALL source binding")?;
        if binding.environment.as_ref() != Some(island) {
            return Err("source-call island differs from the replayed original binding".into());
        }
        if binding.source.as_ref() != Some(selected) {
            return Err("source-call selection differs from the replayed original binding".into());
        }
    }
    let (original, names) = crate::validate::source_call_original_environment(island)?;
    let selected_names = [caller_source, callee_source].map(|selected| {
        names
            .iter()
            .find(|name| name.to_string() == selected.decl)
            .cloned()
            .ok_or("source-call Definition is not in the checked island")
    });
    let [caller_name, callee_name] = selected_names;
    let caller_name = caller_name?;
    let callee_name = callee_name?;
    let mut closure = std::collections::BTreeSet::new();
    for name in [&caller_name, &callee_name] {
        closure.extend(
            original
                .dependency_closure(name)
                .map_err(|error| error.to_string())?,
        );
    }
    crate::source_value_operational::import_checked_declarations(
        &mut environment,
        &original,
        closure,
    )?;
    for name in [&caller_name, &callee_name] {
        if original
            .closure_digest(name)
            .map_err(|error| error.to_string())?
            != environment
                .closure_digest(name)
                .map_err(|error| error.to_string())?
        {
            return Err(
                "original SOURCE_CALL closure changed in the operational environment".into(),
            );
        }
    }
    Ok(environment)
}

/// Checked source-named universal word call, distinct from pointwise or native
/// permission. The closed canonical argument-codec theorem remains explicit.
pub struct CheckedSourceWordCallOperational<'module> {
    inner: CheckedSourceCallOperational<'module>,
    codec_claim: Expr,
    codec_proof: Expr,
}
impl CheckedSourceWordCallOperational<'_> {
    pub fn functions_in(&self, module: &Module) -> Result<(FuncId, FuncId)> {
        self.inner.functions_in(module)
    }
    pub fn environment(&self) -> &Environment {
        self.inner.environment()
    }
    pub fn judgment(&self) -> &Expr {
        self.inner.judgment()
    }
    pub fn proof(&self) -> &Expr {
        self.inner.proof()
    }
    pub fn argument_codec_claim(&self) -> &Expr {
        &self.codec_claim
    }
    pub fn argument_codec_proof(&self) -> &Expr {
        &self.codec_proof
    }
}
pub use crate::core_execution::derive_defined_word_add_call_entry;
/// Connect BOTH independently replayed SOURCE_CALL lambda Definitions with the
/// actual universal initializer/run-five/halt owner for the SAME module.
/// Canonical arithmetic transports raw wrap64 to prelude Nat.mod; the original
/// source lambda itself enters the goal. No source number or native result is
/// accepted as a supplied expected answer.
pub fn check_source_bound_defined_word_add_call_entry<'module>(
    report: &ModuleValidationReport<'module>,
    core: &crate::core_execution::CheckedDefinedWordAddCallEntry<'module>,
    island: &IslandEnvironment,
    caller_source: &SourceDefinitionRef,
    callee_source: &SourceDefinitionRef,
) -> Result<CheckedSourceWordCallOperational<'module>> {
    let checked = || -> core::result::Result<CheckedSourceWordCallOperational<'module>, String> {
        use crate::core_execution::{Assembler, Limits, PendingEquality};
        use crate::scoped_local::LocalScope;
        let module: &'module Module = report
            .validated_module()
            .ok_or("universal source-call requires successful original report")?;
        let (caller, callee) = core.functions_in(module)?;
        let environment = source_call_environment(
            report,
            caller,
            callee,
            island,
            caller_source,
            callee_source,
            core.environment().clone(),
        )
        .map_err(|e| format!("universal source declaration admission: {e}"))?;
        let mut scope = LocalScope::new();
        let raw = scope
            .try_local(Expr::const_str("Nat"))
            .map_err(|e| e.to_string())?;
        let mut a = Assembler::new(
            &mut scope,
            Limits {
                max_operations: 100_000,
                max_locals: 1000,
                max_list_items: 1000,
                max_lookup_candidates: 1000,
                lookup_heartbeats: 2_000_000,
                lookup_cache_entries: 100_000,
            },
        )?;
        let input = core.input_at(raw.term().clone());
        let source = Expr::app(Expr::const_str(&caller_source.decl), input.clone());
        let (_, modulus, _) = a
            .byte_add_word64_mod(input, Expr::nat_lit(core.offset()))
            .map_err(|e| format!("universal source result modulus: {e}"))?;
        let modulus = a
            .ascribe_endpoints(modulus, core.result_at(raw.term().clone()), source)
            .map_err(|e| format!("universal source lambda result: {e}"))?;
        let transported = a.congruence(
            modulus,
            Expr::app(Expr::const_str("IRByteConfigV1"), Expr::const_str("Nat")),
            |word| core.terminal_with_word(word),
        )?;
        // Apply the checked quantified theorem; do not inspect a candidate's
        // stored run endpoints. The query is independently rebuilt by Core.
        let body = match core.judgment().kind() {
            clean_kernel::ExprKind::Pi(_, _, body) => (**body).clone(),
            _ => return Err("universal Core claim lost its Nat binder".into()),
        };
        let at = Expr::app(
            Expr::lam(
                clean_kernel::BinderInfo::Default,
                Expr::const_str("Nat"),
                body,
            ),
            raw.term().clone(),
        );
        let mut checker = clean_kernel::TypeChecker::new(&environment);
        checker.set_allow_unsafe(false);
        checker.set_allow_partial(false);
        let normalized = checker.whnf(&at);
        drop(checker);
        let fields = normalized.get_app_args();
        let [ty, left, right] = fields.as_slice() else {
            return Err("universal Core equality shape differs".into());
        };
        let first = PendingEquality::candidate(
            (*ty).clone(),
            (*left).clone(),
            (*right).clone(),
            Expr::app(core.proof().clone(), raw.term().clone()),
        );
        // WHNF of the quantified Eq may expose definitional forms of the
        // terminal configuration. Transport explicitly back to the original
        // reconstructed terminal before syntactic composition; the final
        // closed kernel replay must check this conversion.
        let first = a
            .convert_endpoints(
                first.clone(),
                first.left().clone(),
                transported.left().clone(),
            )
            .map_err(|e| format!("universal source/Core terminal conversion: {e}"))?;
        let joined = a
            .compose(first, transported)
            .map_err(|e| format!("universal source/Core terminal composition: {e}"))?;
        let proof = scope
            .close(&raw.lam(joined.term().clone()))
            .map_err(|e| e.to_string())?;
        let judgment = scope
            .close(&raw.pi(joined.proposition()))
            .map_err(|e| e.to_string())?;
        crate::source_value_operational::strict_replay(&environment, &judgment, &proof)?;
        crate::source_value_operational::strict_replay(
            &environment,
            core.argument_codec_claim(),
            core.argument_codec_proof(),
        )?;
        Ok(CheckedSourceWordCallOperational {
            inner: CheckedSourceCallOperational {
                module,
                caller,
                callee,
                source: caller_source.clone(),
                environment,
                judgment,
                proof,
            },
            codec_claim: core.argument_codec_claim().clone(),
            codec_proof: core.argument_codec_proof().clone(),
        })
    };
    checked().map_err(SourceValueOperationalError)
}
