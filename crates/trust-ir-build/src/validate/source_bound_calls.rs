// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Closed source-bound call composition, distinct from parametric backend TV.
//!
//! A family maps actual module definitions to monomorphic definitions in ONE
//! checked island. Each rederived IR denotation's outer callee telescope is
//! applied to those source constants, in the rederived symbol order. The
//! kernel checks the resulting CLOSED function equals its own source constant.
//! Every reached callee has its own equation in this same family. No opaque
//! function interpretation, imported body, recursion or source-text authority
//! is manufactured. `SourceDefinitionRef::closure_digest` retains its existing
//! carried-provenance meaning; the checked source here is the island definition.
//!
//! Existing binding/wire fields suffice: the distinct versioned anchor fixes
//! the interpretation of `context` (exact source constant), and the ordinary
//! v8 lineage binds source, environment, statement and actual callee symbols.
//! Old readers refuse the new anchor. The old anchor and its slice-1 guard are
//! unchanged. Normal validation independently rebuilds the whole family once.

use super::{ModuleFunctionCatalog, TvRecheckOutcome};
use std::collections::BTreeMap;
use trust_ir::Module;
use trust_ir::proof::{ProofCertificate, ProofLineageNode, ProofObligation};
use trust_ir::value::ProofId;

/// Complete producer output. Attach all rows/certificates together; the nodes
/// carry the exact independently reconstructible source/target semantic roots.
/// `certificates` includes the ordinary local `InheritedFromCallee` edge rows.
#[derive(Debug)]
pub struct SourceBoundCallCertificates {
    pub nodes: Vec<ProofLineageNode>,
    pub obligations: Vec<ProofObligation>,
    pub certificates: Vec<ProofCertificate>,
}

#[cfg(feature = "clean-tv-anchor")]
mod enabled {
    use super::*;
    use crate::validate::{clean_backend_tv as tv, clean_island, lineage_bundle_digest};
    use clean_kernel::env::{ConstantKind, Environment};
    use clean_kernel::{BinderInfo, Expr, ExprKind, Level, Name, TypeChecker};
    use std::collections::BTreeSet;
    use trust_ir::FuncId;
    use trust_ir::interpret::{
        ExecutionObserver, ExecutionProgress, ExecutionSite, InterpretOptions, ObservedSession,
    };
    use trust_ir::proof::{
        CLEAN_EXPR_V1_MAX_BYTES, CLEAN_EXPR_V1_MAX_NODES, CertificateBinding,
        CleanCicKernelRecheck, ISLAND_DECLARATIONS_V1_MAX_DECLARATIONS, IslandEnvironment,
        KERNEL_ANCHOR_CLEAN_BACKEND_READONLY_CALLS_V1 as READONLY_ANCHOR,
        KERNEL_ANCHOR_CLEAN_BACKEND_SOURCE_CALLS_V1 as SCALAR_ANCHOR, ObligationKind,
        ProofEvidence, ProofLineageId, ProofStatus, ProofTransform, ProofTransformStage,
        SourceDefinitionRef, clean_cic_lineage_binds, clean_cic_lineage_digest_v8,
        clean_cic_statement_digest, decode_clean_expr_v1, encode_clean_expr_v1,
        kernel_environment_digest,
    };

    #[derive(Clone, Copy, PartialEq, Eq)]
    enum Model {
        Scalar,
        ReadonlyByte,
    }
    impl Model {
        fn anchor(self) -> &'static str {
            match self {
                Self::Scalar => SCALAR_ANCHOR,
                Self::ReadonlyByte => READONLY_ANCHOR,
            }
        }
        fn module(self) -> &'static str {
            match self {
                Self::Scalar => "CleanCompiler.SourceCallsV1",
                Self::ReadonlyByte => "CleanCompiler.ReadonlyCallsV1",
            }
        }
        fn carrier_prefix(self) -> &'static [u8] {
            match self {
                Self::Scalar => b"clean_backend_source_calls_v1\0",
                Self::ReadonlyByte => b"clean_backend_readonly_calls_v1\0",
            }
        }
        fn of_module(module: &Module, budget: &mut Allowance) -> Result<Self, String> {
            budget.charge(module.proof_certificates.len(), 0)?;
            let mut model = None;
            for cert in &module.proof_certificates {
                let Some(d) = cert.evidence.clean_cic_kernel_recheck() else {
                    continue;
                };
                let next = match d.anchor.as_str() {
                    SCALAR_ANCHOR => Self::Scalar,
                    READONLY_ANCHOR => Self::ReadonlyByte,
                    _ => continue,
                };
                if model.is_some_and(|old| old != next) {
                    return Err(
                        "mixed scalar/readonly source families are outside the bounded profile"
                            .into(),
                    );
                }
                model = Some(next);
            }
            Ok(model.unwrap_or(Self::Scalar))
        }
    }

    /// Framed source/target semantic carriers, keyed by actual function ID.
    type SemanticCarriers = BTreeMap<FuncId, (String, Vec<u8>, Vec<u8>)>;

    // Aggregate ceilings reuse the existing expression/island owner ceilings,
    // never a new allowance per callee. Admission work counts the observed
    // module walk, table/edge visits and conservatively one unit per encoded
    // byte; proof bytes prepay that bound BEFORE decode (no renewed aggregate
    // node allowance per proof). Derived carriers use the existing bounded
    // encoder before aggregate retention admission, so a failed encode/charge
    // may spend that encoder's one-carrier limit and terminates the whole
    // family. All kernel work, including source island insertion and the
    // audit's internal checkers, shares one ambient <=2M pot. The equation
    // TypeChecker also has a secondary shared 2M heartbeat ceiling, never
    // reset. Existing codec/audit traversal and allocator contracts remain;
    // these cooperative limits are not a wall-time or exact peak-heap bound.
    const MAX_WORK: usize = CLEAN_EXPR_V1_MAX_NODES;
    const MAX_BYTES: usize = CLEAN_EXPR_V1_MAX_BYTES;

    /// ALL kernel checkers (including legacy rooted-audit/dependency checkers)
    /// draw from this ONE ambient pot. The pinned public API cannot restore a
    /// nested caller's exact remaining count, so never replace an active pot:
    /// borrow a remaining allowance <= this ceiling, otherwise refuse. With
    /// no ambient owner, install the fixed finite ceiling once and retire it
    /// on every exit. No per-callee set/reset/suspension is performed here.
    struct KernelBudget {
        owned: bool,
    }
    impl KernelBudget {
        fn enter() -> Result<Self, String> {
            if clean_kernel::env::mm_axiom_only() {
                return Err("source call-family requires strict kernel mode".into());
            }
            if clean_kernel::tc::declaration_budget_limit() == 0 {
                clean_kernel::tc::set_declaration_budget(MAX_WORK as u64);
                Ok(Self { owned: true })
            } else if clean_kernel::tc::declaration_budget_remaining() <= MAX_WORK as u64 {
                Ok(Self { owned: false })
            } else {
                Err("source call-family cannot replace a larger active caller kernel budget; bounded borrowing requires remaining <= 2000000".into())
            }
        }
    }
    impl Drop for KernelBudget {
        fn drop(&mut self) {
            if self.owned {
                clean_kernel::tc::clear_declaration_budget();
            }
        }
    }

    #[derive(Default)]
    struct Allowance {
        work: usize,
        bytes: usize,
        failed: bool,
    }
    impl Allowance {
        fn charge(&mut self, work: usize, bytes: usize) -> Result<(), String> {
            if self.failed {
                return Err("source call-family allowance already refused".into());
            }
            self.failed = true;
            if clean_kernel::tc::declaration_budget_exhausted() || clean_kernel::tc::poll_deadline()
            {
                return Err("source call-family caller kernel budget/deadline stopped".into());
            }
            self.work = self
                .work
                .checked_add(work)
                .ok_or("source family work overflow")?;
            self.bytes = self
                .bytes
                .checked_add(bytes)
                .ok_or("source family bytes overflow")?;
            if self.work > MAX_WORK || self.bytes > MAX_BYTES {
                return Err(
                    "source call-family aggregate allowance exhausted (no per-callee refill)"
                        .into(),
                );
            }
            self.failed = false;
            Ok(())
        }
        fn encoded(&mut self, e: &Expr) -> Result<Vec<u8>, String> {
            // The existing encoder bounds a single carrier. Sum every carrier
            // over the family as well, before retaining or decoding it.
            self.charge(1, 0)?;
            let bytes = encode_clean_expr_v1(e)?;
            self.charge(bytes.len(), bytes.len())?;
            Ok(bytes)
        }
    }
    impl ExecutionObserver for Allowance {
        type Refusal = String;
        fn admit(&mut self, p: ExecutionProgress) -> Result<(), String> {
            self.charge(p.work, p.copy_bytes)
        }
    }

    fn preflight(module: &Module, first: FuncId, budget: &mut Allowance) -> Result<(), String> {
        let mut session = ObservedSession::new(InterpretOptions::default(), budget);
        module
            .checked_stable_digest_observed(&mut session, ExecutionSite::Entry(first))
            .map_err(|e| format!("source call-family bounded input admission: {e}"))?;
        Ok(())
    }

    struct Entry {
        function: FuncId,
        name: String,
        source: SourceDefinitionRef,
        function_type: Expr,
        callee_ids: Vec<FuncId>,
        callee_names: Vec<String>,
        source_expr: Expr,
        target: Expr,
        statement: Expr,
    }

    /// The new anchor's semantic carrier frames (anchor environment digest,
    /// EXACT checked island digest, canonical Expr). The legacy environment
    /// digest displays declaration names; the island digest additionally binds
    /// their actual Num/Str components. Constants without this closure would
    /// give equal endpoint hashes to different source meanings. This is an
    /// anchor-specific carrier inside the EXISTING semantic bundle domain,
    /// not a wire/digest-domain migration or a re-tagged target root.
    fn semantic_bytes(
        model: Model,
        environment: trust_ir::proof::ProofDigest,
        island: trust_ir::proof::ProofDigest,
        expression: &[u8],
        budget: &mut Allowance,
    ) -> Result<Vec<u8>, String> {
        let prefix = model.carrier_prefix();
        let length = prefix
            .len()
            .checked_add(32 + 32 + 8)
            .and_then(|n| n.checked_add(expression.len()))
            .ok_or("semantic carrier overflow")?;
        budget.charge(length, length)?;
        let mut out = Vec::with_capacity(length);
        out.extend_from_slice(prefix);
        out.extend_from_slice(&environment.bytes);
        out.extend_from_slice(&island.bytes);
        out.extend_from_slice(&(expression.len() as u64).to_le_bytes());
        out.extend_from_slice(expression);
        Ok(out)
    }

    fn function_type(den: &tv::TvDenotation) -> Expr {
        den.params
            .iter()
            .rev()
            .fold(den.result.kernel_ty(), |body, sort| {
                Expr::pi(BinderInfo::Default, sort.kernel_ty(), body)
            })
    }
    fn equality(ty: &Expr, lhs: Expr, rhs: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
            [ty.clone(), lhs, rhs],
        )
    }
    fn reflexivity(entry: &Entry) -> Expr {
        Expr::apps(
            Expr::const_(
                Name::from_string("Eq.refl"),
                vec![Level::succ(Level::zero())],
            ),
            [entry.function_type.clone(), entry.target.clone()],
        )
    }

    // This is a denotation of the two admitted original body shapes using the
    // EXISTING total ByteV1 load operation (including errors and memory), not
    // a second memory evaluator or a guessed return word. Context, memory and
    // address are universally bound. The caller selects its actual callee's
    // separately checked source function, never an opaque provider.
    fn readonly_denotation(
        module: &Module,
        catalog: &ModuleFunctionCatalog<'_>,
        f: &trust_ir::Function,
        sources: &BTreeMap<FuncId, Expr>,
    ) -> Result<(Expr, Vec<FuncId>, Vec<String>, Expr), String> {
        use trust_ir::{CallingConv, Inst, Linkage, Ty};
        let target = module
            .target_info
            .as_ref()
            .ok_or("readonly source requires an explicit target")?;
        if target.pointer_size != 8 || target.endianness != trust_ir::Endianness::Little {
            return Err("readonly source requires explicit little-endian 64-bit pointers".into());
        }
        if !module.imports.is_empty()
            || !module.globals.is_empty()
            || !module.enums.is_empty()
            || !module.records.is_empty()
            || !module.closure_types.is_empty()
            || !module.spec_modules.is_empty()
            || !module.predicates.is_empty()
            || !module.universes.is_empty()
        {
            return Err(
                "readonly source family requires the closed primitive module profile".into(),
            );
        }
        let signature = module
            .func_type(f.ty)
            .ok_or("readonly source missing signature")?;
        if f.calling_conv != CallingConv::C
            || !f.attrs.is_empty()
            || !f.proofs.is_empty()
            || f.summary.is_some()
            || f.source_provenance.is_some()
            || matches!(
                f.linkage,
                Linkage::Weak | Linkage::LinkOnce | Linkage::ExternalWeak
            )
            || signature.abi.is_some()
            || signature.is_vararg
            || signature.params != [Ty::Ptr]
            || signature.returns != [Ty::U64]
            || f.blocks.len() != 1
            || f.blocks[0].id != f.entry
        {
            return Err("readonly source requires exact unadorned C(Ptr)->U64 bodies".into());
        }
        let block = &f.blocks[0];
        let [(parameter, Ty::Ptr)] = block.params.as_slice() else {
            return Err("readonly source pointer formal differs".into());
        };
        let [operation, returning] = block.body.as_slice() else {
            return Err("readonly source refuses hidden instructions/effects".into());
        };
        let [result] = operation.results.as_slice() else {
            return Err("readonly source result arity differs".into());
        };
        if block
            .body
            .iter()
            .any(|node| !node.proofs.is_empty() || node.proof_context.is_some())
            || !returning.results.is_empty()
            || !matches!(&returning.inst, Inst::Return { values } if values == &[*result])
        {
            return Err("readonly source must return exactly the original operation result".into());
        }
        let c = |name: &str| Expr::const_(Name::from_string(name), vec![]);
        let domains = [c("IRByteContextV1"), c("IRByteMemoryV1"), c("Nat")];
        let ty = domains
            .iter()
            .rev()
            .fold(c("IRByteMemoryResultV1"), |body, domain| {
                Expr::pi(BinderInfo::Default, domain.clone(), body)
            });
        let (body, ids, names) = match &operation.inst {
            Inst::Load {
                ty: Ty::U64,
                ptr,
                volatile: false,
                align: Some(8),
            } if ptr == parameter && f.linkage == Linkage::Internal => {
                let uint64 = Expr::app(c("IRTy.uint_"), Expr::nat_lit(64));
                (
                    Expr::apps(
                        c("ir_byte_load_v1"),
                        [
                            Expr::bvar(2),
                            uint64,
                            Expr::app(c("IRScalar.ptr_"), Expr::bvar(0)),
                            Expr::nat_lit(8),
                            c("Bool.false"),
                            Expr::bvar(1),
                        ],
                    ),
                    vec![],
                    vec![],
                )
            }
            Inst::Call { callee, args } if *callee != f.id && args == &[*parameter] => {
                let selected = catalog
                    .unique(*callee)
                    .ok_or("readonly source missing/ambiguous original callee")?;
                if selected.linkage != Linkage::Internal
                    || module.func_type(selected.ty) != Some(signature)
                {
                    return Err("readonly source callee ABI/linkage differs".into());
                }
                let source = sources
                    .get(callee)
                    .ok_or("readonly source family misses actual callee")?;
                (
                    Expr::apps(
                        source.clone(),
                        [Expr::bvar(2), Expr::bvar(1), Expr::bvar(0)],
                    ),
                    vec![*callee],
                    vec![selected.name.clone()],
                )
            }
            _ => {
                return Err(
                    "readonly source requires one original aligned LOAD8 or forwarding CALL".into(),
                );
            }
        };
        let target = domains.into_iter().rev().fold(body, |body, domain| {
            Expr::lam(BinderInfo::Default, domain, body)
        });
        Ok((ty, ids, names, target))
    }

    /// No graph metadata is trusted: scan actual IR, require actual defined
    /// callees, and then use Kahn's algorithm (no recursive stack). Multiple
    /// roots are allowed, but every actual outgoing call must stay in the map.
    fn derive(
        model: Model,
        module: &Module,
        catalog: &ModuleFunctionCatalog<'_>,
        sources: &[(FuncId, SourceDefinitionRef)],
        island_names: &[Name],
        budget: &mut Allowance,
    ) -> Result<Vec<Entry>, String> {
        if sources.is_empty() || sources.len() > ISLAND_DECLARATIONS_V1_MAX_DECLARATIONS {
            return Err(
                "source family must be nonempty and fit the existing island declaration ceiling"
                    .into(),
            );
        }
        budget.charge(
            sources.len(),
            sources
                .len()
                .checked_mul(core::mem::size_of::<Entry>())
                .ok_or("source family capacity overflow")?,
        )?;
        // Resolve the ACTUAL already bounded/decoded island Name. Never parse
        // a producer string into a new potentially deep Name, and never
        // conflate numeric and string name components with the same display.
        let mut declared_names = BTreeMap::new();
        for name in island_names {
            budget.charge(1, 0)?;
            let display = name.to_string();
            budget.charge(display.len(), display.len())?;
            if declared_names.insert(display, name).is_some() {
                return Err("ambiguous source definition display selector".into());
            }
        }
        let mut source_map = BTreeMap::new();
        let mut source_names = BTreeSet::new();
        let mut function_names = BTreeSet::new();
        for (id, source) in sources {
            budget.charge(source.decl.len(), source.decl.len())?;
            let name = declared_names
                .get(&source.decl)
                .ok_or("source definition is not in this checked island")?;
            let constant = Expr::const_((*name).clone(), vec![]);
            if source_map.insert(*id, constant).is_some() || !source_names.insert(&source.decl) {
                return Err(
                    "source family has duplicate function or source-definition binding".into(),
                );
            }
            let function = catalog
                .unique(*id)
                .ok_or("source family function is missing or ambiguous")?;
            if function.is_declaration() {
                return Err(format!(
                    "source family requires actual same-module defined bodies: {}",
                    function.name
                ));
            }
            if !function_names.insert(&function.name) {
                return Err("source family link symbol is ambiguous".into());
            }
        }
        if model == Model::ReadonlyByte
            && (module.functions.len() != 2 || sources.len() != 2 || !module.imports.is_empty())
        {
            return Err(
                "readonly source family requires the complete two-definition closed module".into(),
            );
        }
        let mut entries = Vec::new();
        for (id, source) in sources {
            let f = catalog.unique(*id).expect("checked above");
            let (ty, callee_ids, callee_names, target) = match model {
                Model::Scalar => {
                    let den = tv::denote_function_with_catalog(module, catalog, f)?;
                    tv::alloc_release_balance(f)?;
                    let mut target = tv::closed_denotation(&den);
                    for callee in &den.callee_ids {
                        target = Expr::app(
                            target,
                            source_map
                                .get(callee)
                                .ok_or("source family misses actual callee")?
                                .clone(),
                        );
                    }
                    (
                        function_type(&den),
                        den.callee_ids.clone(),
                        den.callees.iter().map(|(n, _)| n.clone()).collect(),
                        target,
                    )
                }
                Model::ReadonlyByte => readonly_denotation(module, catalog, f, &source_map)?,
            };
            budget.charge(callee_ids.len(), 0)?;
            let source_expr = source_map[id].clone();
            let statement = equality(&ty, target.clone(), source_expr.clone());
            // Bound the retained denotation-derived carriers in aggregate.
            budget.encoded(&target)?;
            budget.encoded(&statement)?;
            entries.push(Entry {
                function: *id,
                name: f.name.clone(),
                source: source.clone(),
                function_type: ty,
                callee_ids,
                callee_names,
                source_expr,
                target,
                statement,
            });
        }
        if model == Model::ReadonlyByte
            && entries.iter().filter(|e| !e.callee_ids.is_empty()).count() != 1
        {
            return Err(
                "readonly source family requires exactly one forwarding caller and one load leaf"
                    .into(),
            );
        }
        let mut done = BTreeSet::new();
        while done.len() != entries.len() {
            let before = done.len();
            for e in &entries {
                budget.charge(1 + e.callee_ids.len(), 0)?;
                if e.callee_ids.iter().all(|c| done.contains(c)) {
                    done.insert(e.function);
                }
            }
            if before == done.len() {
                return Err(
                    "recursive source call family is unsupported (including self calls)".into(),
                );
            }
        }
        Ok(entries)
    }

    fn environment(
        model: Model,
        island: &IslandEnvironment,
    ) -> Result<(Environment, Vec<Name>), String> {
        let mut env = match model {
            Model::Scalar => tv::anchor_environment()?,
            Model::ReadonlyByte => {
                #[cfg(feature = "source-value-operational")]
                {
                    clean_verify::eval_ir::shared_specification_with_stack(
                        clean_verify::eval_ir::EvalIrVocabulary::ByteV1,
                    )
                    .map_err(|e| format!("readonly source canonical ByteV1 environment: {e:?}"))?
                    .env()
                    .clone()
                }
                #[cfg(not(feature = "source-value-operational"))]
                {
                    return Err(
                        "readonly source call composition requires source-value-operational".into(),
                    );
                }
            }
        };
        let names = clean_island::install(&mut env, island)?;
        Ok((env, names))
    }

    fn check_entry(
        env: &Environment,
        names: &[Name],
        tc: &mut TypeChecker<'_>,
        entry: &Entry,
        proof: &Expr,
    ) -> Result<(), String> {
        let ExprKind::Const(name, _) = entry.source_expr.kind() else {
            return Err("source family did not derive a source constant".into());
        };
        if !names.contains(name) {
            return Err("source definition is not in this checked island".into());
        }
        let info = env.get_const(name).ok_or("missing source declaration")?;
        if info.kind != ConstantKind::Definition
            || !info.level_params.is_empty()
            || info.value.is_none()
        {
            return Err("source binding requires a monomorphic genuine island definition".into());
        }
        let ty = entry.function_type.clone();
        tc.check_type(&entry.source_expr, &ty)
            .map_err(|e| format!("source signature mismatch for {}: {e:?}", entry.name))?;
        tc.check_type(&entry.target, &ty).map_err(|e| {
            format!(
                "specialized IR signature mismatch for {}: {e:?}",
                entry.name
            )
        })?;
        tc.check_type(proof, &entry.statement)
            .map_err(|e| format!("source equation kernel refusal for {}: {e:?}", entry.name))?;
        // Same rooted authority owner as the ordinary theorem rechecker. The
        // proof itself is the root. The legacy audit constructs internal
        // strict checkers; every one draws from the SAME ambient family pot,
        // including dependency rechecks. No new theorem is installed.
        crate::validate::clean_cic_kernel::recheck_rooted_proof(
            env,
            &entry.statement,
            proof,
            &tv::tv_theorem_name(&entry.name),
            &[],
        )?;
        if tc.heartbeat_spent() {
            return Err("source call-family shared kernel allowance/stop exhausted".into());
        }
        Ok(())
    }

    fn rows<'a>(
        model: Model,
        module: &'a Module,
        catalog: &ModuleFunctionCatalog<'_>,
        budget: &mut Allowance,
    ) -> Result<Vec<(&'a ProofObligation, &'a ProofCertificate)>, String> {
        budget.charge(module.proof_certificates.len(), 0)?;
        if !module.proof_certificates.iter().any(|c| {
            c.evidence
                .clean_cic_kernel_recheck()
                .is_some_and(|d| d.anchor == model.anchor())
        }) {
            return Ok(Vec::new());
        }
        let first = module
            .functions
            .first()
            .ok_or("source family has no actual module function")?
            .id;
        preflight(module, first, budget)?;
        budget.charge(module.proof_obligations.len(), 0)?;
        let mut obligations = BTreeMap::new();
        for o in &module.proof_obligations {
            if obligations.insert(o.id, o).is_some() {
                return Err("source family has ambiguous obligation ids".into());
            }
        }
        let resolve = |id| catalog.unique(id).map(|f| f.name.clone());
        let mut rows = Vec::new();
        let mut ids = BTreeSet::new();
        for cert in &module.proof_certificates {
            let Some(directive) = cert.evidence.clean_cic_kernel_recheck() else {
                continue;
            };
            if directive.anchor != model.anchor() {
                continue;
            }
            let obligation = obligations
                .get(&cert.obligation)
                .ok_or("source family certificate needs one exact obligation")?;
            if !obligation.status.is_kernel_tier() {
                continue;
            }
            if obligation.kind != ObligationKind::TranslationValidation
                || !ids.insert(obligation.id)
                || !clean_cic_lineage_binds(obligation, &cert.evidence, &resolve)
            {
                return Err(
                    "source family has wrong kind, duplicate row or invalid lineage".into(),
                );
            }
            budget.charge(
                1,
                core::mem::size_of::<(&ProofObligation, &ProofCertificate)>(),
            )?;
            if rows.len() == ISLAND_DECLARATIONS_V1_MAX_DECLARATIONS {
                return Err("source family exceeds existing declaration ceiling".into());
            }
            rows.push((*obligation, cert));
        }
        Ok(rows)
    }

    pub(crate) fn recheck_family(
        module: &Module,
        catalog: &ModuleFunctionCatalog<'_>,
    ) -> Result<BTreeMap<ProofId, TvRecheckOutcome>, String> {
        let mut budget = Allowance::default();
        let model = Model::of_module(module, &mut budget)?;
        let rows = rows(model, module, catalog, &mut budget)?;
        if rows.is_empty() {
            return Ok(BTreeMap::new());
        }
        let _kernel_budget = KernelBudget::enter()?;
        let mut sources = Vec::new();
        let mut common_island = None;
        for (obligation, cert) in &rows {
            let d = cert
                .evidence
                .clean_cic_kernel_recheck()
                .expect("rows selected anchor");
            let b = d
                .binding
                .as_deref()
                .ok_or("source family requires a binding")?;
            let island = b
                .environment
                .as_ref()
                .ok_or("source family requires a checked island")?;
            match common_island {
                None => common_island = Some(island),
                Some(old) if old != island => {
                    return Err("source family environments differ".into());
                }
                Some(_) => {}
            }
            if !d.allowed_axioms.is_empty() || d.module != model.module() {
                return Err(
                    "source family requires its canonical module and no added axioms".into(),
                );
            }
            sources.push((
                obligation
                    .function
                    .ok_or("source family row has no function")?,
                b.source
                    .clone()
                    .ok_or("source family requires every source definition binding")?,
            ));
        }
        let (env, names) = environment(model, common_island.expect("nonempty family"))?;
        let entries = derive(model, module, catalog, &sources, &names, &mut budget)?;
        let env_digest = kernel_environment_digest(&env)?;
        let mut tc = TypeChecker::new(&env);
        tc.set_heartbeat_limit(CLEAN_EXPR_V1_MAX_NODES as u32);
        let mut out = BTreeMap::new();
        for ((obligation, cert), entry) in rows.iter().zip(entries) {
            let d = cert
                .evidence
                .clean_cic_kernel_recheck()
                .expect("selected anchor");
            let b = d.binding.as_deref().expect("checked binding");
            let ProofEvidence::CleanCic { term, context, .. } = &cert.evidence else {
                unreachable!()
            };
            let expected = tv::tv_theorem_name(&entry.name);
            if d.theorems != [expected] {
                return Err(
                    "source family theorem citation does not name its actual function".into(),
                );
            }
            let source_bytes = budget.encoded(&entry.source_expr)?;
            if *context != source_bytes {
                return Err("source family context must be its exact source constant".into());
            }
            budget.charge(term.len(), term.len())?;
            let proof = decode_clean_expr_v1(term)?;
            check_entry(&env, &names, &mut tc, &entry, &proof)?;
            let statement_digest = clean_cic_statement_digest(&entry.statement)?;
            let callees = entry.callee_names.clone();
            if b.environment_digest != env_digest
                || b.statement_digest != statement_digest
                || b.callees != callees
            {
                return Err(
                    "source family environment/statement/actual-callee binding mismatch".into(),
                );
            }
            out.insert(
                obligation.id,
                TvRecheckOutcome {
                    callee_ids: entry.callee_ids,
                    callee_names: callees,
                    statement_digest: Some(statement_digest),
                    environment_digest: Some(env_digest),
                    island: Some((common_island.unwrap().digest, entry.source.decl)),
                },
            );
        }
        budget.charge(0, 0)?;
        Ok(out)
    }

    /// Mint a complete acyclic source-bound family from independently supplied
    /// source declarations. No source declaration is synthesized from the IR.
    /// Actual callees must all appear in `sources`, including leaf definitions.
    /// Attach the complete result before ordinary module validation.
    fn certify_family(
        model: Model,
        module: &Module,
        first_node: ProofLineageId,
        first_obligation: ProofId,
        transform: ProofTransform,
        island: &IslandEnvironment,
        sources: &[(FuncId, SourceDefinitionRef)],
    ) -> Result<SourceBoundCallCertificates, String> {
        if transform.stage == ProofTransformStage::Replay {
            return Err("source-call producer does not invent Replay identities".into());
        }
        let _kernel_budget = KernelBudget::enter()?;
        let mut budget = Allowance::default();
        let first = sources.first().ok_or("empty source family")?.0;
        preflight(module, first, &mut budget)?;
        let catalog = ModuleFunctionCatalog::new(module);
        budget.charge(1, island.declarations.len())?;
        let (env, names) = environment(model, island)?;
        let entries = derive(model, module, &catalog, sources, &names, &mut budget)?;
        let environment_digest = kernel_environment_digest(&env)?;
        let mut tc = TypeChecker::new(&env);
        tc.set_heartbeat_limit(CLEAN_EXPR_V1_MAX_NODES as u32);
        let resolve = |id| catalog.unique(id).map(|f| f.name.clone());
        let mut result = SourceBoundCallCertificates {
            nodes: vec![],
            obligations: vec![],
            certificates: vec![],
        };
        let mut obligation_of = BTreeMap::new();
        for (i, entry) in entries.iter().enumerate() {
            let index = u32::try_from(i).map_err(|_| "source family index overflow")?;
            let id = ProofId::new(
                first_obligation
                    .index()
                    .checked_add(index)
                    .ok_or("obligation id overflow")?,
            );
            if module.proof_obligations.iter().any(|o| o.id == id) {
                return Err("source family obligation id already exists".into());
            }
            obligation_of.insert(entry.function, id);
        }
        for (i, entry) in entries.iter().enumerate() {
            let proof = reflexivity(entry);
            check_entry(&env, &names, &mut tc, entry, &proof)?;
            let source_bytes = budget.encoded(&entry.source_expr)?;
            let target_bytes = budget.encoded(&entry.target)?;
            let proof_bytes = budget.encoded(&proof)?;
            let source_carrier = semantic_bytes(
                model,
                environment_digest,
                island.digest,
                &source_bytes,
                &mut budget,
            )?;
            let target_carrier = semantic_bytes(
                model,
                environment_digest,
                island.digest,
                &target_bytes,
                &mut budget,
            )?;
            let source_digest = lineage_bundle_digest(&mut [(
                entry.function.index(),
                entry.name.clone(),
                source_carrier,
            )])?;
            let target_digest = lineage_bundle_digest(&mut [(
                entry.function.index(),
                entry.name.clone(),
                target_carrier,
            )])?;
            let node_id = ProofLineageId::new(
                first_node
                    .index()
                    .checked_add(i as u32)
                    .ok_or("node id overflow")?,
            );
            let mut node =
                ProofLineageNode::new(node_id, transform.clone(), source_digest, target_digest);
            let id = obligation_of[&entry.function];
            let obligation = ProofObligation::new(
                id,
                ObligationKind::TranslationValidation,
                ProofStatus::Certified,
                "closed source-bound call composition",
            )
            .with_function(entry.function)
            .with_formula(node.transform_binding_formula());
            let mut binding = CertificateBinding::new(
                environment_digest,
                clean_cic_statement_digest(&entry.statement)?,
            );
            binding.source = Some(entry.source.clone());
            budget.charge(1, island.declarations.len())?;
            binding.environment = Some(island.clone());
            binding.callees = entry.callee_names.clone();
            let lineage = clean_cic_lineage_digest_v8(&obligation, &resolve, Some(&binding))
                .ok_or("source family has no symbol lineage")?;
            let certificate = ProofCertificate {
                obligation: id,
                prover: "trust_ir.proof.source_calls.producer.v1".into(),
                evidence: ProofEvidence::CleanCic {
                    term: proof_bytes,
                    context: source_bytes,
                    lineage,
                    kernel_recheck: Some(CleanCicKernelRecheck {
                        module: model.module().into(),
                        theorems: vec![tv::tv_theorem_name(&entry.name)],
                        anchor: model.anchor().into(),
                        allowed_axioms: vec![],
                        binding: Some(Box::new(binding)),
                    }),
                },
                assurance: None,
            };
            node.obligations.push(id);
            node.certificates.push(certificate.lineage_ref());
            result.nodes.push(node);
            result.obligations.push(obligation);
            result.certificates.push(certificate);
            for callee in &entry.callee_ids {
                result.certificates.push(ProofCertificate {
                    obligation: id,
                    prover: "trust_ir.proof.source_calls.producer.v1".into(),
                    evidence: ProofEvidence::InheritedFromCallee {
                        callee: *callee,
                        obligation: obligation_of[callee],
                        external: None,
                    },
                    assurance: None,
                });
            }
        }
        budget.charge(0, 0)?;
        Ok(result)
    }

    pub fn certify_source_bound_call_family(
        module: &Module,
        first_node: ProofLineageId,
        first_obligation: ProofId,
        transform: ProofTransform,
        island: &IslandEnvironment,
        sources: &[(FuncId, SourceDefinitionRef)],
    ) -> Result<SourceBoundCallCertificates, String> {
        certify_family(
            Model::Scalar,
            module,
            first_node,
            first_obligation,
            transform,
            island,
            sources,
        )
    }
    /// Universal readonly EFFECT denotations, not a pointwise word comparison.
    /// Both definitions must be independently authored in the checked island.
    pub fn certify_source_bound_readonly_call_family(
        module: &Module,
        first_node: ProofLineageId,
        first_obligation: ProofId,
        transform: ProofTransform,
        island: &IslandEnvironment,
        sources: &[(FuncId, SourceDefinitionRef)],
    ) -> Result<SourceBoundCallCertificates, String> {
        certify_family(
            Model::ReadonlyByte,
            module,
            first_node,
            first_obligation,
            transform,
            island,
            sources,
        )
    }

    pub(crate) fn lineage_semantic_carriers(
        module: &Module,
        catalog: &ModuleFunctionCatalog<'_>,
    ) -> Result<SemanticCarriers, String> {
        // Once for the whole manifest, not a fresh graph/checker allowance
        // for every node. Authority must already have replayed the family.
        let mut budget = Allowance::default();
        let model = Model::of_module(module, &mut budget)?;
        let family = rows(model, module, catalog, &mut budget)?;
        if family.is_empty() {
            return Ok(BTreeMap::new());
        }
        let _kernel_budget = KernelBudget::enter()?;
        let sources = family
            .iter()
            .map(|(o, c)| {
                let source = c
                    .evidence
                    .clean_cic_kernel_recheck()
                    .and_then(|d| d.binding.as_deref())
                    .and_then(|b| b.source.clone())
                    .ok_or("lineage source call family misses a source binding")?;
                Ok((o.function.ok_or("lineage family misses function")?, source))
            })
            .collect::<Result<Vec<_>, String>>()?;
        let island = family[0]
            .1
            .evidence
            .clean_cic_kernel_recheck()
            .and_then(|d| d.binding.as_deref())
            .and_then(|b| b.environment.as_ref())
            .ok_or("lineage source family misses checked environment")?;
        let (env, names) = environment(model, island)?;
        let env_digest = kernel_environment_digest(&env)?;
        let entries = derive(model, module, catalog, &sources, &names, &mut budget)?;
        let mut out = BTreeMap::new();
        for e in entries {
            let source = budget.encoded(&e.source_expr)?;
            let target = budget.encoded(&e.target)?;
            out.insert(
                e.function,
                (
                    e.name,
                    semantic_bytes(model, env_digest, island.digest, &source, &mut budget)?,
                    semantic_bytes(model, env_digest, island.digest, &target, &mut budget)?,
                ),
            );
        }
        budget.charge(0, 0)?;
        Ok(out)
    }
}

#[cfg(feature = "clean-tv-anchor")]
pub use enabled::{certify_source_bound_call_family, certify_source_bound_readonly_call_family};
#[cfg(feature = "clean-tv-anchor")]
pub(super) use enabled::{lineage_semantic_carriers, recheck_family};

#[cfg(not(feature = "clean-tv-anchor"))]
pub fn certify_source_bound_call_family(
    _module: &Module,
    _first_node: trust_ir::proof::ProofLineageId,
    _first_obligation: ProofId,
    _transform: trust_ir::proof::ProofTransform,
    _island: &trust_ir::proof::IslandEnvironment,
    _sources: &[(trust_ir::FuncId, trust_ir::proof::SourceDefinitionRef)],
) -> Result<SourceBoundCallCertificates, String> {
    Err("source-bound call composition requires the clean-tv-anchor feature".into())
}
#[cfg(not(feature = "clean-tv-anchor"))]
pub(crate) fn recheck_family(
    _module: &Module,
    _catalog: &ModuleFunctionCatalog<'_>,
) -> Result<BTreeMap<ProofId, TvRecheckOutcome>, String> {
    Err("source-bound call composition requires the clean-tv-anchor feature".into())
}

#[cfg(not(feature = "clean-tv-anchor"))]
pub fn certify_source_bound_readonly_call_family(
    _module: &Module,
    _first_node: trust_ir::proof::ProofLineageId,
    _first_obligation: ProofId,
    _transform: trust_ir::proof::ProofTransform,
    _island: &trust_ir::proof::IslandEnvironment,
    _sources: &[(trust_ir::FuncId, trust_ir::proof::SourceDefinitionRef)],
) -> Result<SourceBoundCallCertificates, String> {
    Err("readonly source call composition requires the clean-tv-anchor feature".into())
}
