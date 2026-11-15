//! Field-absence ratchets, checked at COMPILE time (roadmap WS8.6, step 1c).
//!
//! Each row below records that a carrier has NO slot for something the
//! two-language design needs (an effect summary / state epoch, an ABI pass
//! mode, a function visibility, an interpreter input oracle). Three rows are
//! FLIPPED: the per-clause obligation backref (WS1.3: the backref is the
//! validator's formula match; the carriers keep their shape), the kernel
//! environment digest (WS1.12a: `CleanCicKernelRecheck.binding`) and the
//! effect summary / state epochs (WS1.14: `FunctionSummary.effects` and
//! `ClausePlace::WorldPre` / `WorldPost`, wire v59). The
//! interpreter-oracle row is RATIFIED-OUT (WS2.11: inputs are entry parameters
//! by ratification, so the absent oracle is held as intended). The archived Part B
//! battery measured these as JSON key sets, which cannot see a field that is
//! serialized with `skip_serializing_if` (finding b2.uf15). Here every carrier
//! is destructured EXHAUSTIVELY, with no `..`:
//!
//! **A new field on any of these structs is a compile error in THIS target
//! only** (`two_language_field_ratchets`), which is exactly the ratchet: the
//! commit that adds the slot must update the destructuring below, flip the
//! row to PASS with a negative twin, and edit `RATCHETS.tsv` in the same
//! commit. No other two-language target is affected.

mod common;

use common::{Expect, Outcome, feature_check, feature_gap, feature_ratified};
use trust_ir::clean_expr_lowering::contract::{
    contract_clean_cic_certificate, contract_clean_cic_certificate_bound_in,
};
use trust_ir::inst::Inst;
use trust_ir::interpret::InterpretOptions;
use trust_ir::proof::{
    CertificateBinding, ClausePlace, CleanCicKernelRecheck, CoverageAssurance, ObligationKind,
    ObligationSite, ProofCertificate, ProofEvidence, ProofFormula, ProofObligation, ProofStatus,
    clean_cic_lineage_digest_v8,
};
use trust_ir::ty::{FuncTy, Ty};
use trust_ir::value::ProofId;
use trust_ir::{
    EffectPlace, EffectSet, EffectSummary, FuncAttrs, Function, FunctionSummary, Global,
    NativeVerificationRequest, NativeVerifierSuite, ParamAttrs, Producer,
};
use trust_ir_build::{ModuleBuilder, ValidationError, validate_module};

// ---------------------------------------------------------------------------
// The exhaustive shapes. Adding a field to any of these structs (or a payload
// to a `ClausePlace` world / unwind place) stops this file compiling.
// ---------------------------------------------------------------------------

fn function_summary_fields(s: &FunctionSummary) -> usize {
    let FunctionSummary {
        requires: _,
        ensures: _,
        params: _,
        proved: _,
        decreases: _,
        backed_by: _,
        effects: _, // v59 (WS1.14): the typed effect frame
    } = s;
    7
}

fn effect_summary_fields(e: &EffectSummary) -> usize {
    let EffectSummary {
        reads: _,
        writes: _,
        allocates: _,
        frees: _,
        may_unwind: _,
        io: _,
    } = e;
    6
}

fn proof_obligation_fields(o: &ProofObligation) -> usize {
    let ProofObligation {
        id: _,
        kind: _,
        status: _,
        description: _,
        formula: _,
        function: _,
        source: _,
        site: _,
        spec: _, // v46 (WS4.14): the temporal-property backref, a spec-machine name pair
    } = o;
    9
}

fn obligation_site_fields(s: &ObligationSite) -> usize {
    let ObligationSite {
        function: _,
        block: _,
        inst_index: _,
    } = s;
    3
}

fn proof_certificate_fields(c: &ProofCertificate) -> usize {
    let ProofCertificate {
        obligation: _,
        prover: _,
        evidence: _,
        assurance: _,
    } = c;
    4
}

fn coverage_assurance_fields(a: &CoverageAssurance) -> usize {
    let CoverageAssurance {
        bound: _,
        request_digest: _,
    } = a;
    2
}

fn proof_formula_fields(f: &ProofFormula) -> usize {
    let ProofFormula {
        schema: _,
        payload: _,
        smtlib: _,
        sort: _,
        bindings: _,
    } = f;
    5
}

/// Every clause place, exhaustively. Since v59 (WS1.14) the world has two
/// EPOCHS — `WorldPre` (entry) and `WorldPost` (exit) — beside the legacy
/// un-epoched `World`, which is unbindable on a proved summary.
fn clause_place_label(p: &ClausePlace) -> &'static str {
    match p {
        ClausePlace::Param { index: _ } => "param",
        ClausePlace::ResultSlot { index: _ } => "result",
        ClausePlace::MutParamExit { index: _ } => "mut_param_exit",
        ClausePlace::World => "world",
        ClausePlace::WorldPre => "world_pre",
        ClausePlace::WorldPost => "world_post",
        ClausePlace::Unwind => "unwind",
        ClausePlace::Value(_) => "value",
        // v46 (WS4.14): a spec machine's state variable in the CURRENT and
        // the SUCCESSOR state. `SpecVarNext` is the primed value of a
        // transition relation, not a heap epoch on a function contract.
        ClausePlace::SpecVar { index: _ } => "spec_var",
        ClausePlace::SpecVarNext { index: _ } => "spec_var_next",
        // v62 (DG-63): the ENTRY value behind one reference parameter — a
        // parameter-indexed place, not a world epoch.
        ClausePlace::ParamPointeeEntry { index: _ } => "param_pointee_entry",
    }
}

fn kernel_recheck_fields(r: &CleanCicKernelRecheck) -> usize {
    let CleanCicKernelRecheck {
        module: _,
        theorems: _,
        anchor: _,
        allowed_axioms: _,
        binding: _,
    } = r;
    5
}

/// The six fields of a [`CertificateBinding`] (WS1.12a; `environment`, the
/// island, WS1.13), exhaustively.
fn certificate_binding_fields(b: &CertificateBinding) -> usize {
    let CertificateBinding {
        environment_digest: _,
        statement_digest: _,
        origin_module: _,
        source: _,
        callees: _,
        environment: _,
    } = b;
    6
}

/// `Some(n)` for the `CleanCic` payload: exactly {term, context, lineage,
/// kernel_recheck}; the environment digest lives on the directive's binding.
fn clean_cic_fields(e: &ProofEvidence) -> Option<usize> {
    match e {
        ProofEvidence::CleanCic {
            term: _,
            context: _,
            lineage: _,
            kernel_recheck: _,
        } => Some(4),
        _ => None,
    }
}

fn param_attrs_fields(p: &ParamAttrs) -> usize {
    let ParamAttrs {
        dereferenceable: _,
        nonnull: _,
        align: _,
        noalias: _,
        readonly: _,
        byval: _,
        sret: _,
        ext: _,
        pass: _,
    } = p;
    9
}

fn func_ty_fields(t: &FuncTy) -> usize {
    let FuncTy {
        params: _,
        returns: _,
        abi: _,
        is_vararg: _,
    } = t;
    3
}

fn func_attrs_fields(a: &FuncAttrs) -> usize {
    let FuncAttrs {
        readonly: _,
        readnone: _,
        inlinehint: _,
        cold: _,
        params: _,
        naked: _,
        target_features: _,
        ret: _,
    } = a;
    8
}

/// A direct call is exactly {callee, args}: no per-argument pass mode.
fn direct_call_fields(i: &Inst) -> Option<usize> {
    match i {
        Inst::Call { callee: _, args: _ } => Some(2),
        _ => None,
    }
}

fn function_fields(f: &Function) -> usize {
    let Function {
        id: _,
        name: _,
        ty: _,
        entry: _,
        blocks: _,
        proofs: _,
        calling_conv: _,
        linkage: _,
        attrs: _,
        summary: _,
        producer: _,
        value_names: _,
        scopes: _,
        source_provenance: _,
        body_gate: _,
        display_path: _,
        section: _,
        visibility: _,
        retained: _,
    } = f;
    19
}

/// `Global` DOES carry a visibility (the contrast the function row states).
fn global_visibility(g: &Global) -> trust_ir::Visibility {
    let Global { visibility, .. } = g;
    *visibility
}

fn interpret_options_fields(o: &InterpretOptions) -> usize {
    let InterpretOptions {
        fuel: _,
        max_call_depth: _,
        panic_strategy: _,
    } = o;
    3
}

// ---------------------------------------------------------------------------
// Rows
// ---------------------------------------------------------------------------

/// A kernel-certified Postcondition `formula` on `fn f() -> u64 { 7 }`.
fn certified(formula: &str) -> (ProofObligation, ProofCertificate) {
    let obligation = ProofObligation::new(
        ProofId::new(0),
        ObligationKind::Postcondition,
        ProofStatus::Certified,
        "ensures",
    )
    .with_function(trust_ir::FuncId::new(0))
    .with_formula(ProofFormula::smtlib2(formula, "Bool"));
    let certificate =
        contract_clean_cic_certificate(&obligation, "field-ratchets").expect("ground clause mints");
    (obligation, certificate)
}

/// FLIPPED (closed by WS1.14, F-013). `FunctionSummary.effects:
/// Option<EffectSummary>` is the typed frame (v59): the memory a call may
/// read and write, and whether it allocates, frees, unwinds or performs I/O —
/// checked against a DEFINED body. `ClausePlace::WorldPre` / `WorldPost` are
/// the entry and exit epochs of the ambient world. The destructurings stay
/// exhaustive. Positive: `fn set(p, q) { *p = 7 }` with `writes: [*param0]`
/// validates. Negative twin: the ONE change is the store's address
/// (parameter 1), refused as `EffectSummaryViolated { effect: "writes" }`.
fn contract_surface_has_no_effect_or_epoch_slot() {
    let module = |through_second: bool| {
        let ptr = || Ty::PtrMut(Box::new(Ty::U64));
        let mut mb = ModuleBuilder::new("field_ratchets_effects");
        let ft = mb.add_func_type(vec![ptr(), ptr()], vec![]);
        let mut fb = mb.function("set", ft);
        fb.set_producer(Producer::TRust);
        let entry = fb.create_block();
        let p = fb.add_block_param(entry, ptr());
        let q = fb.add_block_param(entry, ptr());
        fb.switch_to_block(entry);
        let seven = fb.uconst(Ty::U64, 7);
        fb.store(Ty::U64, if through_second { q } else { p }, seven);
        fb.ret(vec![]);
        fb.set_summary(FunctionSummary::new().with_effects(
            EffectSummary::pure().writing(EffectSet::of([EffectPlace::ParamPointee { index: 0 }])),
        ));
        fb.build();
        mb.build().expect("ModuleBuilder::build: test fixture")
    };
    let honest = module(false);
    let honest_errors = validate_module(&honest);
    let errors = validate_module(&module(true));
    let refused = matches!(
        errors.as_slice(),
        [ValidationError::EffectSummaryViolated { function, effect: "writes", inst, .. }]
            if function == "set" && inst.contains("*param1")
    );
    let summary = honest.functions[0].summary.as_ref().expect("summary");
    let counts = (
        function_summary_fields(summary),
        effect_summary_fields(summary.effects.as_ref().expect("effects")),
    );
    let (obligation, certificate) = certified("(= 1 1)");
    let places: Vec<&str> = [
        ClausePlace::World,
        ClausePlace::WorldPre,
        ClausePlace::WorldPost,
        ClausePlace::Unwind,
    ]
    .iter()
    .map(clause_place_label)
    .collect();
    let other = [
        proof_obligation_fields(&obligation),
        proof_certificate_fields(&certificate),
        proof_formula_fields(obligation.formula.as_ref().expect("formula")),
    ];
    let _ = (
        obligation_site_fields as fn(&ObligationSite) -> usize,
        coverage_assurance_fields as fn(&CoverageAssurance) -> usize,
    );
    feature_check(
        "b2.gap.no_effect_summary_or_state_epoch_field",
        counts == (7, 6)
            && places == ["world", "world_pre", "world_post", "unwind"]
            && honest_errors.is_empty()
            && refused,
        &format!(
            "closed by WS1.14 (wire v59): FunctionSummary {{requires, ensures, params, proved, \
             decreases, backed_by, effects}} and EffectSummary {{reads, writes, allocates, frees, \
             may_unwind, io}} {counts:?}; ClausePlace world epochs {places:?}; other carriers \
             {other:?}; a writer through *param0 with writes [*param0] validates => \
             {honest_errors:?}, the same store through *param1 => {errors:?}"
        ),
    );
}

/// FLIPPED (closed by WS1.12a, F-007). The directive carries
/// `binding: Option<CertificateBinding>` whose `environment_digest` is the
/// content digest of the kernel environment the certificate was checked in
/// (`trust_ir.clean_cic.environment.v1`), and the validator re-checks a bound
/// certificate only in an environment of equal content. The destructurings
/// stay exhaustive. Positive: a bound contract certificate (the
/// `trust_ir_contract` anchor) validates. Twin: the ONE change is the
/// environment digest, refused by name.
fn clean_cic_recheck_has_no_environment_digest() {
    let (module, index) = {
        let mut mb = ModuleBuilder::new("field_ratchets_binding");
        let ft = mb.add_func_type(vec![], vec![Ty::U64]);
        let mut fb = mb.function("f", ft);
        fb.set_producer(Producer::TRust);
        let entry = fb.create_block();
        fb.switch_to_block(entry);
        let v = fb.uconst(Ty::U64, 7);
        fb.ret(vec![v]);
        fb.build();
        let mut m = mb.build().expect("ModuleBuilder::build: test fixture");
        let (obligation, _) = certified("(= 1 1)");
        m.proof_obligations.push(obligation);
        let bound = contract_clean_cic_certificate_bound_in(&m, &m.proof_obligations[0], "bound")
            .expect("a bound contract certificate mints");
        m.proof_certificates.push(bound);
        (m, 0usize)
    };
    let fields = clean_cic_fields(&module.proof_certificates[index].evidence);
    let recheck = module.proof_certificates[index]
        .evidence
        .clean_cic_kernel_recheck()
        .expect("the bound minter emits a directive");
    let binding = recheck.binding.as_deref().expect("bound");
    let counts = (
        kernel_recheck_fields(recheck),
        certificate_binding_fields(binding),
    );
    let honest_errors = validate_module(&module);
    // Negative twin: flip one bit of the environment digest and re-key the
    // v8 lineage, so the binding rule (not the lineage floor) is measured.
    let mut forged = module.clone();
    let obligation = forged.proof_obligations[0].clone();
    let ProofEvidence::CleanCic {
        lineage,
        kernel_recheck: Some(recheck),
        ..
    } = &mut forged.proof_certificates[index].evidence
    else {
        unreachable!("bound certificate")
    };
    let binding = recheck.binding.as_deref_mut().expect("bound");
    binding.environment_digest.bytes[0] ^= 1;
    *lineage = clean_cic_lineage_digest_v8(
        &obligation,
        &|id| module.function_by_id(id).map(|f| f.name.clone()),
        Some(&*binding),
    )
    .expect("keyable");
    let errors = validate_module(&forged);
    let refused = matches!(
        errors.as_slice(),
        [ValidationError::CertificateBindingMismatch { obligation: 0, field, .. }]
            if field == "environment_digest"
    );
    feature_check(
        "b2.gap.no_kernel_environment_digest_on_clean_cic_recheck",
        fields == Some(4) && honest_errors.is_empty() && refused,
        &format!(
            "closed by WS1.12a: CleanCicKernelRecheck {{module, theorems, anchor, allowed_axioms, \
             binding}} and CertificateBinding {{environment_digest, statement_digest, \
             origin_module, source, callees, environment}} {counts:?}; ProofEvidence::CleanCic {{term, \
             context, lineage, kernel_recheck}}; a bound trust_ir_contract certificate validates \
             => {honest_errors:?}, its environment digest with one bit flipped => {errors:?}"
        ),
    );
}

/// FLIPPED (closed by WS1.3, F-002). The per-clause backref is the
/// validator's FORMULA match, not a new field: a clause of a `proved`
/// definition is backed only by a Discharged/Certified row of its role's kind
/// whose `formula` equals it exactly. The destructurings stay exhaustive (the
/// carriers are unchanged, no wire change) and are reported in the detail.
fn proved_has_no_per_clause_backref() {
    // `fn f() -> u64 { 7 }`, `proved` ensures `clause`; the only backing row
    // is a kernel-Certified Postcondition about `(= 1 1)`.
    let module = |clause: &str| {
        let mut mb = ModuleBuilder::new("field_ratchets_backref");
        let ft = mb.add_func_type(vec![], vec![Ty::U64]);
        let mut fb = mb.function("f", ft);
        fb.set_producer(Producer::TRust);
        let entry = fb.create_block();
        fb.switch_to_block(entry);
        let v = fb.uconst(Ty::U64, 7);
        fb.ret(vec![v]);
        fb.build();
        let mut m = mb.build().expect("ModuleBuilder::build: test fixture");
        m.functions[0].summary = Some(
            FunctionSummary::new()
                .ensuring(ProofFormula::smtlib2(clause, "Bool"))
                .proved(),
        );
        let (obligation, certificate) = certified("(= 1 1)");
        m.proof_obligations.push(obligation);
        m.proof_certificates.push(certificate);
        m
    };
    // Positive: the row states exactly the clause.
    let honest = module("(= 1 1)");
    let honest_errors = validate_module(&honest);
    // Negative twin: the ONE change is the summary clause.
    let forged = module("(= result 42)");
    assert_eq!(honest.proof_obligations, forged.proof_obligations);
    let counts = (
        function_summary_fields(forged.functions[0].summary.as_ref().unwrap()),
        proof_obligation_fields(&forged.proof_obligations[0]),
    );
    let errors = validate_module(&forged);
    let refused = matches!(
        errors.as_slice(),
        [ValidationError::InvalidFunctionSummary { function: 0, detail }]
            if detail == "ensures clause 0 `(= result 42)` has no Discharged/Certified \
                          Postcondition row scoped to this function stating exactly this clause \
                          (rows stating other clauses do not count)"
    );
    feature_check(
        "b2.gap.no_per_clause_obligation_backref",
        honest_errors.is_empty() && refused,
        &format!(
            "closed by WS1.3 (formula match, no new field): FunctionSummary {{requires, ensures, \
             params, proved, decreases, backed_by}} and ProofObligation {{id, kind, status, \
             description, formula, function, source, site}} {counts:?}; a Certified `(= 1 1)` \
             Postcondition backs `proved` ensures `(= 1 1)` => {honest_errors:?}, and does NOT back \
             `proved` ensures `(= result 42)` of `fn f() -> u64 {{ 7 }}`: validate_module => {errors:?}"
        ),
    );
}

fn abi_carriers_have_no_extension_pass_mode_or_function_visibility() {
    // WS3.11 (F-054) flipped these two rows: every slot — parameters AND the
    // return slot — carries an integer extension and a pass mode. PASS: a
    // C-ABI declaration with `ret.ext = ZeroExt` on a `u8` return and a
    // `pass = Pair` `(u64, u64)` struct parameter validates and round-trips.
    // Right-reason negative twins: the same extension on a `U64` slot, and
    // the same `Pair` on a three-lane struct, are refused as
    // InvalidAbiSlotFact.
    use trust_ir::ty::{FieldDef, StructDef, Ty};
    use trust_ir::{ArgExt, ParamAttrs as PA, PassMode};

    let build = |lanes: usize, ext_ty: Ty| {
        let mut mb = ModuleBuilder::new_with_target_info(
            "field_ratchets_abi",
            trust_ir::TargetInfo {
                triple: "aarch64-apple-darwin".into(),
                pointer_size: 8,
                endianness: trust_ir::Endianness::Little,
                abi: Some("aapcs64".into()),
                struct_passing: trust_ir::StructPassingPolicy::NativeC,
            },
        );
        let pair = StructDef {
            id: trust_ir::value::StructId::new(0),
            name: "Pair".into(),
            fields: (0..lanes)
                .map(|i| FieldDef {
                    name: format!("f{i}"),
                    ty: Ty::U64,
                    offset: None,
                })
                .collect(),
            size: None,
            align: None,
            repr: trust_ir::ty::StructRepr::C,
            origin: None,
        };
        let struct_ty = Ty::Struct(pair.id);
        let ft = mb.add_func_type(vec![struct_ty], vec![ext_ty]);
        let mut module = mb.build().expect("ModuleBuilder::build: test fixture");
        module.structs.push(pair);
        let mut decl = trust_ir::Function::new(
            trust_ir::FuncId::new(0),
            "c_abi_decl",
            ft,
            trust_ir::value::BlockId::new(0),
        );
        decl.attrs.params = vec![PA {
            pass: Some(PassMode::Pair),
            ..PA::default()
        }];
        decl.attrs.ret = PA {
            ext: ArgExt::ZeroExt,
            ..PA::default()
        };
        module
            .try_add_function(decl)
            .expect("Module::try_add_function: test fixture");
        module
    };

    let positive = build(2, Ty::U8);
    let n_param = param_attrs_fields(&positive.functions[0].attrs.params[0]);
    let n_attrs = func_attrs_fields(&positive.functions[0].attrs);
    let accepted = validate_module(&positive);
    let trip = common::roundtrip_all(&positive);
    let wide_ext = validate_module(&build(2, Ty::U64));
    let three_lane = validate_module(&build(3, Ty::U8));
    // The text form is the known-lossy transport for struct field names
    // (F-072, its own rows); the three LOSSLESS production transports are
    // what an ABI pin has to survive.
    let _ = (
        func_ty_fields as fn(&FuncTy) -> usize,
        direct_call_fields as fn(&Inst) -> Option<usize>,
    );
    let named = |errors: &[trust_ir_build::ValidationError]| {
        errors.iter().all(|e| {
            matches!(
                e,
                trust_ir_build::ValidationError::InvalidAbiSlotFact { .. }
            )
        }) && !errors.is_empty()
    };
    feature_check(
        "b6.abi.no_zeroext_signext_slot",
        n_param == 9 && accepted.is_empty() && named(&wide_ext),
        &format!(
            "compile-time: ParamAttrs carries ext + pass (9 fields, v45 WS3.11) and FuncAttrs a \
             return slot; `ret.ext = ZeroExt` on a u8 return validates => {accepted:?}; twin on a \
             U64 return => {wide_ext:?}"
        ),
    );
    feature_check(
        "b6.abi.no_pass_mode_slot",
        n_attrs == 8 && trip.lossless_production() && named(&three_lane),
        &format!(
            "compile-time: FuncAttrs {{.., ret}} (8 fields) and ParamAttrs.pass; `pass = Pair` on \
             a (u64, u64) struct parameter round-trips {}; twin on a three-lane struct => \
             {three_lane:?}",
            trip.summary()
        ),
    );

    // WS3.10 (F-053) flipped this row: `Function` now carries `Global`'s
    // symbol triple. PASS: an `(External, Hidden)` function validates and
    // survives every lossless codec; the right-reason negative twin is the same
    // function made `Internal`, refused as ContradictoryFunctionVisibility.
    let build = |linkage: trust_ir::Linkage| {
        let mut mb = ModuleBuilder::new("field_ratchets_visibility");
        let ft = mb.add_func_type(vec![], vec![]);
        let mut fb = mb.function("f", ft);
        let entry = fb.create_block();
        fb.switch_to_block(entry);
        fb.ret(vec![]);
        fb.build();
        let mut m = mb.build().expect("ModuleBuilder::build: test fixture");
        m.functions[0].linkage = linkage;
        m.functions[0].visibility = trust_ir::Visibility::Hidden;
        m
    };
    let hidden = build(trust_ir::Linkage::External);
    let n_function = function_fields(&hidden.functions[0]);
    let _ = global_visibility as fn(&Global) -> trust_ir::Visibility;
    let accepted = validate_module(&hidden);
    let trip = common::roundtrip_all(&hidden);
    let twin = validate_module(&build(trust_ir::Linkage::Internal));
    let twin_refused = matches!(
        twin.as_slice(),
        [trust_ir_build::ValidationError::ContradictoryFunctionVisibility { .. }]
    );
    feature_check(
        "b6.abi.no_function_visibility_slot",
        n_function == 19 && accepted.is_empty() && trip.lossless_all() && twin_refused,
        &format!(
            "compile-time: Function carries section / visibility / retained (19 fields, v45 \
             WS3.10); (External, Hidden) validates => {accepted:?}, round trip {}; twin \
             (Internal, Hidden) => {twin:?}",
            trip.summary()
        ),
    );
}

/// The request lanes of a native verification bundle. A FOURTH arm (a typed
/// request that references a `SpecTemporal` by `(spec_module, temporal_name)`
/// plus the module digest — the DG-56 shape) stops this compiling.
fn request_lane(r: &NativeVerificationRequest) -> &'static str {
    match r {
        NativeVerificationRequest::TrustVc(_) => "TrustVc",
        NativeVerificationRequest::TrustMc(_) => "TrustMc",
        NativeVerificationRequest::TrustWp(_) => "TrustWp",
    }
}

/// F-080's second half (roadmap WS4.16, decision gate DG-56): a temporal
/// obligation routed to ty has NO typed request lane — the bundle's request
/// enum is exactly `{TrustVc, TrustMc, TrustWp}`, so such an obligation stays
/// `Pending` (fail-closed) with no request that could discharge it. The
/// language half of F-080 is closed (schema 8; `b1.bundle.*`); this row is
/// the open remainder, held in its exact shape until DG-56 rules after
/// WS4.14's carrier. Never a second formula language inside the request
/// schema: the recommended lane REFERENCES the spec by name and digest.
fn ty_request_lane_is_absent() {
    let _ = request_lane as fn(&NativeVerificationRequest) -> &'static str;
    let suites: Vec<&str> = [
        NativeVerifierSuite::TrustVc,
        NativeVerifierSuite::TrustMc,
        NativeVerifierSuite::TrustWp,
    ]
    .iter()
    .map(|suite| suite.code())
    .collect();
    feature_gap(
        "f080.ty_request_lane",
        Expect::Accepted,
        Outcome::Accepted.given(&[(
            "the three request lanes are trust_vc / trust_mc / trust_wp",
            suites == ["trust_vc", "trust_mc", "trust_wp"],
        )]),
        &format!(
            "compile-time: NativeVerificationRequest {{TrustVc, TrustMc, TrustWp}} — no variant \
             references a SpecTemporal by (spec_module, temporal_name) + module digest, so a \
             TemporalSafety obligation routed to ty has no typed request and stays Pending; \
             verifier suites {suites:?}"
        ),
    );
}

/// RATIFIED (entry-parameter model, SPEC "Harness inputs", WS2.11): the
/// reference interpreter has NO input oracle by ratification — a harness's
/// nondeterministic inputs are its entry parameters (`execute_func` args), an
/// unbounded stream is a `(ptr, len)` tape parameter, and `Assume` is the
/// vacuity filter (`AssumeViolated`). Held exactly like a gap: an oracle
/// field appearing on `InterpretOptions` trips this row and forces the
/// ratification to be amended first. Amended 2026-10-02 (amendment D, Part
/// 2, `docs/SPEC_RATIFICATIONS.md` §21 rule 2): the third field,
/// `panic_strategy`, names which panic runtime the run models (`Abort` /
/// `Unwind`); it is a fixed, deterministic choice of semantics, not a source
/// of inputs, so the ratification stands.
fn interpreter_has_no_input_oracle() {
    let n = interpret_options_fields(&InterpretOptions::default());
    feature_ratified(
        "b7.nondet.interpreter_has_no_input_oracle",
        Expect::Accepted,
        Outcome::Accepted.given(&[("InterpretOptions has 3 fields", n == 3)]),
        "RATIFIED (entry-parameter model, SPEC \"Harness inputs\"): compile-time: InterpretOptions \
         {fuel, max_call_depth, panic_strategy}: no input oracle (the strategy is a fixed choice \
         of semantics, §21); inputs are entry parameters",
    );
}

#[test]
fn two_language_field_ratchets() {
    common::run_target(
        "field",
        &[
            (
                "contract_surface_has_no_effect_or_epoch_slot",
                contract_surface_has_no_effect_or_epoch_slot,
            ),
            (
                "clean_cic_recheck_has_no_environment_digest",
                clean_cic_recheck_has_no_environment_digest,
            ),
            (
                "proved_has_no_per_clause_backref",
                proved_has_no_per_clause_backref,
            ),
            (
                "abi_carriers_have_no_extension_pass_mode_or_function_visibility",
                abi_carriers_have_no_extension_pass_mode_or_function_visibility,
            ),
            (
                "interpreter_has_no_input_oracle",
                interpreter_has_no_input_oracle,
            ),
            ("ty_request_lane_is_absent", ty_request_lane_is_absent),
        ],
    );
}
