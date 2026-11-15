//! b2 — contracts, obligations, certificates (Part B of the two-language
//! proof program).
//!
//! Ported (roadmap WS8.6) from the archived Part B battery
//! `reports/2026-09-17-two-language-proof-program/partb/tests/b2_contracts_obligations.rs`, measured there
//! at trust-ir 4efb21bc and re-measured at the port. Every row is checked against
//! `RATCHETS.tsv` (see `harness.rs`). `file:line` citations are relative to
//! `crates/` and date from 4efb21bc: re-locate them by name.
//! The only proof-checking tool that runs here is the in-process Clean kernel
//! trust-ir-build links (feature `clean-tv-anchor`).
//!
//! Source citations: TI = trust-ir/src, TB = trust-ir-build/src.
//!
//! STATUS <-> AUTHORITY, the rule that shapes every fixture below
//! (TB/validate.rs:12343-12388): `validate_module` supplies
//! `RejectingModuleProofAuthority`, so EVERY `Discharged` row is
//! `DischargedWithoutCertificate` under it, whatever evidence bytes it holds.
//! A module holding all five statuses therefore validates only through
//! `validate_module_with_authority` with a consumer capability. `ReplayStandIn`
//! below is a TEST STAND-IN for such a consumer (ay / lean / kani replay): it
//! proves nothing, it only occupies the capability slot so the FORMAT can be
//! measured. The kernel tier (`Certified` + `CleanCic`) needs no stand-in — the
//! Clean kernel really re-checks those rows in this process.

// The coverage rows below still measure the DEPRECATED legacy rule
// (`coverage_assurance_report`); they move to `coverage_establishment_report`
// when the legacy rule is deleted.
#![allow(deprecated)]

mod common;

use std::collections::BTreeSet;

use common::{
    Expect, Outcome, feature_check, feature_gap, feature_ratified, roundtrip_all, run_nullary,
};
use trust_ir::clean_expr_lowering::contract::{
    contract_clean_cic_certificate, contract_clean_cic_certificate_in,
};
use trust_ir::inst::{BinOp, CastOp, ICmpOp, Inst};
use trust_ir::proof::{
    ClauseBinding, ClausePlace, ClauseSort, CoverageAssurance, CoverageBound, ModuleProofAuthority,
    ObligationKind, ObligationSite, ProofCertificate, ProofCertificateRef, ProofDigest,
    ProofEvidence, ProofFormula, ProofLineageManifest, ProofObligation, ProofStatus,
    clean_cic_lineage_digest,
};
use trust_ir::request::{
    NativeAdapterInput, NativeBundleProducer, NativeRequestId, NativeVerificationBundle,
    NativeVerificationRequest, TrustMcBmcOptions, TrustMcNativeRequest, TrustMcRequestOptions,
    TrustMcVerificationMode, TrustWpNativeRequest, TrustWpVerificationMode,
};
use trust_ir::ty::{FuncTy, Ty};
use trust_ir::value::{BlockId, FuncId, ImportId, ProofId, ValueId};
use trust_ir::{
    BodyGate, Endianness, ExternRef, Function, FunctionSummary, Module, ModuleImport, Producer,
    TargetInfo,
};
use trust_ir_build::validate::coverage_assurance_report;
use trust_ir_build::{
    CodegenAdmission, ModuleBuilder, ValidationError, mint_summary_obligations, validate_module,
    validate_module_for_codegen_with, validate_module_with_authority,
    validate_module_with_bundle_with_authority,
};

// ===========================================================================
// helpers
// ===========================================================================

fn bind(name: &str, sort: ClauseSort, place: ClausePlace) -> (String, ClauseBinding) {
    (name.to_string(), ClauseBinding { sort, place })
}

fn clause(text: &str, sort: &str, bindings: Vec<(String, ClauseBinding)>) -> ProofFormula {
    let mut formula = ProofFormula::smtlib2(text, sort);
    formula.bindings = bindings;
    formula
}

const BV64: ClauseSort = ClauseSort::BitVec(64);

/// The Clean bodies' codegen license. NOT `clean-kernel-tv`: since WS1.5 that
/// authority is bound to a kernel-rechecked `clean_backend_tv` certificate per
/// body, and this module's only TranslationValidation row (#9) is a
/// capability-backed `Discharged` row, which is never license evidence. The
/// direct-lane authority is the evidence-free Clean license a consumer admits
/// only by recognizing it.
const CLEAN_AUTHORITY: &str = "trust-direct-lane-structural";

/// TEST STAND-IN for a consumer-side replay capability (see the file header).
/// Admits exactly the listed certificates, by lineage reference.
struct ReplayStandIn(BTreeSet<ProofCertificateRef>);

impl ModuleProofAuthority for ReplayStandIn {
    fn replays_authority(
        &self,
        _module: &Module,
        obligation: &ProofObligation,
        certificate: &ProofCertificate,
    ) -> bool {
        certificate.obligation == obligation.id && self.0.contains(&certificate.lineage_ref())
    }
}

/// The stand-in for `module`: every NON-kernel certificate it carries.
fn stand_in(module: &Module) -> ReplayStandIn {
    ReplayStandIn(
        module
            .proof_certificates
            .iter()
            .filter(|c| !matches!(c.evidence, ProofEvidence::CleanCic { .. }))
            .map(ProofCertificate::lineage_ref)
            .collect(),
    )
}

/// Errors under the authority tier with the stand-in capability.
fn errors_with_stand_in(module: &Module) -> Vec<ValidationError> {
    validate_module_with_authority(module, &stand_in(module))
}

/// Errors under the authority tier with an explicit capability.
fn errors_with_stand_in_of(module: &Module, capability: &ReplayStandIn) -> Vec<ValidationError> {
    validate_module_with_authority(module, capability)
}

fn summary_details(errors: &[ValidationError]) -> Vec<String> {
    errors
        .iter()
        .filter_map(|e| match e {
            ValidationError::InvalidFunctionSummary { detail, .. } => Some(detail.clone()),
            _ => None,
        })
        .collect()
}

fn summary_refusal(errors: &[ValidationError], function: FuncId, needle: &str) -> bool {
    errors.iter().any(|e| {
        matches!(e, ValidationError::InvalidFunctionSummary { function: f, detail }
            if *f == function.index() && detail.contains(needle))
    })
}

/// EXACTLY `count` errors, every one an `InvalidFunctionSummary` on `function`,
/// and at least one carrying `needle` — the "mutate one thing, get one named
/// refusal" form of a summary twin.
fn summary_refusal_exact(
    errors: &[ValidationError],
    function: FuncId,
    needle: &str,
    count: usize,
) -> bool {
    errors.len() == count
        && errors.iter().all(|e| {
            matches!(e, ValidationError::InvalidFunctionSummary { function: f, .. } if *f == function.index())
        })
        && summary_refusal(errors, function, needle)
}

/// A summary clause and the module obligation that restates it, mutated in
/// step (roadmap WS4.4): EXACTLY two errors — the summary's
/// `InvalidFunctionSummary` naming `summary_needle` on `function`, and the
/// obligation half of the same binding rule, `InvalidObligationBinding` on
/// `obligation` naming `obligation_needle`. Anything else fails the twin.
fn summary_and_obligation_refusal_exact(
    errors: &[ValidationError],
    function: FuncId,
    summary_needle: &str,
    obligation: u32,
    obligation_needle: &str,
) -> bool {
    let (summary_rows, obligation_rows): (Vec<ValidationError>, Vec<ValidationError>) = errors
        .iter()
        .cloned()
        .partition(|e| matches!(e, ValidationError::InvalidFunctionSummary { .. }));
    summary_refusal_exact(&summary_rows, function, summary_needle, 1)
        && matches!(
            obligation_rows.as_slice(),
            [ValidationError::InvalidObligationBinding { obligation: o, detail }]
                if *o == obligation && detail.contains(obligation_needle)
        )
}

/// WS1.3's per-clause refusal: `clause` (e.g. "ensures clause 1") of
/// `function` is stated by no Discharged/Certified row of its role's kind.
fn clause_unbacked(errors: &[ValidationError], function: FuncId, clause: &str) -> bool {
    errors.iter().any(|e| {
        matches!(e, ValidationError::InvalidFunctionSummary { function: f, detail }
            if *f == function.index()
                && detail.starts_with(&format!("{clause} `"))
                && detail.contains("row scoped to this function stating exactly this clause"))
    })
}

/// A twin that breaks the ONE `Certified` row (#6) of the b2 module. The kernel
/// tier is ALL-OR-NOTHING (TB/validate.rs:12311-12321: any `Certified` recheck
/// error empties BOTH authority sets, so "one malformed certificate cannot hide
/// behind a valid one"). The exact expected error set is therefore:
///   * exactly one error matching `specific` (the named refusal under test),
///   * `DischargedWithoutCertificate` for exactly the module's Discharged rows
///     (the capability set was emptied), and
///   * `InheritedProofNotDischarged{11 <- 6}` (the inheritance lost its ground).
///
/// Anything else in the list fails the twin.
fn kernel_tier_collapse_exact(
    module: &Module,
    errors: &[ValidationError],
    specific: impl Fn(&ValidationError) -> bool,
) -> bool {
    let discharged: BTreeSet<u32> = module
        .proof_obligations
        .iter()
        .filter(|o| o.status == ProofStatus::Discharged)
        .map(|o| o.id.index())
        .collect();
    let mut hits = 0usize;
    let mut cascade = BTreeSet::new();
    let mut inheritance = 0usize;
    for e in errors {
        if specific(e) {
            hits += 1;
        } else if let ValidationError::DischargedWithoutCertificate { obligation } = e {
            cascade.insert(*obligation);
        } else if matches!(
            e,
            ValidationError::InheritedProofNotDischarged {
                obligation: 11,
                inherited_obligation: 6,
                ..
            }
        ) {
            inheritance += 1;
        } else {
            return false;
        }
    }
    hits == 1 && cascade == discharged && inheritance == 1 && errors.len() == 2 + discharged.len()
}

/// `(block, inst_index)` of the first instruction of `func` matching `pred`.
fn site_where(module: &Module, func: FuncId, pred: impl Fn(&Inst) -> bool) -> ObligationSite {
    let function = module.function_by_id(func).expect("function exists");
    for block in &function.blocks {
        for (index, node) in block.body.iter().enumerate() {
            if pred(&node.inst) {
                return ObligationSite::new(func, block.id, index as u32);
            }
        }
    }
    panic!("no matching instruction in @{}", function.name);
}

// ===========================================================================
// THE MODULE the design's end state requires for this area
// ===========================================================================

struct Main {
    module: Module,
    countdown: FuncId,
    bump: FuncId,
    is_zero: FuncId,
    program: FuncId,
    /// Native requests the assurance rows were projected from.
    requests: Vec<NativeVerificationRequest>,
}

fn wp_request(id: u32, function: FuncId, obligations: &[u32]) -> NativeVerificationRequest {
    NativeVerificationRequest::TrustWp(TrustWpNativeRequest {
        id: NativeRequestId::new(id),
        mode: TrustWpVerificationMode::WeakestPrecondition,
        function,
        obligations: obligations.iter().map(|o| ProofId::new(*o)).collect(),
        lineage_roots: Vec::new(),
        options: Default::default(),
        diagnostics: Default::default(),
        provenance: Default::default(),
    })
}

fn bmc_request(
    id: u32,
    function: FuncId,
    obligations: &[u32],
    unwind_limit: u32,
) -> NativeVerificationRequest {
    NativeVerificationRequest::TrustMc(TrustMcNativeRequest {
        id: NativeRequestId::new(id),
        mode: TrustMcVerificationMode::BoundedModelCheck,
        function,
        obligations: obligations.iter().map(|o| ProofId::new(*o)).collect(),
        lineage_roots: Vec::new(),
        options: TrustMcRequestOptions {
            bmc: TrustMcBmcOptions {
                unwind_limit,
                unwinding_assertions: true,
            },
            ..TrustMcRequestOptions::default()
        },
        diagnostics: Default::default(),
        provenance: Default::default(),
    })
}

/// ```text
/// [Clean] b2_countdown(n: u64) -> u64     = if n == 0 { 0 } else { countdown(n - 1) }
///         ensures  (= result #x0..0)          [Discharged, LeanProof]
///         ensures  (>= result 0)              [CERTIFIED, Clean kernel re-check]
///         decreases n                         [Discharged Termination, site = the recursive call]
/// [TRust] b2_bump_into(x: u64, out: *mut u64) -> u64 = { let r = x + 1; *out = r; r }
///         requires (bvult x #xff..ff)
///         ensures  (= result (bvadd x 1))     bindings: Param, ResultSlot, Value
///         ensures  (and (= out_exit result) (not unwinding) ..)  MutParamExit, World, Unwind
/// [Clean] b2_is_zero(x: u64) -> bool      = x == 0   (contract published, NOT proved)
/// [TRust] program() -> u64                = bump_into(41, &mut s) + s + countdown(3)   == 84
/// ```
fn build_main() -> Main {
    let mut mb = ModuleBuilder::new("b2_contracts_obligations");
    let u64_to_u64 = mb.add_func_type(vec![Ty::U64], vec![Ty::U64]);
    let bump_ty = mb.add_func_type(vec![Ty::U64, Ty::PtrMut(Box::new(Ty::U64))], vec![Ty::U64]);
    let u64_to_bool = mb.add_func_type(vec![Ty::U64], vec![Ty::Bool]);
    let nullary = mb.add_func_type(vec![], vec![Ty::U64]);

    // --- [Clean] b2_countdown ------------------------------------------------
    let countdown = {
        let this = mb
            .peek_next_func_id()
            .expect("peek_next_func_id: test fixture");
        let mut fb = mb.function("b2_countdown", u64_to_u64);
        fb.set_producer(Producer::Clean);
        fb.set_display_path("B2.countdown");
        fb.set_body_gate(BodyGate::Gated {
            authority: CLEAN_AUTHORITY.into(),
            evidence: None,
        });
        let entry = fb.create_block();
        let rec = fb.create_block();
        let done = fb.create_block();
        let n = fb.add_block_param(entry, Ty::U64);
        let out = fb.add_block_param(done, Ty::U64);
        fb.switch_to_block(entry);
        let zero = fb.uconst(Ty::U64, 0);
        let is0 = fb.icmp(ICmpOp::Eq, Ty::U64, n, zero);
        fb.condbr(is0, done, vec![zero], rec, vec![]);
        fb.switch_to_block(rec);
        let one = fb.uconst(Ty::U64, 1);
        let m = fb.sub(Ty::U64, n, one);
        let r = fb.call(this, vec![m]);
        fb.br(done, vec![r]);
        fb.switch_to_block(done);
        fb.ret(vec![out]);
        fb.build()
    };

    // --- [TRust] b2_bump_into ------------------------------------------------
    let (bump, bump_sum) = {
        let mut fb = mb.function("b2_bump_into", bump_ty);
        fb.set_producer(Producer::TRust);
        fb.set_display_path("b2::bump_into");
        fb.set_body_gate(BodyGate::Gated {
            authority: "trust-verify".into(),
            evidence: None,
        });
        let entry = fb.create_block();
        let x = fb.add_block_param(entry, Ty::U64);
        let out = fb.add_block_param(entry, Ty::PtrMut(Box::new(Ty::U64)));
        fb.switch_to_block(entry);
        let one = fb.uconst(Ty::U64, 1);
        let r = fb.add(Ty::U64, x, one);
        fb.store(Ty::U64, out, r);
        fb.ret(vec![r]);
        (fb.build(), r)
    };

    // --- [Clean] b2_is_zero --------------------------------------------------
    let is_zero = {
        let mut fb = mb.function("b2_is_zero", u64_to_bool);
        fb.set_producer(Producer::Clean);
        fb.set_display_path("B2.isZero");
        fb.set_body_gate(BodyGate::Gated {
            authority: CLEAN_AUTHORITY.into(),
            evidence: None,
        });
        let entry = fb.create_block();
        let x = fb.add_block_param(entry, Ty::U64);
        fb.switch_to_block(entry);
        let zero = fb.uconst(Ty::U64, 0);
        let b = fb.icmp(ICmpOp::Eq, Ty::U64, x, zero);
        fb.ret(vec![b]);
        fb.build()
    };

    // --- [TRust] program -----------------------------------------------------
    let program = {
        let mut fb = mb.function("program", nullary);
        fb.set_producer(Producer::TRust);
        fb.set_display_path("b2::program");
        fb.set_body_gate(BodyGate::Gated {
            authority: "trust-verify".into(),
            evidence: None,
        });
        let entry = fb.create_block();
        fb.switch_to_block(entry);
        let slot = fb.alloca(Ty::U64);
        let zero = fb.uconst(Ty::U64, 0);
        fb.store(Ty::U64, slot, zero);
        let forty_one = fb.uconst(Ty::U64, 41);
        // `&mut s`: the untyped alloca pointer, retyped to the `*mut u64`
        // the callee's MutParamExit binding needs (WS1.2 types that place).
        let out = fb.cast(
            CastOp::PtrToPtr,
            Ty::Ptr,
            Ty::PtrMut(Box::new(Ty::U64)),
            slot,
        );
        let r = fb.call(bump, vec![forty_one, out]);
        let v = fb.load(Ty::U64, slot);
        let three = fb.uconst(Ty::U64, 3);
        let c = fb.call(countdown, vec![three]);
        let s = fb.add(Ty::U64, r, v);
        let s = fb.add(Ty::U64, s, c);
        fb.ret(vec![s]);
        fb.build()
    };

    let mut module = mb.build().expect("ModuleBuilder::build: test fixture");

    // --- summaries -----------------------------------------------------------
    let countdown_ens_zero = clause(
        "(= result #x0000000000000000)",
        "Bool",
        vec![bind("result", BV64, ClausePlace::ResultSlot { index: 0 })],
    );
    // The Clean-kernel-groundable clause: over `Int`, true of every u64.
    let countdown_ens_nonneg = clause(
        "(>= result 0)",
        "Bool",
        vec![bind(
            "result",
            ClauseSort::Int,
            ClausePlace::ResultSlot { index: 0 },
        )],
    );
    let countdown_measure = clause(
        "n",
        "Int",
        vec![bind("n", ClauseSort::Int, ClausePlace::Param { index: 0 })],
    );
    let mut countdown_summary = FunctionSummary::new()
        .with_params(vec!["n".to_string()])
        .ensuring(countdown_ens_zero.clone())
        .ensuring(countdown_ens_nonneg.clone())
        .proved();
    countdown_summary.decreases.push(countdown_measure.clone());
    module.function_by_id_mut(countdown).unwrap().summary = Some(countdown_summary);

    let bump_req = clause(
        "(bvult x #xffffffffffffffff)",
        "Bool",
        vec![bind("x", BV64, ClausePlace::Param { index: 0 })],
    );
    let bump_ens_value = clause(
        "(and (= result (bvadd x #x0000000000000001)) (= sum result))",
        "Bool",
        vec![
            bind("x", BV64, ClausePlace::Param { index: 0 }),
            bind("result", BV64, ClausePlace::ResultSlot { index: 0 }),
            bind("sum", BV64, ClausePlace::Value(bump_sum)),
        ],
    );
    let bump_ens_effect = clause(
        "(and (= out_exit result) (not unwinding) (= (select heap #x0000000000000000) #x00))",
        "Bool",
        vec![
            bind("out_exit", BV64, ClausePlace::MutParamExit { index: 1 }),
            bind("result", BV64, ClausePlace::ResultSlot { index: 0 }),
            bind("unwinding", ClauseSort::Bool, ClausePlace::Unwind),
            // v59 (WS1.14): the heap AFTER the call is the exit epoch; the
            // legacy un-epoched `World` is unbindable on this proved summary.
            bind(
                "heap",
                ClauseSort::Array(Box::new(BV64), Box::new(ClauseSort::BitVec(8))),
                ClausePlace::WorldPost,
            ),
        ],
    );
    module.function_by_id_mut(bump).unwrap().summary = Some(
        FunctionSummary::new()
            .with_params(vec!["x".to_string(), "out".to_string()])
            .requiring(bump_req.clone())
            .ensuring(bump_ens_value.clone())
            .ensuring(bump_ens_effect.clone())
            .proved(),
    );

    let is_zero_ens = clause(
        "(= result (= x #x0000000000000000))",
        "Bool",
        vec![
            bind("x", BV64, ClausePlace::Param { index: 0 }),
            bind(
                "result",
                ClauseSort::Bool,
                ClausePlace::ResultSlot { index: 0 },
            ),
        ],
    );
    // Published, NOT proved: the honest "Pending" reading of a contract.
    module.function_by_id_mut(is_zero).unwrap().summary = Some(
        FunctionSummary::new()
            .with_params(vec!["x".to_string()])
            .ensuring(is_zero_ens.clone()),
    );

    // --- sites ---------------------------------------------------------------
    let at_rec_call = site_where(&module, countdown, |i| matches!(i, Inst::Call { .. }));
    let at_countdown_ret = site_where(&module, countdown, |i| matches!(i, Inst::Return { .. }));
    let at_countdown_branch = site_where(&module, countdown, |i| matches!(i, Inst::CondBr { .. }));
    let at_bump_add = site_where(&module, bump, |i| {
        matches!(i, Inst::BinOp { op: BinOp::Add, .. })
    });
    let at_bump_store = site_where(&module, bump, |i| matches!(i, Inst::Store { .. }));
    let at_bump_ret = site_where(&module, bump, |i| matches!(i, Inst::Return { .. }));
    let at_bump_entry = ObligationSite::new(bump, BlockId::new(0), 0);
    let at_is_zero_ret = site_where(&module, is_zero, |i| matches!(i, Inst::Return { .. }));
    let at_is_zero_cmp = site_where(&module, is_zero, |i| matches!(i, Inst::ICmp { .. }));
    let at_program_bump_call = site_where(
        &module,
        program,
        |i| matches!(i, Inst::Call { callee, .. } if *callee == bump),
    );
    let at_program_load = site_where(&module, program, |i| matches!(i, Inst::Load { .. }));
    let at_program_add = site_where(&module, program, |i| {
        matches!(i, Inst::BinOp { op: BinOp::Add, .. })
    });
    let at_program_ret = site_where(&module, program, |i| matches!(i, Inst::Return { .. }));

    // --- obligations: all 16 kinds x all 5 statuses ---------------------------
    use ObligationKind as K;
    use ProofStatus as S;
    let ob = |id: u32,
              kind: K,
              status: S,
              desc: &str,
              function: FuncId,
              site: ObligationSite,
              formula: Option<&ProofFormula>| {
        let mut o = ProofObligation::new(ProofId::new(id), kind, status, desc)
            .with_function(function)
            .with_site(site);
        if let Some(f) = formula {
            o = o.with_formula(f.clone());
        }
        o
    };
    let obligations = vec![
        ob(
            0,
            K::Precondition,
            S::Discharged,
            "requires clause 0 of 'b2_bump_into'",
            bump,
            at_bump_entry,
            Some(&bump_req),
        ),
        ob(
            1,
            K::Postcondition,
            S::Discharged,
            "ensures clause 0 of 'b2_bump_into'",
            bump,
            at_bump_ret,
            Some(&bump_ens_value),
        ),
        ob(
            2,
            K::Postcondition,
            S::Discharged,
            "ensures clause 1 of 'b2_bump_into'",
            bump,
            at_bump_ret,
            Some(&bump_ens_effect),
        ),
        ob(
            3,
            K::Postcondition,
            S::Discharged,
            "ensures clause 0 of 'b2_countdown' (theorem B2.countdown_eq_zero)",
            countdown,
            at_countdown_ret,
            Some(&countdown_ens_zero),
        ),
        ob(
            4,
            K::Termination,
            S::Discharged,
            "decreases clause 0 of 'b2_countdown': n strictly descends at the recursive call",
            countdown,
            at_rec_call,
            Some(&countdown_measure),
        ),
        ob(
            5,
            K::Postcondition,
            S::Pending,
            "ensures clause 0 of 'b2_is_zero'",
            is_zero,
            at_is_zero_ret,
            Some(&is_zero_ens),
        ),
        ob(
            6,
            K::Postcondition,
            S::Certified,
            "ensures clause 1 of 'b2_countdown'",
            countdown,
            at_countdown_ret,
            Some(&countdown_ens_nonneg),
        ),
        ob(
            7,
            K::LoopInvariant,
            S::Trusted,
            "recursion invariant, manual audit",
            countdown,
            at_countdown_branch,
            None,
        ),
        ob(
            8,
            K::TypeInvariant,
            S::Pending,
            "out points at an initialised u64",
            bump,
            at_bump_store,
            None,
        ),
        ob(
            9,
            K::TranslationValidation,
            S::Discharged,
            "Lean `B2.isZero` == lowered body",
            is_zero,
            at_is_zero_cmp,
            None,
        ),
        ob(
            10,
            K::MemorySafety,
            S::Discharged,
            "store through `out` is in bounds of a live allocation",
            bump,
            at_bump_store,
            None,
        ),
        ob(
            11,
            K::Postcondition,
            S::Discharged,
            "program relies on ensures clause 1 of 'b2_countdown'",
            // WS1.6 (c3819f64): a same-module restatement is scoped to the
            // CALLEE, exactly like a cross-crate one to its declaration.
            countdown,
            at_countdown_ret,
            Some(&countdown_ens_nonneg),
        ),
        ob(
            12,
            K::TemporalSafety,
            S::Pending,
            "slot is written before it is read",
            program,
            at_program_load,
            None,
        ),
        ob(
            13,
            K::Liveness,
            S::Failed,
            "program eventually returns 85 (refuted: it returns 84)",
            program,
            at_program_ret,
            None,
        ),
        ob(
            14,
            K::ArithmeticSafety,
            S::Discharged,
            "x + 1 does not overflow under requires clause 0",
            bump,
            at_bump_add,
            None,
        ),
        ob(
            15,
            K::BoundsCheck,
            S::Pending,
            "slot load is index-in-bounds",
            program,
            at_program_load,
            None,
        ),
        ob(
            16,
            K::GiveBackRefinement,
            S::Pending,
            "give-back view of `out` (emitted Pending by the untrusted elaborator)",
            bump,
            at_bump_store,
            None,
        ),
        ob(
            17,
            K::Ownership,
            S::Discharged,
            "`out` is uniquely borrowed for the call",
            program,
            at_program_bump_call,
            None,
        ),
        ob(
            18,
            K::Custom {
                namespace: "trust.vc".into(),
                name: "nn_output_bound".into(),
            },
            S::Discharged,
            "sum stays inside the verified output box",
            program,
            at_program_add,
            None,
        ),
        ob(
            19,
            K::PanicFreedom,
            S::Discharged,
            "program never panics",
            program,
            at_program_ret,
            None,
        ),
        ob(
            20,
            K::RefinementType,
            S::Pending,
            "{ r: bool | r <-> x = 0 }",
            is_zero,
            at_is_zero_ret,
            None,
        ),
    ];
    module.proof_obligations = obligations;

    // --- requests the assurance rows project from ------------------------------
    let requests = vec![
        wp_request(0, bump, &[0]),
        bmc_request(1, bump, &[1], 1),
        wp_request(2, bump, &[2]),
        wp_request(3, countdown, &[3]),
    ];
    let assurance = |bound: CoverageBound, request: &NativeVerificationRequest| {
        Some(CoverageAssurance {
            bound,
            request_digest: request.stable_digest(),
        })
    };
    let cert = |obligation: u32,
                prover: &str,
                evidence: ProofEvidence,
                assurance: Option<CoverageAssurance>| ProofCertificate {
        obligation: ProofId::new(obligation),
        prover: prover.to_string(),
        evidence,
        assurance,
    };

    // The ONE row whose proof is really checked in this process.
    // Module-bound mint (WS1.1, 0aeae341): `result` must bind to an unsigned
    // IR place read at sort Int before the nonneg tautology grounds.
    let kernel =
        contract_clean_cic_certificate_in(&module, &module.proof_obligations[6], "clean-kernel")
            .expect("(>= result 0) is kernel-provable as a Nat tautology");

    module.proof_certificates = vec![
        cert(0, "ay", ProofEvidence::SmtProof(b"(proof unsat #0)".to_vec()), assurance(CoverageBound::Unbounded, &requests[0])),
        cert(1, "trust-mc", ProofEvidence::SmtProof(b"(proof unsat #1)".to_vec()), assurance(CoverageBound::UnwindBounded { depth: 1 }, &requests[1])),
        cert(2, "kani", ProofEvidence::KaniHarness("b2::bump_into::effect_harness".into()), assurance(CoverageBound::ModelBounded { size: 4 }, &requests[2])),
        cert(3, "lean4", ProofEvidence::LeanProof("theorem B2.countdown_eq_zero : forall n, countdown n = 0 := by intro n; induction n <;> simp_all [countdown]".into()), assurance(CoverageBound::Unrecorded, &requests[3])),
        cert(4, "ay", ProofEvidence::SmtProof(b"(proof unsat #4)".to_vec()), None),
        kernel,
        cert(7, "auditor", ProofEvidence::Trusted("reviewed 2026-09-17".into()), None),
        cert(9, "trust-tv", ProofEvidence::TranslationValidation { rule_name: "clean.icmp_eq_u64".into(), smt_hash: [0xB2; 32] }, None),
        cert(10, "ay", ProofEvidence::SmtProof(b"(proof unsat #10)".to_vec()), None),
        cert(11, "compose", ProofEvidence::InheritedFromCallee { callee: countdown, obligation: ProofId::new(6), external: None }, None),
        cert(14, "ay", ProofEvidence::SmtProof(b"(proof unsat #14)".to_vec()), None),
        cert(17, "ay", ProofEvidence::SmtProof(b"(proof unsat #17)".to_vec()), None),
        cert(18, "gamma-crown", ProofEvidence::GammaCrownBound { epsilon: 0.125, verified_layers: 3 }, None),
        cert(19, "kani", ProofEvidence::KaniHarness("b2::program::no_panic".into()), None),
    ];

    Main {
        module,
        countdown,
        bump,
        is_zero,
        program,
        requests,
    }
}

fn target() -> TargetInfo {
    TargetInfo {
        triple: "aarch64-apple-darwin".into(),
        pointer_size: 8,
        endianness: Endianness::Little,
        abi: None,
        struct_passing: Default::default(),
    }
}

/// A body-less, contract-only declaration of a function PROVED IN ANOTHER
/// CRATE: `fn far_scale(x: f64, n: u64) -> u64`, `proved`, `backed_by` an
/// obligation of a declared import. Also the carrier for the remaining
/// `ClauseSort`s (Float / RoundingMode / Datatype).
fn build_backed_declaration(backed: Option<ExternRef>) -> Module {
    let mut m = Module::new("b2_backed_declaration");
    m.target_info = Some(target());
    m.intern_import(
        ModuleImport::new("b2_upstream", ProofDigest::sha256([0x5A; 32]))
            .with_producer(Producer::Clean)
            // The archived measurement is a v41 row (legacy V2 identity); a
            // V3 row would raise the module to v44 (WS4.10).
            .with_scheme(trust_ir::IdentityScheme::V2),
    )
    .expect("Module::intern_import: test fixture");
    let ft = m
        .add_func_type(FuncTy {
            params: vec![Ty::F64, Ty::U64],
            returns: vec![Ty::U64],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let option_u64 = ClauseSort::Datatype {
        name: "Option".into(),
        constructors: vec![
            ("none".into(), vec![]),
            ("some".into(), vec![("val".into(), BV64)]),
        ],
    };
    let mut summary = FunctionSummary::new()
        .with_params(vec!["x".to_string(), "n".to_string()])
        .requiring(clause(
            "(not (fp.isNaN x))",
            "Bool",
            vec![bind(
                "x",
                ClauseSort::Float { eb: 11, sb: 53 },
                ClausePlace::Param { index: 0 },
            )],
        ))
        .ensuring(clause(
            "(= (some result) (scale rm x n))",
            "Bool",
            vec![
                bind(
                    "x",
                    ClauseSort::Float { eb: 11, sb: 53 },
                    ClausePlace::Param { index: 0 },
                ),
                bind("n", BV64, ClausePlace::Param { index: 1 }),
                bind("result", BV64, ClausePlace::ResultSlot { index: 0 }),
                // v59 (WS1.14): ambient state at the CALL, the entry epoch;
                // the legacy un-epoched `World` is unbindable on a proved
                // summary.
                bind("rm", ClauseSort::RoundingMode, ClausePlace::WorldPre),
                bind("opt", option_u64, ClausePlace::WorldPre),
            ],
        ))
        .proved();
    summary.backed_by = backed;
    let mut f = Function::declaration(FuncId::new(0), "far_scale", ft, summary);
    f.producer = Some(Producer::Clean);
    m.try_add_function(f)
        .expect("Module::try_add_function: test fixture");
    m
}

fn good_backing() -> ExternRef {
    ExternRef::new(ImportId::new(0), "far_scale").relying_on(ProofId::new(3))
}

/// `fn b2_level() -> <ty> { <value> }`, `proved`, ensures `(>= result 0)`
/// with `result` bound at `sort` to ResultSlot 0 (or NOT bound at all),
/// Postcondition `Certified` by a kernel certificate: minted through the
/// module-bound entry point when the binding rule admits the clause, and
/// otherwise FORGED -- the honest nonneg proof term under this obligation's
/// own lineage, which anyone can assemble without the minter (since WS1.1,
/// 0aeae341, the minter refuses a clause that does not bind to a Nat-valued
/// IR place, so the forgery is what the validator must refuse).
fn build_level(signed: bool, binding: Option<ClauseSort>) -> Module {
    let ty = if signed { Ty::I64 } else { Ty::U64 };
    let mut mb = ModuleBuilder::new("b2_level");
    let ft = mb.add_func_type(vec![], vec![ty.clone()]);
    let mut fb = mb.function("b2_level", ft);
    fb.set_producer(Producer::TRust);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    let v = if signed {
        fb.iconst(ty, -1)
    } else {
        fb.uconst(ty, 7)
    };
    fb.ret(vec![v]);
    let f = fb.build();
    let mut m = mb.build().expect("ModuleBuilder::build: test fixture");
    let ensures = clause(
        "(>= result 0)",
        "Bool",
        binding
            .map(|sort| vec![bind("result", sort, ClausePlace::ResultSlot { index: 0 })])
            .unwrap_or_default(),
    );
    m.functions[0].summary = Some(FunctionSummary::new().ensuring(ensures.clone()).proved());
    let obligation = ProofObligation::new(
        ProofId::new(0),
        ObligationKind::Postcondition,
        ProofStatus::Certified,
        "ensures clause 0 of 'b2_level'",
    )
    .with_function(f)
    .with_formula(ensures);
    let cert = contract_clean_cic_certificate_in(&m, &obligation, "clean-kernel")
        .unwrap_or_else(|| forged_nonneg_certificate(&obligation));
    m.proof_obligations.push(obligation);
    m.proof_certificates.push(cert);
    m
}

/// A `CleanCic` certificate for `obligation` carrying the honest nonneg proof
/// term (`fun x : Nat => @Eq.refl Bool Bool.true`, taken from an honest mint
/// over the u64 baseline) under `obligation`'s own lineage.
fn forged_nonneg_certificate(obligation: &ProofObligation) -> ProofCertificate {
    let honest = build_level(false, Some(ClauseSort::Int));
    let ProofEvidence::CleanCic { term, .. } = &honest.proof_certificates[0].evidence else {
        panic!("the honest mint is CleanCic");
    };
    ProofCertificate {
        obligation: obligation.id,
        prover: "clean-kernel".to_string(),
        evidence: ProofEvidence::CleanCic {
            term: term.clone(),
            context: Vec::new(),
            lineage: clean_cic_lineage_digest(obligation),
            kernel_recheck: None,
        },
        assurance: None,
    }
}

/// `true` iff `errors` is EXACTLY one kernel-recheck refusal on obligation #0,
/// and that refusal is the WS1.1 binding rule's (`contract clause does not
/// bind to a Nat-valued IR place: ...`) carrying `needle`.
fn sole_binding_refusal(errors: &[ValidationError], needle: &str) -> bool {
    matches!(
        errors,
        [ValidationError::CertifiedCleanCicKernelRecheckFailed { obligation: 0, reason }]
            if reason.starts_with("contract clause does not bind to a Nat-valued IR place")
                && reason.contains(needle)
    )
}

// ===========================================================================
// PASS rows
// ===========================================================================

fn b2_01_contract_surface_validates_roundtrips_and_runs() {
    let main = build_main();
    let m = &main.module;

    // (1) shape: every summary field populated, every ClausePlace, Int/BitVec/Bool.
    let bump = m
        .function_by_id(main.bump)
        .unwrap()
        .summary
        .clone()
        .unwrap();
    let countdown = m
        .function_by_id(main.countdown)
        .unwrap()
        .summary
        .clone()
        .unwrap();
    let mut places = BTreeSet::new();
    let mut sorts = BTreeSet::new();
    for f in &m.functions {
        if let Some(s) = &f.summary {
            for c in s.requires.iter().chain(&s.ensures).chain(&s.decreases) {
                for (_, b) in &c.bindings {
                    places.insert(match b.place {
                        ClausePlace::Param { .. } => "Param",
                        ClausePlace::ResultSlot { .. } => "ResultSlot",
                        ClausePlace::MutParamExit { .. } => "MutParamExit",
                        ClausePlace::World => "World",
                        // v59 (WS1.14): the world epochs.
                        ClausePlace::WorldPre => "WorldPre",
                        ClausePlace::WorldPost => "WorldPost",
                        ClausePlace::Unwind => "Unwind",
                        ClausePlace::Value(_) => "Value",
                        // v46 (WS4.14): spec-machine places, refused on a
                        // function summary by name; never bound here.
                        ClausePlace::SpecVar { .. } => "SpecVar",
                        ClausePlace::SpecVarNext { .. } => "SpecVarNext",
                        // v62 (DG-63): the entry-state pointee of a reference
                        // parameter; the b2 corpus binds none.
                        ClausePlace::ParamPointeeEntry { .. } => "ParamPointeeEntry",
                    });
                    sorts.insert(match b.sort {
                        ClauseSort::Bool => "Bool",
                        ClauseSort::Int => "Int",
                        ClauseSort::BitVec(_) => "BitVec",
                        ClauseSort::Array(..) => "Array",
                        ClauseSort::Float { .. } => "Float",
                        ClauseSort::RoundingMode => "RoundingMode",
                        ClauseSort::Datatype { .. } => "Datatype",
                    });
                }
            }
        }
    }
    let shape_ok = bump.requires.len() == 1
        && bump.ensures.len() == 2
        && bump.params == ["x", "out"]
        && bump.proved
        && countdown.decreases.len() == 1
        && countdown.proved
        && places.len() == 6
        && ["Bool", "Int", "BitVec"].iter().all(|s| sorts.contains(s));
    assert!(feature_check(
        "b2.summary.fields_places_sorts",
        shape_ok,
        &format!(
            "requires/ensures/decreases/params/proved populated; places={places:?} sorts={sorts:?}"
        ),
    ));

    // (2) validate. The authority tier with the consumer stand-in is the ONLY
    // entry point under which a module holding Discharged rows can be clean.
    let errors = errors_with_stand_in(m);
    assert!(feature_check(
        "b2.validate.authority_tier",
        errors.is_empty(),
        &format!(
            "validate_module_with_authority(stand-in replay) on 4 fns / {} obligations / {} certificates => {errors:?}",
            m.proof_obligations.len(),
            m.proof_certificates.len()
        ),
    ));

    // (2') negative twin + the structural tier, measured exactly: plain
    // `validate_module` refuses precisely the Discharged rows that only a
    // consumer capability could back, and nothing else. Since WS1.6
    // (c3819f64) the one same-module inheritance row (#11, restating the
    // kernel-certified #6) is admitted in-process and is NOT among them.
    let structural = validate_module(m);
    let refused: BTreeSet<u32> = structural
        .iter()
        .filter_map(|e| match e {
            ValidationError::DischargedWithoutCertificate { obligation } => Some(*obligation),
            _ => None,
        })
        .collect();
    let local_inheritance: BTreeSet<u32> = m
        .proof_certificates
        .iter()
        .filter(|c| {
            matches!(
                c.evidence,
                ProofEvidence::InheritedFromCallee { external: None, .. }
            )
        })
        .map(|c| c.obligation.index())
        .collect();
    let discharged: BTreeSet<u32> = m
        .proof_obligations
        .iter()
        .filter(|o| o.status == ProofStatus::Discharged)
        .map(|o| o.id.index())
        .collect();
    let needs_capability: BTreeSet<u32> =
        discharged.difference(&local_inheritance).copied().collect();
    assert!(feature_check(
        "b2.validate.structural_tier_refuses_exactly_discharged",
        local_inheritance == BTreeSet::from([11])
            && refused == needs_capability
            && structural.len() == needs_capability.len(),
        &format!(
            "validate_module (RejectingModuleProofAuthority) => {} errors, all DischargedWithoutCertificate on {refused:?}; Discharged rows = {discharged:?}, of which {local_inheritance:?} is same-module inheritance admitted in-process (WS1.6)",
            structural.len()
        ),
    ));

    // (3) round trip. The v41 contract surface forces wire >= 41; since
    // WS1.14 the proved `b2_bump_into` binds its heap at the exit epoch
    // (`WorldPost`), which only the effect-summary version can spell, so the
    // writer selects exactly that version (the highest requirement wins).
    let rt = roundtrip_all(m);
    assert!(feature_check(
        "b2.roundtrip.production",
        rt.lossless_production(),
        &rt.summary(),
    ));
    assert!(feature_check(
        "b2.wire_version",
        rt.binary_version == trust_ir::binary::EFFECT_SUMMARY_FORMAT_VERSION,
        &format!(
            "writer selected v{} for summary+bindings+Termination/Ownership/Custom+assurance+world epoch",
            rt.binary_version
        ),
    ));
    // Per-field survival through each production codec (not just `==`).
    for trip in [&rt.binary, &rt.json, &rt.msgpack] {
        let back = trip.decoded.as_ref().expect("decoded");
        let same = back.function_by_id(main.bump).unwrap().summary
            == m.function_by_id(main.bump).unwrap().summary
            && back.function_by_id(main.countdown).unwrap().summary
                == m.function_by_id(main.countdown).unwrap().summary
            && back.proof_obligations == m.proof_obligations
            && back.proof_certificates == m.proof_certificates;
        assert!(feature_check(
            &format!(
                "b2.roundtrip.{}.summary_obligations_certificates",
                trip.format
            ),
            same,
            &trip.summary(),
        ));
    }
    // TEXT is measured in `b2_15`. FLIPPED by WS4.4 (F-071): before it the
    // canonical text of this module could not even be parsed (the first v41
    // kind was an unknown obligation kind; under WS4.2 the text was refused as
    // `#lossy`). Now it round-trips EXACTLY, and the decoded module carries
    // the same summaries, obligations and certificates as the production
    // codecs. Twin: the diagnostic `termination` → `terminates` misspelling
    // pasted into the text is refused by name.
    let text_same = rt.text.decoded.as_ref().is_some_and(|back| {
        back.proof_obligations == m.proof_obligations
            && back.proof_certificates == m.proof_certificates
            && back.function_by_id(main.bump).unwrap().summary
                == m.function_by_id(main.bump).unwrap().summary
    });
    let printed = String::from_utf8_lossy(&rt.text.encoded).into_owned();
    let misspelled =
        trust_ir::parser::parse_module(&printed.replacen(" termination ", " terminates ", 1));
    assert!(feature_check(
        "b2.roundtrip.text.measured",
        rt.text.lossless()
            && text_same
            && misspelled.as_ref().is_err_and(|e| e
                .to_string()
                .contains("unknown obligation kind: 'terminates'")),
        &format!(
            "canonical text on the full b2 module: {} (dissected in b2_15); summaries, \
             obligations and certificates equal the production codecs' = {text_same}; \
             misspelled kind => {:?}",
            rt.text.summary(),
            misspelled.err().map(|e| e.to_string())
        ),
    ));

    // (3') the codegen-facing layers a backend stacks on top of validation
    // (TB/validate.rs:8429-8434): license, lowerability, global_asm. All four
    // bodies are `Gated`, so none of them refuses; the twin flips ONE gate.
    let license = trust_ir_build::codegen_license_errors(m);
    let lowerability = trust_ir_build::validate::codegen_lowerability_errors(m);
    let global_asm = trust_ir_build::codegen_global_asm_errors(m);
    let mut ungated = m.clone();
    ungated.function_by_id_mut(main.bump).unwrap().body_gate = Some(BodyGate::Ungated);
    let ungated_errors = trust_ir_build::codegen_license_errors(&ungated);
    assert!(feature_check(
        "b2.validate.codegen_layers_clean",
        license.is_empty()
            && lowerability.is_empty()
            && global_asm.is_empty()
            && matches!(ungated_errors.as_slice(), [ValidationError::UngatedBodyForCodegen { function, name }] if *function == main.bump.index() && name == "b2_bump_into"),
        &format!(
            "codegen_license_errors={license:?} codegen_lowerability_errors={lowerability:?} codegen_global_asm_errors={global_asm:?}; twin b2_bump_into.body_gate := Ungated => {ungated_errors:?}. NOTE the pinned `validate_module_for_codegen` is built on the STRUCTURAL tier, so on this module it reports exactly the same DischargedWithoutCertificate rows as validate_module; the capability-taking lane is `validate_module_for_codegen_with` (b2.gap.no_authority_taking_codegen_or_bundle_entry_point)"
        ),
    ));

    // (4) execute through both languages.
    let got = run_nullary(m, "program");
    let value = got
        .as_ref()
        .ok()
        .and_then(|v| v.first())
        .and_then(common::as_u128);
    assert!(feature_check(
        "b2.interpret.program",
        value == Some(84),
        &format!(
            "program() = {got:?} (bump_into(41,&mut s) + s + countdown(3)), reference interpreter; contracts are NOT evaluated by it"
        ),
    ));
    let _ = main.is_zero;
}

fn b2_02_backed_by_declaration_and_every_clause_sort() {
    let good = build_backed_declaration(Some(good_backing()));
    let errors = validate_module(&good);
    assert!(feature_check(
        "b2.summary.backed_by_declaration",
        errors.is_empty(),
        &format!(
            "body-less Clean declaration, `proved`, backed_by import#0/far_scale/obligation#3, sorts Float+RoundingMode+Datatype => {errors:?}; NOTE validate_module is the STRUCTURAL tier: it checks the import row exists and an obligation is named, and takes the citation ON FAITH (TB/validate.rs:3362-3368); the authority tier refuses it (twin 5) and only validate_linked_module authenticates it (area b4)"
        ),
    ));
    // The declaration binds its ambient rounding mode and option at the entry
    // epoch (`WorldPre`, WS1.14), so the writer selects the effect-summary
    // version for it.
    let rt = roundtrip_all(&good);
    assert!(feature_check(
        "b2.summary.backed_by_declaration.roundtrip",
        rt.lossless_production()
            && rt.binary_version == trust_ir::binary::EFFECT_SUMMARY_FORMAT_VERSION,
        &rt.summary(),
    ));

    // twin 1 (DESIGN: body-less decl `proved` without `backed_by`).
    let bare = build_backed_declaration(None);
    let errors = validate_module(&bare);
    let needle = "a body-less declaration has no body a local obligation could be about";
    assert!(feature_check(
        "b2.summary.backed_by_declaration.twin_no_backing",
        summary_refusal_exact(&errors, FuncId::new(0), needle, 2)
            && summary_refusal(
                &errors,
                FuncId::new(0),
                "with 1 requires clause(s) but no local Precondition obligation can back a clause here"
            )
            && summary_refusal(
                &errors,
                FuncId::new(0),
                "with 1 ensures clause(s) but no local Postcondition obligation can back a clause here"
            )
            && summary_refusal(&errors, FuncId::new(0), "`backed_by: None` is NOT RECORDED"),
        &format!("{:?}", summary_details(&errors)),
    ));

    // twin 2: a kernel-CERTIFIED local obligation beside the declaration still
    // buys nothing (local rows back clauses of definitions only; since WS1.3
    // the refusal names the declaration shape, not a count).
    let mut laundering = build_backed_declaration(None);
    let tautology = ProofObligation::new(
        ProofId::new(0),
        ObligationKind::Postcondition,
        ProofStatus::Certified,
        "ensures (= 1 1)",
    )
    .with_function(FuncId::new(0))
    .with_formula(ProofFormula::smtlib2("(= 1 1)", "Bool"));
    let cert = contract_clean_cic_certificate(&tautology, "clean-kernel").expect("(= 1 1)");
    laundering.proof_obligations.push(tautology);
    laundering.proof_certificates.push(cert);
    let errors = validate_module(&laundering);
    // control: the SAME certified row beside a DEFINITION is what the
    // per-clause rule matches (b2_10's honest baseline), so the refusal below
    // is about the declaration shape, not about the certificate.
    assert!(feature_check(
        "b2.summary.backed_by_declaration.twin_certified_tautology_launders_nothing",
        summary_refusal_exact(
            &errors,
            FuncId::new(0),
            "with 1 ensures clause(s) but no local Postcondition obligation can back a clause here",
            2
        ) && summary_refusal(
            &errors,
            FuncId::new(0),
            "a body-less declaration has no body a local obligation could be about"
        ),
        &format!(
            "kernel-certified `(= 1 1)` scoped to the declaration => {:?}",
            summary_details(&errors)
        ),
    ));

    // twin 3: naming the entity but NO obligation authenticates nothing.
    let named_only = build_backed_declaration(Some(ExternRef::new(ImportId::new(0), "far_scale")));
    let errors = validate_module(&named_only);
    assert!(feature_check(
        "b2.summary.backed_by_declaration.twin_no_obligation_named",
        summary_refusal_exact(&errors, FuncId::new(0), needle, 2),
        &format!(
            "ExternRef{{import#0,'far_scale',obligation:None}} => {:?}",
            summary_details(&errors)
        ),
    ));

    // twin 4: citation into an undeclared import.
    let dangling = build_backed_declaration(Some(
        ExternRef::new(ImportId::new(9), "far_scale").relying_on(ProofId::new(3)),
    ));
    let errors = validate_module(&dangling);
    assert!(feature_check(
        "b2.summary.backed_by_declaration.twin_dangling_import",
        errors.len() == 3
            && errors.iter().filter(|e| matches!(e, ValidationError::DanglingExternRef { detail } if detail.contains("import #9"))).count() == 1
            && errors.iter().filter(|e| matches!(e, ValidationError::InvalidFunctionSummary { function: 0, .. })).count() == 2,
        &format!("{errors:?}"),
    ));

    // twin 5: the authority tier takes no cross-crate claim on faith.
    let errors =
        validate_module_with_authority(&good, &trust_ir::proof::RejectingModuleProofAuthority);
    assert!(feature_check(
        "b2.summary.backed_by_declaration.twin_authority_tier_refuses",
        matches!(
            errors.as_slice(),
            [ValidationError::UnauthenticatedImport {
                import: 0,
                site: "backed_by",
                ..
            }]
        ),
        &format!("{errors:?}"),
    ));

    // twin 6: the STRICTEST entry point, `validate_linked_module`, with no
    // dependency module to authenticate the citation against. (The positive,
    // authenticated form of this row — a real dep whose stable_digest the
    // import pins — is area b4's `b4.validate_linked_module`; this module's
    // import digest is a placeholder, so here only the refusal is measurable.)
    let nothing = trust_ir_build::ModuleSet::new(std::iter::empty::<&Module>());
    let linked = trust_ir_build::validate_linked_module(
        &good,
        &nothing,
        &trust_ir::proof::RejectingModuleProofAuthority,
    );
    assert!(feature_check(
        "b2.summary.backed_by_declaration.twin_linked_tier_needs_the_dependency",
        matches!(linked.errors(), [ValidationError::ImportUnavailable { import: 0, name }] if name == "b2_upstream"),
        &format!(
            "validate_linked_module(empty ModuleSet) => {:?}",
            linked.errors()
        ),
    ));
}

fn b2_03_clause_binding_negative_twins() {
    let main = build_main();
    let base = &main.module;
    assert!(
        errors_with_stand_in(base).is_empty(),
        "baseline must validate"
    );

    // Each twin = the validated baseline + ONE mutated binding on b2_bump_into.
    // Bindings are part of what a clause MEANS, so since WS1.3 a twin that
    // mutates a CLAUSE also leaves that clause stated by no backing row: the
    // fourth field names it, and the twin is exactly the named binding
    // refusal plus that one per-clause refusal (`params_arity` mutates the
    // parameter list, no clause, so it stays a single refusal).
    type Mutation = (
        &'static str,
        fn(&mut FunctionSummary),
        &'static str,
        Option<&'static str>,
    );
    let twins: Vec<Mutation> = vec![
        (
            "param_past_arity",
            |s| s.requires[0].bindings[0].1.place = ClausePlace::Param { index: 2 },
            "names parameter 2 but the signature declares 2",
            Some("requires clause 0"),
        ),
        (
            "result_slot_past_arity",
            |s| s.ensures[0].bindings[1].1.place = ClausePlace::ResultSlot { index: 1 },
            "names result slot 1 but the signature declares 1",
            Some("ensures clause 0"),
        ),
        (
            "value_never_defined",
            |s| s.ensures[0].bindings[2].1.place = ClausePlace::Value(ValueId::new(999)),
            "names SSA value v999, which this function's body never defines",
            Some("ensures clause 0"),
        ),
        (
            "mut_param_exit_on_requires",
            // index 1 is the `*mut u64`: the place TYPES (WS1.2), so only the
            // placement rule speaks.
            |s| s.requires[0].bindings[0].1.place = ClausePlace::MutParamExit { index: 1 },
            "uses MutParamExit, the give-back / primed-output place, on a requires clause",
            Some("requires clause 0"),
        ),
        (
            "unwind_on_requires",
            |s| s.requires[0].bindings[0].1.place = ClausePlace::Unwind,
            "names the in-flight unwind state on a requires clause",
            Some("requires clause 0"),
        ),
        (
            "duplicate_name",
            |s| s.ensures[0].bindings[1].0 = "x".to_string(),
            "is bound more than once",
            Some("ensures clause 0"),
        ),
        (
            "blank_name",
            |s| s.ensures[0].bindings[0].0 = "  ".to_string(),
            "binds a blank free name",
            Some("ensures clause 0"),
        ),
        (
            "params_arity",
            |s| s.params.pop().map(|_| ()).unwrap(),
            "summary lists 1 parameter name(s) but the signature has 2",
            None,
        ),
        (
            "blank_schema",
            |s| s.ensures[1].schema = " ".to_string(),
            "ensures clause 1 has an empty schema",
            Some("ensures clause 1"),
        ),
    ];
    for (name, mutate, needle, unbacked) in twins {
        let mut m = base.clone();
        mutate(
            m.function_by_id_mut(main.bump)
                .unwrap()
                .summary
                .as_mut()
                .unwrap(),
        );
        let errors = errors_with_stand_in(&m);
        assert!(feature_check(
            &format!("b2.bindings.twin.{name}"),
            summary_refusal_exact(
                &errors,
                main.bump,
                needle,
                1 + usize::from(unbacked.is_some())
            ) && unbacked.is_none_or(|clause| clause_unbacked(&errors, main.bump, clause)),
            &format!("{:?}", summary_details(&errors)),
        ));
    }

    // MutParamExit on a `decreases` measure (the third clause list). b2_countdown
    // has only the by-value `n: u64`, so since WS1.2 the same binding also draws
    // the by-value refusal, and since WS1.3 the mutated measure is stated by no
    // Termination row: exactly those three, all named.
    let mut m = base.clone();
    m.function_by_id_mut(main.countdown)
        .unwrap()
        .summary
        .as_mut()
        .unwrap()
        .decreases[0]
        .bindings[0]
        .1
        .place = ClausePlace::MutParamExit { index: 0 };
    let errors = errors_with_stand_in(&m);
    assert!(feature_check(
        "b2.bindings.twin.mut_param_exit_on_decreases",
        summary_refusal_exact(
            &errors,
            main.countdown,
            "uses MutParamExit, the give-back / primed-output place, on a decreases clause",
            3
        ) && summary_refusal(
            &errors,
            main.countdown,
            "decreases clause 0 binding 'n' uses MutParamExit on parameter 0 of type u64, which is not a &mut / *mut",
        ) && clause_unbacked(&errors, main.countdown, "decreases clause 0"),
        &format!("{:?}", summary_details(&errors)),
    ));

    // `Value` on a body-less declaration.
    let mut decl = build_backed_declaration(Some(good_backing()));
    decl.functions[0].summary.as_mut().unwrap().ensures[0].bindings[2]
        .1
        .place = ClausePlace::Value(ValueId::new(0));
    let errors = validate_module(&decl);
    assert!(feature_check(
        "b2.bindings.twin.value_on_declaration",
        summary_refusal_exact(
            &errors,
            FuncId::new(0),
            "on a body-less declaration, which has no body to resolve it in",
            1
        ),
        &format!("{:?}", summary_details(&errors)),
    ));
}

/// DESIGN negative twin "empty bindings = unbindable".
///
/// What trust-ir ENFORCES about it (PASS): bindings are part of what a formula
/// MEANS, so they are part of the certificate lineage — a kernel certificate
/// minted for the BOUND clause does not certify the same text with the
/// bindings stripped (TI/proof/evidence.rs:817-838, lineage domain v5 vs v6).
/// What it does NOT enforce is recorded as a GAP in `b2_08`.
fn b2_04_empty_bindings_are_a_different_claim() {
    let main = build_main();
    let mut m = main.module.clone();
    let bound = m.proof_obligations[6].clone();
    assert!(!bound.formula.as_ref().unwrap().bindings.is_empty());
    let mut unbound = bound.clone();
    unbound.formula.as_mut().unwrap().bindings.clear();
    let differs = trust_ir::proof::clean_cic_lineage_digest(&bound)
        != trust_ir::proof::clean_cic_lineage_digest(&unbound);

    m.proof_obligations[6]
        .formula
        .as_mut()
        .unwrap()
        .bindings
        .clear();
    let errors = errors_with_stand_in(&m);
    let refused = kernel_tier_collapse_exact(&m, &errors, |e| {
        matches!(
            e,
            ValidationError::CertifiedCleanCicLineageMismatch { obligation: 6 }
        )
    });
    assert!(feature_check(
        "b2.bindings.empty_is_a_different_claim",
        differs && refused,
        &format!(
            "lineage(bound) != lineage(unbound) = {differs}; stripping obligation#6's bindings under its kernel certificate => {errors:?}"
        ),
    ));
    // and the converse direction: re-typing the bound name is also a new claim.
    let mut m = main.module.clone();
    m.proof_obligations[6].formula.as_mut().unwrap().bindings[0]
        .1
        .sort = BV64;
    let errors = errors_with_stand_in(&m);
    assert!(feature_check(
        "b2.bindings.retyped_binding_breaks_certificate",
        kernel_tier_collapse_exact(&m, &errors, |e| matches!(
            e,
            ValidationError::CertifiedCleanCicLineageMismatch { obligation: 6 }
        )),
        &format!("result: Int -> BitVec(64) under the same certificate => {errors:?}"),
    ));
}

fn b2_05_all_kinds_statuses_scope_and_site() {
    let main = build_main();
    let m = &main.module;
    assert!(errors_with_stand_in(m).is_empty(), "baseline must validate");

    let kinds: BTreeSet<String> = m
        .proof_obligations
        .iter()
        .map(|o| match &o.kind {
            ObligationKind::Custom { .. } => "custom".to_string(),
            other => other.to_string(),
        })
        .collect();
    let expected_kinds = [
        "precondition",
        "postcondition",
        "loop_invariant",
        "type_invariant",
        "refinement_type",
        "translation_validation",
        "memory_safety",
        "panic_freedom",
        "temporal_safety",
        "liveness",
        "arithmetic_safety",
        "bounds_check",
        "give_back_refinement",
        "termination",
        "ownership",
        "custom",
    ];
    assert!(feature_check(
        "b2.obligations.all_16_kinds",
        kinds.len() == 16 && expected_kinds.iter().all(|k| kinds.contains(*k)),
        &format!("{kinds:?}"),
    ));
    let statuses: BTreeSet<String> = m
        .proof_obligations
        .iter()
        .map(|o| o.status.to_string())
        .collect();
    assert!(feature_check(
        "b2.obligations.all_5_statuses",
        statuses.len() == 5,
        &format!("{statuses:?} — all five in ONE module that validates under the authority tier"),
    ));
    let scoped = m.proof_obligations.iter().all(|o| {
        o.function.is_some() && o.site.map(|s| Some(s.function) == o.function) == Some(true)
    });
    assert!(feature_check(
        "b2.obligations.function_scope_and_site",
        scoped,
        &format!(
            "all {} obligations carry function (B4) + ObligationSite; e.g. Termination#4 site = {:?}",
            m.proof_obligations.len(),
            m.proof_obligations[4].site
        ),
    ));

    // --- site negative twins (DESIGN: dangling site) ---------------------------
    let site4 = m.proof_obligations[4].site.unwrap();
    let mut twin = m.clone();
    twin.proof_obligations[4].site = Some(ObligationSite::new(main.countdown, BlockId::new(77), 0));
    let errors = errors_with_stand_in(&twin);
    assert!(feature_check(
        "b2.obligations.site.twin_dangling_block",
        errors.len() == 1
            && matches!(&errors[0], ValidationError::ObligationSiteOutOfRange { obligation: 4, block: 77, reason, .. } if *reason == "no such block in that function"),
        &format!("{errors:?}"),
    ));
    let mut twin = m.clone();
    twin.proof_obligations[4].site = Some(ObligationSite::new(main.countdown, site4.block, 99));
    let errors = errors_with_stand_in(&twin);
    assert!(feature_check(
        "b2.obligations.site.twin_index_past_block",
        errors.len() == 1
            && matches!(&errors[0], ValidationError::ObligationSiteOutOfRange { obligation: 4, inst_index: 99, reason, .. } if *reason == "instruction index past the end of the block"),
        &format!("{errors:?}"),
    ));
    let mut twin = m.clone();
    twin.proof_obligations[4].site = Some(ObligationSite::new(main.bump, BlockId::new(0), 0));
    let errors = errors_with_stand_in(&twin);
    assert!(feature_check(
        "b2.obligations.site.twin_scope_contradiction",
        errors.len() == 1
            && matches!(&errors[0], ValidationError::ObligationSiteFunctionMismatch { obligation: 4, site_function, scope_function } if *site_function == main.bump.index() && *scope_function == main.countdown.index()),
        &format!("{errors:?}"),
    ));
    let mut twin = m.clone();
    twin.proof_obligations[12].function = None; // unscoped, so only the site speaks
    // intermediate baseline: unscoped + its REAL site still validates, so the
    // refusal below is caused by the ONE change that follows.
    assert!(
        errors_with_stand_in(&twin).is_empty(),
        "unscoped-with-site intermediate must validate"
    );
    twin.proof_obligations[12].site =
        Some(ObligationSite::new(FuncId::new(77), BlockId::new(0), 0));
    let errors = errors_with_stand_in(&twin);
    assert!(feature_check(
        "b2.obligations.site.twin_no_such_function",
        errors.len() == 1
            && matches!(&errors[0], ValidationError::ObligationSiteOutOfRange { obligation: 12, function: 77, reason, .. } if *reason == "no such function"),
        &format!("{errors:?}"),
    ));

    // --- kind negative twin: Custom namespace outside the pinned list ----------
    let mut twin = m.clone();
    twin.proof_obligations[18].kind = ObligationKind::Custom {
        namespace: "clean.theorem".into(),
        name: "nn_output_bound".into(),
    };
    let errors = errors_with_stand_in(&twin);
    assert!(feature_check(
        "b2.obligations.custom.twin_unpinned_namespace",
        matches!(errors.as_slice(), [ValidationError::UnpinnedCustomObligationNamespace { obligation: 18, namespace, .. }] if namespace == "clean.theorem"),
        &format!(
            "{errors:?} (admitted list TB/validate.rs:10210 is six `trust.*`/`trust_vc.*` names; none is Clean-owned)"
        ),
    ));

    // --- id integrity twin ------------------------------------------------------
    let mut twin = m.clone();
    twin.proof_obligations[20].id = ProofId::new(5);
    let errors = errors_with_stand_in(&twin);
    assert!(feature_check(
        "b2.obligations.twin_duplicate_id",
        matches!(
            errors.as_slice(),
            [ValidationError::DuplicateProofObligationId(5)]
        ),
        &format!("{errors:?}"),
    ));
}

fn b2_06_certificates_for_all_8_evidence_variants_and_assurance() {
    let main = build_main();
    let m = &main.module;
    assert!(errors_with_stand_in(m).is_empty(), "baseline must validate");

    let variants: BTreeSet<&str> = m
        .proof_certificates
        .iter()
        .map(|c| match &c.evidence {
            ProofEvidence::SmtProof(_) => "SmtProof",
            ProofEvidence::LeanProof(_) => "LeanProof",
            ProofEvidence::KaniHarness(_) => "KaniHarness",
            ProofEvidence::GammaCrownBound { .. } => "GammaCrownBound",
            ProofEvidence::TranslationValidation { .. } => "TranslationValidation",
            ProofEvidence::Trusted(_) => "Trusted",
            ProofEvidence::InheritedFromCallee { .. } => "InheritedFromCallee",
            ProofEvidence::CleanCic { .. } => "CleanCic",
        })
        .collect();
    assert!(feature_check(
        "b2.certificates.all_8_evidence_variants",
        variants.len() == 8,
        &format!(
            "{variants:?} in one validated module; CleanCic#6 is REALLY re-checked by the in-process Clean kernel, the other seven ride the stand-in capability"
        ),
    ));

    // The kernel tier is real: the report lists exactly one replayed certificate.
    // (kernel tier ONLY: the stand-in-admitted Discharged rows never enter it.)
    let capability = stand_in(m);
    let report = trust_ir_build::validate_module_report_with_authority(m, &capability);
    let replayed = report.replayed_certificate_refs().map(|refs| refs.len());
    assert!(feature_check(
        "b2.certificates.kernel_tier_replayed",
        replayed == Some(1),
        &format!(
            "validate_module_report_with_authority(..).replayed_certificate_refs().len() = {replayed:?} (exactly the Certified Postcondition #6; the 12 capability-admitted rows are not kernel-tier currency)"
        ),
    ));

    // --- CoverageAssurance: all four bounds carried + re-derivation -------------
    let bounds: Vec<CoverageBound> = m
        .proof_certificates
        .iter()
        .filter_map(|c| c.assurance.map(|a| a.bound))
        .collect();
    let mut bundle = NativeVerificationBundle::new(
        NativeBundleProducer::TrustIr,
        NativeAdapterInput::TrustIrModule,
        m.stable_digest(),
        m.clone(),
        ProofLineageManifest::default(),
    );
    bundle.requests = main.requests.clone();
    let report = coverage_assurance_report(m, Some(&bundle));
    assert!(feature_check(
        "b2.certificates.assurance_coverage_bound",
        bounds
            == vec![
                CoverageBound::Unbounded,
                CoverageBound::UnwindBounded { depth: 1 },
                CoverageBound::ModelBounded { size: 4 },
                CoverageBound::Unrecorded,
            ]
            && report.is_checked()
            && report.errors().is_empty()
            && report.agreed() == 1,
        &format!("bounds={bounds:?}; {}", report.summary()),
    ));
    // twin: a depth-1 BMC relabelled Unbounded is refused.
    let mut twin = m.clone();
    twin.proof_certificates[1].assurance.as_mut().unwrap().bound = CoverageBound::Unbounded;
    let mut twin_bundle = bundle.clone();
    twin_bundle.trust_ir_module_digest = twin.stable_digest();
    twin_bundle.module = twin.clone();
    let errors = coverage_assurance_report(&twin, Some(&twin_bundle)).into_errors();
    assert!(feature_check(
        "b2.certificates.assurance.twin_overclaimed_bound",
        matches!(errors.as_slice(), [ValidationError::CoverageAssuranceBoundMismatch { obligation: 1, recorded, derived }] if recorded == "Unbounded" && derived == "UnwindBounded { depth: 1 }"),
        &format!("{errors:?}"),
    ));
    // twin: a digest no request of the bundle re-derives.
    let mut twin = m.clone();
    twin.proof_certificates[0]
        .assurance
        .as_mut()
        .unwrap()
        .request_digest = ProofDigest::sha256([7; 32]);
    let mut twin_bundle = bundle.clone();
    twin_bundle.trust_ir_module_digest = twin.stable_digest();
    twin_bundle.module = twin.clone();
    let errors = coverage_assurance_report(&twin, Some(&twin_bundle)).into_errors();
    assert!(feature_check(
        "b2.certificates.assurance.twin_unknown_request",
        matches!(
            errors.as_slice(),
            [ValidationError::CoverageAssuranceRequestUnknown { obligation: 0, .. }]
        ),
        &format!("{errors:?}"),
    ));

    // --- Certified twins ----------------------------------------------------------
    let kernel_index = m
        .proof_certificates
        .iter()
        .position(|c| matches!(c.evidence, ProofEvidence::CleanCic { .. }))
        .unwrap();
    let mut twin = m.clone();
    twin.proof_certificates[kernel_index].evidence = ProofEvidence::SmtProof(b"(proof)".to_vec());
    let errors = errors_with_stand_in(&twin);
    assert!(feature_check(
        "b2.certificates.twin_certified_without_clean_cic",
        kernel_tier_collapse_exact(&twin, &errors, |e| matches!(
            e,
            ValidationError::CertifiedWithoutCleanCic { obligation: 6 }
        )),
        &format!("{errors:?}"),
    ));
    let mut twin = m.clone();
    twin.proof_obligations[6]
        .description
        .push_str(" (edited after minting)");
    let errors = errors_with_stand_in(&twin);
    assert!(feature_check(
        "b2.certificates.twin_certified_lineage_mismatch",
        kernel_tier_collapse_exact(&twin, &errors, |e| matches!(
            e,
            ValidationError::CertifiedCleanCicLineageMismatch { obligation: 6 }
        )),
        &format!("{errors:?}"),
    ));
    let mut twin = m.clone();
    if let ProofEvidence::CleanCic { term, .. } =
        &mut twin.proof_certificates[kernel_index].evidence
    {
        *term = b"not a proof term".to_vec();
    }
    let errors = errors_with_stand_in(&twin);
    assert!(feature_check(
        "b2.certificates.twin_forged_term_refused_by_kernel",
        kernel_tier_collapse_exact(&twin, &errors, |e| matches!(
            e,
            ValidationError::CertifiedCleanCicKernelRecheckFailed { obligation: 6, .. }
        )),
        &format!("{errors:?}"),
    ));
    // A FALSE ground claim never gets a certificate at all.
    let false_claim = ProofObligation::new(
        ProofId::new(99),
        ObligationKind::Postcondition,
        ProofStatus::Certified,
        "ensures (> 0 5)",
    )
    .with_formula(ProofFormula::smtlib2("(> 0 5)", "Bool"));
    assert!(feature_check(
        "b2.certificates.twin_false_ground_claim_unmintable",
        contract_clean_cic_certificate(&false_claim, "clean-kernel").is_none(),
        "contract_clean_cic_certificate((> 0 5)) = None (kernel refuses)",
    ));

    // --- certificate integrity twins -----------------------------------------------
    let mut twin = m.clone();
    twin.proof_certificates[0].obligation = ProofId::new(4242);
    let errors = errors_with_stand_in(&twin);
    assert!(feature_check(
        "b2.certificates.twin_dangling_certificate",
        errors.len() == 2
            && errors.iter().any(|e| matches!(
                e,
                ValidationError::DanglingProofCertificate { obligation: 4242 }
            ))
            && errors.iter().any(|e| matches!(
                e,
                ValidationError::DischargedWithoutCertificate { obligation: 0 }
            )),
        &format!("{errors:?}"),
    ));

    // --- InheritedFromCallee twins ---------------------------------------------------
    let inherit_index = m
        .proof_certificates
        .iter()
        .position(|c| matches!(c.evidence, ProofEvidence::InheritedFromCallee { .. }))
        .unwrap();
    let set_inherit = |module: &mut Module, callee: FuncId, obligation: u32| {
        module.proof_certificates[inherit_index].evidence = ProofEvidence::InheritedFromCallee {
            callee,
            obligation: ProofId::new(obligation),
            external: None,
        };
    };
    // inherits a capability-replayed Discharged row (#3), not a kernel-tier one.
    let mut twin = m.clone();
    set_inherit(&mut twin, main.countdown, 3);
    let errors = errors_with_stand_in(&twin);
    assert!(feature_check(
        "b2.certificates.inherited.twin_not_kernel_grounded",
        matches!(
            errors.as_slice(),
            [ValidationError::InheritedProofNotDischarged {
                obligation: 11,
                callee: 0,
                inherited_obligation: 3
            }]
        ),
        &format!(
            "inheriting Discharged#3 (stand-in replayed) instead of Certified#6 => {errors:?}"
        ),
    ));
    let mut twin = m.clone();
    set_inherit(&mut twin, main.bump, 6);
    let errors = errors_with_stand_in(&twin);
    assert!(feature_check(
        "b2.certificates.inherited.twin_callee_scope_mismatch",
        matches!(
            errors.as_slice(),
            [ValidationError::InheritedProofCalleeScopeMismatch {
                obligation: 11,
                named_callee: 1,
                actual_owner: 0
            }]
        ),
        &format!("{errors:?}"),
    ));
    let mut twin = m.clone();
    set_inherit(&mut twin, FuncId::new(77), 6);
    let errors = errors_with_stand_in(&twin);
    assert!(feature_check(
        "b2.certificates.inherited.twin_callee_not_found",
        errors.len() == 2
            && errors.iter().any(|e| matches!(
                e,
                ValidationError::InheritedProofCalleeNotFound {
                    obligation: 11,
                    callee: 77
                }
            ))
            && errors.iter().any(|e| matches!(
                e,
                ValidationError::InheritedProofCalleeScopeMismatch {
                    obligation: 11,
                    named_callee: 77,
                    actual_owner: 0
                }
            )),
        &format!("{errors:?}"),
    ));
    let _ = main.program;
}

fn b2_07_the_proved_counting_rule() {
    let main = build_main();
    let m = &main.module;
    assert!(errors_with_stand_in(m).is_empty(), "baseline must validate");
    // MEASURED, not asserted by prose: (clauses, backing rows) per function.
    // The baseline is TIGHT — exactly one Discharged/Certified row of the right
    // kind per clause — so every "one too few" twin below changes ONE row.
    let tally = |function: FuncId| {
        let summary = m
            .function_by_id(function)
            .unwrap()
            .summary
            .as_ref()
            .unwrap();
        let clauses = [
            summary.requires.len(),
            summary.ensures.len(),
            summary.decreases.len(),
        ];
        let mut backing = [0usize; 3];
        for o in m
            .proof_obligations
            .iter()
            .filter(|o| o.function == Some(function))
        {
            let slot = match o.kind {
                ObligationKind::Precondition => 0,
                ObligationKind::Postcondition => 1,
                ObligationKind::Termination => 2,
                _ => continue,
            };
            if matches!(o.status, ProofStatus::Discharged | ProofStatus::Certified) {
                backing[slot] += 1;
            }
        }
        (summary.proved, clauses, backing)
    };
    let bump = tally(main.bump);
    let countdown = tally(main.countdown);
    let is_zero = tally(main.is_zero);
    assert!(feature_check(
        "b2.proved.counting_rule",
        bump == (true, [1, 2, 0], [1, 2, 0])
            && countdown == (true, [0, 2, 1], [0, 3, 1])
            && is_zero == (false, [0, 1, 0], [0, 0, 0]),
        &format!(
            "(proved, [requires,ensures,decreases], [Discharged|Certified Precondition,Postcondition,Termination scoped to the fn]): b2_bump_into={bump:?} b2_countdown={countdown:?} (its Postcondition rows: #2, the kernel-CERTIFIED #6, and #11 — program's restatement of #6, scoped to the callee since WS1.6) b2_is_zero={is_zero:?} (published, not proved: Pending#5); module validates under the authority tier"
        ),
    ));

    // Each twin: EXACTLY `count` errors, all InvalidFunctionSummary on `function`.
    let check = |id: &str, module: &Module, function: FuncId, needle: &str| {
        let errors = errors_with_stand_in(module);
        assert!(feature_check(
            id,
            summary_refusal_exact(&errors, function, needle, 1),
            &format!("{errors:?}"),
        ));
    };
    // Since WS1.3 `proved` is per-clause: the clause a baseline row states
    // (found by formula equality, never assumed) is what a twin that removes
    // that row leaves unbacked — exactly one refusal, naming that clause.
    let stated_by = |row: usize| -> String {
        let o = &m.proof_obligations[row];
        let summary = m
            .function_by_id(o.function.expect("scoped row"))
            .unwrap()
            .summary
            .as_ref()
            .unwrap();
        let (role, list) = match o.kind {
            ObligationKind::Precondition => ("requires", &summary.requires),
            ObligationKind::Postcondition => ("ensures", &summary.ensures),
            ObligationKind::Termination => ("decreases", &summary.decreases),
            _ => panic!("row #{row} is not a contract row"),
        };
        let index = list
            .iter()
            .position(|c| Some(c) == o.formula.as_ref())
            .unwrap_or_else(|| panic!("row #{row} states no {role} clause"));
        format!("{role} clause {index}")
    };
    let check_clause = |id: &str, module: &Module, function: FuncId, clause: &str| {
        let errors = errors_with_stand_in(module);
        assert!(feature_check(
            id,
            errors.len() == 1 && clause_unbacked(&errors, function, clause),
            &format!("{errors:?}"),
        ));
    };

    // DESIGN twin: `proved` with no discharged obligation.
    // ONE logical change: the three contract rows (#0 Precondition, #1/#2
    // Postcondition) and their certificates are absent; every other obligation
    // of b2_bump_into (TypeInvariant#8, MemorySafety#10, ArithmeticSafety#14,
    // GiveBackRefinement#16) stays, Discharged ones included — so the refusal
    // also shows non-contract Discharged rows buy the contract nothing. Each
    // of the three clauses is refused by name (WS1.3).
    let mut twin = m.clone();
    twin.proof_obligations
        .retain(|o| ![0u32, 1, 2].contains(&o.id.index()));
    twin.proof_certificates
        .retain(|c| ![0u32, 1, 2].contains(&c.obligation.index()));
    let still_discharged_on_bump = twin
        .proof_obligations
        .iter()
        .filter(|o| o.function == Some(main.bump) && o.status == ProofStatus::Discharged)
        .count();
    assert_eq!(
        still_discharged_on_bump, 2,
        "MemorySafety#10 + ArithmeticSafety#14 remain Discharged"
    );
    let errors = errors_with_stand_in(&twin);
    assert!(feature_check(
        "b2.proved.twin_no_discharged_obligation",
        errors.len() == 3
            && ["requires clause 0", "ensures clause 0", "ensures clause 1"]
                .iter()
                .all(|clause| clause_unbacked(&errors, main.bump, clause)),
        &format!("{:?}", summary_details(&errors)),
    ));

    // one too few.
    let row2 = stated_by(2);
    let mut twin = m.clone();
    twin.proof_obligations[2].status = ProofStatus::Pending;
    check_clause(
        "b2.proved.twin_pending_does_not_count",
        &twin,
        main.bump,
        &row2,
    );

    // WS1.8 DECIDE 1A: a Trusted row attributes its faith through a
    // `ProofEvidence::Trusted` certificate, so the twin swaps #2's evidence
    // too — the ONE refusal measured stays "Trusted does not count", not
    // `TrustedWithoutJustification`.
    let mut twin = m.clone();
    twin.proof_obligations[2].status = ProofStatus::Trusted;
    for c in twin
        .proof_certificates
        .iter_mut()
        .filter(|c| c.obligation == ProofId::new(2))
    {
        c.evidence = ProofEvidence::Trusted("twin: accepted on faith".into());
    }
    check_clause(
        "b2.proved.twin_trusted_does_not_count",
        &twin,
        main.bump,
        &row2,
    );

    // right kind + status, wrong owner.
    let mut twin = m.clone();
    twin.proof_obligations[2].site = None;
    // intermediate baseline: dropping the site alone changes nothing, so the
    // refusal is caused by the re-scoping that follows.
    assert!(
        errors_with_stand_in(&twin).is_empty(),
        "site-less intermediate must validate"
    );
    twin.proof_obligations[2].function = Some(main.program);
    // Since WS4.4 the move is refused TWICE, each by name and each for its
    // own reason: the counting rule no longer finds a row for bump's clause
    // (the ONE counting refusal this twin measures), and the moved row's
    // clause bindings — `out_exit` is bump's `mut_exit(1)` — no longer
    // resolve in `program`, which has no parameter 1
    // (`InvalidObligationBinding`, the obligation half of the binding rule).
    // Exactly those two; anything else fails the twin.
    let errors = errors_with_stand_in(&twin);
    let binding_refused = |e: &ValidationError| {
        matches!(e, ValidationError::InvalidObligationBinding { obligation: 2, detail }
            if detail.contains("MutParamExit 1")
                && detail.contains("signature declares 0 parameter(s)"))
    };
    assert!(feature_check(
        "b2.proved.twin_other_functions_obligation_does_not_count",
        errors.len() == 2
            && clause_unbacked(&errors, main.bump, &row2)
            && errors.iter().filter(|e| binding_refused(e)).count() == 1,
        &format!("{errors:?}"),
    ));

    // wrong kind.
    let row0 = stated_by(0);
    let mut twin = m.clone();
    // intermediate baseline: #0 is sited on bump's entry `const`, and WS1.8
    // rule (c) refuses a MemorySafety row sited there on its own
    // (`ObligationSiteKindMismatch`, measured by
    // b2.gap.site_not_related_to_obligation_kind). Dropping the site first
    // changes nothing, so the ONE refusal measured below is the kind change's.
    twin.proof_obligations[0].site = None;
    assert!(
        errors_with_stand_in(&twin).is_empty(),
        "site-less intermediate must validate"
    );
    twin.proof_obligations[0].kind = ObligationKind::MemorySafety;
    check_clause(
        "b2.proved.twin_wrong_kind_does_not_count",
        &twin,
        main.bump,
        &row0,
    );

    // decreases needs Termination — Liveness (where it used to be mis-filed) does not count.
    let row4 = stated_by(4);
    let mut twin = m.clone();
    twin.proof_obligations[4].kind = ObligationKind::Liveness;
    check_clause(
        "b2.proved.twin_decreases_needs_termination_not_liveness",
        &twin,
        main.countdown,
        &row4,
    );

    // a Failed contract obligation refutes `proved` even when the counts hold.
    let mut twin = m.clone();
    twin.proof_obligations.push(
        ProofObligation::new(
            ProofId::new(21),
            ObligationKind::Postcondition,
            ProofStatus::Failed,
            "refuted",
        )
        .with_function(main.bump),
    );
    check(
        "b2.proved.twin_failed_refutes",
        &twin,
        main.bump,
        "while contract obligation #21, scoped to this function, is Failed",
    );
}

// ===========================================================================
// GAP ratchets
// ===========================================================================

/// FLIPPED (closed by WS1.3, F-002): `proved` is per-clause. The archived GAP:
/// `FunctionSummary.proved: bool` was earned by COUNTING Discharged/Certified
/// contract rows scoped to the function, never reading a row's `formula`, so
/// a kernel-certified row about one clause backed an unrelated FALSE clause.
/// Now every clause of a `proved` definition must be stated EXACTLY (schema,
/// payload, smtlib, sort, bindings) by a Discharged/Certified row of its
/// role's kind scoped to the function. `proved` stays one derived bool (no
/// wire change); the per-clause backref is the validator's formula match.
/// Requirement: spec-surface E1 "per-clause obligations and per-clause
/// grades"; exec-log "each `proved` contract clause must be tied to the
/// specific obligation that discharged it".
fn b2_08_gap_no_per_clause_backref() {
    let main = build_main();
    let base = main.module.clone();
    assert!(
        errors_with_stand_in(&base).is_empty(),
        "baseline must validate"
    );

    // `b2.gap.no_per_clause_obligation_backref` (the field shapes) is a
    // compile-time row in `field_ratchets.rs`.

    // The SHARPEST form, with NO capability anywhere (plain `validate_module`,
    // kernel tier only). Baseline `build_level(false, Int)`: `fn b2_level() ->
    // u64 { 7 }`, `proved` ensures `(>= result 0)`, backed by a Certified
    // Postcondition whose formula IS that clause — validates, and the kernel
    // tier replays its certificate. The single change (negative twin)
    // rewrites the SUMMARY clause to a claim that is FALSE of the body; the
    // obligation and its kernel certificate are untouched (so the lineage
    // still binds) — and the false clause is now refused by name.
    let honest = build_level(false, Some(ClauseSort::Int));
    assert!(
        validate_module(&honest).is_empty(),
        "baseline must validate"
    );
    assert_eq!(
        honest.functions[0].summary.as_ref().unwrap().ensures[0],
        *honest.proof_obligations[0].formula.as_ref().unwrap()
    );
    let honest_replayed = trust_ir_build::validate_module_report(&honest)
        .replayed_certificate_refs()
        .map(|refs| refs.len());
    let mut forged = honest.clone();
    forged.functions[0].summary.as_mut().unwrap().ensures[0] = clause(
        "(= result #x000000000000002a)",
        "Bool",
        vec![bind("result", BV64, ClausePlace::ResultSlot { index: 0 })],
    );
    assert_eq!(honest.proof_obligations, forged.proof_obligations);
    assert_eq!(honest.proof_certificates, forged.proof_certificates);
    let errors = validate_module(&forged);
    let value = run_nullary(&forged, "b2_level")
        .ok()
        .and_then(|v| v.first().and_then(common::as_u128));
    assert!(feature_check(
        "b2.gap.kernel_certified_row_backs_an_unrelated_false_clause",
        errors.len() == 1
            && clause_unbacked(&errors, FuncId::new(0), "ensures clause 0")
            && honest_replayed == Some(1)
            && value == Some(7),
        &format!(
            "closed by WS1.3: `-> u64 {{ 7 }}` with `proved` ensures `(= result 42)`; the only backing row is Certified Postcondition#0 about `(>= result 0)`: validate_module (no capability) => {errors:?}; the honest twin validates and the kernel tier replays {honest_replayed:?} certificate(s); the interpreter returns {value:?}"
        ),
    ));

    // Related: the unbindable rule is prose-only. A `proved` summary whose
    // clause has EMPTY bindings is accepted once it is backed
    // (TB/validate.rs:3184-3188: "This pass simply has nothing to resolve").
    // Since WS1.3 a clause is backed only by a row stating it EXACTLY,
    // bindings included, so the one logical change strips the bindings from
    // each ensures clause AND from the row stating it — otherwise the
    // refusal would be the per-clause mismatch, not the unbindability this
    // row measures.
    let mut m = base.clone();
    let stated: Vec<ProofFormula> = m
        .function_by_id(main.bump)
        .unwrap()
        .summary
        .as_ref()
        .unwrap()
        .ensures
        .clone();
    for c in m
        .function_by_id_mut(main.bump)
        .unwrap()
        .summary
        .as_mut()
        .unwrap()
        .ensures
        .iter_mut()
    {
        c.bindings.clear();
    }
    let mut stripped_rows = 0usize;
    for o in &mut m.proof_obligations {
        if o.function == Some(main.bump)
            && o.kind == ObligationKind::Postcondition
            && let Some(f) = o.formula.as_mut().filter(|f| stated.contains(f))
        {
            f.bindings.clear();
            stripped_rows += 1;
        }
    }
    assert_eq!(
        stripped_rows,
        stated.len(),
        "one stating row per ensures clause"
    );
    let errors = errors_with_stand_in(&m);
    assert!(feature_gap(
        "b2.gap.unbindable_clause_still_earns_proved",
        Expect::Accepted,
        Outcome::of(&errors),
        &format!(
            "both ensures clauses of b2_bump_into stripped to EMPTY bindings, `proved` kept => errors={errors:?}; `empty = UNBINDABLE` (TI/proof/obligations.rs:291-304) is a consumer duty no trust-ir entry point enforces"
        ),
    ));

    // FLIPPED by WS1.9 (F-011). The archived GAP: the public minter walked
    // `requires` + `ensures` only, so b2_countdown (2 ensures + 1 decreases)
    // minted two Postcondition rows and no Termination row — the row the
    // per-clause rule demands for every `decreases` clause. Now one
    // function-scoped Pending Termination row is minted per measure, stating
    // the measure as its `formula` exactly as the ensures rows state theirs.
    let mut m = base.clone();
    m.proof_obligations.clear();
    m.proof_certificates.clear();
    // baseline: on b2_bump_into (1 requires + 2 ensures, NO decreases) the
    // minter is one-row-per-clause, i.e. complete w.r.t. the per-clause rule.
    let bump_minted = mint_summary_obligations(&mut m, main.bump).expect("fresh obligation ids");
    let bump_kinds: Vec<String> = m
        .proof_obligations
        .iter()
        .map(|o| o.kind.to_string())
        .collect();
    assert_eq!(bump_minted.len(), 3);
    assert_eq!(
        bump_kinds,
        ["precondition", "postcondition", "postcondition"]
    );
    m.proof_obligations.clear();
    let countdown_summary = m
        .function_by_id(main.countdown)
        .unwrap()
        .summary
        .clone()
        .unwrap();
    let minted = mint_summary_obligations(&mut m, main.countdown).expect("fresh obligation ids");
    let kinds: Vec<String> = m
        .proof_obligations
        .iter()
        .map(|o| o.kind.to_string())
        .collect();
    let stated: Vec<&ProofFormula> = countdown_summary
        .ensures
        .iter()
        .chain(countdown_summary.decreases.iter())
        .collect();
    let termination = m.proof_obligations.get(2);
    assert!(feature_check(
        "b2.gap.mint_summary_obligations_skips_decreases",
        minted.len() == 3
            && kinds == ["postcondition", "postcondition", "termination"]
            && m.proof_obligations
                .iter()
                .zip(&stated)
                .all(|(o, c)| o.formula.as_ref() == Some(*c))
            && termination.is_some_and(|t| {
                t.formula.as_ref() == Some(&countdown_summary.decreases[0])
                    && t.function == Some(main.countdown)
                    && t.status == ProofStatus::Pending
            })
            && m.proof_obligations.iter().all(|o| o.site.is_none()),
        &format!(
            "b2_countdown has 2 ensures + 1 decreases; mint_summary_obligations minted {kinds:?}, each row stating its clause as `formula` (the Termination row states the measure `n`), function-scoped, Pending, site=None"
        ),
    ));
    // Negative twin (mutation control): the minter is driven by the clause
    // list, not by the function's shape — the same recursive body with its
    // `decreases` measure removed mints no Termination row.
    let mut twin = base.clone();
    twin.proof_obligations.clear();
    twin.proof_certificates.clear();
    twin.function_by_id_mut(main.countdown)
        .unwrap()
        .summary
        .as_mut()
        .unwrap()
        .decreases
        .clear();
    let twin_minted =
        mint_summary_obligations(&mut twin, main.countdown).expect("fresh obligation ids");
    let twin_kinds: Vec<String> = twin
        .proof_obligations
        .iter()
        .map(|o| o.kind.to_string())
        .collect();
    assert!(feature_check(
        "b2.mint.twin_no_decreases_mints_no_termination_row",
        twin_minted.len() == 2 && twin_kinds == ["postcondition", "postcondition"],
        &format!(
            "b2_countdown with its decreases measure removed mints {twin_kinds:?}: no Termination row without a measure to state"
        ),
    ));
    // Negative twin (the minted row is Pending, so it backs nothing yet): with
    // `proved` kept, the decreases clause is refused BY NAME until the
    // Termination row is discharged.
    let errors = errors_with_stand_in(&m);
    assert!(feature_check(
        "b2.mint.twin_pending_termination_row_backs_nothing",
        summary_refusal(
            &errors,
            main.countdown,
            "decreases clause 0 `n` has no Discharged/Certified Termination row scoped to this function stating exactly this clause",
        ),
        &format!(
            "the freshly minted Pending Termination row does not back the `proved` decreases clause: {:?}",
            summary_details(&errors)
        ),
    ));
}

/// FLIPPED (closed upstream by WS1.2, 31814e51; F-004, always-on half). The archived
/// GAP: `ClauseSort` (and the place's role) was not checked against the IR type of the
/// bound place — `validate_function_summary` resolved INDICES only, so the u64 parameter
/// `x` re-sorted as BitVec(8) / Bool / Float{11,53} / RoundingMode, the u64 result and the
/// SSA value `r` re-sorted as Bool, and `MutParamExit` naming the by-value `x: u64` all
/// validated. Now each single-change mutant is exactly ONE named `InvalidFunctionSummary`
/// on `b2_bump_into` (the restating obligation kept in step, so the sort / place is the
/// only change). Positive: the baseline validates. Mutation control: re-sorting `x` as
/// `Int` (a faithful reading of any integer) keeps it valid, so the rule refuses the
/// wrong sorts, not every re-sort.
fn b2_09_gap_clause_sort_unchecked_against_ir_type() {
    let main = build_main();
    let base = main.module.clone();
    assert!(
        errors_with_stand_in(&base).is_empty(),
        "baseline must validate"
    );
    // baseline binding: x : BitVec(64) @ Param{0}, and param 0 IS Ty::U64.
    let b0 = base
        .function_by_id(main.bump)
        .unwrap()
        .summary
        .as_ref()
        .unwrap()
        .requires[0]
        .bindings[0]
        .clone();
    assert_eq!(
        b0.1,
        ClauseBinding {
            sort: BV64,
            place: ClausePlace::Param { index: 0 }
        }
    );
    let resort_x = |sort: &ClauseSort| {
        let mut m = base.clone();
        m.function_by_id_mut(main.bump)
            .unwrap()
            .summary
            .as_mut()
            .unwrap()
            .requires[0]
            .bindings[0]
            .1
            .sort = sort.clone();
        // keep the restating obligation in step so ONLY the sort changed.
        m.proof_obligations[0].formula.as_mut().unwrap().bindings[0]
            .1
            .sort = sort.clone();
        errors_with_stand_in(&m)
    };

    let mut refused = Vec::new();
    let mut measured = Vec::new();
    for sort in [
        ClauseSort::BitVec(8),
        ClauseSort::Bool,
        ClauseSort::Float { eb: 11, sb: 53 },
        ClauseSort::RoundingMode,
    ] {
        let errors = resort_x(&sort);
        // Since WS4.4 the restating obligation #0 (kept in step) is refused by
        // the obligation half of the same typing rule.
        refused.push(summary_and_obligation_refusal_exact(
            &errors,
            main.bump,
            &format!("requires clause 0 binding 'x' has sort {sort:?} but Param 0 is u64"),
            0,
            &format!("binding \"x\" has sort {sort:?} but Param 0 is u64"),
        ));
        measured.push(format!("x := {sort:?} => {errors:?}"));
    }
    let ClausePlace::Value(sum) = base
        .function_by_id(main.bump)
        .unwrap()
        .summary
        .as_ref()
        .unwrap()
        .ensures[0]
        .bindings[2]
        .1
        .place
    else {
        panic!("ensures clause 0 binding 2 is the SSA value `r`")
    };
    // the other two TYPED places: ensures clause 0 binds `result` @ ResultSlot0 and
    // `sum` @ Value(r), both IR type u64, both BitVec(64) in the baseline. Re-sort each
    // as Bool (one binding per twin, restating obligation #1 kept in step).
    for (binding_index, needle, obligation_needle) in [
        (
            1usize,
            "ensures clause 0 binding 'result' has sort Bool but ResultSlot 0 is u64".to_string(),
            "binding \"result\" has sort Bool but ResultSlot 0 is u64".to_string(),
        ),
        (
            2,
            format!(
                "ensures clause 0 binding 'sum' has sort Bool but SSA value v{} is u64",
                sum.index()
            ),
            format!(
                "binding \"sum\" has sort Bool but SSA value v{} is u64",
                sum.index()
            ),
        ),
    ] {
        let mut m = base.clone();
        let clause = &mut m
            .function_by_id_mut(main.bump)
            .unwrap()
            .summary
            .as_mut()
            .unwrap()
            .ensures[0];
        assert_eq!(clause.bindings[binding_index].1.sort, BV64);
        clause.bindings[binding_index].1.sort = ClauseSort::Bool;
        m.proof_obligations[1].formula.as_mut().unwrap().bindings[binding_index]
            .1
            .sort = ClauseSort::Bool;
        let errors = errors_with_stand_in(&m);
        refused.push(summary_and_obligation_refusal_exact(
            &errors,
            main.bump,
            &needle,
            1,
            &obligation_needle,
        ));
        measured.push(format!("{needle} => {errors:?}"));
    }
    let int_control = resort_x(&ClauseSort::Int);
    assert!(feature_check(
        "b2.gap.clause_sort_unchecked_against_ir_type",
        refused.len() == 6 && refused.iter().all(|r| *r) && int_control.is_empty(),
        &format!(
            "closed upstream by WS1.2 (31814e51): {measured:?}; control x := Int => {int_control:?}"
        ),
    ));

    // same rule on the PLACE axis: MutParamExit on the by-value `x: u64` (the
    // baseline's MutParamExit{index:1} over `*mut u64` validates).
    let mut m = base.clone();
    m.function_by_id_mut(main.bump)
        .unwrap()
        .summary
        .as_mut()
        .unwrap()
        .ensures[1]
        .bindings[0]
        .1
        .place = ClausePlace::MutParamExit { index: 0 };
    m.proof_obligations[2].formula.as_mut().unwrap().bindings[0]
        .1
        .place = ClausePlace::MutParamExit { index: 0 };
    let errors = errors_with_stand_in(&m);
    // Since WS4.4 the restating obligation #2 (kept in step) is refused by
    // the obligation half of the same rule, by name.
    assert!(feature_check(
        "b2.gap.mut_param_exit_on_by_value_param_accepted",
        summary_and_obligation_refusal_exact(
            &errors,
            main.bump,
            "ensures clause 1 binding 'out_exit' uses MutParamExit on parameter 0 of type u64, which is not a &mut / *mut",
            2,
            "binding \"out_exit\" uses MutParamExit on parameter 0 of type u64, which is not a &mut / *mut",
        ),
        &format!(
            "closed upstream by WS1.2 (31814e51): MutParamExit{{index:0}} names the by-value `x: u64` (not the `*mut u64` at index 1) => errors={errors:?}"
        ),
    ));
}

/// FLIPPED (closed upstream by 0aeae341, roadmap WS1.1, F-001). The archived
/// GAP (the soundness-relevant consequence of the row above): the in-process
/// kernel contract re-check read `(>= v 0)` as a `Nat` tautology whatever the
/// clause's bindings said and whatever IR type the bound place had, so a FALSE
/// postcondition over a signed result reached `Certified` + `proved` under
/// plain `validate_module`. Since WS1.1 the nonneg tautology grounds only
/// through `bind_nat_nonneg` (sort Int, an unsigned IR place), and both rows
/// below are PASS rows over forged certificates.
fn b2_10_gap_kernel_certifies_nonneg_over_a_signed_result() {
    let level = |m: &Module| {
        run_nullary(m, "b2_level")
            .ok()
            .and_then(|v| v.first().and_then(common::as_i128))
    };

    // Well-formed baseline: u64 result 7, `result: Int`, the claim is TRUE,
    // plain validate_module (no capability at all) is clean, and the kernel
    // tier really replayed the certificate.
    let honest = build_level(false, Some(ClauseSort::Int));
    let honest_errors = validate_module(&honest);
    assert!(
        honest_errors.is_empty(),
        "baseline must validate: {honest_errors:?}"
    );
    assert_eq!(level(&honest), Some(7));
    let replayed = trust_ir_build::validate_module_report(&honest)
        .replayed_certificate_refs()
        .map(|refs| refs.len());
    assert_eq!(replayed, Some(1), "baseline certificate is kernel-replayed");
    // PASS row: a `proved` contract backed ONLY at the kernel tier is clean
    // under plain `validate_module` — no consumer capability, no stand-in.
    // (The main b2 module cannot show this: it holds Discharged rows.)
    let honest_rt = roundtrip_all(&honest);
    let mut stripped = honest.clone();
    stripped.proof_certificates.clear();
    let stripped_errors = validate_module(&stripped);
    assert!(feature_check(
        "b2.proved.kernel_tier_only_contract_clean_under_validate_module",
        honest_rt.lossless_production()
            && matches!(
                stripped_errors.as_slice(),
                [ValidationError::CertifiedWithoutCleanCic { obligation: 0 }]
            ),
        &format!(
            "`fn b2_level() -> u64 {{ 7 }}`, proved ensures `(>= result 0)` [result: Int @ ResultSlot0], Postcondition#0 Certified + kernel-rechecked CleanCic: validate_module (RejectingModuleProofAuthority) => [], replayed_certificate_refs = {replayed:?}, interpreter = 7, {}; twin (certificate removed, ONE change) => {stripped_errors:?}",
            honest_rt.summary()
        ),
    ));
    // Control: the kernel tier is not a rubber stamp — the FALSE bound `(>= result 5)`
    // is unmintable, so what follows is about what `(>= v 0)` is read AS.
    let mut five = honest.proof_obligations[0].clone();
    five.formula = Some(clause(
        "(>= result 5)",
        "Bool",
        vec![bind(
            "result",
            ClauseSort::Int,
            ClausePlace::ResultSlot { index: 0 },
        )],
    ));
    assert!(contract_clean_cic_certificate(&five, "clean-kernel").is_none());

    // FLIPPED (closed upstream by 0aeae341, roadmap WS1.1, F-001). Change 1
    // (IR side only): the function is `-> i64 { -1 }`, same clause, same
    // bindings. Was: minted, kernel-replayed and `validate_module => []`. Now:
    // neither entry point mints it, and the forged certificate (the honest
    // term under this obligation's lineage) is refused by exactly one named
    // binding-rule refusal; the u64 baseline above is the negative twin.
    let lying = build_level(true, Some(ClauseSort::Int));
    let errors = validate_module(&lying);
    let value = level(&lying);
    let lying_replayed = trust_ir_build::validate_module_report(&lying)
        .replayed_certificate_refs()
        .map(|refs| refs.len());
    let unmintable = contract_clean_cic_certificate(&lying.proof_obligations[0], "clean-kernel")
        .is_none()
        && contract_clean_cic_certificate_in(&lying, &lying.proof_obligations[0], "clean-kernel")
            .is_none();
    assert!(feature_check(
        "b2.gap.kernel_certifies_nat_nonneg_ignoring_bindings_and_ir_type",
        unmintable
            && sole_binding_refusal(&errors, "is not an unsigned integer")
            && lying_replayed.is_none()
            && value == Some(-1)
            && honest_errors.is_empty(),
        &format!(
            "closed upstream by 0aeae341: `fn b2_level() -> i64 {{ -1 }}` with `proved` ensures `(>= result 0)` [result: Int @ ResultSlot0]: unmintable={unmintable}; forged certificate => validate_module={errors:?}, replayed={lying_replayed:?}; interpreter returns {value:?}"
        ),
    ));

    // FLIPPED (closed upstream by 0aeae341, WS1.1, F-001). Change 2 (binding
    // side only, IR untouched = honest u64 body): `result` bound as Bool, a
    // rounding mode, a 64-bit bit-vector, or NOT AT ALL. Was: each minted,
    // re-checked and validated. Now: none is minted, and each forged
    // certificate is refused by exactly the binding rule's named reason.
    let mut measured = Vec::new();
    let mut all_refused = true;
    // Since WS1.2 (31814e51) a sort that is not a faithful reading of the u64
    // result (Bool, RoundingMode) ALSO draws the always-on summary refusal, beside
    // the kernel's; BitVec(64) is a faithful reading, and an empty list binds
    // nothing, so those two keep the kernel's refusal alone.
    // Since WS4.4 those two also draw the OBLIGATION half of the typing rule
    // (`InvalidObligationBinding` on the Postcondition row #0, whose formula
    // carries the same binding) — one named refusal per rule, exactly.
    for (binding, needle, summary) in [
        (
            Some(ClauseSort::Bool),
            "binding sort Bool is not Int",
            Some((
                "ensures clause 0 binding 'result' has sort Bool but ResultSlot 0 is u64",
                "binding \"result\" has sort Bool but ResultSlot 0 is u64",
            )),
        ),
        (
            Some(ClauseSort::RoundingMode),
            "binding sort RoundingMode is not Int",
            Some((
                "ensures clause 0 binding 'result' has sort RoundingMode but ResultSlot 0 is u64",
                "binding \"result\" has sort RoundingMode but ResultSlot 0 is u64",
            )),
        ),
        (Some(BV64), "binding sort BitVec(64) is not Int", None),
        (None, "carries 0 bindings", None),
    ] {
        let m = build_level(false, binding.clone());
        let errors = validate_module(&m);
        let unmintable =
            contract_clean_cic_certificate_in(&m, &m.proof_obligations[0], "clean-kernel")
                .is_none();
        let refused = match summary {
            None => sole_binding_refusal(&errors, needle),
            Some((detail, obligation_detail)) => {
                let (sort_rows, kernel_rows): (Vec<ValidationError>, Vec<ValidationError>) =
                    errors.iter().cloned().partition(|e| {
                        matches!(
                            e,
                            ValidationError::InvalidFunctionSummary { .. }
                                | ValidationError::InvalidObligationBinding { .. }
                        )
                    });
                matches!(
                    sort_rows.as_slice(),
                    [
                        ValidationError::InvalidFunctionSummary { function: 0, detail: d },
                        ValidationError::InvalidObligationBinding { obligation: 0, detail: o },
                    ] | [
                        ValidationError::InvalidObligationBinding { obligation: 0, detail: o },
                        ValidationError::InvalidFunctionSummary { function: 0, detail: d },
                    ] if d == detail && o == obligation_detail
                ) && sole_binding_refusal(&kernel_rows, needle)
            }
        };
        all_refused &= unmintable && refused;
        measured.push(format!(
            "{binding:?}: unmintable={unmintable} => {errors:?}"
        ));
    }
    assert!(feature_check(
        "b2.gap.kernel_certificate_ignores_clause_binding_sort",
        all_refused && honest_errors.is_empty(),
        &format!(
            "closed upstream by 0aeae341: honest `-> u64 {{ 7 }}` body, ensures `(>= result 0)`, `result` re-bound: {measured:?}"
        ),
    ));
}

/// FLIPPED (closed by WS1.14, F-013; wire v59) — the effect-summary /
/// state-epoch field. It was: `FunctionSummary` had no effects field and
/// `ClausePlace::World` was one payload-free place. Now
/// `FunctionSummary.effects` is the typed, body-checked frame and
/// `ClausePlace::WorldPre` / `WorldPost` are the world epochs (this module's
/// proved `b2_bump_into` binds its heap at `WorldPost`).
fn b2_11_gap_no_effect_summary_or_state_epoch() {
    let main = build_main();
    let m = &main.module;
    // `b2.gap.no_effect_summary_or_state_epoch_field` is a compile-time ratchet in
    // `field_ratchets.rs`, flipped to PASS there.

    // Related: the only effect carrier, FuncAttrs.readnone/readonly.
    // FLIPPED (closed upstream by WS2.7, 5f28fc7e, F-021): it was an unchecked
    // CLAIM; a defined body must now honour it. Twin: the function that
    // STORES through `out` stamped readnone+readonly is exactly ONE named
    // FuncAttrClaimViolated (`readnone`, the claim checked when both are set);
    // readonly alone names `readonly`. Mutation control: the same stamp on
    // `b2_is_zero` (an icmp, no memory effect) keeps the module valid, so the
    // rule refuses the store, not the attribute.
    let stamp = |f: FuncId, readnone: bool| {
        let mut twin = m.clone();
        let attrs = &mut twin.function_by_id_mut(f).unwrap().attrs;
        attrs.readnone = readnone;
        attrs.readonly = true;
        errors_with_stand_in(&twin)
    };
    let sole_violation = |errors: &[ValidationError], want: &str| {
        matches!(
            errors,
            [ValidationError::FuncAttrClaimViolated { function, attr, inst, .. }]
                if function == "b2_bump_into" && *attr == want && inst.starts_with("store")
        )
    };
    let both = stamp(main.bump, true);
    let readonly = stamp(main.bump, false);
    let control = stamp(main.is_zero, true);
    assert!(feature_check(
        "b2.gap.readnone_claim_on_a_storing_function_accepted",
        errors_with_stand_in(m).is_empty()
            && sole_violation(&both, "readnone")
            && sole_violation(&readonly, "readonly")
            && control.is_empty(),
        &format!(
            "closed upstream by 5f28fc7e: b2_bump_into executes `store u64, out, r`; stamped readnone+readonly => {both:?}; readonly alone => {readonly:?}; control b2_is_zero stamped readnone+readonly => {control:?}"
        ),
    ));
}

/// GAP — no RuntimeChecked / Unknown (/ Unsupported) discharge state.
/// Cause: `ProofStatus` is exactly five variants (TI/proof/obligations.rs:165-175).
/// Blocks: TRUST_IR_OBLIGATION_BIRTH §3 discharge slot
/// `Proved(cert) | RuntimeChecked | Unknown | Unsupported`.
fn b2_13_gap_no_runtime_checked_or_unknown_status() {
    let json_refused: Vec<String> = ["RuntimeChecked", "Unknown", "Unsupported"]
        .iter()
        .filter(|s| serde_json::from_str::<ProofStatus>(&format!("\"{s}\"")).is_err())
        .map(|s| s.to_string())
        .collect();
    let json_accepted: Vec<String> = ["Pending", "Discharged", "Failed", "Trusted", "Certified"]
        .iter()
        .filter(|s| serde_json::from_str::<ProofStatus>(&format!("\"{s}\"")).is_ok())
        .map(|s| s.to_string())
        .collect();

    // Binary: locate the status tag byte by differencing two one-obligation
    // modules, then write the first unassigned tag into it.
    let blob = |status: ProofStatus| {
        let mut m = Module::new("b2_status_probe");
        m.proof_obligations.push(ProofObligation::new(
            ProofId::new(0),
            ObligationKind::PanicFreedom,
            status,
            "probe",
        ));
        trust_ir::binary::serialize_module(&m).expect("serialize_module: test fixture")
    };
    let pending = blob(ProofStatus::Pending);
    let certified = blob(ProofStatus::Certified);
    assert_eq!(pending.len(), certified.len());
    let diff: Vec<usize> = (0..pending.len())
        .filter(|i| pending[*i] != certified[*i])
        .collect();
    assert_eq!(diff.len(), 1, "exactly the status tag differs: {diff:?}");
    let at = diff[0];
    let (lo, hi) = (pending[at], certified[at]);
    let mut forged = certified.clone();
    forged[at] = hi + 1;
    let decoded = trust_ir::binary::deserialize_module(&forged);
    assert!(feature_gap(
        "b2.gap.no_runtime_checked_or_unknown_status",
        Expect::refused("InvalidTag"),
        Outcome::of_result(&decoded).given(&[
            (
                "JSON refuses RuntimeChecked/Unknown/Unsupported",
                json_refused.len() == 3
            ),
            (
                "JSON accepts exactly the five statuses",
                json_accepted.len() == 5
            ),
            ("binary status tags are 0..=4", (lo, hi) == (0, 4)),
        ]),
        &format!(
            "ProofStatus JSON accepts {json_accepted:?}, refuses {json_refused:?}; binary status tags Pending={lo}..Certified={hi}, tag {} => {:?}",
            hi + 1,
            decoded.as_ref().err()
        ),
    ));
}

/// Validator holes found while building this area. Each is a ratchet on a
/// well-formed baseline + one change.
fn b2_14_gap_related_validator_holes() {
    let main = build_main();
    let base = main.module.clone();
    assert!(
        errors_with_stand_in(&base).is_empty(),
        "baseline must validate"
    );

    // (a) FLIPPED by WS1.8 rule (a), Failed half (F-018). The archived
    // ratchet recorded `GroundCertificateStatusInconsistent` as a dead
    // variant: a discharging certificate on a Pending OR Failed row validated.
    // WS1.8 revived it NARROWLY: the certificate on Failed#13 is refused by
    // exactly that variant, while the same certificate on Pending#5 stays
    // legal by design — it is the honest "evidence awaiting replay" carrier
    // (a solver payload the validator has no capability to replay yet).
    // Mutation control: the Pending half alone adds no error.
    let stamp = |ids: &[u32]| {
        let mut m = base.clone();
        for id in ids {
            m.proof_certificates.push(ProofCertificate {
                obligation: ProofId::new(*id),
                prover: "ay".into(),
                evidence: ProofEvidence::SmtProof(b"(proof unsat)".to_vec()),
                assurance: None,
            });
        }
        errors_with_stand_in(&m)
    };
    let both = stamp(&[5, 13]);
    let pending_only = stamp(&[5]);
    assert!(feature_check(
        "b2.gap.certificate_on_pending_or_failed_obligation_accepted",
        matches!(
            both.as_slice(),
            [ValidationError::GroundCertificateStatusInconsistent {
                obligation: 13,
                status: "Failed",
            }]
        ) && pending_only.is_empty(),
        &format!(
            "WS1.8 (a): SmtProof certificates on Pending#5 and Failed#13 => {both:?}; Pending#5 alone => {pending_only:?}"
        ),
    ));

    // (b) FLIPPED (closed upstream by 5a945757 "fix(validate): check
    // LandingPad/Invoke placement and B4 function scope"): the archived ratchet
    // recorded that a B4 `function` scope naming a function that does not
    // exist was accepted when no `site` accompanied it. A scope now resolves
    // to exactly one function (`ObligationFunctionScopeUnresolved`). PASS:
    // the dangling scope is refused by exactly that one variant, naming the
    // obligation, the id and "no such function". Mutation control: the same
    // obligation, still without a site, scoped to EVERY function the module
    // really has, adds no error (the rule refuses the dangling id, not
    // site-less scoping).
    let mut m = base.clone();
    m.proof_obligations[12].function = Some(FuncId::new(77));
    m.proof_obligations[12].site = None;
    let errors = errors_with_stand_in(&m);
    let baseline = errors_with_stand_in(&base);
    let controls: Vec<(FuncId, usize)> = base
        .functions
        .iter()
        .map(|f| {
            let mut c = base.clone();
            c.proof_obligations[12].function = Some(f.id);
            c.proof_obligations[12].site = None;
            (f.id, errors_with_stand_in(&c).len())
        })
        .collect();
    let refused_by_name = matches!(
        errors.as_slice(),
        [ValidationError::ObligationFunctionScopeUnresolved {
            obligation: 12,
            function: 77,
            reason,
        }] if *reason == "no such function"
    );
    assert!(feature_check(
        "b2.gap.dangling_function_scope_accepted",
        refused_by_name
            && baseline.is_empty()
            && !controls.is_empty()
            && controls.iter().all(|(_, n)| *n == 0),
        &format!(
            "closed upstream by 5a945757: obligation#12.function = Some(FuncId(77)) in a {}-function \
             module, site=None => errors={errors:?}; baseline errors={baseline:?}; mutation control \
             (scope = each real function, site=None) => error counts {controls:?}",
            base.functions.len()
        ),
    ));

    // (c) FLIPPED by WS1.8 rule (c) (F-018): a site is now related to the
    // obligation KIND through the kind->instruction table. BoundsCheck#15
    // re-sited onto the program's `ret` is refused by exactly
    // `ObligationSiteKindMismatch` naming the kind and the mnemonic. Mutation
    // control: the same row re-sited onto its own kind's admitted shape (the
    // `assert` #19 originally sat beside) adds nothing beyond the baseline.
    let mut m = base.clone();
    m.proof_obligations[15].site = base.proof_obligations[19].site;
    let errors = errors_with_stand_in(&m);
    let resited_kind = base.proof_obligations[15].kind.clone();
    assert!(feature_check(
        "b2.gap.site_not_related_to_obligation_kind",
        resited_kind == ObligationKind::BoundsCheck
            && matches!(
                errors.as_slice(),
                [ValidationError::ObligationSiteKindMismatch {
                    obligation: 15,
                    kind: "bounds_check",
                    op: "return",
                }]
            ),
        &format!(
            "WS1.8 (c): {resited_kind:?}#15 re-sited onto program's `ret` => errors={errors:?}"
        ),
    ));

    // (d) coverage: only `UnwindBounded` is ever re-derivable
    // (TB/validate.rs:8640-8654); an `Unbounded` claim citing a deductive
    // request is left UNDETERMINED, never agreed and never refused.
    let mut bundle = NativeVerificationBundle::new(
        NativeBundleProducer::TrustIr,
        NativeAdapterInput::TrustIrModule,
        base.stable_digest(),
        base.clone(),
        ProofLineageManifest::default(),
    );
    bundle.requests = main.requests.clone();
    let report = coverage_assurance_report(&base, Some(&bundle));
    assert!(feature_gap(
        "b2.gap.unbounded_coverage_claim_not_rederivable",
        Expect::measured("recorded=4 agreed=1 undetermined=3"),
        Outcome::measured(format!(
            "recorded={} agreed={} undetermined={}",
            report.recorded(),
            report.agreed(),
            report.undetermined()
        ))
        .given(&[("the report raises no error", report.errors().is_empty())]),
        &format!(
            "{} — Unbounded / ModelBounded / Unrecorded rows are carried but no bundle field re-derives them",
            report.summary()
        ),
    ));

    // (e) FLIPPED (closed upstream by WS1.6, c3819f64, F-010). A LOCAL
    // InheritedFromCallee composition from a kernel-Certified callee obligation
    // was DischargedWithoutCertificate under validate_module AND
    // validate_linked_module (only `external: Some` rows were admitted). Now the
    // validator admits it in-process into the Discharged tier, with no
    // capability. Baseline: #11 = Postcondition `(>= result 0)` scoped to the
    // callee b2_countdown, inheriting its Certified #6 (same kind, byte-identical
    // formula). Mutation control: a capability that admits every OTHER
    // non-kernel certificate but NOT #11's still validates the module, so the
    // admission is trust-ir's own, not the stand-in's.
    let structural = validate_module(&base);
    let no_imports = trust_ir_build::ModuleSet::new(std::iter::empty::<&Module>());
    let linked = trust_ir_build::validate_linked_module(
        &base,
        &no_imports,
        &trust_ir::proof::RejectingModuleProofAuthority,
    );
    let about_11 = |errors: &[ValidationError]| {
        errors.iter().any(|e| {
            matches!(
                e,
                ValidationError::DischargedWithoutCertificate { obligation: 11 }
                    | ValidationError::LocalInheritanceRestatementMismatch { .. }
                    | ValidationError::InheritedProofNotDischarged { .. }
                    | ValidationError::InheritedProofCalleeNotFound { .. }
                    | ValidationError::InheritedProofCalleeScopeMismatch { .. }
            )
        })
    };
    let inherit_ref = base
        .proof_certificates
        .iter()
        .find(|c| matches!(c.evidence, ProofEvidence::InheritedFromCallee { .. }))
        .expect("the baseline carries one inheritance certificate")
        .lineage_ref();
    let mut without_inherit = stand_in(&base);
    assert!(without_inherit.0.remove(&inherit_ref));
    let capability_minus_11 = validate_module_with_authority(&base, &without_inherit);
    assert!(feature_check(
        "b2.gap.local_inheritance_not_admitted_without_capability",
        !about_11(&structural) && !about_11(linked.errors()) && capability_minus_11.is_empty(),
        &format!(
            "closed upstream by c3819f64: Rust `program` relies on Clean `b2_countdown`'s kernel-certified #6 through #11; no error about #11 under validate_module ({} errors, the other capability-backed rows) or validate_linked_module(no imports, RejectingModuleProofAuthority) ({} errors); a capability omitting #11's certificate => {capability_minus_11:?}",
            structural.len(),
            linked.errors().len()
        ),
    ));

    // (e') FLIPPED (closed upstream by WS1.6, c3819f64, F-010). LOCAL
    // inheritance related the two obligations by nothing but the callee's
    // FuncId, so a restatement of another kind or formula, or owned by some
    // other function, left validate_module's error list byte-identical and a
    // capability admitting the row got []. Now the cross-crate restatement rule
    // runs on the local edge too: each single change of #11 draws exactly the
    // named LocalInheritanceRestatementMismatch (plus #11 left without
    // authority), EVEN WITH the stand-in admitting the certificate.
    assert_eq!(
        base.proof_obligations[11].formula,
        base.proof_obligations[6].formula
    );
    assert_eq!(
        base.proof_obligations[11].kind,
        base.proof_obligations[6].kind
    );
    let structural_baseline = structural.clone();
    let mismatch_only = |errors: &[ValidationError], needle: &str| {
        errors.iter().any(|e| {
            matches!(e, ValidationError::LocalInheritanceRestatementMismatch { certificate_obligation: 11, detail } if detail == needle)
        }) && errors.iter().all(|e| {
            matches!(
                e,
                ValidationError::LocalInheritanceRestatementMismatch { certificate_obligation: 11, .. }
                    | ValidationError::DischargedWithoutCertificate { obligation: 11 }
            )
        })
    };
    let mut refused = true;
    let mut measured = Vec::new();
    // `also`: since WS4.4 a re-scoped #11 has its clause bindings resolved in
    // its NEW owner, so an owner whose signature the binding cannot read also
    // draws exactly one `InvalidObligationBinding` naming that binding —
    // required when expected, refused when not.
    let mut probe = |label: &str, m: &Module, needle: String, also: Option<&str>| {
        let (binding_rows, admitted): (Vec<ValidationError>, Vec<ValidationError>) =
            errors_with_stand_in(m)
                .into_iter()
                .partition(|e| matches!(e, ValidationError::InvalidObligationBinding { .. }));
        let binding_ok = match also {
            None => binding_rows.is_empty(),
            Some(expected) => matches!(
                binding_rows.as_slice(),
                [ValidationError::InvalidObligationBinding { obligation: 11, detail }]
                    if detail == expected
            ),
        };
        let structural = validate_module(m);
        let ok = binding_ok
            && mismatch_only(&admitted, &needle)
            && structural != structural_baseline
            && structural.iter().any(|e| matches!(e, ValidationError::LocalInheritanceRestatementMismatch { certificate_obligation: 11, detail } if *detail == needle));
        refused &= ok;
        measured.push(format!(
            "{label}: ok={ok} stand-in => {admitted:?} + {binding_rows:?}"
        ));
    };
    let mut m = base.clone();
    m.proof_obligations[11].formula = Some(ProofFormula::smtlib2("(= result 12345)", "Bool"));
    probe(
        "formula := (= result 12345)",
        &m,
        "local restatement obligation #11 does not restate far obligation #6's formula".into(),
        None,
    );
    let mut m = base.clone();
    m.proof_obligations[11].formula = None;
    probe(
        "formula := None",
        &m,
        "local restatement obligation #11 carries no formula; an inherited claim must be stated, not implied".into(),
        None,
    );
    // #11 is sited on the callee's `ret`, where WS1.8 rule (c) refuses a
    // MemorySafety row on its own; the site-less intermediate (as for the
    // owner probes below) keeps the one refusal measured the restatement's.
    let mut m = base.clone();
    m.proof_obligations[11].site = None;
    assert!(
        errors_with_stand_in(&m).is_empty(),
        "site-less intermediate must validate"
    );
    m.proof_obligations[11].kind = ObligationKind::MemorySafety;
    probe(
        "kind := MemorySafety",
        &m,
        "local restatement obligation #11 has kind memory_safety, far obligation #6 has kind postcondition".into(),
        None,
    );
    for (label, owner, also) in [
        ("owner := program (the caller)", main.program, None),
        (
            "owner := b2_is_zero (no call edge to the callee)",
            main.is_zero,
            // `b2_is_zero` returns `bool`: #11's `result: Int` cannot read it.
            Some("binding \"result\" has sort Int but ResultSlot 0 is bool"),
        ),
    ] {
        let mut m = base.clone();
        m.proof_obligations[11].site = None;
        assert!(
            errors_with_stand_in(&m).is_empty(),
            "site-less intermediate must validate"
        );
        m.proof_obligations[11].function = Some(owner);
        probe(
            label,
            &m,
            format!(
                "local restatement obligation #11 is scoped to Some({}), not the callee declaration #{}",
                owner.index(),
                main.countdown.index()
            ),
            also,
        );
    }
    assert!(feature_check(
        "b2.gap.local_inheritance_restatement_unchecked",
        refused,
        &format!(
            "closed upstream by c3819f64: InheritedFromCallee{{callee: b2_countdown, obligation: #6, external: None}} on #11, one field changed each: {measured:?}"
        ),
    ));

    // (e'') FLIPPED by WS1.8 DECIDE 1A (F-018): `Trusted` is no longer a bare
    // label. The baseline's LoopInvariant#7 carries ProofEvidence::Trusted;
    // with that certificate removed the row is refused by exactly
    // `TrustedWithoutJustification` — faith must be attributed. `Trusted`
    // still never counts toward `proved` (b2.proved.twin_trusted_does_not_count)
    // and still fails `--forbid-trusted`; the rule grants nothing. Mutation
    // control: a blank justification is refused the same way, and the
    // baseline's non-blank one validates.
    let mut m = base.clone();
    let before = m.proof_certificates.len();
    m.proof_certificates
        .retain(|c| c.obligation != ProofId::new(7));
    let errors = errors_with_stand_in(&m);
    let mut blank = base.clone();
    for c in blank
        .proof_certificates
        .iter_mut()
        .filter(|c| c.obligation == ProofId::new(7))
    {
        c.evidence = ProofEvidence::Trusted(" ".into());
    }
    let blank_errors = errors_with_stand_in(&blank);
    assert!(feature_check(
        "b2.gap.trusted_status_needs_no_certificate",
        m.proof_certificates.len() + 1 == before
            && matches!(
                errors.as_slice(),
                [ValidationError::TrustedWithoutJustification { obligation: 7 }]
            )
            && matches!(
                blank_errors.as_slice(),
                [ValidationError::TrustedWithoutJustification { obligation: 7 }]
            ),
        &format!(
            "WS1.8 DECIDE 1A: LoopInvariant#7 status Trusted with its only certificate removed => errors={errors:?}; with a blank justification => {blank_errors:?}"
        ),
    ));

    // (g) FLIPPED by WS1.5 (F-009). The two COMPOSED entry points —
    // `validate_module_with_bundle` and `validate_module_for_codegen` — are
    // hard-wired to the structural tier, and until WS1.5 neither had a
    // capability-taking sibling, so a consumer holding a replay capability had
    // to re-compose the layers by hand. Now
    // `validate_module_with_bundle_with_authority` and
    // `validate_module_for_codegen_with(CodegenAdmission::with_authority)` take
    // the capability. PASS: under the stand-in both admit the b2 module (clean
    // under the authority tier, clean coverage report, clean codegen layers),
    // while the pinned entry points keep the structural floor (roadmap WS1.5
    // DECIDE 3: exactly validate_module's DischargedWithoutCertificate rows).
    // Negative twin: a capability that admits every non-kernel certificate
    // EXCEPT one — the single change — makes both new lanes refuse exactly
    // what `validate_module_with_authority` refuses under it, so the admission
    // is the capability's, obligation by obligation.
    let with_bundle = trust_ir_build::validate_module_with_bundle(&base, &bundle);
    let for_codegen = trust_ir_build::validate_module_for_codegen(&base);
    let capability = stand_in(&base);
    let bundle_lane = validate_module_with_bundle_with_authority(&base, &bundle, &capability);
    let codegen_lane = validate_module_for_codegen_with(
        &base,
        &CodegenAdmission::pinned().with_authority(&capability),
    );
    let withheld = base
        .proof_certificates
        .iter()
        .find(|c| {
            !matches!(c.evidence, ProofEvidence::CleanCic { .. })
                && base
                    .proof_obligations
                    .iter()
                    .any(|o| o.id == c.obligation && o.status == ProofStatus::Discharged)
        })
        .expect("the b2 module carries a capability-backed Discharged certificate")
        .lineage_ref();
    let mut partial = stand_in(&base);
    assert!(partial.0.remove(&withheld));
    let partial_authority = errors_with_stand_in_of(&base, &partial);
    let partial_bundle = validate_module_with_bundle_with_authority(&base, &bundle, &partial);
    let partial_codegen = validate_module_for_codegen_with(
        &base,
        &CodegenAdmission::pinned().with_authority(&partial),
    );
    let floor_kept = structural_baseline.len() == 11
        && structural
            .iter()
            .all(|e| matches!(e, ValidationError::DischargedWithoutCertificate { .. }))
        && with_bundle == structural_baseline
        && for_codegen == structural_baseline;
    let twin = !partial_authority.is_empty()
        && partial_bundle == partial_authority
        && partial_codegen == partial_authority;
    assert!(feature_check(
        "b2.gap.no_authority_taking_codegen_or_bundle_entry_point",
        errors_with_stand_in(&base).is_empty()
            && bundle_lane.is_empty()
            && codegen_lane.is_empty()
            && floor_kept
            && twin,
        &format!(
            "closed by WS1.5: with_bundle_with_authority(stand-in) => {bundle_lane:?}, for_codegen_with(stand-in) => {codegen_lane:?}; pinned floor kept: with_bundle => {} errors, for_codegen => {} errors, validate_module => {} DischargedWithoutCertificate rows; twin (one certificate withheld from the capability) => authority={partial_authority:?} bundle={partial_bundle:?} codegen={partial_codegen:?}",
            with_bundle.len(),
            for_codegen.len(),
            structural_baseline.len()
        ),
    ));

    // (f) RATIFIED-OUT by WS1.9 DECIDE A (F-011; docs/SPEC_RATIFICATIONS.md
    // §11). The kernel tier is closed to `decreases` BY DECISION: the contract
    // grounder grounds only Precondition/Postcondition/LoopInvariant/
    // RefinementType (`is_contract_kind`), and no well-founded-measure kernel
    // anchor is built now, so a Termination obligation — the row the
    // per-clause rule demands for every `decreases` clause, and which
    // `mint_summary_obligations` now mints — reaches `proved` only through a
    // consumer capability (ay / trust-mc) as `Discharged`, never `Certified`.
    // Ownership takes the same route. Held in its exact shape: a kernel
    // grounder that started certifying either kind would trip this row, and
    // needs the ratification amended first.
    let ground = |kind: ObligationKind| {
        let o = ProofObligation::new(ProofId::new(0), kind, ProofStatus::Certified, "ground")
            .with_formula(ProofFormula::smtlib2("(= 1 1)", "Bool"));
        contract_clean_cic_certificate(&o, "clean-kernel").is_some()
    };
    let baseline = ground(ObligationKind::Postcondition);
    let termination = ground(ObligationKind::Termination);
    let ownership = ground(ObligationKind::Ownership);
    assert!(feature_ratified(
        "b2.gap.termination_not_kernel_certifiable",
        Expect::measured("Postcondition=mintable Termination=unmintable Ownership=unmintable"),
        Outcome::measured(format!(
            "Postcondition={} Termination={} Ownership={}",
            if baseline { "mintable" } else { "unmintable" },
            if termination {
                "mintable"
            } else {
                "unmintable"
            },
            if ownership { "mintable" } else { "unmintable" },
        )),
        &format!(
            "contract_clean_cic_certificate on `(= 1 1)`: Postcondition={baseline}, Termination={termination}, Ownership={ownership}"
        ),
    ));
}

/// FLIPPED by WS4.4 (F-064, F-071) — canonical TEXT is now a carrier for this
/// area (b7 owns the general TEXT rows; these are the b2-specific
/// measurements). Before WS4.4:
///  (a) `parse_obligation_kind` had arms for the 13 pre-v41 kinds only, while
///      `Display` printed `termination` / `ownership` / `custom:<ns>/<name>`
///      — the writer emitted text its own parser refused;
///  (b) `FunctionSummary` (hence every clause binding, `proved`, `decreases`,
///      `backed_by`) had no text spelling at all;
///  (c) obligation clause bindings and certificate `assurance` were rebuilt
///      empty, so the text image of a VALID module was INVALID
///      (`CertifiedCleanCicLineageMismatch` on obligation #6).
/// WS4.2 turned each into a `#lossy` refusal; WS4.4 gives each a spelling.
/// Every row below is a PASS with a mutation-control twin: deleting the new
/// spelling from the printed text reproduces exactly the old loss.
fn b2_15_text_format() {
    let probe = |kind: ObligationKind| {
        let mut m = Module::new("b2_text_probe");
        m.proof_obligations.push(ProofObligation::new(
            ProofId::new(0),
            kind,
            ProofStatus::Pending,
            "probe",
        ));
        roundtrip_all(&m).text
    };
    // (a) every v41 kind round-trips EXACTLY; the diagnostic `custom:` form
    // is not module text and is refused (twin).
    let baseline = probe(ObligationKind::Liveness);
    assert!(baseline.lossless(), "baseline: {}", baseline.summary());
    let mut carried = Vec::new();
    for kind in [
        ObligationKind::Termination,
        ObligationKind::Ownership,
        ObligationKind::Custom {
            namespace: "trust.vc".into(),
            name: "k".into(),
        },
    ] {
        let trip = probe(kind.clone());
        if trip.lossless() && trip.decoded.as_ref().unwrap().proof_obligations[0].kind == kind {
            carried.push(kind.to_string());
        }
    }
    let custom = probe(ObligationKind::Custom {
        namespace: "trust.vc".into(),
        name: "k".into(),
    });
    let diagnostic = String::from_utf8_lossy(&custom.encoded).replacen(
        "custom(\"trust.vc\", \"k\")",
        "custom:trust.vc/k",
        1,
    );
    let diagnostic_refused = trust_ir::parser::parse_module(&diagnostic)
        .is_err_and(|e| e.to_string().contains("expected '(', got ':'"));
    assert!(feature_check(
        "b2.gap.text_cannot_parse_v41_obligation_kinds",
        carried.len() == 3 && diagnostic_refused,
        &format!(
            "Liveness and {carried:?} round-trip through text exactly (WS4.4: `termination`, \
             `ownership`, `custom(\"<ns>\", \"<name>\")`); the diagnostic `custom:trust.vc/k` \
             spelling is refused = {diagnostic_refused}"
        ),
    ));

    // (b) the summary, on the body-less backed declaration (no obligations).
    let decl = build_backed_declaration(Some(good_backing()));
    let text = roundtrip_all(&decl).text;
    let canon = trust_ir::format::canonicalize(&decl);
    let summary_kept = text
        .decoded
        .as_ref()
        .is_some_and(|back| back.functions[0].summary == canon.functions[0].summary);
    let printed = String::from_utf8_lossy(&text.encoded).into_owned();
    let stripped: String = printed
        .lines()
        .filter(|line| {
            ![
                "; #summary:",
                "; #requires:",
                "; #ensures:",
                "; #decreases:",
                "; #backed-by:",
            ]
            .iter()
            .any(|word| line.contains(word))
        })
        .map(|line| format!("{line}\n"))
        .collect();
    let dropped_is_lossy = trust_ir::parser::parse_module(&stripped)
        .is_ok_and(|back| back.functions[0].summary.is_none() && back != canon);
    assert!(feature_check(
        "b2.gap.text_drops_function_summary_and_bindings",
        text.lossless() && summary_kept && dropped_is_lossy,
        &format!(
            "{} ; decoded Function.summary == canonical (requires/ensures/params/proved/\
             backed_by + every ClauseBinding) = {summary_kept}; mutation control: the text \
             with its summary block deleted decodes to summary None = {dropped_is_lossy}",
            text.summary()
        ),
    ));

    // (c) the obligation / certificate tables of the FULL b2 module (the v41
    // kinds included, since WS4.4 parses them).
    let main = build_main();
    let m = main.module.clone();
    let text = roundtrip_all(&m).text;
    let canon = trust_ir::format::canonicalize(&m);
    let back = text
        .decoded
        .clone()
        .expect("the full b2 module decodes from text");
    let bound_rows = canon
        .proof_obligations
        .iter()
        .filter(|o| o.formula.as_ref().is_some_and(|f| !f.bindings.is_empty()))
        .count();
    let bindings_kept = back
        .proof_obligations
        .iter()
        .zip(&canon.proof_obligations)
        .all(|(b, c)| {
            b.formula.as_ref().map(|f| &f.bindings) == c.formula.as_ref().map(|f| &f.bindings)
        });
    let assured = canon
        .proof_certificates
        .iter()
        .filter(|c| c.assurance.is_some())
        .count();
    let assurance_kept = back
        .proof_certificates
        .iter()
        .zip(&canon.proof_certificates)
        .all(|(b, c)| b.assurance == c.assurance);
    let same_verdict = errors_with_stand_in(&back) == errors_with_stand_in(&canon);
    let lineage_kept = !errors_with_stand_in(&back).iter().any(|e| {
        matches!(
            e,
            ValidationError::CertifiedCleanCicLineageMismatch { obligation: 6 }
        )
    });
    // Mutation control: cut obligation #6's bind list from the printed text —
    // the pre-WS4.4 grammar's drop — and its kernel certificate no longer
    // binds (b2_04's rule, reached through the codec).
    let printed = String::from_utf8_lossy(&text.encoded).into_owned();
    let row6 = printed
        .lines()
        .find(|line| line.starts_with("obligation 6 "))
        .expect("obligation 6 is printed")
        .to_owned();
    // The bind list follows the formula; it ends at the next clause keyword
    // (`source`, `site`, `spec`) or at the end of the line.
    let formula_at = row6
        .find(" formula \"")
        .expect("obligation 6 carries a formula");
    let bind = formula_at
        + row6[formula_at..]
            .find(" bind \"")
            .expect("obligation 6's formula is bound");
    let rest = [" source \"", " site f", " spec \""]
        .iter()
        .filter_map(|keyword| row6[bind..].find(keyword).map(|at| bind + at))
        .min()
        .unwrap_or(row6.len());
    let unbound_row = format!("{}{}", &row6[..bind], &row6[rest..]);
    let unbound = trust_ir::parser::parse_module(&printed.replacen(&row6, &unbound_row, 1))
        .expect("the unbound text parses");
    let control_breaks = errors_with_stand_in(&unbound).iter().any(|e| {
        matches!(
            e,
            ValidationError::CertifiedCleanCicLineageMismatch { obligation: 6 }
        )
    });
    assert!(feature_check(
        "b2.gap.text_drops_obligation_bindings_and_certificate_assurance",
        // 8 bound rows, measured: the 7 pre-v41-kind rows the WS4.2 shape of
        // this test counted (it had to drop the v41 kinds to parse at all)
        // plus the bound v41-kind row now that text parses those kinds.
        text.lossless()
            && bound_rows == 8
            && bindings_kept
            && assured == 4
            && assurance_kept
            && same_verdict
            && lineage_kept
            && control_breaks,
        &format!(
            "{} ; obligation formulas with bindings: {bound_rows}, all kept = {bindings_kept}; \
             certificates with `assurance`: {assured}, all kept = {assurance_kept}; the text \
             image re-validates with the binary image's verdict = {same_verdict} (no \
             CertifiedCleanCicLineageMismatch{{6}} = {lineage_kept}); mutation control: obligation \
             #6's bind list cut from the text => CertifiedCleanCicLineageMismatch{{6}} = \
             {control_breaks}",
            text.summary()
        ),
    ));
    assert!(
        text.lossless(),
        "WS4.4: text is lossless for the b2 tables; a regression re-opens F-064"
    );
}

#[test]
fn two_language_b2() {
    common::run_target(
        "b2",
        &[
            (
                "b2_01_contract_surface_validates_roundtrips_and_runs",
                b2_01_contract_surface_validates_roundtrips_and_runs,
            ),
            (
                "b2_02_backed_by_declaration_and_every_clause_sort",
                b2_02_backed_by_declaration_and_every_clause_sort,
            ),
            (
                "b2_03_clause_binding_negative_twins",
                b2_03_clause_binding_negative_twins,
            ),
            (
                "b2_04_empty_bindings_are_a_different_claim",
                b2_04_empty_bindings_are_a_different_claim,
            ),
            (
                "b2_05_all_kinds_statuses_scope_and_site",
                b2_05_all_kinds_statuses_scope_and_site,
            ),
            (
                "b2_06_certificates_for_all_8_evidence_variants_and_assurance",
                b2_06_certificates_for_all_8_evidence_variants_and_assurance,
            ),
            (
                "b2_07_the_proved_counting_rule",
                b2_07_the_proved_counting_rule,
            ),
            (
                "b2_08_gap_no_per_clause_backref",
                b2_08_gap_no_per_clause_backref,
            ),
            (
                "b2_09_gap_clause_sort_unchecked_against_ir_type",
                b2_09_gap_clause_sort_unchecked_against_ir_type,
            ),
            (
                "b2_10_gap_kernel_certifies_nonneg_over_a_signed_result",
                b2_10_gap_kernel_certifies_nonneg_over_a_signed_result,
            ),
            (
                "b2_11_gap_no_effect_summary_or_state_epoch",
                b2_11_gap_no_effect_summary_or_state_epoch,
            ),
            (
                "b2_13_gap_no_runtime_checked_or_unknown_status",
                b2_13_gap_no_runtime_checked_or_unknown_status,
            ),
            (
                "b2_14_gap_related_validator_holes",
                b2_14_gap_related_validator_holes,
            ),
            ("b2_15_text_format", b2_15_text_format),
        ],
    );
}
