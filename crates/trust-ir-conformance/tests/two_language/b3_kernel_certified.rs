//! b3 — the KERNEL-CERTIFIED tier of the two-language plan.
//!
//! Subject: a `Producer::Clean` `UInt64` function (`addmul a b = a*b + a`, the
//! standalone-Lean envelope's body) carrying a `TranslationValidation`
//! obligation at `ProofStatus::Certified`, backed by `ProofEvidence::CleanCic`
//! under the `clean_backend_tv` anchor, which trust-ir-build re-checks
//! IN-PROCESS with the Clean kernel (`trust-ir-build` feature
//! `clean-tv-anchor`, default ON).
//!
//! Ported (roadmap WS8.6) from the archived Part B battery
//! `reports/2026-09-17-two-language-proof-program/partb/tests/b3_kernel_certified.rs`, measured there
//! at trust-ir 4efb21bc and re-measured at the port. Every row is checked against
//! `RATCHETS.tsv` (see `harness.rs`). `file:line` citations are relative to
//! `crates/` and date from 4efb21bc: re-locate them by name.
//! No proof claim is made about THIS test binary; the proof claim under test is
//! the one the in-process kernel (the clean-kernel rev the workspace pins) makes
//! about the certificate.
//!
//! How the certificate is minted here (and why it is not circular): the
//! comparand (`CleanCic.context`) is built INDEPENDENTLY, by hand, from the
//! SOURCE term `fun a b : Nat => ((a*b) % 2^64 + a) % 2^64` as a
//! `clean_kernel::Expr` — it is NOT read back from trust-ir's own denotation
//! of the emitted function (`trust_ir_build::certify_identity_lineage_rung`
//! does that; it is used below only as a cross-check and as the "does the
//! public minter also refuse" probe). The validator re-derives the emitted
//! side from the module (`validate.rs:15046`), constructs the statement itself
//! (`:15068`) and lets the kernel decide (`:15089`).
//!
//! All `validate.rs:N` citations are `trust-ir-build/src/validate.rs` at 4efb21bc.

mod common;

// The conformance corpus's fixture builders: the WS4.15 Lean-library-envelope
// rows below measure the SAME module the `lean_library_envelope` golden pins.
// The fixture generators (tests/generate.rs), compiled once as the library's
// `fixtures` module rather than again inside every test binary.
use trust_ir_conformance::fixtures as generate;

use common::{
    Expect, Outcome, feature_check, feature_gap, feature_ratified, roundtrip_all, run_nullary,
    run_with_args,
};
// `clean_kernel` through trust-ir-build's `#[doc(hidden)]` test-plumbing re-export: the
// ONE rev the workspace pins, and no pin leg of its own (roadmap WS8.6 step 3).
use trust_ir::constant::Constant;
use trust_ir::inst::{BinOp, CastOp, ICmpOp, Inst, SwitchCase};
use trust_ir::interpret::InterpretValue;
use trust_ir::proof::{
    ClauseBinding, ClausePlace, ClauseSort, CleanCicKernelRecheck, IslandEnvironment,
    KERNEL_ANCHOR_CLEAN_BACKEND_TV, KERNEL_ANCHOR_CLEAN_ISLAND, KERNEL_ANCHOR_CLEAN_ISLAND_MODULE,
    KERNEL_ANCHOR_FARKAS_CONSTRUCTIVE, KERNEL_ANCHOR_GIVEBACK_REFINEMENT, KERNEL_ANCHOR_SLACKCERTZ,
    KERNEL_ANCHOR_TRUSTCG_LOWERING_RESOLUTION, ObligationKind, ProofCertificate, ProofEvidence,
    ProofFormula, ProofLineageId, ProofObligation, ProofStatus, ProofTransform,
    ProofTransformStage, RejectingModuleProofAuthority, SourceDefinitionRef,
    clean_cic_lineage_digest, encode_clean_expr_v1, encode_island_declarations_v1,
};
use trust_ir::ty::{EnumDef, EnumVariant, Ty};
use trust_ir::value::{EnumId, ProofId};
use trust_ir::{BodyGate, FuncId, Module, Producer};
use trust_ir_build::clean_kernel::env::{Declaration, Environment};
use trust_ir_build::clean_kernel::{BinderInfo, Expr, Level, Name};
use trust_ir_build::{
    ModuleBuilder, ModuleSet, ValidationError, certify_identity_lineage_rung,
    certify_identity_lineage_rung_island_bound, certify_island_theorem, validate_linked_module,
    validate_module, validate_module_for_codegen, validate_module_report,
    validate_module_with_authority,
};

const TV_MODULE: &str = "CleanCompiler.BackendTV";
/// The authority string the Clean producer stamps on a body it certified
/// (clean-compiler `emit_trust_ir_tv.rs:145` at the pinned rev).
const CLEAN_KERNEL_TV_AUTHORITY: &str = "clean-kernel-tv";
/// The evidence-free Clean license (not in `EVIDENCE_BOUND_GATE_AUTHORITIES`),
/// worn by a Clean body the module carries no TV certificate for.
const DIRECT_LANE_AUTHORITY: &str = "trust-direct-lane-structural";

// ---------------------------------------------------------------------------
// Kernel-term vocabulary (the SOURCE side, built by hand)
// ---------------------------------------------------------------------------

fn nat() -> Expr {
    Expr::const_str("Nat")
}

fn app2(f: &str, a: Expr, b: Expr) -> Expr {
    Expr::apps(Expr::const_str(f), [a, b])
}

fn modulus(width: u32) -> Expr {
    match width {
        64 => Expr::nat_lit_u128(1u128 << 64),
        w => Expr::nat_lit(1u64 << w),
    }
}

/// `e % 2^w` — how a Lean `UIntN` operation reads at `Nat`.
fn wmod(e: Expr, width: u32) -> Expr {
    app2("Nat.mod", e, modulus(width))
}

/// `fun (x1 .. xn : Nat) => body`.
fn lam_nat(arity: usize, body: Expr) -> Expr {
    (0..arity).fold(body, |acc, _| Expr::lam(BinderInfo::Default, nat(), acc))
}

/// `forall (x1 .. xn : Nat), body`.
fn pi_nat(arity: usize, body: Expr) -> Expr {
    (0..arity).fold(body, |acc, _| Expr::pi(BinderInfo::Default, nat(), acc))
}

fn eq_nat(lhs: Expr, rhs: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
        [nat(), lhs, rhs],
    )
}

fn refl_nat(e: Expr) -> Expr {
    Expr::apps(
        Expr::const_(
            Name::from_string("Eq.refl"),
            vec![Level::succ(Level::zero())],
        ),
        [nat(), e],
    )
}

/// `Bool.rec.{1} (fun _ => Nat) else then cond` — `if cond then t else e` at Nat.
fn ite_nat(cond: Expr, then_e: Expr, else_e: Expr) -> Expr {
    let motive = Expr::lam(BinderInfo::Default, Expr::const_str("Bool"), nat());
    Expr::apps(
        Expr::const_(
            Name::from_string("Bool.rec"),
            vec![Level::succ(Level::zero())],
        ),
        [motive, else_e, then_e, cond],
    )
}

/// SOURCE body of `addmul (a b : UIntW) := a * b + a` over the telescope
/// `fun a b` (a = bvar 1, b = bvar 0).
fn addmul_source_body(width: u32) -> Expr {
    let a = || Expr::bvar(1);
    let b = || Expr::bvar(0);
    wmod(
        app2("Nat.add", wmod(app2("Nat.mul", a(), b()), width), a()),
        width,
    )
}

/// WRONG source: `a * b + b`.
fn addmul_wrong_source_body(width: u32) -> Expr {
    let a = || Expr::bvar(1);
    let b = || Expr::bvar(0);
    wmod(
        app2("Nat.add", wmod(app2("Nat.mul", a(), b()), width), b()),
        width,
    )
}

// ---------------------------------------------------------------------------
// Module fixtures
// ---------------------------------------------------------------------------

/// `[Clean] addmul(a, b) = a*b + a` at `ty`, plus `[TRust] program() =
/// addmul(6, 7)` when `with_rust_caller`. `second_op` is the body's second
/// BinOp (Add in the honest module).
fn addmul_module(ty: Ty, with_rust_caller: bool) -> (Module, FuncId) {
    let mut mb = ModuleBuilder::new("b3_kernel_certified");
    let binary = mb.add_func_type(vec![ty.clone(), ty.clone()], vec![ty.clone()]);
    let nullary = mb.add_func_type(vec![], vec![ty.clone()]);
    let addmul = {
        let mut fb = mb.function("addmul", binary);
        fb.set_producer(Producer::Clean);
        fb.set_display_path("Envelope.addmul");
        fb.set_body_gate(BodyGate::Gated {
            authority: CLEAN_KERNEL_TV_AUTHORITY.into(),
            evidence: None,
        });
        let entry = fb.create_block();
        let a = fb.add_block_param(entry, ty.clone());
        let b = fb.add_block_param(entry, ty.clone());
        fb.switch_to_block(entry);
        let ab = fb.mul(ty.clone(), a, b);
        let out = fb.add(ty.clone(), ab, a);
        fb.ret(vec![out]);
        fb.build()
    };
    if with_rust_caller {
        let mut fb = mb.function("program", nullary);
        fb.set_producer(Producer::TRust);
        fb.set_display_path("app::program");
        fb.set_body_gate(BodyGate::Gated {
            authority: "trust-verify".into(),
            evidence: None,
        });
        let entry = fb.create_block();
        fb.switch_to_block(entry);
        let six = fb.uconst(ty.clone(), 6);
        let seven = fb.uconst(ty.clone(), 7);
        let out = fb.call(addmul, vec![six, seven]);
        fb.ret(vec![out]);
        fb.build();
    }
    (
        mb.build().expect("ModuleBuilder::build: test fixture"),
        addmul,
    )
}

/// The obligation exactly as the Clean producer shapes it
/// (clean-compiler `emit_trust_ir_tv.rs:569-585`: no formula, function-scoped,
/// no site — TV certifies the function as a whole).
fn tv_obligation(id: u32, func: FuncId, name: &str, width: u32) -> ProofObligation {
    ProofObligation::new(
        ProofId::new(id),
        ObligationKind::TranslationValidation,
        ProofStatus::Certified,
        format!(
            "backend translation validation: '{name}' denotes its Clean definition \
             (mod 2^{width}, kernel-decided)"
        ),
    )
    .with_function(func)
}

fn tv_certificate(
    obligation: &ProofObligation,
    func_name: &str,
    comparand: &Expr,
    proof: &Expr,
) -> ProofCertificate {
    ProofCertificate {
        obligation: obligation.id,
        prover: "clean-backend-tv".to_string(),
        evidence: ProofEvidence::CleanCic {
            term: encode_clean_expr_v1(proof).expect("proof term encodes"),
            context: encode_clean_expr_v1(comparand).expect("comparand encodes"),
            lineage: clean_cic_lineage_digest(obligation),
            kernel_recheck: Some(CleanCicKernelRecheck {
                module: TV_MODULE.to_string(),
                theorems: vec![format!("CleanTV.{func_name}.denotes")],
                anchor: KERNEL_ANCHOR_CLEAN_BACKEND_TV.to_string(),
                allowed_axioms: vec![],
                binding: None,
            }),
        },
        assurance: None,
    }
}

/// Attach an obligation + certificate whose comparand is `fun x1..xn => body`
/// and whose proof is `fun x1..xn => Eq.refl Nat body`.
fn attach_tv(module: &mut Module, func: FuncId, arity: usize, width: u32, body: Expr) -> u32 {
    let name = module
        .function_by_id(func)
        .expect("function exists")
        .name
        .clone();
    let id = u32::try_from(module.proof_obligations.len()).unwrap();
    let obligation = tv_obligation(id, func, &name, width);
    let certificate = tv_certificate(
        &obligation,
        &name,
        &lam_nat(arity, body.clone()),
        &lam_nat(arity, refl_nat(body)),
    );
    module.proof_obligations.push(obligation);
    module.proof_certificates.push(certificate);
    id
}

fn certified_addmul(ty: Ty, width: u32, with_rust_caller: bool) -> (Module, FuncId) {
    let (mut module, addmul) = addmul_module(ty, with_rust_caller);
    attach_tv(&mut module, addmul, 2, width, addmul_source_body(width));
    (module, addmul)
}

/// `Some(reason)` iff `errors` is EXACTLY ONE
/// `CertifiedCleanCicKernelRecheckFailed` for `obligation`.
fn sole_recheck_refusal(errors: &[ValidationError], obligation: u32) -> Option<&str> {
    match errors {
        [
            ValidationError::CertifiedCleanCicKernelRecheckFailed {
                obligation: got,
                reason,
            },
        ] if *got == obligation => Some(reason.as_str()),
        _ => None,
    }
}

/// `true` iff `errors` is EXACTLY ONE kernel-recheck refusal for `obligation`
/// AND the refusal is the KERNEL's own judgment on the re-derived equation
/// (validate.rs:15095-15101) — not a decode / relevance / fragment refusal.
fn sole_kernel_rejection(errors: &[ValidationError], obligation: u32, func_name: &str) -> bool {
    sole_recheck_refusal(errors, obligation).is_some_and(|r| {
        r.contains(&format!(
            "in-process kernel REJECTED the translation-validation equation for '{func_name}'"
        ))
    })
}

/// The CODEGEN lane's form of [`sole_kernel_rejection`] (roadmap WS1.5): the
/// structural pass's kernel rejection, then the license follow-on — the body
/// still wears `Gated{clean-kernel-tv}`, whose evidence is a
/// `clean_backend_tv` certificate that THIS pass must have kernel-replayed,
/// and a rejected recheck (which also empties the all-or-nothing kernel tier)
/// replayed nothing, so the license is refused by name.
fn kernel_rejection_revokes_license(
    errors: &[ValidationError],
    obligation: u32,
    func_name: &str,
    function: FuncId,
) -> bool {
    match errors {
        [
            rejection,
            ValidationError::GatedWithoutEvidence {
                function: f,
                authority,
                detail,
            },
        ] => {
            sole_kernel_rejection(std::slice::from_ref(rejection), obligation, func_name)
                && *f == function.index()
                && authority == CLEAN_KERNEL_TV_AUTHORITY
                && detail.contains("was not kernel-replayed in this validation pass")
        }
        _ => false,
    }
}

fn identity_rung(
    module: &Module,
    obligation: u32,
    func: FuncId,
) -> Result<(ProofObligation, ProofCertificate), String> {
    certify_identity_lineage_rung(
        module,
        ProofLineageId::new(0),
        ProofId::new(obligation),
        ProofTransform::new(
            ProofTransformStage::Frontend,
            "identity",
            "partb-b3",
            "1.0.0",
        ),
        func,
    )
    .map(|(_node, obligation, certificate)| (obligation, certificate))
}

fn mul_to_add(module: &mut Module, func: FuncId) {
    let f = module.function_by_id_mut(func).expect("function exists");
    let hit = f.blocks[0]
        .body
        .iter_mut()
        .find_map(|node| match &mut node.inst {
            Inst::BinOp { op, .. } if *op == BinOp::Mul => Some(op),
            _ => None,
        })
        .expect("fixture has a Mul");
    *hit = BinOp::Add;
}

fn u64v(v: u64) -> InterpretValue {
    InterpretValue::int(Ty::U64, i128::from(v)).unwrap()
}

fn first_u128(r: &Result<Vec<InterpretValue>, String>) -> Option<u128> {
    r.as_ref()
        .ok()
        .and_then(|v| v.first())
        .and_then(common::as_u128)
}

// ===========================================================================
// PASS — the certified function, and its mutation control
// ===========================================================================

fn b3_addmul_is_kernel_certified_and_mul_to_add_is_refused() {
    let (module, addmul) = certified_addmul(Ty::U64, 64, true);

    // Shape: Clean producer, TranslationValidation / Certified / CleanCic /
    // clean_backend_tv, function-scoped.
    let f = module.function_by_id(addmul).unwrap();
    let o = &module.proof_obligations[0];
    let c = &module.proof_certificates[0];
    let shape_ok = f.producer == Some(Producer::Clean)
        && o.kind == ObligationKind::TranslationValidation
        && o.status == ProofStatus::Certified
        && o.function == Some(addmul)
        && matches!(
            &c.evidence,
            ProofEvidence::CleanCic { kernel_recheck: Some(r), term, context, .. }
                if r.anchor == KERNEL_ANCHOR_CLEAN_BACKEND_TV
                    && r.module == TV_MODULE
                    && r.theorems == ["CleanTV.addmul.denotes"]
                    && r.allowed_axioms.is_empty()
                    && !term.is_empty()
                    && !context.is_empty()
        );
    assert!(feature_check(
        "b3.addmul.shape",
        shape_ok,
        &format!(
            "producer={:?} obligation={{kind:{:?},status:{:?},function:{:?}}} evidence=CleanCic \
             anchor={KERNEL_ANCHOR_CLEAN_BACKEND_TV}",
            f.producer, o.kind, o.status, o.function
        ),
    ));

    // The in-process kernel re-check ACCEPTS, on every entry point.
    let structural = validate_module(&module);
    assert!(feature_check(
        "b3.addmul.validate_module",
        structural.is_empty(),
        &format!(
            "validate_module (clean-kernel 61c10a67 in-process, comparand built from the SOURCE \
             term, not from trust-ir's denotation) errors={structural:?}"
        ),
    ));
    let authority = validate_module_with_authority(&module, &RejectingModuleProofAuthority);
    assert!(feature_check(
        "b3.addmul.validate_module_with_authority",
        authority.is_empty(),
        &format!(
            "validate_module_with_authority(RejectingModuleProofAuthority) — the capability \
             replays NOTHING, so Certified is earned by the kernel alone; errors={authority:?}"
        ),
    ));
    let report = validate_module_report(&module);
    let replayed = report.replayed_certificate_refs().map(|r| r.len());
    assert!(feature_check(
        "b3.addmul.kernel_tier_ref",
        replayed == Some(1),
        &format!("ModuleValidationReport::replayed_certificate_refs().len() = {replayed:?}"),
    ));
    let codegen = validate_module_for_codegen(&module);
    assert!(feature_check(
        "b3.addmul.codegen_license",
        codegen.is_empty(),
        &format!("validate_module_for_codegen (Gated{{clean-kernel-tv}}) errors={codegen:?}"),
    ));

    // REVIEW ADDITION — the closest license twin: the SAME kernel-certified body
    // stamped `Ungated`. The certificate still re-checks (structural pass is
    // clean), and the license layer ALONE refuses — a Certified TV obligation
    // does not license a body the producer affirmatively left ungated.
    let mut ungated = module.clone();
    ungated.function_by_id_mut(addmul).unwrap().body_gate = Some(BodyGate::Ungated);
    let structural_ungated = validate_module(&ungated);
    let codegen_ungated = validate_module_for_codegen(&ungated);
    assert!(feature_check(
        "b3.addmul.codegen_license.negative_twin.ungated_certified_body",
        structural_ungated.is_empty()
            && matches!(
                codegen_ungated.as_slice(),
                [ValidationError::UngatedBodyForCodegen { name, .. }] if name == "addmul"
            ),
        &format!(
            "same certified body, body_gate Gated->Ungated: validate_module={structural_ungated:?} \
             validate_module_for_codegen={codegen_ungated:?}"
        ),
    ));

    // REVIEW ADDITION — the linked (closure-walking) entry point, the strictest
    // one a consumer has: no imports, an EMPTY resolver, a capability that
    // replays nothing. linked.rs:300.
    let resolver = ModuleSet::default();
    let linked = validate_linked_module(&module, &resolver, &RejectingModuleProofAuthority);
    let linked_refs = linked.replayed_certificate_refs().map(|r| r.len());
    assert!(feature_check(
        "b3.addmul.validate_linked_module",
        linked.is_ok() && linked_refs == Some(1),
        &format!(
            "validate_linked_module(empty ModuleSet, RejectingModuleProofAuthority) errors={:?} \
             kernel-tier refs={linked_refs:?}",
            linked.errors()
        ),
    ));

    // Cross-check: the comparand built by hand from the source term is
    // byte-identical to what trust-ir's own public identity-rung minter derives
    // from the EMITTED function — i.e. the two sides really are the same term.
    let (_, identity_cert) = identity_rung(&module, 9, addmul).expect("in fragment");
    let same_comparand = match (
        &identity_cert.evidence,
        &module.proof_certificates[0].evidence,
    ) {
        (
            ProofEvidence::CleanCic {
                context: theirs,
                term: their_term,
                ..
            },
            ProofEvidence::CleanCic {
                context: ours,
                term: our_term,
                ..
            },
        ) => theirs == ours && their_term == our_term,
        _ => false,
    };
    assert!(feature_check(
        "b3.addmul.source_term_equals_emitted_denotation",
        same_comparand,
        "hand-built source comparand/proof bytes == certify_identity_lineage_rung's bytes \
         (validate.rs:9408) for the emitted function",
    ));

    // Executes through both languages: TRust program() -> Clean addmul.
    let program = run_nullary(&module, "program");
    assert!(feature_check(
        "b3.addmul.interpret.rust_calls_certified_clean",
        first_u128(&program) == Some(48),
        &format!("program() = addmul(6,7) = {program:?}"),
    ));
    let wrapped = run_with_args(&module, "addmul", vec![u64v(u64::MAX), u64v(2)]);
    let expect = u128::from(u64::MAX.wrapping_mul(2).wrapping_add(u64::MAX));
    assert!(feature_check(
        "b3.addmul.interpret.wrapping",
        first_u128(&wrapped) == Some(expect),
        &format!("addmul(u64::MAX,2) = {wrapped:?}, UInt64 wrapping expects {expect}"),
    ));

    // ---- NEGATIVE TWIN (the design's mutation control): mul -> add in the
    // body, SAME certificate. validate.rs:15089-15102.
    let mut miscompiled = module.clone();
    mul_to_add(&mut miscompiled, addmul);
    let errors = validate_module(&miscompiled);
    let reason = sole_recheck_refusal(&errors, 0);
    let twin = reason.is_some_and(|r| {
        r.contains("in-process kernel REJECTED the translation-validation equation for 'addmul'")
            && r.contains("signature (Nat64, Nat64) -> Nat64, arity 2")
    });
    assert!(feature_check(
        "b3.addmul.negative_twin.mul_to_add",
        twin,
        &format!("body Mul->Add under the unchanged certificate => {errors:?}"),
    ));
    // ... and the same refusal on the authority entry point, with no kernel-tier ref.
    let errors = validate_module_with_authority(&miscompiled, &RejectingModuleProofAuthority);
    let no_refs = validate_module_report(&miscompiled)
        .replayed_certificate_refs()
        .is_none();
    assert!(feature_check(
        "b3.addmul.negative_twin.mul_to_add.authority",
        sole_kernel_rejection(&errors, 0, "addmul") && no_refs,
        &format!("validate_module_with_authority => {errors:?}; replayed refs withheld={no_refs}"),
    ));
    // ... and on the codegen entry point: the structural pass's kernel
    // re-check, then (since WS1.5) the license follow-on — the body still
    // wears Gated{clean-kernel-tv}, and its certificate was not replayed.
    let errors = validate_module_for_codegen(&miscompiled);
    assert!(feature_check(
        "b3.addmul.negative_twin.mul_to_add.codegen",
        kernel_rejection_revokes_license(&errors, 0, "addmul", addmul),
        &format!("validate_module_for_codegen => {errors:?}"),
    ));
    // REVIEW ADDITION — ... and on the linked entry point.
    let linked = validate_linked_module(&miscompiled, &resolver, &RejectingModuleProofAuthority);
    assert!(feature_check(
        "b3.addmul.negative_twin.mul_to_add.linked",
        sole_kernel_rejection(linked.errors(), 0, "addmul")
            && linked.replayed_certificate_refs().is_none(),
        &format!("validate_linked_module => {:?}", linked.errors()),
    ));
    // The interpreter agrees the mutation is a real miscompile (6+7+6 = 19).
    let program = run_nullary(&miscompiled, "program");
    assert!(feature_check(
        "b3.addmul.negative_twin.mul_to_add.is_observable",
        first_u128(&program) == Some(19),
        &format!("miscompiled program() = {program:?} (honest = 48)"),
    ));
}

/// Every other way to forge the certificate is refused for its OWN reason.
fn b3_certificate_forgeries_are_each_refused_for_the_right_reason() {
    let (good, addmul) = certified_addmul(Ty::U64, 64, false);
    assert!(validate_module(&good).is_empty(), "baseline must certify");

    // (1) wrong SOURCE comparand (a*b + b) with an honest-looking refl proof.
    let (mut m, f) = addmul_module(Ty::U64, false);
    attach_tv(&mut m, f, 2, 64, addmul_wrong_source_body(64));
    let e = validate_module(&m);
    assert!(feature_check(
        "b3.forgery.wrong_source_comparand",
        sole_recheck_refusal(&e, 0).is_some_and(|r| r.contains("in-process kernel REJECTED")),
        &format!("comparand a*b+b vs emitted a*b+a => {e:?}"),
    ));

    // (2) right comparand, proof term proves a DIFFERENT proposition
    //     (Eq.refl of the wrong body).
    let (mut m, f) = addmul_module(Ty::U64, false);
    let obligation = tv_obligation(0, f, "addmul", 64);
    let cert = tv_certificate(
        &obligation,
        "addmul",
        &lam_nat(2, addmul_source_body(64)),
        &lam_nat(2, refl_nat(addmul_wrong_source_body(64))),
    );
    m.proof_obligations.push(obligation);
    m.proof_certificates.push(cert);
    let e = validate_module(&m);
    assert!(feature_check(
        "b3.forgery.wrong_proof_term",
        sole_recheck_refusal(&e, 0).is_some_and(|r| r.contains("in-process kernel REJECTED")),
        &format!("proof = refl of another term => {e:?}"),
    ));

    // (3) undecodable proof bytes. validate.rs:15060.
    let mut m = good.clone();
    if let ProofEvidence::CleanCic { term, .. } = &mut m.proof_certificates[0].evidence {
        *term = vec![0xde, 0xad, 0xbe, 0xef];
    }
    let e = validate_module(&m);
    assert!(feature_check(
        "b3.forgery.undecodable_term",
        sole_recheck_refusal(&e, 0)
            .is_some_and(|r| r.contains("`term` does not decode to a kernel Expr")),
        &format!("{e:?}"),
    ));

    // (4) cites another function's theorem. validate.rs:15034.
    let mut m = good.clone();
    if let ProofEvidence::CleanCic {
        kernel_recheck: Some(r),
        ..
    } = &mut m.proof_certificates[0].evidence
    {
        r.theorems = vec!["CleanTV.other.denotes".into()];
    }
    let e = validate_module(&m);
    assert!(feature_check(
        "b3.forgery.wrong_theorem_name",
        sole_recheck_refusal(&e, 0).is_some_and(|r| r.contains("TV relevance mismatch")),
        &format!("{e:?}"),
    ));

    // (5) anchor <-> module pair is validator-owned. validate.rs:12495.
    let mut m = good.clone();
    if let ProofEvidence::CleanCic {
        kernel_recheck: Some(r),
        ..
    } = &mut m.proof_certificates[0].evidence
    {
        r.module = "Envelope".into();
    }
    let e = validate_module(&m);
    assert!(feature_check(
        "b3.forgery.wrong_anchor_module",
        sole_recheck_refusal(&e, 0)
            .is_some_and(|r| r.contains("requires canonical module 'CleanCompiler.BackendTV'")),
        &format!("{e:?}"),
    ));

    // (6) certificate replayed onto an edited obligation: lineage digest binds
    //     the obligation content. validate.rs:12454.
    let mut m = good.clone();
    m.proof_obligations[0].description.push_str(" (edited)");
    let e = validate_module(&m);
    assert!(feature_check(
        "b3.forgery.lineage_mismatch",
        matches!(
            e.as_slice(),
            [ValidationError::CertifiedCleanCicLineageMismatch { obligation: 0 }]
        ),
        &format!("{e:?}"),
    ));

    // (7) Certified with no CleanCic at all (a Trusted note instead).
    let mut m = good.clone();
    m.proof_certificates[0].evidence = ProofEvidence::Trusted("clean said so".into());
    let e = validate_module(&m);
    assert!(feature_check(
        "b3.forgery.certified_without_clean_cic",
        matches!(
            e.as_slice(),
            [ValidationError::CertifiedWithoutCleanCic { obligation: 0 }]
        ),
        &format!("{e:?}"),
    ));

    // (8) no owning function: the LHS cannot be re-derived. validate.rs:15014.
    //     (lineage re-minted so the ONLY defect is the missing scope.)
    let mut m = good.clone();
    m.proof_obligations[0].function = None;
    let digest = clean_cic_lineage_digest(&m.proof_obligations[0]);
    if let ProofEvidence::CleanCic { lineage, .. } = &mut m.proof_certificates[0].evidence {
        *lineage = digest;
    }
    let e = validate_module(&m);
    assert!(feature_check(
        "b3.forgery.unscoped_obligation",
        sole_recheck_refusal(&e, 0).is_some_and(|r| r.contains("carries no function")),
        &format!("{e:?}"),
    ));

    // (9) the TV anchor cannot launder another obligation KIND. validate.rs:12580.
    let mut m = good.clone();
    m.proof_obligations[0].kind = ObligationKind::PanicFreedom;
    let digest = clean_cic_lineage_digest(&m.proof_obligations[0]);
    if let ProofEvidence::CleanCic { lineage, .. } = &mut m.proof_certificates[0].evidence {
        *lineage = digest;
    }
    let e = validate_module(&m);
    assert!(feature_check(
        "b3.forgery.tv_anchor_on_other_kind",
        sole_recheck_refusal(&e, 0)
            .is_some_and(|r| r.contains("may only certify TranslationValidation obligations")),
        &format!("{e:?}"),
    ));

    // (10) EMPTY proof term: content-free evidence never counts as a CleanCic
    //      (validate.rs:12435-12444), so the row reads as "Certified with no
    //      CleanCic at all" — not as a lineage match.
    let mut m = good.clone();
    if let ProofEvidence::CleanCic { term, .. } = &mut m.proof_certificates[0].evidence {
        term.clear();
    }
    let e = validate_module(&m);
    assert!(feature_check(
        "b3.forgery.empty_term",
        matches!(
            e.as_slice(),
            [ValidationError::CertifiedWithoutCleanCic { obligation: 0 }]
        ),
        &format!("{e:?}"),
    ));

    // (11) a valid proof term followed by ONE trailing byte: each Expr carrier
    //      must be consumed completely (clean_expr_codec), so nothing can be
    //      spliced behind an honest payload.
    let mut m = good.clone();
    if let ProofEvidence::CleanCic { term, .. } = &mut m.proof_certificates[0].evidence {
        term.push(0);
    }
    let e = validate_module(&m);
    assert!(feature_check(
        "b3.forgery.trailing_byte_after_term",
        sole_recheck_refusal(&e, 0)
            .is_some_and(|r| r.contains("`term` does not decode to a kernel Expr")),
        &format!("{e:?}"),
    ));
    let mut m = good.clone();
    if let ProofEvidence::CleanCic { context, .. } = &mut m.proof_certificates[0].evidence {
        context.push(0);
    }
    let e = validate_module(&m);
    assert!(feature_check(
        "b3.forgery.trailing_byte_after_comparand",
        sole_recheck_refusal(&e, 0)
            .is_some_and(|r| r.contains("`context` does not decode to a kernel Expr")),
        &format!("{e:?}"),
    ));

    // (12) comparand over the WRONG telescope (one binder for a binary
    //      function). validate.rs:14942-14948.
    let (mut m, f) = addmul_module(Ty::U64, false);
    let obligation = tv_obligation(0, f, "addmul", 64);
    let unary = wmod(app2("Nat.add", Expr::bvar(0), Expr::bvar(0)), 64);
    let cert = tv_certificate(
        &obligation,
        "addmul",
        &lam_nat(1, unary.clone()),
        &lam_nat(1, refl_nat(unary)),
    );
    m.proof_obligations.push(obligation);
    m.proof_certificates.push(cert);
    let e = validate_module(&m);
    assert!(feature_check(
        "b3.forgery.comparand_arity_mismatch",
        sole_recheck_refusal(&e, 0).is_some_and(|r| r.contains("arity mismatch, REJECTED")),
        &format!("{e:?}"),
    ));

    // (13) TWO theorems cited (the honest one plus a rider). validate.rs:15028.
    let mut m = good.clone();
    if let ProofEvidence::CleanCic {
        kernel_recheck: Some(r),
        ..
    } = &mut m.proof_certificates[0].evidence
    {
        r.theorems.push("CleanTV.rider.denotes".into());
    }
    let e = validate_module(&m);
    assert!(feature_check(
        "b3.forgery.two_theorems_cited",
        sole_recheck_refusal(&e, 0)
            .is_some_and(|r| r.contains("TV certificate must cite exactly one theorem")),
        &format!("{e:?}"),
    ));

    // (14) a "proof" that ASSUMES its conclusion through a constant the ground
    //      prelude does not declare: `fun a b => Oracle.trust_me`. The kernel
    //      has no such constant, so the theorem cannot be declared.
    let (mut m, f) = addmul_module(Ty::U64, false);
    let obligation = tv_obligation(0, f, "addmul", 64);
    let cert = tv_certificate(
        &obligation,
        "addmul",
        &lam_nat(2, addmul_source_body(64)),
        &lam_nat(2, Expr::const_str("Oracle.trust_me")),
    );
    m.proof_obligations.push(obligation);
    m.proof_certificates.push(cert);
    let e = validate_module(&m);
    assert!(feature_check(
        "b3.forgery.proof_cites_undeclared_constant",
        sole_kernel_rejection(&e, 0, "addmul"),
        &format!("{e:?}"),
    ));

    // (15) a producer-listed `allowed_axioms` entry buys nothing: the honest
    //      proof uses no axiom, and a proof that USES one the prelude lacks is
    //      still refused even when the producer "allows" it.
    let (mut m, f) = addmul_module(Ty::U64, false);
    let obligation = tv_obligation(0, f, "addmul", 64);
    let mut cert = tv_certificate(
        &obligation,
        "addmul",
        &lam_nat(2, addmul_source_body(64)),
        &lam_nat(2, Expr::const_str("Oracle.trust_me")),
    );
    if let ProofEvidence::CleanCic {
        kernel_recheck: Some(r),
        ..
    } = &mut cert.evidence
    {
        r.allowed_axioms = vec!["Oracle.trust_me".into()];
    }
    m.proof_obligations.push(obligation);
    m.proof_certificates.push(cert);
    let e = validate_module(&m);
    assert!(feature_check(
        "b3.forgery.allowed_axioms_cannot_admit_an_oracle",
        sole_kernel_rejection(&e, 0, "addmul"),
        &format!("{e:?}"),
    ));
    let _ = addmul;
}

/// The kernel DECIDES the equation (definitional equality), it does not
/// byte-compare two serialisations.
fn b3_kernel_decides_rather_than_byte_compares() {
    // (a) a `let`-shaped source term — `let t := (a*b) % M; (t + a) % M` — is
    //     NOT syntactically the emitted denotation, but is def-eq to it (zeta).
    let (mut m, f) = addmul_module(Ty::U64, false);
    let t = wmod(app2("Nat.mul", Expr::bvar(1), Expr::bvar(0)), 64);
    // under the let binder: t = bvar 0, a = bvar 2.
    let let_body = Expr::let_named(
        Name::from_string("t"),
        nat(),
        t,
        wmod(app2("Nat.add", Expr::bvar(0), Expr::bvar(2)), 64),
        false,
    );
    let obligation = tv_obligation(0, f, "addmul", 64);
    // proof: refl of the FLAT (emitted-side) form; statement's RHS is the let form.
    let cert = tv_certificate(
        &obligation,
        "addmul",
        &lam_nat(2, let_body.clone()),
        &lam_nat(2, refl_nat(addmul_source_body(64))),
    );
    let flat_bytes = encode_clean_expr_v1(&lam_nat(2, addmul_source_body(64))).unwrap();
    let let_bytes = encode_clean_expr_v1(&lam_nat(2, let_body)).unwrap();
    m.proof_obligations.push(obligation);
    m.proof_certificates.push(cert);
    let e = validate_module(&m);
    assert!(feature_check(
        "b3.kernel_decides.let_shaped_source",
        e.is_empty() && flat_bytes != let_bytes,
        &format!(
            "comparand bytes differ from the emitted denotation ({} vs {} B) yet the kernel \
             accepts by zeta/def-eq; errors={e:?}",
            let_bytes.len(),
            flat_bytes.len()
        ),
    ));

    // (b) a CLOSED term: `[Clean] k() = 6*7 + 6` certified against the literal
    //     48 — the kernel COMPUTES (Nat.mul/Nat.add/Nat.mod at 2^64) and agrees
    //     with the reference interpreter; 49 is refused.
    let build = || {
        let mut mb = ModuleBuilder::new("b3_closed");
        let nullary = mb.add_func_type(vec![], vec![Ty::U64]);
        let mut fb = mb.function("k", nullary);
        fb.set_producer(Producer::Clean);
        fb.set_body_gate(BodyGate::Gated {
            authority: CLEAN_KERNEL_TV_AUTHORITY.into(),
            evidence: None,
        });
        let entry = fb.create_block();
        fb.switch_to_block(entry);
        let six = fb.uconst(Ty::U64, 6);
        let seven = fb.uconst(Ty::U64, 7);
        let p = fb.mul(Ty::U64, six, seven);
        let out = fb.add(Ty::U64, p, six);
        fb.ret(vec![out]);
        let k = fb.build();
        (mb.build().expect("ModuleBuilder::build: test fixture"), k)
    };
    let certify_against = |literal: u64| {
        let (mut m, k) = build();
        let obligation = tv_obligation(0, k, "k", 64);
        let cert = tv_certificate(
            &obligation,
            "k",
            &Expr::nat_lit(literal),
            &refl_nat(Expr::nat_lit(literal)),
        );
        m.proof_obligations.push(obligation);
        m.proof_certificates.push(cert);
        m
    };
    let good = certify_against(48);
    let e = validate_module(&good);
    let ran = run_nullary(&good, "k");
    assert!(feature_check(
        "b3.kernel_decides.closed_term_computes",
        e.is_empty() && first_u128(&ran) == Some(48),
        &format!("kernel accepts `k = 48` by reduction; interpreter k() = {ran:?}; errors={e:?}"),
    ));
    let bad = validate_module(&certify_against(49));
    assert!(feature_check(
        "b3.kernel_decides.closed_term_negative_twin",
        sole_recheck_refusal(&bad, 0).is_some_and(|r| r.contains("in-process kernel REJECTED")),
        &format!("`k = 49` => {bad:?}"),
    ));
}

/// The fragment as it stands at HEAD is wider than "Add/Sub/Mul": all four
/// unsigned widths, an `ICmp`+`CondBr` diamond (Fragment-3a) and a
/// compositional call (Fragment-3b) certify. These are the WELL-FORMED
/// BASELINES the GAP ratchets below are derived from.
fn b3_fragment_baselines_certify() {
    for (ty, width) in [(Ty::U8, 8), (Ty::U16, 16), (Ty::U32, 32), (Ty::U64, 64)] {
        let (m, f) = certified_addmul(ty.clone(), width, false);
        let e = validate_module(&m);
        let mut bad = m.clone();
        mul_to_add(&mut bad, f);
        let refused = validate_module(&bad);
        assert!(feature_check(
            &format!("b3.width.u{width}"),
            e.is_empty()
                && sole_kernel_rejection(&refused, 0, "addmul")
                && sole_recheck_refusal(&refused, 0).is_some_and(|r| r.contains(&format!(
                    "signature (Nat{width}, Nat{width}) -> Nat{width}, arity 2"
                ))),
            &format!(
                "addmul at {ty} certified={}, Mul->Add twin => {refused:?}",
                e.is_empty()
            ),
        ));
    }

    // Fragment-3a: min(a,b) as a diamond; twin = swapped arms.
    let (mut m, f) = min_diamond();
    attach_tv(&mut m, f, 2, 64, min_source_body());
    let e = validate_module(&m);
    let lo = run_with_args(&m, "umin", vec![u64v(3), u64v(9)]);
    let mut swapped = m.clone();
    if let Some(Inst::CondBr {
        then_target,
        else_target,
        ..
    }) = swapped.function_by_id_mut(f).unwrap().blocks[0]
        .body
        .last_mut()
        .map(|n| &mut n.inst)
    {
        std::mem::swap(then_target, else_target);
    }
    let refused = validate_module(&swapped);
    let rt = roundtrip_all(&m);
    assert!(feature_check(
        "b3.fragment3a.condbr_diamond",
        e.is_empty()
            && first_u128(&lo) == Some(3)
            && rt.lossless_production()
            && sole_kernel_rejection(&refused, 0, "umin"),
        &format!(
            "umin = if a<b then a else b certified={}; umin(3,9)={lo:?}; {}; swapped-arm twin => \
             {refused:?}",
            e.is_empty(),
            rt.summary()
        ),
    ));

    // Fragment-3b: [Clean] twice(a,b) = addmul(addmul(a,b), b) — the callee is
    // an opaque `Nat -> Nat -> Nat` symbol bound OUTSIDE the params.
    let (mut m, addmul, twice) = composition_module();
    attach_tv(&mut m, addmul, 2, 64, addmul_source_body(64));
    {
        // telescope: fun (G : Nat->Nat->Nat) (a b : Nat) => G (G a b) b
        let g = || Expr::bvar(2);
        let body = Expr::apps(
            g(),
            [
                Expr::apps(g(), [Expr::bvar(1), Expr::bvar(0)]),
                Expr::bvar(0),
            ],
        );
        let g_ty = Expr::arrow(nat(), Expr::arrow(nat(), nat()));
        let close = |inner: Expr| Expr::lam(BinderInfo::Default, g_ty.clone(), lam_nat(2, inner));
        let obligation = tv_obligation(1, twice, "twice", 64);
        let cert = tv_certificate(
            &obligation,
            "twice",
            &close(body.clone()),
            &close(refl_nat(body)),
        );
        m.proof_obligations.push(obligation);
        m.proof_certificates.push(cert);
        // Since WS1.4 (795f57f8) every call edge of a Certified TV caller must
        // be grounded by exactly one `InheritedFromCallee` row citing the
        // callee's own kernel-rechecked TV obligation.
        m.proof_certificates.push(inherited_tv(1, addmul, 0));
    }
    let e = validate_module(&m);
    let ran = run_with_args(&m, "twice", vec![u64v(6), u64v(7)]);
    // twin: the caller passes (a, a) to the inner call instead of (a, b).
    let mut bad = m.clone();
    if let Some(Inst::Call { args, .. }) = bad.function_by_id_mut(twice).unwrap().blocks[0]
        .body
        .first_mut()
        .map(|n| &mut n.inst)
    {
        args[1] = args[0];
    }
    let refused = validate_module(&bad);
    // The kernel's rejection of `twice`, plus ONE named follow-on: a failed
    // Certified recheck empties the kernel tier (all-or-nothing), so the
    // grounding row's cited `addmul` obligation is no longer discharged.
    let (follow_ons, kernel_part): (Vec<ValidationError>, Vec<ValidationError>) =
        refused.iter().cloned().partition(|x| {
            matches!(
                x,
                ValidationError::InheritedProofNotDischarged {
                    obligation: 1,
                    inherited_obligation: 0,
                    ..
                }
            )
        });
    assert!(feature_check(
        "b3.fragment3b.compositional_call",
        e.is_empty()
            && first_u128(&ran) == Some(48 * 7 + 48)
            && follow_ons.len() == 1
            && sole_kernel_rejection(&kernel_part, 1, "twice"),
        &format!(
            "twice certified over an opaque callee symbol: errors={e:?}; twice(6,7)={ran:?}; \
             miscompiled-argument twin => {refused:?}"
        ),
    ));
}

/// `umin(a,b) = if a < b then a else b` as the Fragment-3a diamond.
fn min_diamond() -> (Module, FuncId) {
    let mut mb = ModuleBuilder::new("b3_min");
    let binary = mb.add_func_type(vec![Ty::U64, Ty::U64], vec![Ty::U64]);
    let mut fb = mb.function("umin", binary);
    fb.set_producer(Producer::Clean);
    fb.set_body_gate(BodyGate::Gated {
        authority: CLEAN_KERNEL_TV_AUTHORITY.into(),
        evidence: None,
    });
    let entry = fb.create_block();
    let then_b = fb.create_block();
    let else_b = fb.create_block();
    let a = fb.add_block_param(entry, Ty::U64);
    let b = fb.add_block_param(entry, Ty::U64);
    fb.switch_to_block(entry);
    let c = fb.icmp(ICmpOp::Ult, Ty::U64, a, b);
    fb.condbr(c, then_b, vec![], else_b, vec![]);
    fb.switch_to_block(then_b);
    fb.ret(vec![a]);
    fb.switch_to_block(else_b);
    fb.ret(vec![b]);
    let f = fb.build();
    (mb.build().expect("ModuleBuilder::build: test fixture"), f)
}

fn min_source_body() -> Expr {
    ite_nat(
        app2("Nat.blt", Expr::bvar(1), Expr::bvar(0)),
        Expr::bvar(1),
        Expr::bvar(0),
    )
}

fn composition_module() -> (Module, FuncId, FuncId) {
    let mut mb = ModuleBuilder::new("b3_compose");
    let binary = mb.add_func_type(vec![Ty::U64, Ty::U64], vec![Ty::U64]);
    mb.set_default_producer(Producer::Clean);
    let addmul = {
        let mut fb = mb.function("addmul", binary);
        fb.set_body_gate(BodyGate::Gated {
            authority: CLEAN_KERNEL_TV_AUTHORITY.into(),
            evidence: None,
        });
        let entry = fb.create_block();
        let a = fb.add_block_param(entry, Ty::U64);
        let b = fb.add_block_param(entry, Ty::U64);
        fb.switch_to_block(entry);
        let ab = fb.mul(Ty::U64, a, b);
        let out = fb.add(Ty::U64, ab, a);
        fb.ret(vec![out]);
        fb.build()
    };
    let twice = {
        let mut fb = mb.function("twice", binary);
        fb.set_body_gate(BodyGate::Gated {
            authority: CLEAN_KERNEL_TV_AUTHORITY.into(),
            evidence: None,
        });
        let entry = fb.create_block();
        let a = fb.add_block_param(entry, Ty::U64);
        let b = fb.add_block_param(entry, Ty::U64);
        fb.switch_to_block(entry);
        let inner = fb.call(addmul, vec![a, b]);
        let outer = fb.call(addmul, vec![inner, b]);
        fb.ret(vec![outer]);
        fb.build()
    };
    (
        mb.build().expect("ModuleBuilder::build: test fixture"),
        addmul,
        twice,
    )
}

/// The certificate survives the three production transports and RE-CERTIFIES
/// after decoding (the kernel runs again on the decoded bytes).
fn b3_certificate_round_trips_and_recertifies() {
    let (module, addmul) = certified_addmul(Ty::U64, 64, true);
    let rt = roundtrip_all(&module);
    assert!(feature_check(
        "b3.roundtrip.production",
        rt.lossless_production(),
        &rt.summary(),
    ));
    assert!(feature_check(
        "b3.roundtrip.wire_version",
        rt.binary_version == 41,
        &format!(
            "writer selected v{} (body_gate/display_path are v41 surface; CleanCic itself is \
             pre-v41)",
            rt.binary_version
        ),
    ));
    for trip in [&rt.binary, &rt.json, &rt.msgpack] {
        let decoded = trip.decoded.as_ref().expect("decoded");
        let ok = validate_module(decoded);
        let mut bad = decoded.clone();
        mul_to_add(&mut bad, addmul);
        let refused = validate_module(&bad);
        assert!(feature_check(
            &format!("b3.roundtrip.recertifies.{}", trip.format),
            ok.is_empty() && sole_kernel_rejection(&refused, 0, "addmul"),
            &format!(
                "decoded-from-{} module: kernel re-check errors={ok:?}; Mul->Add twin on the \
                 decoded module => refused={}",
                trip.format,
                sole_kernel_rejection(&refused, 0, "addmul")
            ),
        ));
    }

    // FLIPPED by WS4.4 (F-070), formerly a GAP: canonical TEXT dropped
    // `CleanCic.kernel_recheck` (display.rs never printed it and the parser
    // rebuilt `None`), so a Certified TV module did not survive the text
    // format — the decoded module was REFUSED; WS4.2 then refused the text at
    // print time (`#lossy: kernel-recheck(obligation 0)`). Text now CARRIES
    // the directive as a trailing `recheck module .. anchor .. theorems [..]
    // axioms [..]` clause, so the text image re-certifies in-process exactly
    // like the three production transports, and its Mul->Add twin is refused
    // by the kernel.
    let text = &rt.text;
    let decoded = text.decoded.as_ref();
    let recheck_kept = decoded.is_some_and(|m| {
        matches!(
            &m.proof_certificates[0].evidence,
            ProofEvidence::CleanCic { kernel_recheck: Some(_), term, context, .. }
                if !term.is_empty() && !context.is_empty()
        )
    });
    let errors = decoded.map(validate_module).unwrap_or_default();
    let twin_refused = decoded.is_some_and(|m| {
        let mut bad = m.clone();
        mul_to_add(&mut bad, addmul);
        sole_kernel_rejection(&validate_module(&bad), 0, "addmul")
    });
    assert!(feature_check(
        "b3.gap.text_drops_kernel_recheck",
        text.lossless() && recheck_kept && errors.is_empty() && twin_refused,
        &format!(
            "text round trip {} carries kernel_recheck = {recheck_kept}; the decoded module \
             re-certifies (errors={errors:?}); its Mul->Add twin is kernel-refused = \
             {twin_refused}",
            text.summary()
        ),
    ));

    // Sole-cause control (roadmap WS4.4 mutation control 1): print, then cut
    // ONLY the `recheck` clause from the certificate line — what the pre-WS4.4
    // grammar did. The decoded module fails
    // `CertifiedCleanCicKernelRecheckFailed`, and restoring only the directive
    // re-certifies it, so the carried clause is what keeps the module
    // Certified and nothing else the text format did to it.
    let printed = String::from_utf8_lossy(&text.encoded).into_owned();
    let cut = printed
        .find(" recheck module ")
        .expect("the certificate line spells its recheck clause");
    let end = cut + printed[cut..].find('\n').expect("line end");
    let dropped = format!("{}{}", &printed[..cut], &printed[end..]);
    let without = trust_ir::parser::parse_module(&dropped).expect("the cut text parses");
    let cut_refused = matches!(
        validate_module(&without).as_slice(),
        [ValidationError::CertifiedCleanCicKernelRecheckFailed { reason, .. }]
            if reason.contains("carries no kernel-recheck directive")
    );
    let directive = match &module.proof_certificates[0].evidence {
        ProofEvidence::CleanCic { kernel_recheck, .. } => kernel_recheck.clone(),
        _ => None,
    };
    let mut restored = without.clone();
    if let ProofEvidence::CleanCic { kernel_recheck, .. } =
        &mut restored.proof_certificates[0].evidence
    {
        *kernel_recheck = directive;
    }
    let e = validate_module(&restored);
    assert!(feature_check(
        "b3.gap.text_drops_kernel_recheck.sole_cause_control",
        cut_refused && e.is_empty(),
        &format!(
            "text with ONLY the recheck clause cut => CertifiedCleanCicKernelRecheckFailed = \
             {cut_refused}; that module with ONLY `kernel_recheck` restored re-certifies \
             in-process; errors={e:?}"
        ),
    ));
}

// ===========================================================================
// GAP ratchets — the edge of the `clean_backend_tv` fragment
// ===========================================================================

/// One fragment-edge probe. `module` must be WELL-FORMED without the
/// certificate; with an honest-looking certificate attached the ONLY error must
/// be the kernel-recheck refusal whose reason contains every `needles` entry;
/// the public minter must refuse for the same reason; nothing reaches the
/// kernel tier.
#[allow(clippy::too_many_arguments)]
fn fragment_edge(
    id: &str,
    mut module: Module,
    func: FuncId,
    arity: usize,
    width: u32,
    source_body: Expr,
    needles: &[&str],
    cite: &str,
) {
    let wellformed = validate_module(&module);
    assert!(
        wellformed.is_empty(),
        "{id}: the probe module must be well-formed WITHOUT the certificate: {wellformed:?}"
    );
    let minter = identity_rung(&module, 0, func);
    let minter_refuses = minter
        .as_ref()
        .err()
        .is_some_and(|r| needles.iter().all(|n| r.contains(n)));
    attach_tv(&mut module, func, arity, width, source_body);
    let errors = validate_module(&module);
    let no_kernel_tier = validate_module_report(&module)
        .replayed_certificate_refs()
        .is_none();
    assert!(feature_gap(
        id,
        Expect::refused_with("CertifiedCleanCicKernelRecheckFailed", needles),
        Outcome::of(&errors).given(&[
            (
                "the public minter refuses for the same reason",
                minter_refuses
            ),
            ("nothing reaches the kernel tier", no_kernel_tier),
        ]),
        &format!(
            "never certified: validate_module => {errors:?}; certify_identity_lineage_rung => \
             {:?}; [{cite}]",
            minter.as_ref().err()
        ),
    ));
}

fn clean_fn<'a>(
    mb: &'a mut ModuleBuilder,
    name: &str,
    sig: trust_ir::FuncTyId,
) -> trust_ir_build::FunctionBuilder<'a> {
    let mut fb = mb.function(name, sig);
    fb.set_producer(Producer::Clean);
    // The honest demotion: no kernel-tv license is claimed for these bodies.
    fb.set_body_gate(BodyGate::Ungated);
    fb
}

// ---------------------------------------------------------------------------
// FLIPPED by WS1.15 (F-015): the widened `clean_backend_tv` fragment
// ---------------------------------------------------------------------------
//
// Each archived `b3.gap.*` fragment-edge row below is now a PASS: the honest
// certificate — comparand built BY HAND from the source term, never read back
// from trust-ir's denotation — certifies in-process, and its negative twin
// (a miscompile under the unchanged certificate) is refused by the kernel's
// own judgment. `b3.gap.width.{u128,usize}` stay GAP by ruling (§2.2.1: no
// bignum scalar; a pointer-width integer has no width without a target).

fn app1(f: &str, a: Expr) -> Expr {
    Expr::app(Expr::const_str(f), a)
}

/// `fun (x1 : T1) .. (xn : Tn) => body` over named kernel sorts.
fn lam_sorted(binders: &[&str], body: Expr) -> Expr {
    binders.iter().rev().fold(body, |acc, t| {
        Expr::lam(BinderInfo::Default, Expr::const_str(t), acc)
    })
}

fn refl_at(sort: &str, e: Expr) -> Expr {
    Expr::apps(
        Expr::const_(
            Name::from_string("Eq.refl"),
            vec![Level::succ(Level::zero())],
        ),
        [Expr::const_str(sort), e],
    )
}

/// `attach_tv` over a SORTED telescope: binder sorts `binders`, `Eq` at
/// `result`.
fn attach_tv_sorted(
    module: &mut Module,
    func: FuncId,
    binders: &[&str],
    result: &str,
    width: u32,
    body: Expr,
) -> u32 {
    let name = module
        .function_by_id(func)
        .expect("function exists")
        .name
        .clone();
    let id = u32::try_from(module.proof_obligations.len()).unwrap();
    let obligation = tv_obligation(id, func, &name, width);
    let certificate = tv_certificate(
        &obligation,
        &name,
        &lam_sorted(binders, body.clone()),
        &lam_sorted(binders, refl_at(result, body)),
    );
    module.proof_obligations.push(obligation);
    module.proof_certificates.push(certificate);
    id
}

/// One flipped fragment-edge row. The probe is well-formed, executes as
/// `runs` says, certifies under the hand-built `source` (kernel-tier), and
/// its `twin` (a body edit under the SAME certificate) is refused by the
/// kernel's own judgment with nothing reaching the kernel tier.
#[allow(clippy::too_many_arguments)]
fn flipped_edge(
    id: &str,
    mut module: Module,
    func: FuncId,
    binders: &[&str],
    result: &str,
    width: u32,
    source: Expr,
    twin: impl FnOnce(&mut Module),
    cite: &str,
) {
    let wellformed = validate_module(&module);
    assert!(
        wellformed.is_empty(),
        "{id}: the probe module must be well-formed WITHOUT the certificate: {wellformed:?}"
    );
    let minted = identity_rung(&module, 0, func).is_ok();
    attach_tv_sorted(&mut module, func, binders, result, width, source);
    let honest = validate_module(&module);
    let strict = validate_module_with_authority(&module, &RejectingModuleProofAuthority);
    let refs = validate_module_report(&module)
        .replayed_certificate_refs()
        .map(|r| r.len());
    let name = module.function_by_id(func).expect("func").name.clone();
    let mut twinned = module.clone();
    twin(&mut twinned);
    let twin_errors = validate_module(&twinned);
    let twin_refused = sole_kernel_rejection(&twin_errors, 0, &name)
        && validate_module_report(&twinned)
            .replayed_certificate_refs()
            .is_none();
    assert!(feature_check(
        id,
        minted && honest.is_empty() && strict.is_empty() && refs == Some(1) && twin_refused,
        &format!(
            "FLIPPED by WS1.15: public minter accepts={minted}; honest certificate => \
             validate_module={honest:?} with_authority={strict:?} kernel-tier refs={refs:?}; \
             negative twin => {twin_errors:?}; [{cite}]"
        ),
    ));
}

fn set_icmp(module: &mut Module, func: FuncId, to: ICmpOp) {
    for block in &mut module.function_by_id_mut(func).expect("f").blocks {
        for node in &mut block.body {
            if let Inst::ICmp { op, .. } = &mut node.inst {
                *op = to;
            }
        }
    }
}

fn set_binop(module: &mut Module, func: FuncId, to: BinOp) {
    for block in &mut module.function_by_id_mut(func).expect("f").blocks {
        for node in &mut block.body {
            if let Inst::BinOp { op, .. } = &mut node.inst {
                *op = to;
            }
        }
    }
}

fn b3_gap_bool_result_has_no_tv_rule() {
    // Baseline (certifies): `ult_flag(a,b) = if a < b then 1 else 0 : UInt64`.
    let (mut base, f) = {
        let mut mb = ModuleBuilder::new("b3_ult_flag");
        let sig = mb.add_func_type(vec![Ty::U64, Ty::U64], vec![Ty::U64]);
        let mut fb = clean_fn(&mut mb, "ult_flag", sig);
        let entry = fb.create_block();
        let t = fb.create_block();
        let e = fb.create_block();
        let a = fb.add_block_param(entry, Ty::U64);
        let b = fb.add_block_param(entry, Ty::U64);
        fb.switch_to_block(entry);
        let c = fb.icmp(ICmpOp::Ult, Ty::U64, a, b);
        fb.condbr(c, t, vec![], e, vec![]);
        fb.switch_to_block(t);
        let one = fb.uconst(Ty::U64, 1);
        fb.ret(vec![one]);
        fb.switch_to_block(e);
        let zero = fb.uconst(Ty::U64, 0);
        fb.ret(vec![zero]);
        let f = fb.build();
        (mb.build().expect("ModuleBuilder::build: test fixture"), f)
    };
    let cmp = || app2("Nat.blt", Expr::bvar(1), Expr::bvar(0));
    attach_tv(
        &mut base,
        f,
        2,
        64,
        ite_nat(cmp(), Expr::nat_lit(1), Expr::nat_lit(0)),
    );
    let e = validate_module(&base);
    assert!(feature_check(
        "b3.gap.bool_result.baseline_certifies",
        e.is_empty(),
        &format!("UInt64-valued comparison diamond certifies; errors={e:?}"),
    ));

    // FLIPPED (WS1.15 S1): the comparison itself, at `Ty::Bool`
    // (Lean `def ult (a b : UInt64) : Bool := a < b`) — the statement is
    // `∀ a b : Nat, ⟦ult⟧ = Nat.blt a b` at `Eq Bool` (DG-34: Lean `Bool`).
    // Twin: `ult` → `ule`.
    let mut mb = ModuleBuilder::new("b3_ult_bool");
    let sig = mb.add_func_type(vec![Ty::U64, Ty::U64], vec![Ty::Bool]);
    let mut fb = clean_fn(&mut mb, "ult", sig);
    let entry = fb.create_block();
    let a = fb.add_block_param(entry, Ty::U64);
    let b = fb.add_block_param(entry, Ty::U64);
    fb.switch_to_block(entry);
    let c = fb.icmp(ICmpOp::Ult, Ty::U64, a, b);
    fb.ret(vec![c]);
    let f = fb.build();
    let module = mb.build().expect("ModuleBuilder::build: test fixture");
    let ran = run_with_args(&module, "ult", vec![u64v(3), u64v(9)]);
    assert_eq!(
        ran.as_ref()
            .ok()
            .and_then(|v| v.first())
            .and_then(|v| v.as_bool()),
        Some(true),
        "the Bool-returning function is a real, executable program: {ran:?}"
    );
    flipped_edge(
        "b3.gap.bool_result",
        module,
        f,
        &["Nat", "Nat"],
        "Bool",
        64,
        cmp(),
        |m| set_icmp(m, f, ICmpOp::Ule),
        "WS1.15 S1: Bool result sort",
    );

    // FLIPPED (WS1.15 S1): Bool on the PARAMETER side (a connective):
    // `band(p,q) = p && q` = `Bool.and p q` over `Bool` binders. Twin: `&&` → `||`.
    let mut mb = ModuleBuilder::new("b3_band");
    let sig = mb.add_func_type(vec![Ty::Bool, Ty::Bool], vec![Ty::Bool]);
    let mut fb = clean_fn(&mut mb, "band", sig);
    let entry = fb.create_block();
    let p = fb.add_block_param(entry, Ty::Bool);
    let q = fb.add_block_param(entry, Ty::Bool);
    fb.switch_to_block(entry);
    let r = fb.binop(BinOp::And, Ty::Bool, p, q);
    fb.ret(vec![r]);
    let f = fb.build();
    flipped_edge(
        "b3.gap.bool_connective",
        mb.build().expect("ModuleBuilder::build: test fixture"),
        f,
        &["Bool", "Bool"],
        "Bool",
        64,
        app2("Bool.and", Expr::bvar(1), Expr::bvar(0)),
        |m| set_binop(m, f, BinOp::Or),
        "WS1.15 S1: Bool connectives",
    );
}

fn b3_gap_select_has_no_tv_rule() {
    // Baseline: the SAME function as a CondBr diamond certifies
    // (`b3.fragment3a.condbr_diamond`); re-established here so the ratchet is
    // self-contained.
    let (mut base, f) = min_diamond();
    attach_tv(&mut base, f, 2, 64, min_source_body());
    let e = validate_module(&base);
    assert!(feature_check(
        "b3.gap.select.baseline_certifies",
        e.is_empty(),
        &format!("umin as a CondBr diamond certifies; errors={e:?}"),
    ));

    // FLIPPED (WS1.15 S1): the if-select lowering `select (icmp ult a b) a b`
    // denotes to the SAME `Bool.rec` the diamond denotes to (the source `if`
    // is unchanged: `min_source_body`). Twin: the select arms swapped.
    let swap_select = |m: &mut Module, f: FuncId| {
        for block in &mut m.function_by_id_mut(f).expect("f").blocks {
            for node in &mut block.body {
                if let Inst::Select {
                    then_val, else_val, ..
                } = &mut node.inst
                {
                    core::mem::swap(then_val, else_val);
                }
            }
        }
    };
    let mut mb = ModuleBuilder::new("b3_min_select");
    let sig = mb.add_func_type(vec![Ty::U64, Ty::U64], vec![Ty::U64]);
    let mut fb = clean_fn(&mut mb, "umin", sig);
    let entry = fb.create_block();
    let a = fb.add_block_param(entry, Ty::U64);
    let b = fb.add_block_param(entry, Ty::U64);
    fb.switch_to_block(entry);
    let c = fb.icmp(ICmpOp::Ult, Ty::U64, a, b);
    let s = fb.select(Ty::U64, c, a, b);
    fb.ret(vec![s]);
    let f = fb.build();
    let module = mb.build().expect("ModuleBuilder::build: test fixture");
    let ran = run_with_args(&module, "umin", vec![u64v(9), u64v(3)]);
    assert_eq!(first_u128(&ran), Some(3), "select form executes: {ran:?}");
    flipped_edge(
        "b3.gap.select.natural_lowering",
        module,
        f,
        &["Nat", "Nat"],
        "Nat",
        64,
        min_source_body(),
        move |m| swap_select(m, f),
        "WS1.15 S1: Select as Bool.rec at the result sort",
    );

    // FLIPPED (WS1.15 S1): `Select` inside the prefix of an entry CondBr (both
    // arms return the select): `if a < b then (if a < b then a else b) else
    // (same)`. Twin: the select arms swapped.
    let mut mb = ModuleBuilder::new("b3_min_select_in_prefix");
    let sig = mb.add_func_type(vec![Ty::U64, Ty::U64], vec![Ty::U64]);
    let mut fb = clean_fn(&mut mb, "umin", sig);
    let entry = fb.create_block();
    let t = fb.create_block();
    let e = fb.create_block();
    let a = fb.add_block_param(entry, Ty::U64);
    let b = fb.add_block_param(entry, Ty::U64);
    fb.switch_to_block(entry);
    let c = fb.icmp(ICmpOp::Ult, Ty::U64, a, b);
    let s = fb.select(Ty::U64, c, a, b);
    fb.condbr(c, t, vec![], e, vec![]);
    fb.switch_to_block(t);
    fb.ret(vec![s]);
    fb.switch_to_block(e);
    fb.ret(vec![s]);
    let f = fb.build();
    let cmp = app2("Nat.blt", Expr::bvar(1), Expr::bvar(0));
    flipped_edge(
        "b3.gap.select.instruction",
        mb.build().expect("ModuleBuilder::build: test fixture"),
        f,
        &["Nat", "Nat"],
        "Nat",
        64,
        ite_nat(cmp, min_source_body(), min_source_body()),
        move |m| swap_select(m, f),
        "WS1.15 S1: Select in a CondBr prefix",
    );
}

fn b3_gap_enum_and_switch_have_no_tv_rule() {
    // Baseline: `is_zero(t) = if t == 0 then 1 else 0` as ICmp Eq + CondBr.
    let (mut base, f) = {
        let mut mb = ModuleBuilder::new("b3_is_zero_condbr");
        let sig = mb.add_func_type(vec![Ty::U64], vec![Ty::U64]);
        let mut fb = clean_fn(&mut mb, "is_zero", sig);
        let entry = fb.create_block();
        let t = fb.create_block();
        let e = fb.create_block();
        let tag = fb.add_block_param(entry, Ty::U64);
        fb.switch_to_block(entry);
        let zero = fb.uconst(Ty::U64, 0);
        let c = fb.icmp(ICmpOp::Eq, Ty::U64, tag, zero);
        fb.condbr(c, t, vec![], e, vec![]);
        fb.switch_to_block(t);
        let one = fb.uconst(Ty::U64, 1);
        fb.ret(vec![one]);
        fb.switch_to_block(e);
        let z = fb.uconst(Ty::U64, 0);
        fb.ret(vec![z]);
        let f = fb.build();
        (mb.build().expect("ModuleBuilder::build: test fixture"), f)
    };
    let source = || {
        ite_nat(
            app2("Nat.beq", Expr::bvar(0), Expr::nat_lit(0)),
            Expr::nat_lit(1),
            Expr::nat_lit(0),
        )
    };
    attach_tv(&mut base, f, 1, 64, source());
    let e = validate_module(&base);
    assert!(feature_check(
        "b3.gap.switch.baseline_certifies",
        e.is_empty(),
        &format!("is_zero as ICmp Eq + CondBr certifies; errors={e:?}"),
    ));

    // FLIPPED (WS1.15 S2): the same decision as a `Switch` terminator (how a
    // Lean `match` on a tag lowers) denotes to the SAME nested-ite the
    // diamond does. Twin: the case arm and the default swapped.
    let swap_switch_arms = |m: &mut Module, f: FuncId| {
        for block in &mut m.function_by_id_mut(f).expect("f").blocks {
            for node in &mut block.body {
                if let Inst::Switch { default, cases, .. } = &mut node.inst {
                    core::mem::swap(default, &mut cases[0].target);
                }
            }
        }
    };
    let mut mb = ModuleBuilder::new("b3_is_zero_switch");
    let sig = mb.add_func_type(vec![Ty::U64], vec![Ty::U64]);
    let mut fb = clean_fn(&mut mb, "is_zero", sig);
    let entry = fb.create_block();
    let t = fb.create_block();
    let e = fb.create_block();
    let tag = fb.add_block_param(entry, Ty::U64);
    fb.switch_to_block(entry);
    fb.switch(
        tag,
        vec![SwitchCase {
            value: Constant::Int(0),
            target: t,
            args: vec![],
        }],
        e,
        vec![],
    );
    fb.switch_to_block(t);
    let one = fb.uconst(Ty::U64, 1);
    fb.ret(vec![one]);
    fb.switch_to_block(e);
    let z = fb.uconst(Ty::U64, 0);
    fb.ret(vec![z]);
    let f = fb.build();
    let module = mb.build().expect("ModuleBuilder::build: test fixture");
    let (r0, r5) = (
        run_with_args(&module, "is_zero", vec![u64v(0)]),
        run_with_args(&module, "is_zero", vec![u64v(5)]),
    );
    assert_eq!(
        (first_u128(&r0), first_u128(&r5)),
        (Some(1), Some(0)),
        "switch form executes"
    );
    flipped_edge(
        "b3.gap.switch_terminator",
        module,
        f,
        &["Nat"],
        "Nat",
        64,
        source(),
        move |m| swap_switch_arms(m, f),
        "WS1.15 S2: Switch as a nested ite in case order",
    );

    // FLIPPED (WS1.15 S2): the inductive carrier itself: `inductive Lvl | zero
    // | succ | max | imax | param` as a fieldless `Ty::Enum`, `lvl_is_zero :
    // Lvl -> UInt64` by a Switch over the tag (field 0). The enum PARAM
    // denotes as its tag (a `Nat` binder) and the tag-lane read is the
    // identity, so the source is the same `if t = 0 then 1 else 0`.
    // Twin: the case arm and the default swapped.
    let mut mb = ModuleBuilder::new("b3_lvl_is_zero");
    let lvl = Ty::Enum(EnumId::new(0));
    let sig = mb.add_func_type(vec![lvl.clone()], vec![Ty::U64]);
    let nullary = mb.add_func_type(vec![], vec![Ty::U64]);
    let f = {
        let mut fb = clean_fn(&mut mb, "lvl_is_zero", sig);
        let entry = fb.create_block();
        let t = fb.create_block();
        let e = fb.create_block();
        let l = fb.add_block_param(entry, lvl.clone());
        fb.switch_to_block(entry);
        let tag = fb.extract_field(Ty::U8, l, 0);
        fb.switch(
            tag,
            vec![SwitchCase {
                value: Constant::Int(0),
                target: t,
                args: vec![],
            }],
            e,
            vec![],
        );
        fb.switch_to_block(t);
        let one = fb.uconst(Ty::U64, 1);
        fb.ret(vec![one]);
        fb.switch_to_block(e);
        let z = fb.uconst(Ty::U64, 0);
        fb.ret(vec![z]);
        fb.build()
    };
    for (name, tag) in [("probe_zero", 0i128), ("probe_max", 2)] {
        let mut fb = clean_fn(&mut mb, name, nullary);
        let entry = fb.create_block();
        fb.switch_to_block(entry);
        let v = fb.const_value(lvl.clone(), Constant::Aggregate(vec![Constant::Int(tag)]));
        let out = fb.call(f, vec![v]);
        fb.ret(vec![out]);
        fb.build();
    }
    let mut module = mb.build().expect("ModuleBuilder::build: test fixture");
    module.add_enum(EnumDef::new(
        EnumId::new(0),
        "Lvl",
        ["zero", "succ", "max", "imax", "param"]
            .into_iter()
            .map(|n| EnumVariant {
                name: n.into(),
                fields: vec![],
                field_names: vec![],
            })
            .collect(),
    ));
    let (z, m) = (
        run_nullary(&module, "probe_zero"),
        run_nullary(&module, "probe_max"),
    );
    assert_eq!(
        (first_u128(&z), first_u128(&m)),
        (Some(1), Some(0)),
        "the enum+switch program executes: {z:?} {m:?}"
    );
    flipped_edge(
        "b3.gap.enum_param",
        module,
        f,
        &["Nat"],
        "Nat",
        64,
        source(),
        move |m| swap_switch_arms(m, f),
        "WS1.15 S2: fieldless enum param as a Nat tag",
    );
}

fn b3_gap_signed_and_other_widths_have_no_tv_rule() {
    // FLIPPED (WS1.15 S3): `addmul` at i64 / i32 / i8 certifies — a signed
    // value is its two's-complement bit pattern over Nat mod 2^w, so the
    // source is `addmul_source_body(w)` unchanged, stated at the signed
    // carrier alias `CleanTV.Int<w>` (a reducible `:= Nat` the validator
    // installs beside the heap vocabulary — the binder the comparand MUST
    // spell for a signed position, so a sign-only relabel of the emission is
    // refused by name). Twin: Mul → Add.
    for (tag, ty, width, alias) in [
        ("i64", Ty::I64, 64, "CleanTV.Int64"),
        ("i32", Ty::I32, 32, "CleanTV.Int32"),
        ("i8", Ty::I8, 8, "CleanTV.Int8"),
    ] {
        let (mut module, f) = addmul_module(ty.clone(), false);
        module.function_by_id_mut(f).unwrap().body_gate = Some(BodyGate::Ungated);
        flipped_edge(
            &format!("b3.gap.width.{tag}"),
            module,
            f,
            &[alias, alias],
            alias,
            width,
            addmul_source_body(width),
            move |m| mul_to_add(m, f),
            "WS1.15 S3: signed widths as two's complement over Nat mod 2^w",
        );
    }

    // STILL GAP by ruling: `u128` (no bignum scalar, §2.2.1) and `usize` (no
    // width without a target). The refusal moved to the widened type gate.
    for (tag, ty) in [("u128", Ty::U128), ("usize", Ty::Usize)] {
        let (mut module, f) = addmul_module(ty.clone(), false);
        module.function_by_id_mut(f).unwrap().body_gate = Some(BodyGate::Ungated);
        fragment_edge(
            &format!("b3.gap.width.{tag}"),
            module,
            f,
            2,
            64,
            addmul_source_body(64),
            &[
                "return type",
                "is outside the TV fragment (U8..U64, I8..I64, Bool, fieldless enums)",
            ],
            "validate.rs clean_backend_tv::sort_of_ty (WS1.15: U128/Usize stay outside)",
        );
    }

    // FLIPPED (WS1.15 S3/S1): a signed comparison inside an otherwise-unsigned
    // diamond denotes through the bias `(x + 2^63) mod 2^64`; `Ne` is
    // `Bool.not (Nat.beq a b)`. Twins: `slt` → `sle`, `ne` → `eq`.
    let bias = |x: Expr| wmod(app2("Nat.add", x, Expr::nat_lit(1u64 << 63)), 64);
    let slt_source = ite_nat(
        app2("Nat.blt", bias(Expr::bvar(1)), bias(Expr::bvar(0))),
        Expr::bvar(1),
        Expr::bvar(0),
    );
    let ne_source = ite_nat(
        app1("Bool.not", app2("Nat.beq", Expr::bvar(1), Expr::bvar(0))),
        Expr::bvar(1),
        Expr::bvar(0),
    );
    for (tag, op, source, twin) in [
        ("slt", ICmpOp::Slt, slt_source, ICmpOp::Sle),
        ("ne", ICmpOp::Ne, ne_source, ICmpOp::Eq),
    ] {
        let (mut module, f) = min_diamond();
        module.function_by_id_mut(f).unwrap().body_gate = Some(BodyGate::Ungated);
        set_icmp(&mut module, f, op);
        flipped_edge(
            &format!("b3.gap.icmp.{tag}"),
            module,
            f,
            &["Nat", "Nat"],
            "Nat",
            64,
            source,
            move |m| set_icmp(m, f, twin),
            "WS1.15 S3/S1: signed comparison bias; Ne",
        );
    }

    // FLIPPED (WS1.15 S4): `and`/`xor`/`shl` (by a constant below w) and
    // `udiv` (by a nonzero constant) certify with their Lean spellings.
    // Twins: and → or, xor → and, shl by 3 → shl by 4 (constant edit), udiv →
    // urem.
    let a = || Expr::bvar(1);
    let b = || Expr::bvar(0);
    let x = || Expr::bvar(0);
    let three = || Expr::nat_lit(3);
    let binary = |op: BinOp| {
        let mut mb = ModuleBuilder::new("b3_binop");
        let sig = mb.add_func_type(vec![Ty::U64, Ty::U64], vec![Ty::U64]);
        let mut fb = clean_fn(&mut mb, "op", sig);
        let entry = fb.create_block();
        let a = fb.add_block_param(entry, Ty::U64);
        let b = fb.add_block_param(entry, Ty::U64);
        fb.switch_to_block(entry);
        let r = fb.binop(op, Ty::U64, a, b);
        fb.ret(vec![r]);
        let f = fb.build();
        (mb.build().expect("ModuleBuilder::build: test fixture"), f)
    };
    let by_const = |op: BinOp, k: u128| {
        let mut mb = ModuleBuilder::new("b3_binop_k");
        let sig = mb.add_func_type(vec![Ty::U64], vec![Ty::U64]);
        let mut fb = clean_fn(&mut mb, "op", sig);
        let entry = fb.create_block();
        let a = fb.add_block_param(entry, Ty::U64);
        fb.switch_to_block(entry);
        let kk = fb.uconst(Ty::U64, k);
        let r = fb.binop(op, Ty::U64, a, kk);
        fb.ret(vec![r]);
        let f = fb.build();
        (mb.build().expect("ModuleBuilder::build: test fixture"), f)
    };
    let (m_and, f_and) = binary(BinOp::And);
    flipped_edge(
        "b3.gap.binop.and",
        m_and,
        f_and,
        &["Nat", "Nat"],
        "Nat",
        64,
        app2("Nat.land", a(), b()),
        move |m| set_binop(m, f_and, BinOp::Or),
        "WS1.15 S4: Nat.land",
    );
    let (m_xor, f_xor) = binary(BinOp::Xor);
    flipped_edge(
        "b3.gap.binop.xor",
        m_xor,
        f_xor,
        &["Nat", "Nat"],
        "Nat",
        64,
        app2("Nat.xor", a(), b()),
        move |m| set_binop(m, f_xor, BinOp::And),
        "WS1.15 S4: Nat.xor",
    );
    let (m_shl, f_shl) = by_const(BinOp::Shl, 3);
    flipped_edge(
        "b3.gap.binop.shl",
        m_shl,
        f_shl,
        &["Nat"],
        "Nat",
        64,
        wmod(
            app2("Nat.mul", x(), app2("Nat.pow", Expr::nat_lit(2), three())),
            64,
        ),
        move |m| {
            for block in &mut m.function_by_id_mut(f_shl).expect("f").blocks {
                for node in &mut block.body {
                    if let Inst::Const { value, .. } = &mut node.inst {
                        *value = Constant::Int(4);
                    }
                }
            }
        },
        "WS1.15 S4: shl by a constant below w",
    );
    let (m_div, f_div) = by_const(BinOp::UDiv, 3);
    flipped_edge(
        "b3.gap.binop.udiv",
        m_div,
        f_div,
        &["Nat"],
        "Nat",
        64,
        app2("Nat.div", x(), three()),
        move |m| set_binop(m, f_div, BinOp::URem),
        "WS1.15 S4: udiv by a provably nonzero divisor",
    );

    // FLIPPED (WS1.15 S5): a widening cast across mixed widths denotes as
    // `Nat.mod x 2^64` (the one shared Nat-mod-2^w vocabulary). Twin: the
    // same widening at u8 -> u16 (the modulus changes: 2^16 is not 2^64).
    let mut mb = ModuleBuilder::new("b3_zext");
    let sig = mb.add_func_type(vec![Ty::U32], vec![Ty::U64]);
    let mut fb = clean_fn(&mut mb, "widen", sig);
    let entry = fb.create_block();
    let a = fb.add_block_param(entry, Ty::U32);
    fb.switch_to_block(entry);
    let r = fb.cast(CastOp::ZExt, Ty::U32, Ty::U64, a);
    fb.ret(vec![r]);
    let f = fb.build();
    flipped_edge(
        "b3.gap.mixed_width_cast",
        mb.build().expect("ModuleBuilder::build: test fixture"),
        f,
        &["Nat"],
        "Nat",
        64,
        wmod(x(), 64),
        move |m| {
            let func = m.function_by_id_mut(f).expect("f");
            let sig = func.ty;
            for block in &mut func.blocks {
                for (_, ty) in &mut block.params {
                    *ty = Ty::U8;
                }
                for node in &mut block.body {
                    if let Inst::Cast { src_ty, dst_ty, .. } = &mut node.inst {
                        *src_ty = Ty::U8;
                        *dst_ty = Ty::U16;
                    }
                }
            }
            m.func_types[sig.as_usize()].params = vec![Ty::U8];
            m.func_types[sig.as_usize()].returns = vec![Ty::U16];
        },
        "WS1.15 S5: ZExt/Trunc as Nat.mod by 2^dst",
    );
}

/// Closely related: what "demoted" looks like in the format, and what the
/// format does NOT check about it.
fn b3_demotion_is_expressible_but_the_license_is_not_bound_to_the_certificate() {
    // A demoted (out-of-fragment) Clean body: no TV obligation, `Ungated`.
    let mut mb = ModuleBuilder::new("b3_demoted");
    let sig = mb.add_func_type(vec![Ty::U64, Ty::U64], vec![Ty::Bool]);
    let mut fb = clean_fn(&mut mb, "ult", sig);
    let entry = fb.create_block();
    let a = fb.add_block_param(entry, Ty::U64);
    let b = fb.add_block_param(entry, Ty::U64);
    fb.switch_to_block(entry);
    let c = fb.icmp(ICmpOp::Ult, Ty::U64, a, b);
    fb.ret(vec![c]);
    let f = fb.build();
    let demoted = mb.build().expect("ModuleBuilder::build: test fixture");
    let structural = validate_module(&demoted);
    let codegen = validate_module_for_codegen(&demoted);
    let refused = matches!(
        codegen.as_slice(),
        [ValidationError::UngatedBodyForCodegen { name, .. }] if name == "ult"
    );
    assert!(feature_check(
        "b3.demotion.ungated_is_carried_and_refused_for_codegen",
        structural.is_empty() && refused,
        &format!("validate_module={structural:?}; validate_module_for_codegen={codegen:?}"),
    ));

    // REVIEW ADDITION — the in-band spelling of "not (yet) certified": the
    // demoted body may carry its TranslationValidation obligation at `Pending`.
    // Twin: flipping ONLY the status to `Certified` (no certificate) is refused.
    let mut pending = demoted.clone();
    pending.proof_obligations.push(
        ProofObligation::new(
            ProofId::new(0),
            ObligationKind::TranslationValidation,
            ProofStatus::Pending,
            "backend translation validation: 'ult' is outside the clean_backend_tv fragment",
        )
        .with_function(f),
    );
    let carried = validate_module(&pending);
    let strict = validate_module_with_authority(&pending, &RejectingModuleProofAuthority);
    let rt = roundtrip_all(&pending);
    let mut claimed_certified = pending.clone();
    claimed_certified.proof_obligations[0].status = ProofStatus::Certified;
    let refused = validate_module(&claimed_certified);
    assert!(feature_check(
        "b3.demotion.pending_tv_obligation_is_carried",
        carried.is_empty()
            && strict.is_empty()
            && rt.lossless_production()
            && matches!(
                refused.as_slice(),
                [ValidationError::CertifiedWithoutCleanCic { obligation: 0 }]
            ),
        &format!(
            "Pending TV obligation on the Ungated Bool body: validate_module={carried:?} \
             with_authority={strict:?}; {}; status Pending->Certified twin => {refused:?}",
            rt.summary()
        ),
    ));

    // FLIPPED by WS1.5 (F-006): the same out-of-fragment body claiming
    // `Gated{"clean-kernel-tv"}` with NO TranslationValidation obligation at
    // all passed the codegen gate — `codegen_license_errors` matched
    // `Gated { .. }` and never looked for the Certified obligation the
    // authority string NAMES. PASS: it is refused by name
    // (`GatedWithoutEvidence`). Negative twin: the kernel-certified `addmul`
    // under the same license is admitted (b3.addmul.codegen_license), and the
    // same body under an authority outside the evidence table is admitted by
    // the policy-free gate, so the refusal is the evidence rule's.
    let mut claimed = demoted.clone();
    claimed.function_by_id_mut(f).unwrap().body_gate = Some(BodyGate::Gated {
        authority: CLEAN_KERNEL_TV_AUTHORITY.into(),
        evidence: None,
    });
    let codegen = validate_module_for_codegen(&claimed);
    let mut direct = demoted.clone();
    direct.function_by_id_mut(f).unwrap().body_gate = Some(BodyGate::Gated {
        authority: DIRECT_LANE_AUTHORITY.into(),
        evidence: None,
    });
    let direct_codegen = validate_module_for_codegen(&direct);
    let (certified, _) = certified_addmul(Ty::U64, 64, false);
    let certified_codegen = validate_module_for_codegen(&certified);
    assert!(feature_check(
        "b3.gap.kernel_tv_license_not_bound_to_certificate",
        claimed.proof_obligations.is_empty()
            && validate_module(&claimed).is_empty()
            && matches!(
                codegen.as_slice(),
                [ValidationError::GatedWithoutEvidence { function, authority, detail }]
                    if *function == f.index()
                        && authority == CLEAN_KERNEL_TV_AUTHORITY
                        && detail.contains("no TranslationValidation obligation")
            )
            && direct_codegen.is_empty()
            && certified_codegen.is_empty(),
        &format!(
            "closed by WS1.5: Gated{{authority:\"clean-kernel-tv\"}} on an UNCERTIFIABLE body \
             with 0 obligations: validate_module_for_codegen={codegen:?}; twins: direct-lane \
             authority => {direct_codegen:?}, kernel-certified addmul => {certified_codegen:?}"
        ),
    ));
}

// ===========================================================================
// GAP — a USER theorem cannot certify a contract obligation
// ===========================================================================

fn b3_gap_user_theorem_cannot_certify_a_contract_obligation() {
    use trust_ir::clean_expr_lowering::contract::contract_clean_cic_certificate;

    // ---- Baseline (validates): a Postcondition on `addmul`, Certified through
    // the ONLY contract path that exists — a closed ground predicate the
    // validator re-grounds itself (`(= 1 1)`; contract.rs:404-449, :657).
    let (mut base, addmul) = addmul_module(Ty::U64, false);
    let ground = ProofObligation::new(
        ProofId::new(0),
        ObligationKind::Postcondition,
        ProofStatus::Certified,
        "ground closed predicate",
    )
    .with_function(addmul)
    .with_formula(ProofFormula::smtlib2("(= 1 1)", "Bool"));
    let cert = contract_clean_cic_certificate(&ground, "partb-b3").expect("(= 1 1) grounds");
    base.proof_obligations.push(ground);
    base.proof_certificates.push(cert);
    let e = validate_module(&base);
    assert!(feature_check(
        "b3.gap.user_theorem.baseline_ground_predicate_certifies",
        e.is_empty(),
        &format!("Postcondition `(= 1 1)` Certified via the contract re-grounder; errors={e:?}"),
    ));

    // ---- The user theorem. Lean:
    //   theorem addmul_spec (a b : Nat) :
    //       addmul_den a b = ((a*b) % 2^64 + a) % 2^64 := rfl
    // It is a REAL theorem: the same kernel accepts it in the ground prelude.
    let statement = pi_nat(2, eq_nat(addmul_source_body(64), addmul_source_body(64)));
    let proof = lam_nat(2, refl_nat(addmul_source_body(64)));
    let mut env = Environment::try_with_prelude().expect("prelude");
    let accepted = env
        .add_decl(Declaration::Theorem {
            name: Name::from_string("Envelope.addmul_spec"),
            level_params: vec![],
            type_: statement,
            value: proof.clone(),
        })
        .is_ok();
    assert!(
        accepted,
        "the user theorem must be kernel-valid, or the refusals below prove nothing"
    );

    // The single change: the obligation states the REAL contract of addmul,
    // with typed bindings (v41), instead of a closed literal predicate.
    let bv64 = |place| ClauseBinding {
        sort: ClauseSort::BitVec(64),
        place,
    };
    let mut formula = ProofFormula::smtlib2("(= result (bvadd (bvmul a b) a))", "Bool");
    formula.bindings = vec![
        ("a".into(), bv64(ClausePlace::Param { index: 0 })),
        ("b".into(), bv64(ClausePlace::Param { index: 1 })),
        ("result".into(), bv64(ClausePlace::ResultSlot { index: 0 })),
    ];
    let contract = |status| {
        ProofObligation::new(
            ProofId::new(0),
            ObligationKind::Postcondition,
            status,
            "ensures result == a*b + a (wrapping)",
        )
        .with_function(addmul)
        .with_formula(formula.clone())
    };

    // The obligation itself is carried fine (Pending validates).
    let (mut pending, _) = addmul_module(Ty::U64, false);
    pending
        .proof_obligations
        .push(contract(ProofStatus::Pending));
    let e = validate_module(&pending);
    assert!(feature_check(
        "b3.user_theorem.contract_obligation_is_carried_pending",
        e.is_empty(),
        &format!("Postcondition with BitVec(64) bindings at Pending; errors={e:?}"),
    ));

    // (a) the contract minter has no rule for it.
    let certified = contract(ProofStatus::Certified);
    let minted = contract_clean_cic_certificate(&certified, "partb-b3");

    // (b) a CleanCic carrying the user's kernel-valid proof term, no directive:
    //     validate.rs:12467-12480 re-grounds the goal from the FORMULA and the
    //     formula is outside the grounded fragment (contract.rs:404-449).
    let with_cert = |recheck: Option<CleanCicKernelRecheck>| {
        let (mut m, _) = addmul_module(Ty::U64, false);
        let obligation = contract(ProofStatus::Certified);
        m.proof_certificates.push(ProofCertificate {
            obligation: obligation.id,
            prover: "lean-user-theorem".into(),
            evidence: ProofEvidence::CleanCic {
                term: encode_clean_expr_v1(&proof).unwrap(),
                context: Vec::new(),
                lineage: clean_cic_lineage_digest(&obligation),
                kernel_recheck: recheck,
            },
            assurance: None,
        });
        m.proof_obligations.push(obligation);
        validate_module(&m)
    };
    let bare = with_cert(None);

    // (c) the same certificate NAMING the user's module/theorem under a
    //     user-chosen anchor: validate.rs:12664-12675 — the anchor list is
    //     closed and validator-owned.
    let directive = |anchor: &str, module: &str| {
        Some(CleanCicKernelRecheck {
            module: module.into(),
            theorems: vec!["Envelope.addmul_spec".into()],
            anchor: anchor.into(),
            allowed_axioms: vec![],
            binding: None,
        })
    };
    let user_anchor = with_cert(directive("user_theorem", "Envelope"));
    let user_anchor_refused = sole_recheck_refusal(&user_anchor, 0)
        .is_some_and(|r| r.contains("has no obligation-bound Certified validation path"));

    // (d) no EXISTING anchor can be borrowed for a contract kind either.
    let borrowed: Vec<(&str, Vec<ValidationError>, &str)> = vec![
        (
            KERNEL_ANCHOR_CLEAN_BACKEND_TV,
            with_cert(directive(KERNEL_ANCHOR_CLEAN_BACKEND_TV, TV_MODULE)),
            "may only certify TranslationValidation obligations",
        ),
        (
            KERNEL_ANCHOR_TRUSTCG_LOWERING_RESOLUTION,
            with_cert(directive(
                KERNEL_ANCHOR_TRUSTCG_LOWERING_RESOLUTION,
                "Clean.Res",
            )),
            "relevant only as non-authoritative CNF assurance",
        ),
        (
            KERNEL_ANCHOR_GIVEBACK_REFINEMENT,
            with_cert(directive(
                KERNEL_ANCHOR_GIVEBACK_REFINEMENT,
                "RustSem.GiveBack",
            )),
            "give-back anchors may certify only GiveBackRefinement obligations",
        ),
        (
            KERNEL_ANCHOR_FARKAS_CONSTRUCTIVE,
            with_cert(directive(
                KERNEL_ANCHOR_FARKAS_CONSTRUCTIVE,
                "Crownproof.SlackCertZ",
            )),
            "it cannot mint Certified evidence",
        ),
        (
            KERNEL_ANCHOR_SLACKCERTZ,
            with_cert(directive(KERNEL_ANCHOR_SLACKCERTZ, "Crownproof.SlackCertZ")),
            "it cannot mint Certified evidence",
        ),
        // WS1.13: the island anchor certifies `lean.theorem` rows only — a
        // contract clause over IR places is slice 2.
        (
            KERNEL_ANCHOR_CLEAN_ISLAND,
            with_cert(directive(
                KERNEL_ANCHOR_CLEAN_ISLAND,
                KERNEL_ANCHOR_CLEAN_ISLAND_MODULE,
            )),
            "may certify only `lean.theorem` obligations",
        ),
    ];
    let borrowed_refused = borrowed.iter().all(|(_, errors, needle)| {
        sole_recheck_refusal(errors, 0).is_some_and(|r| r.contains(needle))
    });
    let bare_refused = sole_recheck_refusal(&bare, 0).is_some_and(|r| {
        r.contains("carries no kernel-recheck directive")
            && r.contains("obligation-grounded Clean contract recheck")
    });

    // ---- WS1.13 (F-012 closed for slice 1): the user theorem SHIPPED WITH
    // ITS ISLAND is a Certified `lean.theorem` row. The island declares the
    // source `Envelope.addmul` (the hand-built comparand above) and the
    // closed theorem `Envelope.addmul_6_7 : Envelope.addmul 6 7 = 48`; the
    // emitted `addmul` carries a TV certificate SOURCE-BOUND to
    // `Envelope.addmul` in the same island, which is what makes the theorem
    // a statement about the code.
    let island = IslandEnvironment::new(
        encode_island_declarations_v1(&[
            Declaration::Definition {
                name: Name::from_string("Envelope.addmul"),
                level_params: vec![],
                type_: pi_nat(2, nat()),
                value: lam_nat(2, addmul_source_body(64)),
                is_reducible: true,
            },
            Declaration::Theorem {
                name: Name::from_string("Envelope.addmul_6_7"),
                level_params: vec![],
                type_: eq_nat(
                    Expr::apps(
                        Expr::const_str("Envelope.addmul"),
                        [Expr::nat_lit(6), Expr::nat_lit(7)],
                    ),
                    Expr::nat_lit(48),
                ),
                value: refl_nat(Expr::nat_lit(48)),
            },
        ])
        .expect("island encodes"),
    );
    let island_module = |statement: &str| {
        let (mut m, addmul) = addmul_module(Ty::U64, true);
        let (_, tv, tv_cert) = certify_identity_lineage_rung_island_bound(
            &m,
            ProofLineageId::new(0),
            ProofId::new(0),
            ProofTransform::new(
                ProofTransformStage::Frontend,
                "identity",
                "partb-b3",
                "1.0.0",
            ),
            addmul,
            &island,
            SourceDefinitionRef {
                decl: "Envelope.addmul".into(),
                closure_digest: trust_ir::proof::ProofDigest::sha256([0x61; 32]),
            },
        )
        .expect("the emitted addmul denotes Envelope.addmul");
        m.proof_obligations.push(tv);
        m.proof_certificates.push(tv_cert);
        let (mut theorem, mut theorem_cert) = certify_island_theorem(
            ProofId::new(1),
            "Envelope.addmul_6_7",
            ProofFormula::smtlib2("(= (Envelope.addmul 6 7) 48)", "Bool"),
            &island,
        )
        .expect("the island theorem states the formula");
        theorem.formula = Some(ProofFormula::smtlib2(statement, "Bool"));
        let lineage = trust_ir::proof::clean_cic_lineage_digest_v8(
            &theorem,
            &|_| None,
            theorem_cert
                .evidence
                .clean_cic_kernel_recheck()
                .and_then(|r| r.binding.as_deref()),
        )
        .expect("keyable");
        if let ProofEvidence::CleanCic { lineage: slot, .. } = &mut theorem_cert.evidence {
            *slot = lineage;
        }
        m.proof_obligations.push(theorem);
        m.proof_certificates.push(theorem_cert);
        m
    };
    let certified_theorem = island_module("(= (Envelope.addmul 6 7) 48)");
    let island_layers = [
        validate_module(&certified_theorem),
        validate_module_with_authority(&certified_theorem, &RejectingModuleProofAuthority),
        validate_module_for_codegen(&certified_theorem),
    ];
    let island_certifies = island_layers.iter().all(Vec::is_empty)
        && validate_module_report(&certified_theorem)
            .replayed_certificate_refs()
            .map(|r| r.len())
            == Some(2);
    // Its single-change twin: the row states `= 49`, the theorem proves `= 48`.
    let false_statement = validate_module(&island_module("(= (Envelope.addmul 6 7) 49)"));
    let twin_refused = sole_recheck_refusal(&false_statement, 1)
        .is_some_and(|r| r.contains("does not state the obligation's formula"));

    assert!(feature_check(
        "b3.gap.user_theorem_cannot_certify_contract",
        island_certifies
            && twin_refused
            && minted.is_none()
            && bare_refused
            && user_anchor_refused
            && borrowed_refused,
        &format!(
            "closed by WS1.13 slice 1 (F-012): the kernel-valid user theorem \
             `Envelope.addmul_6_7 : Envelope.addmul 6 7 = 48`, shipped with its island and \
             stated as the lean.theorem row `(= (Envelope.addmul 6 7) 48)`, certifies through \
             the clean_island anchor on every layer => {island_layers:?}, bridged to addmul's \
             island-bound TV; the row stating `= 49` is refused by defeq => {false_statement:?}. \
             SLICE 2 RESIDUAL, pinned: the CONTRACT form — Postcondition `(= result (bvadd \
             (bvmul a b) a))` over IR places — is still refused: minter={:?}; no-directive => \
             {bare:?}; user anchor => {user_anchor:?}; borrowed anchors (clean_island included) \
             all refused={borrowed_refused} {:?}",
            minted.map(|_| "Some"),
            borrowed
                .iter()
                .map(|(a, e, _)| (*a, sole_recheck_refusal(e, 0).is_some()))
                .collect::<Vec<_>>()
        ),
    ));
}

// ===========================================================================
// GAP — what a Fragment-3b (compositional) certificate does NOT bind
// ===========================================================================

/// `[Clean] addmul`, `[Clean] submul(a,b) = a*b - a` (same signature), and
/// `[Clean] twice(a,b) = addmul(addmul(a,b), b)`, with ONLY `twice` carrying a
/// certificate when `certify_callee` is false.
fn composition_with_decoy(certify_callee: bool) -> (Module, FuncId, FuncId, FuncId) {
    let mut mb = ModuleBuilder::new("b3_compose_decoy");
    let binary = mb.add_func_type(vec![Ty::U64, Ty::U64], vec![Ty::U64]);
    mb.set_default_producer(Producer::Clean);
    // A body wears the evidence-bound `clean-kernel-tv` license only when the
    // module carries its TV certificate (roadmap WS1.5); the decoy `submul`
    // and an uncertified `addmul` wear the evidence-free direct-lane license.
    let leaf = |mb: &mut ModuleBuilder, name: &str, second: BinOp, certified: bool| {
        let mut fb = mb.function(name, binary);
        fb.set_body_gate(BodyGate::Gated {
            authority: if certified {
                CLEAN_KERNEL_TV_AUTHORITY
            } else {
                DIRECT_LANE_AUTHORITY
            }
            .into(),
            evidence: None,
        });
        let entry = fb.create_block();
        let a = fb.add_block_param(entry, Ty::U64);
        let b = fb.add_block_param(entry, Ty::U64);
        fb.switch_to_block(entry);
        let ab = fb.mul(Ty::U64, a, b);
        let out = fb.binop(second, Ty::U64, ab, a);
        fb.ret(vec![out]);
        fb.build()
    };
    let addmul = leaf(&mut mb, "addmul", BinOp::Add, certify_callee);
    let submul = leaf(&mut mb, "submul", BinOp::Sub, false);
    let twice = {
        let mut fb = mb.function("twice", binary);
        fb.set_body_gate(BodyGate::Gated {
            authority: CLEAN_KERNEL_TV_AUTHORITY.into(),
            evidence: None,
        });
        let entry = fb.create_block();
        let a = fb.add_block_param(entry, Ty::U64);
        let b = fb.add_block_param(entry, Ty::U64);
        fb.switch_to_block(entry);
        let inner = fb.call(addmul, vec![a, b]);
        let outer = fb.call(addmul, vec![inner, b]);
        fb.ret(vec![outer]);
        fb.build()
    };
    let mut m = mb.build().expect("ModuleBuilder::build: test fixture");
    if certify_callee {
        attach_tv(&mut m, addmul, 2, 64, addmul_source_body(64));
    }
    // fun (G : Nat->Nat->Nat) (a b : Nat) => G (G a b) b
    let g = || Expr::bvar(2);
    let body = Expr::apps(
        g(),
        [
            Expr::apps(g(), [Expr::bvar(1), Expr::bvar(0)]),
            Expr::bvar(0),
        ],
    );
    let g_ty = Expr::arrow(nat(), Expr::arrow(nat(), nat()));
    let close = |inner: Expr| Expr::lam(BinderInfo::Default, g_ty.clone(), lam_nat(2, inner));
    let id = u32::try_from(m.proof_obligations.len()).unwrap();
    let obligation = tv_obligation(id, twice, "twice", 64);
    let cert = tv_certificate(
        &obligation,
        "twice",
        &close(body.clone()),
        &close(refl_nat(body)),
    );
    m.proof_obligations.push(obligation);
    m.proof_certificates.push(cert);
    (m, addmul, submul, twice)
}

fn b3_gap_compositional_certificate_binds_neither_callee_identity_nor_callee_proof() {
    // Baseline: callee AND caller certified, and (since WS1.4, 795f57f8) the
    // caller grounded by `InheritedFromCallee{addmul, #0}`; validates on the
    // three layers the rows below probe.
    let grounded = || {
        let (mut m, addmul, submul, twice) = composition_with_decoy(true);
        m.proof_certificates.push(inherited_tv(1, addmul, 0));
        (m, addmul, submul, twice)
    };
    let layers = |m: &Module| {
        [
            validate_module(m),
            validate_module_with_authority(m, &RejectingModuleProofAuthority),
            validate_module_for_codegen(m),
        ]
    };
    // `true` iff every layer refuses with EXACTLY the named composition
    // refusals on `obligation` (each needle one error) plus, when a grounding
    // row is present, its one all-or-nothing follow-on (a failed Certified
    // recheck empties the kernel tier, so the row's cited obligation #0 is no
    // longer discharged: `InheritedProofNotDischarged`), plus — on the CODEGEN
    // layer only (roadmap WS1.5) — one `GatedWithoutEvidence` per
    // `Gated{clean-kernel-tv}` body, whose certificate the emptied kernel tier
    // no longer holds; nothing else.
    let refused_on_every_layer = |m: &Module, obligation: u32, needles: &[&str]| {
        let rows = m
            .proof_certificates
            .iter()
            .filter(|c| matches!(c.evidence, ProofEvidence::InheritedFromCallee { .. }))
            .count();
        let kernel_tv_bodies = m
            .functions
            .iter()
            .filter(|f| {
                f.body_gate
                    == Some(BodyGate::Gated {
                        authority: CLEAN_KERNEL_TV_AUTHORITY.into(),
                        evidence: None,
                    })
            })
            .count();
        layers(m).iter().enumerate().all(|(layer, errors)| {
            let licenses = errors
                .iter()
                .filter(|e| matches!(e, ValidationError::GatedWithoutEvidence { .. }))
                .count();
            let license_ok = errors.iter().all(|e| match e {
                ValidationError::GatedWithoutEvidence { detail, .. } => {
                    detail.contains("was not kernel-replayed")
                }
                _ => true,
            }) && licenses == if layer == 2 { kernel_tv_bodies } else { 0 };
            let follow_ons = errors
                .iter()
                .filter(|e| {
                    matches!(
                        e,
                        ValidationError::InheritedProofNotDischarged {
                            obligation: o,
                            inherited_obligation: 0,
                            ..
                        } if *o == obligation
                    )
                })
                .count();
            follow_ons == rows
                && license_ok
                && errors.len() == needles.len() + rows + licenses
                && needles.iter().all(|needle| {
                    errors.iter().any(|e| {
                        matches!(
                            e,
                            ValidationError::CertifiedCleanCicKernelRecheckFailed {
                                obligation: o,
                                reason,
                            } if *o == obligation && reason.contains(needle)
                        )
                    })
                })
        })
    };
    let (base, _, _, _) = grounded();
    let base_layers = layers(&base);
    assert!(feature_check(
        "b3.gap.composition.baseline_certifies",
        base_layers.iter().all(Vec::is_empty),
        &format!(
            "addmul + twice both Certified, twice grounded at addmul's TV obligation; \
             validate_module / with_authority / for_codegen => {base_layers:?}"
        ),
    ));

    // FLIPPED (closed upstream by 795f57f8, roadmap WS1.4, F-005): the caller
    // was `Certified` although its callee carried NO certificate at all --
    // nothing required the `InheritedFromCallee` grounding. PASS: the caller
    // with an uncertified callee and no row is refused on every layer by
    // exactly one named composition refusal. Negative twin / baseline: the
    // grounded module above certifies on the same layers.
    let (ungrounded, _, _, _) = composition_with_decoy(false);
    let ungrounded_layers = layers(&ungrounded);
    assert!(feature_check(
        "b3.gap.composition.callee_need_not_be_certified",
        refused_on_every_layer(
            &ungrounded,
            0,
            &["callee `addmul` (fn#0) is called by `twice` but no InheritedFromCallee row"],
        ) && base_layers.iter().all(Vec::is_empty),
        &format!(
            "closed upstream by 795f57f8: twice certified over an UNCERTIFIED callee with no \
             grounding row => {ungrounded_layers:?}"
        ),
    ));

    // FLIPPED (closed upstream by 795f57f8, WS1.4): a call-retargeting
    // miscompile was NOT detected, the callee being an opaque forall-bound
    // symbol on both sides. PASS: retargeting every call from `addmul` to the
    // same-signature `submul` (the grounding row left alone -- the c04 face)
    // is refused on every layer by exactly the two composition refusals: the
    // called `submul` has no row, and the row names an `addmul` that is no
    // longer called. twice(6,7) goes 384 -> 216.
    let (mut retargeted, _addmul, submul, twice) = grounded();
    let before = run_with_args(&retargeted, "twice", vec![u64v(6), u64v(7)]);
    for node in &mut retargeted.function_by_id_mut(twice).unwrap().blocks[0].body {
        if let Inst::Call { callee, .. } = &mut node.inst {
            *callee = submul;
        }
    }
    let after = run_with_args(&retargeted, "twice", vec![u64v(6), u64v(7)]);
    let retargeted_layers = layers(&retargeted);
    let retarget_refused = refused_on_every_layer(
        &retargeted,
        1,
        &[
            "callee `submul` (fn#1) is called by `twice` but no InheritedFromCallee row",
            "InheritedFromCallee row names `addmul` (fn#0), which `twice` never calls",
        ],
    );
    assert!(feature_check(
        "b3.gap.composition.call_retargeting_not_detected",
        retarget_refused
            && first_u128(&before) == Some(384)
            && first_u128(&after) == Some(216)
            && base_layers.iter().all(Vec::is_empty),
        &format!(
            "closed upstream by 795f57f8: post-certification retarget addmul->submul in `twice` \
             (twice(6,7) {:?} -> {:?}) => {retargeted_layers:?}",
            first_u128(&before),
            first_u128(&after)
        ),
    ));

    // FLIPPED (closed upstream by 795f57f8, WS1.4): the inheritance row was
    // never compared with the callees the body actually calls. PASS: the row
    // naming `addmul` on a body that calls only `submul` is refused by name
    // ("... which `twice` never calls"), under validate_module. Negative twin:
    // the same row on the unretargeted body validates (baseline above).
    let e = validate_module(&retargeted);
    assert!(feature_check(
        "b3.gap.composition.inherited_callee_not_compared_with_called_callee",
        e.iter().any(|x| matches!(
            x,
            ValidationError::CertifiedCleanCicKernelRecheckFailed { obligation: 1, reason }
                if reason.contains("InheritedFromCallee row names `addmul` (fn#0), which `twice` never calls")
        )) && base_layers[0].is_empty(),
        &format!(
            "closed upstream by 795f57f8: caller grounded at addmul's TV obligation, body \
             retargeted to submul => {e:?}"
        ),
    ));

    // FLIPPED (closed by WS1.12a, F-005 residual): the CONSISTENT edit --
    // retarget the calls AND rewrite the grounding row to an honestly
    // certified `submul` of the same arity and name rank -- was ACCEPTED,
    // the TV statement being callee-agnostic and the certificate recording
    // no callee list. PASS: with BOUND certificates (`CertificateBinding.
    // callees`, minted by `certify_identity_lineage_rung_bound`), the same
    // edit is refused on all three layers by exactly one
    // `CertificateBindingMismatch { field: "callees" }` on the caller's
    // obligation (plus the all-or-nothing follow-ons the other composition
    // rows carry). Negative twin / baseline: the honest bound module
    // validates on the same layers. The legacy UNBOUND form of the edit is
    // still accepted by the default lanes and refused only under
    // `ValidationConfig::with_bound_certificates(true)` -- recorded in the
    // detail as the disclosed residual for pre-binding certificates.
    let bound = |m: &Module, obligation: u32, func: FuncId| {
        trust_ir_build::certify_identity_lineage_rung_bound(
            m,
            ProofLineageId::new(0),
            ProofId::new(obligation),
            ProofTransform::new(
                ProofTransformStage::Frontend,
                "identity",
                "partb-b3",
                "1.0.0",
            ),
            func,
        )
        .map(|(_node, obligation, certificate)| (obligation, certificate))
    };
    let (mut consistent, addmul, submul, twice) = composition_with_decoy(false);
    consistent.proof_obligations.clear();
    consistent.proof_certificates.clear();
    let mut minted_ok = true;
    for (id, func) in [(0u32, addmul), (1, twice), (2, submul)] {
        match bound(&consistent, id, func) {
            Ok((obligation, certificate)) => {
                consistent.proof_obligations.push(obligation);
                consistent.proof_certificates.push(certificate);
            }
            Err(_) => minted_ok = false,
        }
    }
    consistent
        .proof_certificates
        .push(inherited_tv(1, addmul, 0));
    let honest_baseline = layers(&consistent);
    for node in &mut consistent.function_by_id_mut(twice).unwrap().blocks[0].body {
        if let Inst::Call { callee, .. } = &mut node.inst {
            *callee = submul;
        }
    }
    let row = consistent
        .proof_certificates
        .iter()
        .position(|c| matches!(c.evidence, ProofEvidence::InheritedFromCallee { .. }))
        .expect("the grounding row");
    consistent.proof_certificates[row] = inherited_tv(1, submul, 2);
    let after = run_with_args(&consistent, "twice", vec![u64v(6), u64v(7)]);
    let consistent_layers = layers(&consistent);
    let refused_by_callees = consistent_layers.iter().all(|errors| {
        errors
            .iter()
            .filter(|e| {
                matches!(
                    e,
                    ValidationError::CertificateBindingMismatch { obligation: 1, field, detail }
                        if field == "callees"
                            && detail.contains("[\"addmul\"]")
                            && detail.contains("[\"submul\"]")
                )
            })
            .count()
            == 1
            && errors.iter().all(|e| {
                matches!(
                    e,
                    ValidationError::CertificateBindingMismatch { obligation: 1, .. }
                        | ValidationError::InheritedProofNotDischarged { obligation: 1, .. }
                        | ValidationError::GatedWithoutEvidence { .. }
                )
            })
    });
    // The legacy unbound form of the same edit (the archived shape).
    let (mut legacy, _addmul, submul, twice) = grounded();
    let legacy_submul = u32::try_from(legacy.proof_obligations.len()).unwrap();
    if let Ok((obligation, certificate)) = identity_rung(&legacy, legacy_submul, submul) {
        legacy.proof_obligations.push(obligation);
        legacy.proof_certificates.push(certificate);
    }
    for node in &mut legacy.function_by_id_mut(twice).unwrap().blocks[0].body {
        if let Inst::Call { callee, .. } = &mut node.inst {
            *callee = submul;
        }
    }
    let row = legacy
        .proof_certificates
        .iter()
        .position(|c| matches!(c.evidence, ProofEvidence::InheritedFromCallee { .. }))
        .expect("the grounding row");
    legacy.proof_certificates[row] = inherited_tv(1, submul, legacy_submul);
    let legacy_default = validate_module(&legacy);
    let legacy_strict = trust_ir_build::validate_module_with_config(
        &legacy,
        &trust_ir_build::ValidationConfig::pinned().with_bound_certificates(true),
    )
    .into_errors();
    let legacy_disclosed = legacy_default.is_empty()
        && legacy_strict.len() == 3
        && legacy_strict
            .iter()
            .all(|e| matches!(e, ValidationError::UnboundCertificate { .. }));
    assert!(feature_check(
        "b3.gap.composition.consistent_retarget_to_certified_callee",
        minted_ok
            && honest_baseline.iter().all(Vec::is_empty)
            && first_u128(&after) == Some(216)
            && refused_by_callees
            && legacy_disclosed,
        &format!(
            "closed by WS1.12a (CertificateBinding.callees): bound addmul/twice/submul, retarget \
             addmul->submul AND the row -> InheritedFromCallee{{submul, #2}}: validate_module / \
             with_authority / for_codegen => {consistent_layers:?} while twice(6,7) = {:?}; the \
             honest bound baseline => {honest_baseline:?}; the legacy UNBOUND edit is still \
             accepted by validate_module ({legacy_default:?}) and refused under \
             require_bound_certificates ({legacy_strict:?}). TWO DISCLOSED RESIDUALS, pinned \
             in trust-ir-build/tests/certificate_binding.rs: an unbound certificate carries no \
             callee list, so the same edit passes the default lanes until producers mint bound \
             certificates; and an adversary that ALSO re-mints the binding and re-keys the v8 \
             lineage is stopped only by comparand<->source binding (F-008 -> WS1.13)",
            first_u128(&after)
        ),
    ));
}

fn inherited_tv(
    caller_obligation: u32,
    callee: FuncId,
    callee_obligation: u32,
) -> ProofCertificate {
    ProofCertificate {
        obligation: ProofId::new(caller_obligation),
        prover: "clean-backend-tv-compose".to_string(),
        evidence: ProofEvidence::InheritedFromCallee {
            callee,
            obligation: ProofId::new(callee_obligation),
            external: None,
        },
        assurance: None,
    }
}

/// The design's END STATE for Fragment-3b (validate.rs:13699-13701): the caller
/// obligation carries the parametric CleanCic AND an `InheritedFromCallee`
/// certificate grounding the opaque callee symbol at the callee's OWN
/// kernel-certified TV obligation.
fn b3_compositional_grounding_is_carried_and_checked_when_present() {
    let (mut m, addmul, submul, twice) = composition_with_decoy(true);
    // obligation 0 = addmul's TV, obligation 1 = twice's TV.
    m.proof_certificates.push(inherited_tv(1, addmul, 0));
    let e = validate_module(&m);
    let strict = validate_module_with_authority(&m, &RejectingModuleProofAuthority);
    let refs = validate_module_report(&m)
        .replayed_certificate_refs()
        .map(|r| r.len());
    let rt = roundtrip_all(&m);
    assert!(feature_check(
        "b3.fragment3b.grounded_by_inherited_callee_certificate",
        e.is_empty() && strict.is_empty() && refs == Some(2) && rt.lossless_production(),
        &format!(
            "twice: CleanCic + InheritedFromCallee{{callee: addmul, obligation: 0}}; \
             validate_module={e:?} with_authority={strict:?} kernel-tier refs={refs:?}; {}",
            rt.summary()
        ),
    ));

    // twin 1: the callee is miscompiled (Mul->Add in addmul). Its own
    // certificate fails, the kernel tier empties (all-or-nothing,
    // validate.rs:12319), and the caller's inheritance no longer bottoms out.
    let mut bad = m.clone();
    mul_to_add(&mut bad, addmul);
    let e = validate_module(&bad);
    let kernel = e.iter().any(|x| {
        matches!(
            x,
            ValidationError::CertifiedCleanCicKernelRecheckFailed { obligation: 0, reason }
                if reason.contains("in-process kernel REJECTED")
        )
    });
    let ungrounded = e.iter().any(|x| {
        matches!(
            x,
            ValidationError::InheritedProofNotDischarged {
                obligation: 1,
                inherited_obligation: 0,
                ..
            }
        )
    });
    // Since WS1.4 (795f57f8) the composition rule adds its own named refusal:
    // the row cites an obligation that is no longer kernel-rechecked.
    let composition = e.iter().any(|x| {
        matches!(
            x,
            ValidationError::CertifiedCleanCicKernelRecheckFailed { obligation: 1, reason }
                if reason.contains("callee `addmul` (fn#0) has no kernel-rechecked clean_backend_tv obligation of its own")
        )
    });
    assert!(feature_check(
        "b3.fragment3b.grounding.negative_twin.miscompiled_callee",
        kernel && ungrounded && composition && e.len() == 3,
        &format!("{e:?}"),
    ));

    // twin 2: the inheritance names the same-signature decoy `submul`, but the
    // inherited obligation is scoped to `addmul`.
    let mut bad = m.clone();
    let last = bad.proof_certificates.len() - 1;
    bad.proof_certificates[last] = inherited_tv(1, submul, 0);
    let e = validate_module(&bad);
    // Since WS1.4 (795f57f8) the scope mismatch is joined by the composition
    // rule's two named refusals (the row names an uncalled `submul`; the
    // called `addmul` has no row) and their all-or-nothing follow-on.
    let scope_mismatch = e.iter().any(|x| {
        matches!(
            x,
            ValidationError::InheritedProofCalleeScopeMismatch {
                obligation: 1,
                named_callee,
                actual_owner,
            } if *named_callee == submul.index() && *actual_owner == addmul.index()
        )
    });
    let composition = |needle: &str| {
        e.iter().any(|x| {
            matches!(
                x,
                ValidationError::CertifiedCleanCicKernelRecheckFailed { obligation: 1, reason }
                    if reason.contains(needle)
            )
        })
    };
    let follow_on = e.iter().any(|x| {
        matches!(
            x,
            ValidationError::InheritedProofNotDischarged {
                obligation: 1,
                inherited_obligation: 0,
                ..
            }
        )
    });
    assert!(feature_check(
        "b3.fragment3b.grounding.negative_twin.wrong_callee_scope",
        e.len() == 4
            && scope_mismatch
            && follow_on
            && composition(
                "InheritedFromCallee row names `submul` (fn#1), which `twice` never calls"
            )
            && composition(
                "callee `addmul` (fn#0) is called by `twice` but no InheritedFromCallee row"
            ),
        &format!("{e:?}"),
    ));
    let _ = twice;
}

/// FINDING: the `clean_backend_tv` anchor never consults `Function.producer`
/// (validate.rs:15001-15107 reads the function's type, blocks and name only).
/// Since WS1.4 (795f57f8, F-016 DECIDE A) this is a DOCUMENTED PROPERTY: the
/// anchor is producer-agnostic by decision (`Producer` docs, TRUST.md item 6).
/// As the roadmap directs, the row stays GAP (by design) rather than flipping.
fn b3_gap_tv_certificate_is_not_bound_to_the_clean_producer() {
    // Baseline: the Clean-producer addmul certifies (b3.addmul.*).
    let (mut m, addmul) = certified_addmul(Ty::U64, 64, false);
    assert!(validate_module(&m).is_empty(), "baseline must certify");
    // Single change: the SAME function claims `Producer::TRust`.
    m.function_by_id_mut(addmul).unwrap().producer = Some(Producer::TRust);
    let e = validate_module(&m);
    let strict = validate_module_with_authority(&m, &RejectingModuleProofAuthority);
    let refs = validate_module_report(&m)
        .replayed_certificate_refs()
        .map(|r| r.len());
    assert!(feature_gap(
        "b3.gap.tv_certificate_not_bound_to_producer",
        Expect::Accepted,
        Outcome::of(&[e.clone(), strict.clone()].concat())
            .given(&[("the kernel tier replayed it", refs == Some(1))]),
        &format!(
            "a Producer::TRust body carries a kernel-tier `clean_backend_tv` certificate \
             (module CleanCompiler.BackendTV): validate_module={e:?} with_authority={strict:?} \
             refs={refs:?} — the equation is true, but NOTHING in-band says the comparand is a \
             Clean source definition (validate.rs:13754-13764 'HONEST SCOPE')"
        ),
    ));
}

/// FLIPPED (WS1.13, the check half of F-008). What a `clean_backend_tv`
/// certificate proves is "the emitted function denotes the RECORDED
/// comparand", and the comparand is the minter's choice — so a producer that
/// miscompiled and THEN minted was indistinguishable, to a consumer of the
/// module alone, from an honest one (validate.rs:13754-13764 "HONEST SCOPE"
/// at 4efb21bc). WS1.13 binds the comparand to the SOURCE for a certificate
/// that carries an ISLAND: the comparand must be definitionally equal to the
/// value of `source.decl` in the island, so the miscompile-then-mint forgery
/// carrying the honest island is refused by name. The island-free form keeps
/// its mint-time meaning on the default lanes (the roadmap's control) and is
/// refused under `ValidationConfig::with_source_bound_certificates(true)` —
/// the disclosed residual, closed for real once producers mint island-bound
/// certificates (WS6.7).
fn b3_gap_comparand_is_not_bound_to_a_source_definition() {
    use trust_ir_build::{ValidationConfig, validate_module_with_config};
    let (honest, addmul) = certified_addmul(Ty::U64, 64, true);
    assert!(
        validate_module(&honest).is_empty(),
        "honest module certifies"
    );

    // Baseline (REFUSED — this is b3.addmul.negative_twin.mul_to_add): the
    // miscompiled body under the honest certificate.
    let mut miscompiled = honest.clone();
    mul_to_add(&mut miscompiled, addmul);
    let baseline = validate_module(&miscompiled);
    assert!(
        sole_kernel_rejection(&baseline, 0, "addmul"),
        "baseline must be the kernel refusal: {baseline:?}"
    );

    // The island-FREE forgery: the certificate is minted AFTER the
    // miscompile, its comparand being the miscompiled term
    // `((a+b) % M + a) % M` instead of the source `((a*b) % M + a) % M`.
    let (mut forged, f) = addmul_module(Ty::U64, true);
    mul_to_add(&mut forged, f);
    let a = || Expr::bvar(1);
    let b = || Expr::bvar(0);
    let wrong = wmod(
        app2("Nat.add", wmod(app2("Nat.add", a(), b()), 64), a()),
        64,
    );
    attach_tv(&mut forged, f, 2, 64, wrong.clone());
    let island_free_default = validate_module(&forged);
    let ran = run_nullary(&forged, "program");
    let source_bound_policy = ValidationConfig::pinned().with_source_bound_certificates(true);
    let island_free_strict =
        validate_module_with_config(&forged, &source_bound_policy).into_errors();
    let island_free_refused_under_policy = matches!(
        island_free_strict.as_slice(),
        [ValidationError::CertificateBindingMismatch { obligation: 0, field, .. }]
            if field == "environment"
    );

    // The island-BOUND forgery: the SAME miscompile-then-mint, but the
    // certificate carries the island declaring the honest source
    // `Envelope.addmul`. Minted as the forger would: an island whose
    // `Envelope.addmul` IS the miscompiled term (self-consistent, so the
    // minter's own source check passes), then the island swapped for the
    // honest one with the honest environment digest, the lineage re-keyed.
    let island_of = |value: Expr| {
        IslandEnvironment::new(
            encode_island_declarations_v1(&[Declaration::Definition {
                name: Name::from_string("Envelope.addmul"),
                level_params: vec![],
                type_: pi_nat(2, nat()),
                value: lam_nat(2, value),
                is_reducible: true,
            }])
            .expect("island encodes"),
        )
    };
    let honest_island = island_of(addmul_source_body(64));
    let forged_island = island_of(wrong);
    let mint = |m: &Module, func: FuncId, island: &IslandEnvironment| {
        certify_identity_lineage_rung_island_bound(
            m,
            ProofLineageId::new(0),
            ProofId::new(0),
            ProofTransform::new(
                ProofTransformStage::Frontend,
                "identity",
                "partb-b3",
                "1.0.0",
            ),
            func,
            island,
            SourceDefinitionRef {
                decl: "Envelope.addmul".into(),
                closure_digest: trust_ir::proof::ProofDigest::sha256([0x61; 32]),
            },
        )
    };
    let honest_environment = {
        let (h, hf) = addmul_module(Ty::U64, true);
        let (_, _, c) = mint(&h, hf, &honest_island).expect("honest addmul is its source");
        c.evidence
            .clean_cic_kernel_recheck()
            .and_then(|r| r.binding.as_deref())
            .expect("bound")
            .environment_digest
    };
    let honest_minter_refuses = mint(&forged, f, &honest_island).is_err();
    let (mut bound_forged, bf) = addmul_module(Ty::U64, true);
    mul_to_add(&mut bound_forged, bf);
    let (_, obligation, mut certificate) =
        mint(&bound_forged, bf, &forged_island).expect("a self-consistent forged island mints");
    let self_consistent_accepted = {
        let mut m = bound_forged.clone();
        m.proof_obligations.push(obligation.clone());
        m.proof_certificates.push(certificate.clone());
        validate_module(&m).is_empty()
    };
    if let ProofEvidence::CleanCic {
        lineage,
        kernel_recheck: Some(recheck),
        ..
    } = &mut certificate.evidence
    {
        let binding = recheck.binding.as_deref_mut().expect("bound");
        binding.environment = Some(honest_island);
        binding.environment_digest = honest_environment;
        let resolve = |id: FuncId| bound_forged.function_by_id(id).map(|g| g.name.clone());
        *lineage =
            trust_ir::proof::clean_cic_lineage_digest_v8(&obligation, &resolve, Some(binding))
                .expect("keyable");
    }
    bound_forged.proof_obligations.push(obligation);
    bound_forged.proof_certificates.push(certificate);
    let bound_errors = validate_module(&bound_forged);
    let bound_refused = sole_recheck_refusal(&bound_errors, 0).is_some_and(|r| {
        r.contains("the TV comparand is not the value of island declaration `Envelope.addmul`")
    });
    assert!(feature_check(
        "b3.gap.comparand_not_bound_to_source_definition",
        bound_refused
            && honest_minter_refuses
            && self_consistent_accepted
            && island_free_default.is_empty()
            && first_u128(&ran) == Some(19)
            && island_free_refused_under_policy,
        &format!(
            "closed by WS1.13 for island-bound certificates (F-008): the miscompiled addmul \
             (a+b+a; program()={:?}, honest=48) with a certificate minted AFTER the miscompile \
             and carrying the island that declares the honest source Envelope.addmul => \
             {bound_errors:?}; the public island minter refuses the miscompile against the \
             honest island ={honest_minter_refuses}; a SELF-CONSISTENT forged island is its own \
             source and validates ={self_consistent_accepted} (a theorem about the honest \
             Envelope.addmul is not bridged to it: another island digest). DISCLOSED RESIDUAL: \
             the island-FREE forgery keeps its mint-time meaning on validate_module => \
             {island_free_default:?}, and is refused under with_source_bound_certificates => \
             {island_free_strict:?}",
            first_u128(&ran)
        ),
    ));
}

/// The design's Lean -> Rust edge at the kernel-certified tier: a Clean function
/// whose body CALLS a `Producer::TRust` function.
///
/// RATIFIED-OUT (roadmap WS1.4 design item 4, landed 795f57f8): the archived
/// PASS row certified this caller with the Rust callee an opaque, UNGROUNDED
/// `Nat -> Nat -> Nat` symbol -- the same shape as
/// `b3.gap.composition.callee_need_not_be_certified` (F-005). WS1.4 ratifies
/// that "a callee with no TV (a `clean_*` runtime declaration or a non-Clean
/// body) can never satisfy (b). Its caller must be emitted Pending, which is
/// the disclosed incomplete state G4 names." The row holds that exact shape:
/// the Certified claim is refused by name on every layer, and the SAME
/// obligation emitted Pending (no certificate) validates and runs.
fn b3_clean_function_calling_rust_certifies_with_the_rust_callee_opaque() {
    let mut mb = ModuleBuilder::new("b3_clean_calls_rust");
    let binary = mb.add_func_type(vec![Ty::U64, Ty::U64], vec![Ty::U64]);
    let rust_leaf = {
        let mut fb = mb.function("rust_leaf", binary);
        fb.set_producer(Producer::TRust);
        fb.set_body_gate(BodyGate::Gated {
            authority: "trust-verify".into(),
            evidence: None,
        });
        let entry = fb.create_block();
        let a = fb.add_block_param(entry, Ty::U64);
        let b = fb.add_block_param(entry, Ty::U64);
        fb.switch_to_block(entry);
        // Deliberately OUTSIDE the TV fragment (UDiv-free but uses Xor): the
        // Rust body is never denoted.
        let x = fb.binop(BinOp::Xor, Ty::U64, a, b);
        fb.ret(vec![x]);
        fb.build()
    };
    let via_rust = {
        let mut fb = mb.function("via_rust", binary);
        fb.set_producer(Producer::Clean);
        fb.set_body_gate(BodyGate::Gated {
            authority: CLEAN_KERNEL_TV_AUTHORITY.into(),
            evidence: None,
        });
        let entry = fb.create_block();
        let a = fb.add_block_param(entry, Ty::U64);
        let b = fb.add_block_param(entry, Ty::U64);
        fb.switch_to_block(entry);
        let r = fb.call(rust_leaf, vec![a, b]);
        let out = fb.add(Ty::U64, r, a);
        fb.ret(vec![out]);
        fb.build()
    };
    let mut m = mb.build().expect("ModuleBuilder::build: test fixture");
    // fun (R : Nat->Nat->Nat) (a b : Nat) => (R a b + a) % 2^64
    let body = wmod(
        app2(
            "Nat.add",
            Expr::apps(Expr::bvar(2), [Expr::bvar(1), Expr::bvar(0)]),
            Expr::bvar(1),
        ),
        64,
    );
    let r_ty = Expr::arrow(nat(), Expr::arrow(nat(), nat()));
    let close = |inner: Expr| Expr::lam(BinderInfo::Default, r_ty.clone(), lam_nat(2, inner));
    let obligation = tv_obligation(0, via_rust, "via_rust", 64);
    let cert = tv_certificate(
        &obligation,
        "via_rust",
        &close(body.clone()),
        &close(refl_nat(body)),
    );
    m.proof_obligations.push(obligation);
    m.proof_certificates.push(cert);

    let e = validate_module(&m);
    let strict = validate_module_with_authority(&m, &RejectingModuleProofAuthority);
    let codegen = validate_module_for_codegen(&m);
    let ran = run_with_args(&m, "via_rust", vec![u64v(6), u64v(7)]);
    // The ratified alternative: the same obligation emitted Pending, with no
    // certificate at all.
    let mut pending = m.clone();
    pending.proof_certificates.clear();
    pending.proof_obligations[0].status = ProofStatus::Pending;
    let pending_errors = validate_module(&pending);
    let rt = roundtrip_all(&pending);
    let needle = "callee `rust_leaf` (fn#0) is called by `via_rust` but no InheritedFromCallee row";
    let refusal = |errors: &[ValidationError]| {
        matches!(
            errors,
            [ValidationError::CertifiedCleanCicKernelRecheckFailed { obligation: 0, reason }]
                if reason.contains(needle)
        )
    };
    // The codegen lane adds exactly the WS1.5 license follow-on: `via_rust`
    // still wears `Gated{clean-kernel-tv}`, and its refused certificate was
    // not kernel-replayed.
    let same_on_every_layer = refusal(&strict)
        && codegen.len() == 2
        && refusal(&codegen[..1])
        && matches!(
            &codegen[1],
            ValidationError::GatedWithoutEvidence { function, detail, .. }
                if *function == via_rust.index() && detail.contains("was not kernel-replayed")
        );
    assert!(feature_ratified(
        "b3.fragment3b.clean_calls_rust_opaque_callee",
        Expect::refused_with(
            "CertifiedCleanCicKernelRecheckFailed",
            &["obligation: 0", needle]
        ),
        Outcome::of(&e).given(&[
            (
                "with_authority and for_codegen refuse identically (for_codegen plus its WS1.5 license follow-on)",
                same_on_every_layer
            ),
            ("the Pending emission validates", pending_errors.is_empty()),
            (
                "the Pending emission survives the production transports",
                rt.lossless_production()
            ),
            (
                "via_rust(6,7) = (6^7)+6 on the interpreter",
                first_u128(&ran) == Some((6 ^ 7) + 6)
            ),
        ]),
        &format!(
            "[Clean] via_rust(a,b) = [TRust] rust_leaf(a,b) + a claimed Certified => \
             validate_module={e:?} with_authority={strict:?} for_codegen={codegen:?}; emitted \
             Pending => {pending_errors:?}; {}; via_rust(6,7)={:?}",
            rt.summary(),
            first_u128(&ran)
        ),
    ));
}

// ===========================================================================
// WS4.15 — the Lean library envelope's facts have an in-format home
// ===========================================================================

/// The `trust.lean.ir-library/v1` envelope's `addmul` with every load-bearing
/// fact in its in-format home (`docs/SPEC_RATIFICATIONS.md` §9; the corpus
/// golden `lean_library_envelope`, whose acceptance is pinned by the gate-8
/// `lean_library_envelope_*` tests in `conformance.rs`). The rows here are the
/// halves that depend on WS1 (F-006, F-008) and on the text codec (F-070):
/// each GAP asserts today's exact wrong outcome and flips with its finding.
fn b3_envelope_every_fact_has_an_in_format_home() {
    let honest = generate::build_lean_library_envelope().expect("the fixture builds");
    let addmul = honest.function_by_name("addmul").expect("addmul").id;
    // The TV obligation is the LAST row (id 1); the theorem reference is id 0.
    const TV: u32 = 1;

    // PASS — the baseline every row below mutates.
    let e = validate_module(&honest);
    let strict = validate_module_with_authority(&honest, &RejectingModuleProofAuthority);
    let codegen = validate_module_for_codegen(&honest);
    let refs = validate_module_report(&honest)
        .replayed_certificate_refs()
        .map(|r| r.len());
    let rt = roundtrip_all(&honest);
    let honest_run = run_with_args(&honest, "addmul", vec![u64v(6), u64v(7)]);
    assert!(feature_check(
        "b3.envelope.certifies",
        e.is_empty()
            && strict.is_empty()
            && codegen.is_empty()
            && refs == Some(1)
            && rt.lossless_production()
            && rt.binary_version == 41
            && first_u128(&honest_run) == Some(48),
        &format!(
            "envelope addmul: validate_module={e:?} with_authority={strict:?} \
             for_codegen={codegen:?} kernel-tier refs={refs:?}; {}; addmul(6,7)={:?}",
            rt.summary(),
            first_u128(&honest_run)
        ),
    ));

    // PASS — negative twin: the body miscompiled (`a*b + a` -> `a+b + a`)
    // under the SAME certificate is refused by the kernel at every layer (the
    // codegen layer adding its WS1.5 license follow-on).
    let mut miscompiled = honest.clone();
    mul_to_add(&mut miscompiled, addmul);
    let layers = [
        validate_module(&miscompiled),
        validate_module_with_authority(&miscompiled, &RejectingModuleProofAuthority),
        validate_module_for_codegen(&miscompiled),
    ];
    assert!(feature_check(
        "b3.envelope.negative_twin.same_certificate_mutated_body",
        layers[..2]
            .iter()
            .all(|errors| sole_kernel_rejection(errors, TV, "addmul"))
            && kernel_rejection_revokes_license(&layers[2], TV, "addmul", addmul),
        &format!("a+b+a under the honest certificate: {layers:?}"),
    ));

    // GAP (F-008) — the certificate RE-MINTED against the miscompiled body
    // (comparand `((a+b) % M + a) % M`) certifies: nothing binds the comparand
    // to the Clean SOURCE definition. Every row a consumer can READ — both
    // obligations, the carrier/method formula, prover and kernel directive —
    // is identical to the honest module's; only the opaque term/context bytes
    // differ. Flips when WS1.12 puts F-008's source-definition digest on
    // `CleanCicKernelRecheck` (the envelope's `source_closure_sha256` home).
    let mut forged = miscompiled.clone();
    let tv = forged.proof_obligations[TV as usize].clone();
    forged.proof_certificates[0] =
        generate::lean_envelope_tv_certificate(&tv, generate::lean_envelope_terms::add_add_body())
            .expect("the fixture builds");
    let e = validate_module(&forged);
    let strict = validate_module_with_authority(&forged, &RejectingModuleProofAuthority);
    let codegen = validate_module_for_codegen(&forged);
    let refs = validate_module_report(&forged)
        .replayed_certificate_refs()
        .map(|r| r.len());
    let ran = run_with_args(&forged, "addmul", vec![u64v(6), u64v(7)]);
    let directive = |m: &Module| match &m.proof_certificates[0].evidence {
        ProofEvidence::CleanCic { kernel_recheck, .. } => kernel_recheck.clone(),
        _ => None,
    };
    let same_readable_surface = forged.proof_obligations == honest.proof_obligations
        && forged.proof_certificates[0].prover == honest.proof_certificates[0].prover
        && directive(&forged) == directive(&honest)
        && directive(&forged).is_some();
    assert!(feature_gap(
        "b3.envelope.gap.recertified_mutation_not_bound_to_source",
        Expect::Accepted,
        Outcome::of(&[e.clone(), strict.clone(), codegen.clone()].concat()).given(&[
            ("the kernel tier replayed it", refs == Some(1)),
            (
                "the miscompiled addmul(6,7) returns 19, not 48",
                first_u128(&ran) == Some(19)
            ),
            (
                "the readable surface equals the honest module's",
                same_readable_surface
            ),
        ]),
        &format!(
            "envelope addmul miscompiled to a+b+a with a certificate minted AFTER the \
             miscompile: validate_module={e:?} with_authority={strict:?} for_codegen={codegen:?} \
             refs={refs:?}; addmul(6,7)={:?}; readable surface identical={same_readable_surface}",
            first_u128(&ran)
        ),
    ));

    // FLIPPED by WS1.5 (F-006) — mutation control: drop the TV obligation and
    // its certificate. The license `Gated{"clean-kernel-tv"}` then names a
    // certificate that does not exist, and the codegen gate refuses it by name
    // (`GatedWithoutEvidence`). Sole-cause twin: the same drop with the body
    // `Ungated` is refused as `UngatedBodyForCodegen` instead, so the refusal
    // above is the evidence rule's, not a side effect of the drop.
    let mut dropped = honest.clone();
    dropped.proof_obligations.pop();
    dropped.proof_certificates.pop();
    let codegen = validate_module_for_codegen(&dropped);
    let mut ungated = dropped.clone();
    ungated.function_by_id_mut(addmul).unwrap().body_gate = Some(BodyGate::Ungated);
    let ungated_refused = matches!(
        validate_module_for_codegen(&ungated).as_slice(),
        [ValidationError::UngatedBodyForCodegen { name, .. }] if name == "addmul"
    );
    let no_tv_row = !dropped
        .proof_obligations
        .iter()
        .any(|o| o.kind == ObligationKind::TranslationValidation);
    let refused = matches!(
        codegen.as_slice(),
        [ValidationError::GatedWithoutEvidence { function, authority, detail }]
            if *function == addmul.index()
                && authority == CLEAN_KERNEL_TV_AUTHORITY
                && detail.contains("no TranslationValidation obligation")
    );
    assert!(feature_check(
        "b3.envelope.gap.license_survives_dropped_tv_obligation",
        no_tv_row && validate_module(&dropped).is_empty() && refused && ungated_refused,
        &format!(
            "closed by WS1.5: envelope with its TV obligation + certificate dropped: \
             validate_module_for_codegen={codegen:?}; Ungated twin refused={ungated_refused}"
        ),
    ));

    // FLIPPED by WS1.5 (F-006) — the stronger mutation control: the TV
    // obligation is KEPT but marked `Failed` (an in-module refutation of the
    // very claim the license cites; its certificate dropped, since a Failed
    // row carries none). The module still validates structurally, and the
    // codegen gate now revokes the license by name (`GatedFunctionRefuted`,
    // citing the Failed row). Negative twin: the honest module (the same row
    // Certified) is admitted (b3.envelope.certifies).
    let mut refuted = honest.clone();
    refuted.proof_obligations[TV as usize].status = ProofStatus::Failed;
    refuted.proof_certificates.clear();
    let e = validate_module(&refuted);
    let codegen = validate_module_for_codegen(&refuted);
    let scoped = refuted.proof_obligations[TV as usize].function == Some(addmul);
    assert!(feature_check(
        "b3.envelope.gap.license_survives_failed_tv_obligation",
        e.is_empty()
            && scoped
            && codegen
                == vec![ValidationError::GatedFunctionRefuted {
                    function: addmul.index(),
                    obligation: TV,
                }]
            && validate_module_for_codegen(&honest).is_empty(),
        &format!(
            "closed by WS1.5: envelope with its TV obligation Failed: validate_module={e:?} \
             validate_module_for_codegen={codegen:?}"
        ),
    ));

    // FLIPPED by WS4.4 (F-071), formerly a GAP — the fourth format, first
    // blocker: canonical text could not re-read the `custom:` obligation kind
    // the theorem reference uses (and under WS4.2 refused it at print time as
    // `#lossy: obligation-kind(obligation 0 custom)`). The parser now reads
    // `custom("<ns>", "<name>")`, so the WHOLE envelope — theorem reference,
    // TV row and its kernel re-check directive — travels through text and the
    // decoded module certifies exactly as the binary one. Twin: the diagnostic
    // `custom:<ns>/<name>` spelling pasted into the text is still refused.
    let printed = String::from_utf8_lossy(&rt.text.encoded).into_owned();
    let envelope_ok = rt.text.decoded.as_ref().map(validate_module);
    let custom_line = printed
        .lines()
        .find(|line| line.starts_with("obligation 0 custom("))
        .map(str::to_owned);
    let diagnostic_refused = custom_line.as_ref().is_some_and(|line| {
        let kind_end = line.find(") ").expect("the custom kind closes");
        let ObligationKind::Custom { namespace, name } = &honest.proof_obligations[0].kind else {
            return false;
        };
        let forged = printed.replacen(
            &line[..=kind_end],
            &format!("obligation 0 custom:{namespace}/{name}"),
            1,
        );
        trust_ir::parser::parse_module(&forged).is_err()
    });
    assert!(feature_check(
        "b3.envelope.gap.text_cannot_parse_theorem_ref_kind",
        rt.text.lossless() && envelope_ok.as_ref().is_some_and(Vec::is_empty) && diagnostic_refused,
        &format!(
            "envelope text round trip: {}; decoded envelope validate_module = {envelope_ok:?}; \
             line {custom_line:?}; the diagnostic `custom:` spelling is refused = \
             {diagnostic_refused}",
            rt.text.summary()
        ),
    ));

    // FLIPPED by WS4.4 (F-070), formerly a GAP — the fourth format, second
    // blocker, isolated: the envelope WITHOUT the theorem reference (the TV
    // row renumbered to 0 and its certificate re-minted for that id). Text
    // now carries `CleanCic.kernel_recheck`, so the text copy re-certifies;
    // cutting ONLY the recheck clause makes it fail
    // `CertifiedCleanCicKernelRecheckFailed` (mutation control).
    let mut tv_only = honest.clone();
    tv_only.proof_obligations = vec![generate::lean_envelope_tv_obligation(0, addmul)];
    tv_only.proof_certificates = vec![
        generate::lean_envelope_tv_certificate(
            &tv_only.proof_obligations[0],
            generate::lean_envelope_terms::addmul_body(),
        )
        .expect("the fixture builds"),
    ];
    let tv_only_ok = validate_module(&tv_only);
    let text = roundtrip_all(&tv_only).text;
    let decoded_ok = text.decoded.as_ref().map(validate_module);
    let printed = String::from_utf8_lossy(&text.encoded).into_owned();
    let cut_refused = printed.find(" recheck module ").is_some_and(|cut| {
        let end = cut + printed[cut..].find('\n').expect("line end");
        let dropped = format!("{}{}", &printed[..cut], &printed[end..]);
        trust_ir::parser::parse_module(&dropped).is_ok_and(|m| {
            matches!(
                validate_module(&m).as_slice(),
                [ValidationError::CertifiedCleanCicKernelRecheckFailed { reason, .. }]
                    if reason.contains("carries no kernel-recheck directive")
            )
        })
    });
    assert!(feature_check(
        "b3.envelope.gap.text_drops_kernel_recheck",
        tv_only_ok.is_empty()
            && text.lossless()
            && decoded_ok.as_ref().is_some_and(Vec::is_empty)
            && cut_refused,
        &format!(
            "TV-only envelope: validate_module={tv_only_ok:?}; text {} re-certifies = \
             {decoded_ok:?}; the recheck clause cut => CertifiedCleanCicKernelRecheckFailed = \
             {cut_refused}",
            text.summary()
        ),
    ));
}

#[test]
fn two_language_b3() {
    common::run_target(
        "b3",
        &[
            (
                "b3_addmul_is_kernel_certified_and_mul_to_add_is_refused",
                b3_addmul_is_kernel_certified_and_mul_to_add_is_refused,
            ),
            (
                "b3_certificate_forgeries_are_each_refused_for_the_right_reason",
                b3_certificate_forgeries_are_each_refused_for_the_right_reason,
            ),
            (
                "b3_kernel_decides_rather_than_byte_compares",
                b3_kernel_decides_rather_than_byte_compares,
            ),
            (
                "b3_fragment_baselines_certify",
                b3_fragment_baselines_certify,
            ),
            (
                "b3_certificate_round_trips_and_recertifies",
                b3_certificate_round_trips_and_recertifies,
            ),
            (
                "b3_gap_bool_result_has_no_tv_rule",
                b3_gap_bool_result_has_no_tv_rule,
            ),
            ("b3_gap_select_has_no_tv_rule", b3_gap_select_has_no_tv_rule),
            (
                "b3_gap_enum_and_switch_have_no_tv_rule",
                b3_gap_enum_and_switch_have_no_tv_rule,
            ),
            (
                "b3_gap_signed_and_other_widths_have_no_tv_rule",
                b3_gap_signed_and_other_widths_have_no_tv_rule,
            ),
            (
                "b3_demotion_is_expressible_but_the_license_is_not_bound_to_the_certificate",
                b3_demotion_is_expressible_but_the_license_is_not_bound_to_the_certificate,
            ),
            (
                "b3_gap_user_theorem_cannot_certify_a_contract_obligation",
                b3_gap_user_theorem_cannot_certify_a_contract_obligation,
            ),
            (
                "b3_gap_compositional_certificate_binds_neither_callee_identity_nor_callee_proof",
                b3_gap_compositional_certificate_binds_neither_callee_identity_nor_callee_proof,
            ),
            (
                "b3_compositional_grounding_is_carried_and_checked_when_present",
                b3_compositional_grounding_is_carried_and_checked_when_present,
            ),
            (
                "b3_gap_tv_certificate_is_not_bound_to_the_clean_producer",
                b3_gap_tv_certificate_is_not_bound_to_the_clean_producer,
            ),
            (
                "b3_gap_comparand_is_not_bound_to_a_source_definition",
                b3_gap_comparand_is_not_bound_to_a_source_definition,
            ),
            (
                "b3_clean_function_calling_rust_certifies_with_the_rust_callee_opaque",
                b3_clean_function_calling_rust_certifies_with_the_rust_callee_opaque,
            ),
            (
                "b3_envelope_every_fact_has_an_in_format_home",
                b3_envelope_every_fact_has_an_in_format_home,
            ),
        ],
    );
}
