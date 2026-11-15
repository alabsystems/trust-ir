// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0
//
// WS1.1 — the contract grounder binds the clause to its sort, place and IR
// type (finding F-001, critical; the obligation-formula half of F-004).
//
// THE HOLE. `contract_goal` mapped any single-symbol `(>= s 0)` clause to the
// CLOSED kernel goal `∀ x : Nat, Nat.ble 0 x = true`, discarding the symbol. No
// minter or rechecker read `ProofFormula.bindings`, the `ClauseSort`, the
// obligation's function or its `FuncTy`. So `fn level() -> i64 { -1 }` with a
// `proved` `ensures (>= result 0)` reached kernel-`Certified` under every entry
// point while the interpreter returned -1 — and, through
// `proof_ref_kind_can_back`, that freely-mintable Postcondition row backed a
// `DivNonZero` claim on `1 sdiv 0`.
//
// THE RULE. The free-name tautology is produced only with the module in scope
// (`contract_goal_in` / `contract_clean_cic_certificate_in` / the
// `ModuleCleanCicRechecker` impl), and only after `bind_nat_nonneg` binds the
// symbol to a `Param` / `ResultSlot` / `MutParamExit` place whose IR type is an
// unsigned integer, read at sort `Int`. A ProofRef backs a safety-class claim
// only with a row of that claim's own kind, and a node-level ProofRef only with
// a row sited on that very node.
//
// Every negative twin below is ONE mutation of a validating fixture, and
// asserts its SPECIFIC refusal. Certificates on the negative side are FORGED
// the way an attacker would: the fixed closed-lambda proof term, re-labelled
// with the twin obligation's (publicly recomputable) lineage digest.

use clean_kernel::{BinderInfo, Environment, Expr, Level, LocalContext, Name, TypeChecker};
use trust_ir::clean_expr_lowering::contract::{
    contract_clean_cic_certificate, contract_clean_cic_certificate_in,
};
use trust_ir::inst::BinOp;
use trust_ir::proof::RejectingModuleProofAuthority;
use trust_ir::proof::{
    ClauseBinding, ClausePlace, ClauseSort, ModuleCleanCicRechecker, ModuleProofAuthority,
    ObligationKind, ObligationSite, ProofAnnotation, ProofCertificate, ProofEvidence, ProofFormula,
    ProofLineageId, ProofLineageManifest, ProofLineageNode, ProofObligation, ProofReplayIdentity,
    ProofStatus, ProofTransform, ProofTransformStage, clean_cic_lineage_digest,
    decode_clean_expr_v1, obligation_has_kernel_rechecked_clean_cic_in,
};
use trust_ir::request::{
    NativeAdapterInput, NativeAssertionId, NativeBundleProducer, NativeObligationCause,
    NativeObligationSource, NativeRequestId, NativeRequestProvenance, NativeSourceLanguage,
    NativeToolIdentity, NativeVerificationBundle, NativeVerificationBundleError,
    NativeVerificationRequest, NativeVerifierSuite, TrustVcNativeRequest, TrustVcVerificationMode,
};
use trust_ir::ty::Ty;
use trust_ir::value::{BlockId, ProofId, ValueId};
use trust_ir::{
    Endianness, FunctionSummary, KernelCleanCicRechecker, Module, Producer, ProofDigest, TargetInfo,
};
use trust_ir::{ProofObligationSourceIdentity, PublicObligationIdentity, SourceSpan};
use trust_ir_build::{
    ModuleBuilder, ModuleSet, ValidationError, validate_linked_module, validate_module,
    validate_module_for_codegen, validate_module_report, validate_module_with_authority,
};

const PROVER: &str = "trust_vc-clean-kernel";
const BIND_REFUSAL: &str = "contract clause does not bind to a Nat-valued IR place";

// ===========================================================================
// fixtures
// ===========================================================================

fn formula(text: &str, bindings: Vec<(&str, ClauseSort, ClausePlace)>) -> ProofFormula {
    let mut formula = ProofFormula::smtlib2(text, "Bool");
    formula.bindings = bindings
        .into_iter()
        .map(|(name, sort, place)| (name.to_string(), ClauseBinding { sort, place }))
        .collect();
    formula
}

fn result_int(text: &str) -> ProofFormula {
    formula(
        text,
        vec![(
            "result",
            ClauseSort::Int,
            ClausePlace::ResultSlot { index: 0 },
        )],
    )
}

/// `fn level() -> <ty> { <value> }`, a `proved` summary ensuring `clause`, and
/// a Certified Postcondition #0 scoped to it stating `clause`. No certificate.
fn level_module(ty: Ty, value: Value, clause: ProofFormula) -> Module {
    let mut mb = ModuleBuilder::new("ws1_1_level");
    let ft = mb.add_func_type(vec![], vec![ty.clone()]);
    let mut fb = mb.function("level", ft);
    fb.set_producer(Producer::TRust);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    let v = match value {
        Value::Int(n) => fb.iconst(ty, n),
        Value::Uint(n) => fb.uconst(ty, n),
        Value::Float(x) => fb.fconst(ty, x),
        Value::Bool(b) => fb.bool_const(b),
    };
    fb.ret(vec![v]);
    let f = fb.build();
    let mut m = mb.build().expect("ModuleBuilder::build: test fixture");
    m.functions[0].summary = Some(FunctionSummary::new().ensuring(clause.clone()).proved());
    m.proof_obligations.push(
        ProofObligation::new(
            ProofId::new(0),
            ObligationKind::Postcondition,
            ProofStatus::Certified,
            "ensures clause 0 of 'level'",
        )
        .with_function(f)
        .with_formula(clause),
    );
    m
}

#[derive(Clone, Copy)]
enum Value {
    Int(i128),
    Uint(u128),
    Float(f64),
    Bool(bool),
}

/// Mint obligation #0's certificate through the MODULE-BOUND entry point.
fn minted(mut m: Module) -> Module {
    let cert = contract_clean_cic_certificate_in(&m, &m.proof_obligations[0], PROVER)
        .expect("a bound nonneg clause over an unsigned place is mintable");
    m.proof_certificates.push(cert);
    m
}

/// The fixed closed-lambda proof term `fun x : Nat => @Eq.refl Bool Bool.true`
/// every nonneg certificate carries, taken from an honest mint.
fn nonneg_term() -> Vec<u8> {
    let honest = minted(level_module(
        Ty::U64,
        Value::Uint(7),
        result_int("(>= result 0)"),
    ));
    let ProofEvidence::CleanCic { term, .. } = &honest.proof_certificates[0].evidence else {
        panic!("minter produces CleanCic");
    };
    term.clone()
}

/// Attach a FORGED certificate to obligation #0: the honest term under the
/// obligation's own lineage — what anyone can build without the minter.
fn forged(mut m: Module) -> Module {
    let obligation = &m.proof_obligations[0];
    let cert = ProofCertificate {
        obligation: obligation.id,
        prover: PROVER.to_string(),
        evidence: ProofEvidence::CleanCic {
            term: nonneg_term(),
            context: Vec::new(),
            lineage: clean_cic_lineage_digest(obligation),
            kernel_recheck: None,
        },
        assurance: None,
    };
    m.proof_certificates.push(cert);
    m
}

/// The binding refusal on obligation #0 is present and carries `needle`, and
/// EVERY kernel-recheck refusal is the binding refusal (the kernel judgment
/// itself is not what fails).
fn assert_bind_refusal(errors: &[ValidationError], needle: &str) {
    let reasons: Vec<&str> = errors
        .iter()
        .filter_map(|e| match e {
            ValidationError::CertifiedCleanCicKernelRecheckFailed {
                obligation: 0,
                reason,
            } => Some(reason.as_str()),
            _ => None,
        })
        .collect();
    assert_eq!(reasons.len(), 1, "exactly one recheck refusal: {errors:?}");
    assert!(
        reasons[0].starts_with(BIND_REFUSAL) && reasons[0].contains(needle),
        "refusal must be the binding rule's `{needle}`: {reasons:?}"
    );
}

fn replayed(m: &Module) -> Option<usize> {
    validate_module_report(m)
        .replayed_certificate_refs()
        .map(|refs| refs.len())
}

// ===========================================================================
// positive fixtures
// ===========================================================================

#[test]
fn postcondition_over_u64_result_is_certified_and_replayed() {
    let m = minted(level_module(
        Ty::U64,
        Value::Uint(7),
        result_int("(>= result 0)"),
    ));
    assert_eq!(validate_module(&m), vec![]);
    assert_eq!(
        replayed(&m),
        Some(1),
        "the kernel tier replayed the certificate"
    );
}

#[test]
fn postcondition_over_u32_param_is_certified() {
    let mut mb = ModuleBuilder::new("ws1_1_param");
    let ft = mb.add_func_type(vec![Ty::U32], vec![Ty::U32]);
    let mut fb = mb.function("id32", ft);
    fb.set_producer(Producer::TRust);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    let x = fb.add_block_param(entry, Ty::U32);
    fb.ret(vec![x]);
    let f = fb.build();
    let mut m = mb.build().expect("ModuleBuilder::build: test fixture");
    let clause = formula(
        "(>= x 0)",
        vec![("x", ClauseSort::Int, ClausePlace::Param { index: 0 })],
    );
    m.functions[0].summary = Some(
        FunctionSummary::new()
            .with_params(vec!["x".into()])
            .ensuring(clause.clone())
            .proved(),
    );
    m.proof_obligations.push(
        ProofObligation::new(
            ProofId::new(0),
            ObligationKind::Postcondition,
            ProofStatus::Certified,
            "ensures clause 0 of 'id32'",
        )
        .with_function(f)
        .with_formula(clause),
    );
    let m = minted(m);
    assert_eq!(validate_module(&m), vec![]);
    assert_eq!(replayed(&m), Some(1));
}

/// `fn bump(p: &mut u16)` with `ensures (>= p_exit 0)` over the exit value.
fn mut_exit_module(pointee: Ty) -> Module {
    mut_exit_module_named(pointee, "p_exit")
}

/// [`mut_exit_module`] with the exit value named `exit` in the clause.
fn mut_exit_module_named(pointee: Ty, exit: &str) -> Module {
    let mut mb = ModuleBuilder::new("ws1_1_mut_exit");
    let param = Ty::RefMut(Box::new(pointee));
    let ft = mb.add_func_type(vec![param.clone()], vec![]);
    let mut fb = mb.function("bump", ft);
    fb.set_producer(Producer::TRust);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    let _p = fb.add_block_param(entry, param);
    fb.ret(vec![]);
    let f = fb.build();
    let mut m = mb.build().expect("ModuleBuilder::build: test fixture");
    let clause = formula(
        &format!("(>= {exit} 0)"),
        vec![(
            exit,
            ClauseSort::Int,
            ClausePlace::MutParamExit { index: 0 },
        )],
    );
    m.functions[0].summary = Some(
        FunctionSummary::new()
            .with_params(vec!["p".into()])
            .ensuring(clause.clone())
            .proved(),
    );
    m.proof_obligations.push(
        ProofObligation::new(
            ProofId::new(0),
            ObligationKind::Postcondition,
            ProofStatus::Certified,
            "ensures clause 0 of 'bump'",
        )
        .with_function(f)
        .with_formula(clause),
    );
    m
}

#[test]
fn postcondition_over_mut_u16_exit_is_certified() {
    let m = minted(mut_exit_module(Ty::U16));
    assert_eq!(validate_module(&m), vec![]);
    assert_eq!(replayed(&m), Some(1));
    // Twin: the exit value is an i16 — refused.
    let twin = forged(mut_exit_module(Ty::I16));
    assert!(contract_clean_cic_certificate_in(&twin, &twin.proof_obligations[0], PROVER).is_none());
    assert_bind_refusal(&validate_module(&twin), "is not an unsigned integer");
    // Twin: the exit value spelled `p'`. A `'` is in no SMT-LIB2 token (z3:
    // "unexpected character"), so trust-ir's one reader refuses the clause:
    // nothing is minted, and the honest term forged onto it is not replayed.
    let primed = forged(mut_exit_module_named(Ty::U16, "p'"));
    assert!(
        contract_clean_cic_certificate_in(&primed, &primed.proof_obligations[0], PROVER).is_none()
    );
    assert!(matches!(
        trust_ir::clean_expr_lowering::contract::bind_nat_nonneg(
            &primed,
            &primed.proof_obligations[0]
        ),
        Err(trust_ir::clean_expr_lowering::contract::ContractLoweringError::UnsupportedPredicate(
            reason
        )) if reason.contains("`p'` at byte 4, which is no SMT-LIB2 token")
    ));
    assert!(
        validate_module(&primed).iter().any(|error| matches!(
            error,
            ValidationError::CertifiedCleanCicKernelRecheckFailed { obligation: 0, .. }
        )),
        "{:?}",
        validate_module(&primed)
    );
    assert_eq!(replayed(&primed), None);
}

// ===========================================================================
// negative twins
// ===========================================================================

/// The c01 repro: `fn level() -> i64 { -1 }`, certified `(>= result 0)`.
#[test]
fn i64_result_returning_minus_one_is_refused() {
    let base = level_module(Ty::I64, Value::Int(-1), result_int("(>= result 0)"));
    assert!(
        contract_clean_cic_certificate_in(&base, &base.proof_obligations[0], PROVER).is_none(),
        "the minter refuses a signed place"
    );
    let m = forged(base);
    let errors = validate_module(&m);
    assert_bind_refusal(&errors, "has IR type i64, which is not an unsigned integer");
    assert_eq!(replayed(&m), None, "nothing enters the kernel tier");
}

#[test]
fn narrow_float_and_bool_results_are_refused() {
    for (ty, value) in [
        (Ty::I8, Value::Int(-128)),
        (Ty::F64, Value::Float(-1.5)),
        (Ty::Bool, Value::Bool(false)),
    ] {
        let m = forged(level_module(ty.clone(), value, result_int("(>= result 0)")));
        assert_bind_refusal(&validate_module(&m), &format!("has IR type {ty}"));
    }
}

#[test]
fn bitvec_sort_is_refused() {
    let clause = formula(
        "(>= result 0)",
        vec![(
            "result",
            ClauseSort::BitVec(64),
            ClausePlace::ResultSlot { index: 0 },
        )],
    );
    let m = forged(level_module(Ty::U64, Value::Uint(7), clause));
    assert_bind_refusal(&validate_module(&m), "binding sort BitVec(64) is not Int");
}

#[test]
fn empty_bindings_are_refused() {
    let m = forged(level_module(
        Ty::U64,
        Value::Uint(7),
        formula("(>= result 0)", vec![]),
    ));
    assert_bind_refusal(&validate_module(&m), "carries 0 bindings");
}

#[test]
fn binding_name_other_than_the_clause_symbol_is_refused() {
    let clause = formula(
        "(<= 0 zzz)",
        vec![(
            "result",
            ClauseSort::Int,
            ClausePlace::ResultSlot { index: 0 },
        )],
    );
    let m = forged(level_module(Ty::U64, Value::Uint(7), clause));
    assert_bind_refusal(
        &validate_module(&m),
        "binding `result` does not name the clause symbol `zzz`",
    );
}

#[test]
fn non_symbol_operands_are_refused() {
    for atom in ["-5", "true"] {
        let clause = formula(
            &format!("(>= {atom} 0)"),
            vec![(atom, ClauseSort::Int, ClausePlace::ResultSlot { index: 0 })],
        );
        let m = forged(level_module(Ty::U64, Value::Uint(7), clause));
        assert_bind_refusal(
            &validate_module(&m),
            &format!("clause operand `{atom}` is not an SMT simple symbol"),
        );
    }
}

#[test]
fn value_place_is_refused() {
    let base = level_module(Ty::U64, Value::Uint(7), result_int("(>= result 0)"));
    // Bind `result` to the SSA value the function returns — a Value place.
    let returned = base.functions[0].blocks[0].body[0].results[0];
    let clause = formula(
        "(>= result 0)",
        vec![("result", ClauseSort::Int, ClausePlace::Value(returned))],
    );
    let mut m = base;
    m.proof_obligations[0].formula = Some(clause);
    let m = forged(m);
    assert_bind_refusal(&validate_module(&m), "is an SSA value place");
    let _: ValueId = returned;
}

#[test]
fn unscoped_obligation_is_refused() {
    let mut m = level_module(Ty::U64, Value::Uint(7), result_int("(>= result 0)"));
    m.proof_obligations[0].function = None;
    let m = forged(m);
    assert_bind_refusal(&validate_module(&m), "no owning function");
}

#[test]
fn usize_place_needs_target_info() {
    let without = forged(level_module(
        Ty::Usize,
        Value::Uint(7),
        result_int("(>= result 0)"),
    ));
    assert_eq!(without.target_info, None);
    assert_bind_refusal(&validate_module(&without), "target_info");
    // Mutation control: the same place WITH a target binds.
    let mut with = level_module(Ty::Usize, Value::Uint(7), result_int("(>= result 0)"));
    with.target_info = Some(TargetInfo {
        triple: "aarch64-apple-darwin".into(),
        pointer_size: 8,
        endianness: Endianness::Little,
        abi: None,
        struct_passing: Default::default(),
    });
    let with = minted(with);
    assert!(
        !validate_module(&with).iter().any(|e| matches!(
            e,
            ValidationError::CertifiedCleanCicKernelRecheckFailed { .. }
        )),
        "a usize place under a target binds"
    );
}

// ---------------------------------------------------------------------------
// the same i64 twin through NativeVerificationBundle validation
// ---------------------------------------------------------------------------

const PUBLIC_ID: &str = "vc:level:postcondition:0";

/// Give obligation #0 the embedded source identity a native bundle requires.
/// Done BEFORE minting/forging: the source is part of the lineage digest.
fn with_source(mut m: Module) -> Module {
    let source = ProofObligationSourceIdentity::new("rust:level", "rust-assertion:0").with_public(
        PublicObligationIdentity {
            obligation_id: PUBLIC_ID.to_string(),
            semantic_digest: ProofDigest::sha256_domain("ws1_1.public", b"level:post:0"),
        },
    );
    let obligation = m.proof_obligations.remove(0).with_source(source);
    m.proof_obligations.insert(0, obligation);
    m
}

fn trust_vc_bundle(module: Module) -> NativeVerificationBundle {
    let function = module.proof_obligations[0].function;
    let cert = module.proof_certificates[0].lineage_ref();
    let digest = module.stable_digest();
    let source = ProofDigest::sha256_domain("ws1_1.source", b"level");
    let mut node = ProofLineageNode::new(
        ProofLineageId::new(0),
        ProofTransform::new(
            ProofTransformStage::Frontend,
            "rustc-mir-to-trust_ir",
            "tRust",
            "native-request-schema-v1",
        ),
        source,
        digest,
    );
    node.obligations.push(ProofId::new(0));
    node.certificates.push(cert.clone());
    node.replay = Some(
        ProofReplayIdentity::new("trust-full-verify", "trust verify --emit-trust_ir-bundle")
            .with_transcript_digest(ProofDigest::sha256_domain("ws1_1.transcript", b"level")),
    );
    let lineage = ProofLineageManifest {
        schema_version: ProofLineageManifest::SCHEMA_VERSION,
        nodes: vec![node],
        roots: vec![ProofLineageId::new(0)],
    };
    let mut bundle = NativeVerificationBundle::new(
        NativeBundleProducer::TRust,
        NativeAdapterInput::RustMir {
            body_digest: source,
        },
        digest,
        module,
        lineage,
    );
    // Schema 8 (WS4.16, F-080): the bundle must SAY the languages of the
    // package it verifies, and the set must cover every `Function.producer`
    // of the bound module. `level` is stamped `Producer::TRust`, so the
    // default `{Unknown}` provenance would be refused
    // (`BundleLanguageUncovered`) before this fixture ever reached the clause
    // rule it is about.
    bundle.provenance.source_language = NativeSourceLanguage::Rust;
    bundle.provenance.source_languages = [NativeSourceLanguage::Rust].into_iter().collect();
    bundle
        .compiler_facts
        .obligation_sources
        .push(NativeObligationSource {
            obligation: ProofId::new(0),
            public_obligation_id: PUBLIC_ID.to_string(),
            function,
            span: Some(SourceSpan {
                file: 0,
                line: 1,
                col: 1,
            }),
            assertion_id: Some(NativeAssertionId::new(0)),
            cause: NativeObligationCause::Postcondition,
            monomorphization: None,
            facts: Vec::new(),
        });
    bundle
        .requests
        .push(NativeVerificationRequest::TrustVc(TrustVcNativeRequest {
            id: NativeRequestId::new(0),
            mode: TrustVcVerificationMode::ImportProofCertificates,
            obligations: vec![ProofId::new(0)],
            certificates: vec![cert],
            lineage_roots: vec![ProofLineageId::new(0)],
            options: Default::default(),
            diagnostics: Default::default(),
            provenance: NativeRequestProvenance::new(
                NativeVerifierSuite::TrustVc,
                NativeToolIdentity::new("trust_vc").with_version("semantics-v1"),
            )
            .with_solver(NativeToolIdentity::new("clean-kernel").with_version("0.9.0"))
            .with_replay(
                ProofReplayIdentity::new("trust_vc", "trust_vc import")
                    .with_transcript_digest(ProofDigest::sha256_domain("ws1_1.vc", b"level")),
            ),
            function: None,
        }));
    bundle
}

#[test]
fn i64_twin_is_refused_through_native_bundle_validation() {
    let honest = minted(with_source(level_module(
        Ty::U64,
        Value::Uint(7),
        result_int("(>= result 0)"),
    )));
    assert_eq!(trust_vc_bundle(honest).validate(), Ok(()));

    let lying = forged(with_source(level_module(
        Ty::I64,
        Value::Int(-1),
        result_int("(>= result 0)"),
    )));
    let errors = trust_vc_bundle(lying)
        .validate()
        .expect_err("an unbound certificate is not replayed authority");
    assert!(
        errors.iter().any(|e| matches!(
            e,
            NativeVerificationBundleError::TrustVcCertificateNotDischarged {
                obligation,
                status: ProofStatus::Certified,
                ..
            } if *obligation == ProofId::new(0)
        )),
        "{errors:?}"
    );
    assert_eq!(errors.len(), 1, "the refusal is the one change: {errors:?}");
}

// ===========================================================================
// mutation controls
// ===========================================================================

/// TEST-ONLY rechecker that re-grounds the nonneg tautology from the clause
/// SHAPE and SKIPS `bind_nat_nonneg` — the pre-WS1.1 behaviour. It accepts the
/// i64 twin, which proves the refusal above comes from the binding rule and not
/// from the kernel judgment or the certificate bytes.
struct SkipsBinding;

impl ModuleCleanCicRechecker for SkipsBinding {
    fn kernel_rechecks_clean_cic_in(
        &self,
        _module: &Module,
        _obligation: &ProofObligation,
        cert: &ProofCertificate,
    ) -> bool {
        let ProofEvidence::CleanCic { term, .. } = &cert.evidence else {
            return false;
        };
        let Ok(proof) = decode_clean_expr_v1(term) else {
            return false;
        };
        let eq = Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]);
        let ble = Expr::apps(
            Expr::const_str("Nat.ble"),
            [Expr::nat_lit(0), Expr::bvar(0)],
        );
        let body = Expr::apps(
            eq,
            [Expr::const_str("Bool"), ble, Expr::const_str("Bool.true")],
        );
        let goal = Expr::pi(BinderInfo::Default, Expr::const_str("Nat"), body);
        Environment::with_reusable_prelude(|env| {
            TypeChecker::with_context(env, LocalContext::new())
                .check_type(&proof, &goal)
                .is_ok()
        })
        .unwrap_or(false)
    }
}

#[test]
fn a_rechecker_without_the_binding_rule_accepts_the_i64_twin() {
    let m = forged(level_module(
        Ty::I64,
        Value::Int(-1),
        result_int("(>= result 0)"),
    ));
    let ob = &m.proof_obligations[0];
    assert!(obligation_has_kernel_rechecked_clean_cic_in(
        &m,
        ob,
        &m.proof_certificates,
        &SkipsBinding
    ));
    assert!(!obligation_has_kernel_rechecked_clean_cic_in(
        &m,
        ob,
        &m.proof_certificates,
        &KernelCleanCicRechecker
    ));
}

#[test]
fn literal_certificates_still_validate_through_the_module_free_entry_point() {
    let clause = formula("(= 1 1)", vec![]);
    let mut m = level_module(Ty::U64, Value::Uint(7), clause);
    // A literal clause says nothing about the function; keep the summary out.
    m.functions[0].summary = None;
    let cert = contract_clean_cic_certificate(&m.proof_obligations[0], PROVER)
        .expect("a ground tautology is kernel-certified module-free");
    m.proof_certificates.push(cert);
    assert_eq!(validate_module(&m), vec![]);
    assert_eq!(replayed(&m), Some(1));
}

// ---------------------------------------------------------------------------
// ProofRef: the category link, not only the position
// ---------------------------------------------------------------------------

/// `fn level() -> u64 { let _ = 1 sdiv 0 [claims]; 7 }` with the honest,
/// kernel-replayed `(>= result 0)` Postcondition #0. Returns the module and the
/// sdiv node's site.
fn sdiv_module(claims: Vec<ProofAnnotation>) -> (Module, ObligationSite) {
    let mut mb = ModuleBuilder::new("ws1_1_sdiv");
    let ft = mb.add_func_type(vec![], vec![Ty::U64]);
    let mut fb = mb.function("level", ft);
    fb.set_producer(Producer::TRust);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    let one = fb.iconst(Ty::I64, 1);
    let zero = fb.iconst(Ty::I64, 0);
    let _q = fb.binop_proven(BinOp::SDiv, Ty::I64, one, zero, claims);
    let seven = fb.uconst(Ty::U64, 7);
    fb.ret(vec![seven]);
    let f = fb.build();
    let mut m = mb.build().expect("ModuleBuilder::build: test fixture");
    let clause = result_int("(>= result 0)");
    m.functions[0].summary = Some(FunctionSummary::new().ensuring(clause.clone()).proved());
    m.proof_obligations.push(
        ProofObligation::new(
            ProofId::new(0),
            ObligationKind::Postcondition,
            ProofStatus::Certified,
            "ensures clause 0 of 'level'",
        )
        .with_function(f)
        .with_formula(clause),
    );
    let sdiv = m.functions[0].blocks[0]
        .body
        .iter()
        .position(|node| {
            matches!(
                node.inst,
                trust_ir::inst::Inst::BinOp {
                    op: BinOp::SDiv,
                    ..
                }
            )
        })
        .expect("the sdiv node");
    let site = ObligationSite::new(f, BlockId::new(0), sdiv as u32);
    (m, site)
}

fn backref_claims(claim: ProofAnnotation) -> Vec<ProofAnnotation> {
    vec![claim, ProofAnnotation::ProofRef(ProofId::new(0))]
}

fn kind_mismatch(errors: &[ValidationError], kind: &str) -> bool {
    errors.iter().any(|e| {
        matches!(e, ValidationError::ProofRefKindMismatch { obligation: 0, kind: k, .. } if *k == kind)
    })
}

#[test]
fn certified_postcondition_cannot_back_div_non_zero_unsited_or_resited() {
    // Unsited: the c01 amplification.
    let (m, site) = sdiv_module(backref_claims(ProofAnnotation::DivNonZero));
    let m = minted(m);
    assert_eq!(
        replayed(&m),
        None,
        "the report is not clean, so nothing is exported"
    );
    let errors = validate_module(&m);
    assert!(kind_mismatch(&errors, "postcondition"), "{errors:?}");
    assert_eq!(errors.len(), 1, "{errors:?}");

    // Re-sited onto the sdiv node — the shape a site-only rule would admit.
    let (mut m, _) = sdiv_module(backref_claims(ProofAnnotation::DivNonZero));
    m.proof_obligations[0].site = Some(site);
    let m = minted(m);
    let errors = validate_module(&m);
    assert!(kind_mismatch(&errors, "postcondition"), "{errors:?}");
    assert!(
        !errors
            .iter()
            .any(|e| matches!(e, ValidationError::ProofRefSiteMismatch { .. })),
        "the refusal is the category, not the position: {errors:?}"
    );
}

/// TEST STAND-IN consumer capability: replays the non-kernel certificates the
/// fixture lists. It proves nothing; it occupies the capability slot so the
/// ProofRef BINDING can be measured apart from authority.
struct ReplayStandIn;

impl ModuleProofAuthority for ReplayStandIn {
    fn replays_authority(
        &self,
        _module: &Module,
        obligation: &ProofObligation,
        certificate: &ProofCertificate,
    ) -> bool {
        certificate.obligation == obligation.id
            && matches!(certificate.evidence, ProofEvidence::SmtProof(_))
    }
}

/// Replace row #0 with a Discharged ArithmeticSafety row sited at `site`.
fn arithmetic_row(site: ObligationSite) -> Module {
    let (mut m, _) = sdiv_module(backref_claims(ProofAnnotation::DivNonZero));
    m.functions[0].summary = None;
    let mut row = ProofObligation::new(
        ProofId::new(0),
        ObligationKind::ArithmeticSafety,
        ProofStatus::Discharged,
        "1 sdiv 0 divisor is non-zero",
    )
    .with_function(site.function);
    row.site = Some(site);
    m.proof_obligations = vec![row];
    m.proof_certificates.push(ProofCertificate {
        obligation: ProofId::new(0),
        prover: "stand-in".into(),
        evidence: ProofEvidence::SmtProof(b"(proof)".to_vec()),
        assurance: None,
    });
    m
}

#[test]
fn sited_arithmetic_row_binds_on_its_node_and_not_elsewhere() {
    let (_, site) = sdiv_module(vec![]);
    // Same node: the binding is structurally legal. The ONLY refusal is the
    // (pre-existing) tier rule: a capability-replayed Discharged row is never
    // ProofRef currency — only the kernel tier is.
    let here = arithmetic_row(site);
    let errors = validate_module_with_authority(&here, &ReplayStandIn);
    assert!(
        matches!(
            errors.as_slice(),
            [ValidationError::ProofRefUnresolved {
                obligation: 0,
                missing: false,
                ..
            }]
        ),
        "{errors:?}"
    );
    // A different node: refused by site.
    let elsewhere = arithmetic_row(ObligationSite::new(
        site.function,
        site.block,
        site.inst_index - 1,
    ));
    let errors = validate_module_with_authority(&elsewhere, &ReplayStandIn);
    assert!(
        errors.iter().any(|e| matches!(
            e,
            ValidationError::ProofRefSiteMismatch {
                function: 0,
                obligation: 0
            }
        )),
        "{errors:?}"
    );
}

#[test]
fn function_level_pure_backed_by_a_postcondition_is_still_accepted() {
    let (mut m, _) = sdiv_module(vec![]);
    m.functions[0].proofs.push(ProofAnnotation::Pure);
    m.functions[0]
        .proofs
        .push(ProofAnnotation::ProofRef(ProofId::new(0)));
    let m = minted(m);
    assert_eq!(validate_module(&m), vec![]);
    // …but the SAME row may not back it on a node.
    let (m, _) = sdiv_module(backref_claims(ProofAnnotation::Pure));
    let m = minted(m);
    assert!(kind_mismatch(&validate_module(&m), "postcondition"));
}

// ===========================================================================
// proof-program GAP rows, flipped (2026-09-17 audit; roadmap §2.4). Each test
// is named after its row id and asserts the CLOSED behaviour.
// ===========================================================================

/// `b2.gap.kernel_certifies_nat_nonneg_ignoring_bindings_and_ir_type` — was:
/// `fn b2_level() -> i64 { -1 }` with a `proved` `ensures (>= result 0)`
/// [result: Int @ ResultSlot0], Certified, kernel-replayed, `validate_module
/// => []`. Now: unmintable, and the forged certificate is refused by the
/// binding rule under `validate_module`; the honest `u64 7` baseline and its
/// certificate-stripped twin keep their PASS behaviour.
#[test]
fn b2_gap_kernel_certifies_nat_nonneg_ignoring_bindings_and_ir_type() {
    let honest = minted(level_module(
        Ty::U64,
        Value::Uint(7),
        result_int("(>= result 0)"),
    ));
    assert_eq!(validate_module(&honest), vec![]);
    assert_eq!(replayed(&honest), Some(1));
    let mut stripped = honest.clone();
    stripped.proof_certificates.clear();
    assert!(matches!(
        validate_module(&stripped).as_slice(),
        [ValidationError::CertifiedWithoutCleanCic { obligation: 0 }]
    ));

    let lying = level_module(Ty::I64, Value::Int(-1), result_int("(>= result 0)"));
    assert!(contract_clean_cic_certificate(&lying.proof_obligations[0], PROVER).is_none());
    assert!(
        contract_clean_cic_certificate_in(&lying, &lying.proof_obligations[0], PROVER).is_none()
    );
    let lying = forged(lying);
    assert_bind_refusal(&validate_module(&lying), "is not an unsigned integer");
    assert_eq!(replayed(&lying), None);
}

/// `b2.gap.kernel_certificate_ignores_clause_binding_sort` — was: over the
/// honest `-> u64 { 7 }` body, `result` bound as Bool / RoundingMode /
/// BitVec(64) / NOT AT ALL each minted, re-checked and validated. Now: none is
/// minted by either entry point, and each forged certificate is refused with
/// the binding rule's reason.
#[test]
fn b2_gap_kernel_certificate_ignores_clause_binding_sort() {
    for (binding, needle) in [
        (Some(ClauseSort::Bool), "binding sort Bool is not Int"),
        (
            Some(ClauseSort::RoundingMode),
            "binding sort RoundingMode is not Int",
        ),
        (
            Some(ClauseSort::BitVec(64)),
            "binding sort BitVec(64) is not Int",
        ),
        (None, "carries 0 bindings"),
    ] {
        let clause = formula(
            "(>= result 0)",
            binding
                .map(|sort| vec![("result", sort, ClausePlace::ResultSlot { index: 0 })])
                .unwrap_or_default(),
        );
        let base = level_module(Ty::U64, Value::Uint(7), clause);
        assert!(contract_clean_cic_certificate(&base.proof_obligations[0], PROVER).is_none());
        assert!(
            contract_clean_cic_certificate_in(&base, &base.proof_obligations[0], PROVER).is_none(),
            "{needle}"
        );
        assert_bind_refusal(&validate_module(&forged(base)), needle);
    }
}

/// `verify.c01.L1` (independent repro lens) — was: the i64 `-1` twin validated
/// under `validate_module`, `validate_module_with_authority(Rejecting)`,
/// `validate_module_for_codegen` and `validate_linked_module`, and `(>= -5 0)`
/// minted and validated Certified. Now every entry point refuses it with the
/// binding rule's reason, and `(>= -5 0)` is neither minted nor admitted.
#[test]
fn verify_c01_l1() {
    let m = forged(level_module(
        Ty::I64,
        Value::Int(-1),
        result_int("(>= result 0)"),
    ));
    let needle = "is not an unsigned integer";
    assert_bind_refusal(&validate_module(&m), needle);
    assert_bind_refusal(
        &validate_module_with_authority(&m, &RejectingModuleProofAuthority),
        needle,
    );
    assert_bind_refusal(&validate_module_for_codegen(&m), needle);
    let set = ModuleSet::new([]);
    let linked = validate_linked_module(&m, &set, &RejectingModuleProofAuthority);
    assert_bind_refusal(linked.errors(), needle);
    assert_eq!(linked.replayed_certificate_refs(), None);

    let minus_five = formula(
        "(>= -5 0)",
        vec![("-5", ClauseSort::Int, ClausePlace::ResultSlot { index: 0 })],
    );
    let base = level_module(Ty::U64, Value::Uint(7), minus_five);
    assert!(contract_clean_cic_certificate(&base.proof_obligations[0], PROVER).is_none());
    assert!(contract_clean_cic_certificate_in(&base, &base.proof_obligations[0], PROVER).is_none());
    assert_bind_refusal(
        &validate_module(&forged(base)),
        "clause operand `-5` is not an SMT simple symbol",
    );
}

/// `verify.c01.L2` (real / known / matters lens) — was: i8 `-128` [BitVec(8)],
/// f64 `-1.5` [Float{11,53}] and `(<= 0 zzz)` bound as `result` all certified,
/// and the certified row backed `[DivNonZero, ProofRef(#0)]` on `1 sdiv 0`.
/// Now each is refused by name, and the amplification is a kind mismatch.
#[test]
fn verify_c01_l2() {
    let cases = [
        (
            Ty::I8,
            Value::Int(-128),
            formula(
                "(>= result 0)",
                vec![(
                    "result",
                    ClauseSort::BitVec(8),
                    ClausePlace::ResultSlot { index: 0 },
                )],
            ),
            "has IR type i8",
        ),
        (
            Ty::F64,
            Value::Float(-1.5),
            formula(
                "(>= result 0)",
                vec![(
                    "result",
                    ClauseSort::Float { eb: 11, sb: 53 },
                    ClausePlace::ResultSlot { index: 0 },
                )],
            ),
            "has IR type f64",
        ),
        (
            Ty::I64,
            Value::Int(-1),
            formula(
                "(<= 0 zzz)",
                vec![(
                    "result",
                    ClauseSort::Int,
                    ClausePlace::ResultSlot { index: 0 },
                )],
            ),
            "does not name the clause symbol `zzz`",
        ),
    ];
    for (ty, value, clause, needle) in cases {
        let m = forged(level_module(ty, value, clause));
        assert_bind_refusal(&validate_module(&m), needle);
        assert_bind_refusal(
            &validate_module_with_authority(&m, &RejectingModuleProofAuthority),
            needle,
        );
    }

    let (m, _) = sdiv_module(backref_claims(ProofAnnotation::DivNonZero));
    let m = minted(m);
    let errors = validate_module(&m);
    assert!(
        matches!(
            errors.as_slice(),
            [ValidationError::ProofRefKindMismatch {
                obligation: 0,
                kind: "postcondition",
                ..
            }]
        ),
        "{errors:?}"
    );
}

// ===========================================================================
// adversarial review (WS1.1 review pass): shapes the implementation's own
// fixtures did not try.
// ===========================================================================

/// The literal proof term `@Eq.refl Bool Bool.true` from an honest literal
/// mint — the other fixed term an attacker has without any minter.
fn literal_term() -> Vec<u8> {
    let honest = level_module(Ty::U64, Value::Uint(7), formula("(= 1 1)", vec![]));
    let cert = contract_clean_cic_certificate(&honest.proof_obligations[0], PROVER)
        .expect("a ground tautology mints module-free");
    let ProofEvidence::CleanCic { term, .. } = cert.evidence else {
        panic!("minter produces CleanCic");
    };
    term
}

/// Attach `term` to obligation #0 under its own (recomputable) lineage.
fn forged_with(mut m: Module, term: Vec<u8>) -> Module {
    let obligation = &m.proof_obligations[0];
    let cert = ProofCertificate {
        obligation: obligation.id,
        prover: PROVER.to_string(),
        evidence: ProofEvidence::CleanCic {
            term,
            context: Vec::new(),
            lineage: clean_cic_lineage_digest(obligation),
            kernel_recheck: None,
        },
        assurance: None,
    };
    m.proof_certificates.push(cert);
    m
}

/// `+1` is an SMT-LIB2 simple SYMBOL (a simple symbol may begin with `+`; only
/// a leading digit makes a numeral), but Rust's `u64::from_str` accepts it as
/// the numeral 1. Before the review fix the LITERAL path grounded
/// `(>= +1 0)` as `1 >= 0` and certified it module-free, ignoring a binding
/// that names `+1` as the i64 result — so an SMT consumer reading the clause
/// with its bindings saw a certified `result >= 0` over `-1`. Numerals are now
/// ASCII digits only; `+1` is a non-literal operand, and the binding rule
/// refuses it as not a simple symbol under the shared grammar.
#[test]
fn plus_signed_atom_is_neither_a_numeral_nor_a_bindable_symbol() {
    for text in ["(>= +1 0)", "(<= 0 +1)"] {
        let base = level_module(
            Ty::I64,
            Value::Int(-1),
            formula(
                text,
                vec![("+1", ClauseSort::Int, ClausePlace::ResultSlot { index: 0 })],
            ),
        );
        assert!(
            contract_clean_cic_certificate(&base.proof_obligations[0], PROVER).is_none(),
            "{text}: the module-free literal path must not read `+1` as a numeral"
        );
        assert!(
            contract_clean_cic_certificate_in(&base, &base.proof_obligations[0], PROVER).is_none(),
            "{text}"
        );
        for term in [literal_term(), nonneg_term()] {
            assert_bind_refusal(
                &validate_module(&forged_with(base.clone(), term)),
                "clause operand `+1` is not an SMT simple symbol",
            );
        }
    }
    // A `+`-signed literal inside a larger ground clause is simply ungroundable.
    let base = level_module(Ty::U64, Value::Uint(7), formula("(= +1 1)", vec![]));
    assert!(contract_clean_cic_certificate(&base.proof_obligations[0], PROVER).is_none());
}

/// Kind and place mutations the binding rule decides: a RefinementType and a
/// LoopInvariant over a SIGNED place, and a Precondition that names the result.
#[test]
fn kind_and_place_mutations_are_refused() {
    let signed_param = |kind: ObligationKind| {
        let mut mb = ModuleBuilder::new("ws1_1_review_kind");
        let ft = mb.add_func_type(vec![Ty::I32], vec![Ty::U64]);
        let mut fb = mb.function("k", ft);
        fb.set_producer(Producer::TRust);
        let entry = fb.create_block();
        fb.switch_to_block(entry);
        let _x = fb.add_block_param(entry, Ty::I32);
        let seven = fb.uconst(Ty::U64, 7);
        fb.ret(vec![seven]);
        let f = fb.build();
        let mut m = mb.build().expect("ModuleBuilder::build: test fixture");
        m.proof_obligations.push(
            ProofObligation::new(ProofId::new(0), kind, ProofStatus::Certified, "x >= 0")
                .with_function(f)
                .with_formula(formula(
                    "(>= x 0)",
                    vec![("x", ClauseSort::Int, ClausePlace::Param { index: 0 })],
                )),
        );
        m
    };
    for kind in [
        ObligationKind::RefinementType,
        ObligationKind::LoopInvariant,
        ObligationKind::Precondition,
    ] {
        let m = forged(signed_param(kind.clone()));
        assert_bind_refusal(&validate_module(&m), "has IR type i32");
    }
    // A Precondition may not name the result, even an unsigned one.
    let mut m = level_module(Ty::U64, Value::Uint(7), result_int("(>= result 0)"));
    m.functions[0].summary = None;
    m.proof_obligations[0].kind = ObligationKind::Precondition;
    assert_bind_refusal(
        &validate_module(&forged(m)),
        "a Precondition cannot name the result or exit place",
    );
}

/// Retargeting the certified row onto a DIFFERENT (honest, u64) function does
/// not launder the i64 function's `proved` ensures: the row is true of the
/// function it names, and the lying function's summary has no backing row.
#[test]
fn retargeted_row_does_not_back_the_lying_summary() {
    let mut mb = ModuleBuilder::new("ws1_1_review_retarget");
    let lie_ty = mb.add_func_type(vec![], vec![Ty::I64]);
    let ok_ty = mb.add_func_type(vec![], vec![Ty::U64]);
    let mut fb = mb.function("lie", lie_ty);
    fb.set_producer(Producer::TRust);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    let v = fb.iconst(Ty::I64, -1);
    fb.ret(vec![v]);
    let _lie = fb.build();
    let mut fb = mb.function("ok", ok_ty);
    fb.set_producer(Producer::TRust);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    let v = fb.uconst(Ty::U64, 7);
    fb.ret(vec![v]);
    let ok = fb.build();
    let mut m = mb.build().expect("ModuleBuilder::build: test fixture");
    let clause = result_int("(>= result 0)");
    m.functions[0].summary = Some(FunctionSummary::new().ensuring(clause.clone()).proved());
    m.proof_obligations.push(
        ProofObligation::new(
            ProofId::new(0),
            ObligationKind::Postcondition,
            ProofStatus::Certified,
            "ensures clause 0 of 'ok'",
        )
        .with_function(ok)
        .with_formula(clause),
    );
    let m = minted(m);
    let errors = validate_module(&m);
    assert!(
        !errors.iter().any(|e| matches!(
            e,
            ValidationError::CertifiedCleanCicKernelRecheckFailed { .. }
        )),
        "the row over `ok`'s u64 result is honest: {errors:?}"
    );
    assert!(
        errors.iter().any(|e| matches!(
            e,
            ValidationError::InvalidFunctionSummary { function: 0, .. }
        )),
        "the lying function's proved summary is unbacked: {errors:?}"
    );
}

/// A bound clause still needs the RIGHT kernel term: the literal `Eq.refl`
/// term under the u64 nonneg obligation's own lineage does not inhabit the
/// closed `∀ x : Nat` goal, and the honest term under a different obligation's
/// lineage is a lineage mismatch.
#[test]
fn bound_clause_with_a_mutated_certificate_is_refused() {
    let base = level_module(Ty::U64, Value::Uint(7), result_int("(>= result 0)"));
    let wrong_term = forged_with(base.clone(), literal_term());
    let errors = validate_module(&wrong_term);
    assert!(
        errors.iter().any(|e| matches!(
            e,
            ValidationError::CertifiedCleanCicKernelRecheckFailed { obligation: 0, reason }
                if reason.contains("does not pass the obligation-grounded Clean contract recheck")
        )),
        "{errors:?}"
    );
    let mut wrong_lineage = minted(base);
    wrong_lineage.proof_obligations[0].description = "a different obligation".into();
    assert!(
        validate_module(&wrong_lineage).iter().any(|e| matches!(
            e,
            ValidationError::CertifiedCleanCicLineageMismatch { obligation: 0 }
        )),
        "the certificate names the old lineage"
    );
}

/// Legitimate shapes the rule must NOT refuse: `(<= 0 x)` over a `u8`
/// parameter of a function that is not the module's first, and a `u128`
/// RefinementType result.
#[test]
fn legitimate_normal_form_on_a_second_function_is_certified() {
    let mut mb = ModuleBuilder::new("ws1_1_review_legit");
    let first_ty = mb.add_func_type(vec![], vec![Ty::I64]);
    let second_ty = mb.add_func_type(vec![Ty::U8], vec![Ty::U128]);
    let mut fb = mb.function("first", first_ty);
    fb.set_producer(Producer::TRust);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    let v = fb.iconst(Ty::I64, -1);
    fb.ret(vec![v]);
    let _first = fb.build();
    let mut fb = mb.function("second", second_ty);
    fb.set_producer(Producer::TRust);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    let _x = fb.add_block_param(entry, Ty::U8);
    let v = fb.uconst(Ty::U128, u128::MAX);
    fb.ret(vec![v]);
    let second = fb.build();
    let mut m = mb.build().expect("ModuleBuilder::build: test fixture");
    m.proof_obligations.push(
        ProofObligation::new(
            ProofId::new(0),
            ObligationKind::Postcondition,
            ProofStatus::Certified,
            "0 <= x",
        )
        .with_function(second)
        .with_formula(formula(
            "(<= 0 x)",
            vec![("x", ClauseSort::Int, ClausePlace::Param { index: 0 })],
        )),
    );
    m.proof_obligations.push(
        ProofObligation::new(
            ProofId::new(1),
            ObligationKind::RefinementType,
            ProofStatus::Certified,
            "result >= 0",
        )
        .with_function(second)
        .with_formula(result_int("(>= result 0)")),
    );
    for index in 0..2 {
        let cert = contract_clean_cic_certificate_in(&m, &m.proof_obligations[index], PROVER)
            .expect("a bound nonneg clause over an unsigned place mints");
        m.proof_certificates.push(cert);
    }
    assert_eq!(validate_module(&m), vec![]);
    assert_eq!(replayed(&m), Some(2));
}

/// ProofRef shapes beyond the spec's: an ambiguous kind sited on the node may
/// not back a KIND-LESS or `Custom` claim there either, and a function-level
/// safety claim is refused just like a node-level one.
#[test]
fn ambiguous_kind_backs_no_node_claim_and_no_function_safety_claim() {
    use trust_ir::value::ProofTag;
    for claims in [
        vec![ProofAnnotation::DivNonZero, ProofAnnotation::Pure],
        vec![ProofAnnotation::Custom(ProofTag::new(3))],
    ] {
        let (mut m, site) = sdiv_module(
            claims
                .into_iter()
                .chain([ProofAnnotation::ProofRef(ProofId::new(0))])
                .collect(),
        );
        m.proof_obligations[0].site = Some(site);
        let errors = validate_module(&minted(m));
        assert!(kind_mismatch(&errors, "postcondition"), "{errors:?}");
    }
    let (mut m, _) = sdiv_module(vec![]);
    m.functions[0].proofs.push(ProofAnnotation::NoPanic);
    m.functions[0]
        .proofs
        .push(ProofAnnotation::ProofRef(ProofId::new(0)));
    let errors = validate_module(&minted(m));
    assert!(kind_mismatch(&errors, "postcondition"), "{errors:?}");
}

// ===========================================================================
// WS1.2 — summary clause bindings are type-checked against the IR (F-004).
//
// THE HOLE. `validate_function_summary` resolved binding INDICES and place
// legality only: it never compared a binding's `ClauseSort` with the IR type
// of its place, never required a bound name to occur in the clause (or a
// clause name to be bound), let `MutParamExit` name a by-value parameter, and
// read an EMPTY `bindings` — documented as UNBINDABLE — as nothing to check.
// So a `proved` summary could carry clauses whose names denote nothing, or
// denote a u64 read as `BitVec(8)` / `Bool`, or a `handle<Nat>` read as a
// machine word.
//
// THE RULE. Always on: the sort must be a faithful reading of the place's IR
// type (`clause_sort_admits`, the WS1.1 helper; the default arm refuses),
// `MutParamExit` types against the pointee of a `&mut` / `*mut` parameter, and
// a `Value` place is typed through the SSA type map. Every refusal is
// `InvalidFunctionSummary` naming the clause, the binding and the reason.
//
// DEFERRED (the `proved`-only half): empty bindings, free-name closure,
// binders, uninterpreted heads and World/Unwind on a `proved` summary. It
// refuses the published `composition` conformance fixture, so it lands with
// that fixture's re-spelling; `b2_gap_unbindable_clause_still_earns_proved`
// pins the open gap until then.
// ===========================================================================

const BV64: ClauseSort = ClauseSort::BitVec(64);

/// The honest bindings of `bump`'s ensures clause.
fn bump_bindings() -> Vec<(&'static str, ClauseSort, ClausePlace)> {
    vec![
        ("result", BV64, ClausePlace::ResultSlot { index: 0 }),
        ("x", BV64, ClausePlace::Param { index: 0 }),
    ]
}

fn bump_ensures(bindings: Vec<(&str, ClauseSort, ClausePlace)>) -> ProofFormula {
    formula("(= result (bvadd x #x0000000000000001))", bindings)
}

/// `fn bump(x: u64) -> u64 { x + 1 }` with a summary ensuring `ensures`
/// (`proved` when asked), backed by a Discharged Postcondition #0 restating it
/// with an SMT certificate the [`ReplayStandIn`] capability replays.
fn bump_module(ensures: ProofFormula, proved: bool) -> Module {
    let mut mb = ModuleBuilder::new("ws1_2_bump");
    let ft = mb.add_func_type(vec![Ty::U64], vec![Ty::U64]);
    let mut fb = mb.function("bump", ft);
    fb.set_producer(Producer::TRust);
    let entry = fb.create_block();
    let x = fb.add_block_param(entry, Ty::U64);
    fb.switch_to_block(entry);
    let one = fb.uconst(Ty::U64, 1);
    let r = fb.add(Ty::U64, x, one);
    fb.ret(vec![r]);
    let f = fb.build();
    let mut m = mb.build().expect("ModuleBuilder::build: test fixture");
    let mut summary = FunctionSummary::new()
        .with_params(vec!["x".into()])
        .ensuring(ensures.clone());
    if proved {
        summary = summary.proved();
    }
    m.functions[0].summary = Some(summary);
    m.proof_obligations.push(
        ProofObligation::new(
            ProofId::new(0),
            ObligationKind::Postcondition,
            ProofStatus::Discharged,
            "ensures clause 0 of 'bump'",
        )
        .with_function(f)
        .with_formula(ensures),
    );
    m.proof_certificates.push(ProofCertificate {
        obligation: ProofId::new(0),
        prover: "stand-in".into(),
        evidence: ProofEvidence::SmtProof(b"(proof)".to_vec()),
        assurance: None,
    });
    m
}

fn stand_in_errors(m: &Module) -> Vec<ValidationError> {
    validate_module_with_authority(m, &ReplayStandIn)
}

/// EXACTLY one error, an `InvalidFunctionSummary` on function `function`
/// whose detail carries `needle` — the "one mutation, one named refusal" form.
fn assert_only_summary_refusal(errors: &[ValidationError], function: u32, needle: &str) {
    assert!(
        matches!(
            errors,
            [ValidationError::InvalidFunctionSummary { function: f, detail }]
                if *f == function && detail.contains(needle)
        ),
        "expected exactly one InvalidFunctionSummary on f{function} mentioning {needle:?}; got \
         {errors:?}"
    );
}

/// EXACTLY two errors, for one mutation of a bound clause that the summary
/// AND its restating obligation both carry: the summary's
/// `InvalidFunctionSummary` on `function` carrying `needle`, and roadmap
/// WS4.4's `InvalidObligationBinding` on row `obligation` carrying
/// `row_needle` — the same bad binding refused on each carrier, by name, and
/// nothing else. (Before WS4.4 a module obligation's bindings were validated
/// by no rule, so these fixtures saw only the summary's refusal.)
fn assert_summary_and_row_refusal(
    errors: &[ValidationError],
    function: u32,
    needle: &str,
    obligation: u32,
    row_needle: &str,
) {
    let summary = errors
        .iter()
        .filter(|e| {
            matches!(
                e,
                ValidationError::InvalidFunctionSummary { function: f, detail }
                    if *f == function && detail.contains(needle)
            )
        })
        .count();
    let row = errors
        .iter()
        .filter(|e| {
            matches!(
                e,
                ValidationError::InvalidObligationBinding { obligation: o, detail }
                    if *o == obligation && detail.contains(row_needle)
            )
        })
        .count();
    assert!(
        errors.len() == 2 && summary == 1 && row == 1,
        "expected exactly one InvalidFunctionSummary on f{function} mentioning {needle:?} and \
         one InvalidObligationBinding on #{obligation} mentioning {row_needle:?}; got {errors:?}"
    );
}

#[test]
fn ws1_2_positive_bound_bump_contract_validates() {
    let m = bump_module(bump_ensures(bump_bindings()), true);
    assert_eq!(stand_in_errors(&m), vec![]);
}

#[test]
fn ws1_2_twin_bitvec32_on_u64_param_is_refused() {
    let mut bindings = bump_bindings();
    bindings[1].1 = ClauseSort::BitVec(32);
    let m = bump_module(bump_ensures(bindings), true);
    assert_summary_and_row_refusal(
        &stand_in_errors(&m),
        0,
        "ensures clause 0 binding 'x' has sort BitVec(32) but Param 0 is u64",
        0,
        "binding \"x\" has sort BitVec(32) but Param 0 is u64",
    );
}

#[test]
fn ws1_2_twin_bool_on_u64_result_is_refused() {
    let mut bindings = bump_bindings();
    bindings[0].1 = ClauseSort::Bool;
    let m = bump_module(bump_ensures(bindings), true);
    assert_summary_and_row_refusal(
        &stand_in_errors(&m),
        0,
        "ensures clause 0 binding 'result' has sort Bool but ResultSlot 0 is u64",
        0,
        "binding \"result\" has sort Bool but ResultSlot 0 is u64",
    );
}

#[test]
fn ws1_2_twin_mut_param_exit_on_by_value_u64_is_refused() {
    let mut bindings = bump_bindings();
    bindings[1].2 = ClausePlace::MutParamExit { index: 0 };
    let m = bump_module(bump_ensures(bindings), true);
    assert_summary_and_row_refusal(
        &stand_in_errors(&m),
        0,
        "ensures clause 0 binding 'x' uses MutParamExit on parameter 0 of type u64, which is not \
         a &mut / *mut",
        0,
        "binding \"x\" uses MutParamExit on parameter 0 of type u64, which is not a &mut / *mut",
    );
}

/// `fn nat_twice(n: handle<Nat>) -> handle<Nat> { add(n, n) }` over the pinned
/// `trust_bignum::Nat` runtime, with an UNPROVED summary ensuring
/// `(= result (* 2 n))` bound at `sort` — the always-on rule is what decides.
fn nat_module(sort: ClauseSort) -> (Module, u32) {
    use trust_ir_build::TRUSTED_HANDLE_RUNTIMES;
    let pin = TRUSTED_HANDLE_RUNTIMES
        .iter()
        .find(|pin| pin.runtime == "trust_bignum::Nat")
        .expect("v1 pins trust_bignum::Nat");
    let mut mb = ModuleBuilder::new_with_target_info("ws1_2_nat", aarch64());
    let decls = mb
        .declare_handle_runtime(pin)
        .expect("pinned declarations on an empty module");
    let nat = decls.handle.clone();
    let add = decls.entry("add").expect("the Nat row pins add");
    let ft = mb.add_func_type(vec![nat.clone()], vec![nat.clone()]);
    let mut fb = mb.function("nat_twice", ft);
    fb.set_producer(Producer::Clean);
    let entry = fb.create_block();
    let n = fb.add_block_param(entry, nat);
    fb.switch_to_block(entry);
    let twice = fb.call(add, vec![n, n]);
    fb.ret(vec![twice]);
    let f = fb.build();
    let mut m = mb.build().expect("ModuleBuilder::build: test fixture");
    let ensures = formula(
        "(= result (* 2 n))",
        vec![
            ("n", sort.clone(), ClausePlace::Param { index: 0 }),
            ("result", sort, ClausePlace::ResultSlot { index: 0 }),
        ],
    );
    let index = m
        .functions
        .iter()
        .position(|func| func.id == f)
        .expect("nat_twice");
    m.functions[index].summary = Some(
        FunctionSummary::new()
            .with_params(vec!["n".into()])
            .ensuring(ensures),
    );
    (m, f.index())
}

fn aarch64() -> TargetInfo {
    TargetInfo {
        triple: "aarch64-apple-darwin".into(),
        pointer_size: 8,
        endianness: Endianness::Little,
        abi: None,
        struct_passing: Default::default(),
    }
}

#[test]
fn ws1_2_twin_bitvec64_on_a_nat_handle_param_is_refused() {
    let (m, f) = nat_module(BV64);
    let errors = validate_module(&m);
    assert_eq!(errors.len(), 2, "{errors:?}");
    for (name, place) in [("n", "Param 0"), ("result", "ResultSlot 0")] {
        assert!(
            errors.iter().any(|e| matches!(
                e,
                ValidationError::InvalidFunctionSummary { function, detail }
                    if *function == f
                        && detail.contains(&format!(
                            "binding '{name}' has sort BitVec(64) but {place} is "
                        ))
                        && detail.contains("Nat")
            )),
            "{name}: {errors:?}"
        );
    }
}

/// The default arm: a `Ty` without a row admits no sort. `Int` on a struct
/// parameter is refused on an UNPROVED summary — rule 1 is always on.
#[test]
fn ws1_2_twin_int_on_a_struct_param_is_refused_by_the_default_arm() {
    use trust_ir::{FieldDef, StructDef, StructId, StructRepr};
    let mut mb = ModuleBuilder::new("ws1_2_struct");
    let s = mb.add_struct(StructDef {
        id: StructId::new(0),
        name: "Pair".into(),
        fields: vec![
            FieldDef {
                name: "lo".into(),
                ty: Ty::U64,
                offset: Some(0),
            },
            FieldDef {
                name: "hi".into(),
                ty: Ty::U64,
                offset: Some(8),
            },
        ],
        size: Some(16),
        align: Some(8),
        repr: StructRepr::C,
        origin: None,
    });
    let ft = mb.add_func_type(vec![Ty::Struct(s)], vec![Ty::U64]);
    let mut fb = mb.function("lo", ft);
    fb.set_producer(Producer::TRust);
    let entry = fb.create_block();
    let _p = fb.add_block_param(entry, Ty::Struct(s));
    fb.switch_to_block(entry);
    let zero = fb.uconst(Ty::U64, 0);
    fb.ret(vec![zero]);
    fb.build();
    let mut m = mb.build().expect("ModuleBuilder::build: test fixture");
    let requires = formula(
        "(>= p 0)",
        vec![("p", ClauseSort::Int, ClausePlace::Param { index: 0 })],
    );
    m.functions[0].summary = Some(
        FunctionSummary::new()
            .with_params(vec!["p".into()])
            .requiring(requires),
    );
    assert_only_summary_refusal(
        &validate_module(&m),
        0,
        "requires clause 0 binding 'p' has sort Int but Param 0 is ",
    );
}

/// A pointer-like place admits no sort, even `Int`.
#[test]
fn ws1_2_twin_int_on_a_pointer_param_is_refused() {
    let mut mb = ModuleBuilder::new("ws1_2_ptr");
    let ft = mb.add_func_type(vec![Ty::Ptr], vec![]);
    let mut fb = mb.function("touch", ft);
    fb.set_producer(Producer::TRust);
    let entry = fb.create_block();
    let _p = fb.add_block_param(entry, Ty::Ptr);
    fb.switch_to_block(entry);
    fb.ret(vec![]);
    fb.build();
    let mut m = mb.build().expect("ModuleBuilder::build: test fixture");
    m.functions[0].summary = Some(
        FunctionSummary::new()
            .with_params(vec!["p".into()])
            .requiring(formula(
                "(>= p 0)",
                vec![("p", ClauseSort::Int, ClausePlace::Param { index: 0 })],
            )),
    );
    assert_only_summary_refusal(
        &validate_module(&m),
        0,
        "requires clause 0 binding 'p' has sort Int but Param 0 is ptr",
    );
}

/// `Value(v)` is typed through the function's SSA type map.
#[test]
fn ws1_2_value_places_are_typed_through_the_ssa_type_map() {
    let base = bump_module(bump_ensures(bump_bindings()), true);
    let sum = base.functions[0].blocks[0]
        .body
        .iter()
        .find(|node| {
            matches!(
                node.inst,
                trust_ir::inst::Inst::BinOp { op: BinOp::Add, .. }
            )
        })
        .expect("the add")
        .results[0];
    let with_value = |sort: ClauseSort| {
        bump_module(
            formula(
                "(and (= result (bvadd x #x0000000000000001)) (= sum result))",
                vec![
                    ("result", BV64, ClausePlace::ResultSlot { index: 0 }),
                    ("x", BV64, ClausePlace::Param { index: 0 }),
                    ("sum", sort, ClausePlace::Value(sum)),
                ],
            ),
            true,
        )
    };
    assert_eq!(stand_in_errors(&with_value(BV64)), vec![]);
    assert_summary_and_row_refusal(
        &stand_in_errors(&with_value(ClauseSort::Bool)),
        0,
        &format!(
            "ensures clause 0 binding 'sum' has sort Bool but SSA value v{} is u64",
            sum.index()
        ),
        0,
        &format!(
            "binding \"sum\" has sort Bool but SSA value v{} is u64",
            sum.index()
        ),
    );
}

// ---------------------------------------------------------------------------
// WS1.2 mutation controls
// ---------------------------------------------------------------------------

/// A correct binding with a wrong index still yields exactly the pre-existing
/// arity error: the typing rule adds nothing on an unresolved place. The
/// restating row carries the same clause, so it gets exactly its own arity
/// refusal (WS4.4) and, likewise, no typing refusal.
#[test]
fn ws1_2_control_wrong_index_keeps_the_pre_existing_arity_error() {
    let mut bindings = bump_bindings();
    bindings[1].2 = ClausePlace::Param { index: 5 };
    let m = bump_module(bump_ensures(bindings), true);
    assert_summary_and_row_refusal(
        &stand_in_errors(&m),
        0,
        "ensures clause 0 binding 'x' names parameter 5 but the signature declares 1 parameter(s)",
        0,
        "binds \"x\" to Param 5 but function #0's signature declares 1 parameter(s)",
    );
}

/// `Int` on a signed parameter is a faithful (mathematical) reading — the
/// carry.py canary shape (F-086) — and must stay legal.
#[test]
fn ws1_2_control_int_on_a_signed_param_is_legal() {
    let mut mb = ModuleBuilder::new("ws1_2_i32");
    let ft = mb.add_func_type(vec![Ty::I32], vec![Ty::I32]);
    let mut fb = mb.function("id", ft);
    fb.set_producer(Producer::TRust);
    let entry = fb.create_block();
    let x = fb.add_block_param(entry, Ty::I32);
    fb.switch_to_block(entry);
    fb.ret(vec![x]);
    fb.build();
    let mut m = mb.build().expect("ModuleBuilder::build: test fixture");
    m.functions[0].summary = Some(
        FunctionSummary::new()
            .with_params(vec!["x".into()])
            .requiring(formula(
                "(>= x (- 5))",
                vec![("x", ClauseSort::Int, ClausePlace::Param { index: 0 })],
            ))
            .ensuring(formula(
                "(= result x)",
                vec![
                    ("x", ClauseSort::BitVec(32), ClausePlace::Param { index: 0 }),
                    (
                        "result",
                        ClauseSort::BitVec(32),
                        ClausePlace::ResultSlot { index: 0 },
                    ),
                ],
            )),
    );
    assert_eq!(validate_module(&m), vec![]);
}

// ---------------------------------------------------------------------------
// WS1.2 proof-program GAP rows, flipped (roadmap §2.4)
// ---------------------------------------------------------------------------

/// A reduction of the b2 `b2_bump_into` fixture with well-typed places:
/// `fn b2_bump_into(x: u64, out: *mut u64) -> u64 { let r = x + 1; *out = r; r }`,
/// `proved` with one requires and two ensures clauses, each restated by a
/// Discharged row the stand-in replays. Returns the module and the `r` value.
fn b2_bump_into() -> (Module, ValueId) {
    let mut mb = ModuleBuilder::new("ws1_2_b2_bump_into");
    let out_ty = Ty::PtrMut(Box::new(Ty::U64));
    let ft = mb.add_func_type(vec![Ty::U64, out_ty.clone()], vec![Ty::U64]);
    let mut fb = mb.function("b2_bump_into", ft);
    fb.set_producer(Producer::TRust);
    let entry = fb.create_block();
    let x = fb.add_block_param(entry, Ty::U64);
    let out = fb.add_block_param(entry, out_ty);
    fb.switch_to_block(entry);
    let one = fb.uconst(Ty::U64, 1);
    let r = fb.add(Ty::U64, x, one);
    fb.store(Ty::U64, out, r);
    fb.ret(vec![r]);
    let f = fb.build();
    let mut m = mb.build().expect("ModuleBuilder::build: test fixture");
    let requires = formula(
        "(bvult x #xffffffffffffffff)",
        vec![("x", BV64, ClausePlace::Param { index: 0 })],
    );
    let ensures_value = formula(
        "(and (= result (bvadd x #x0000000000000001)) (= sum result))",
        vec![
            ("x", BV64, ClausePlace::Param { index: 0 }),
            ("result", BV64, ClausePlace::ResultSlot { index: 0 }),
            ("sum", BV64, ClausePlace::Value(r)),
        ],
    );
    let ensures_effect = formula(
        "(= out_exit result)",
        vec![
            ("out_exit", BV64, ClausePlace::MutParamExit { index: 1 }),
            ("result", BV64, ClausePlace::ResultSlot { index: 0 }),
        ],
    );
    m.functions[0].summary = Some(
        FunctionSummary::new()
            .with_params(vec!["x".into(), "out".into()])
            .requiring(requires.clone())
            .ensuring(ensures_value.clone())
            .ensuring(ensures_effect.clone())
            .proved(),
    );
    for (id, kind, clause) in [
        (0, ObligationKind::Precondition, requires),
        (1, ObligationKind::Postcondition, ensures_value),
        (2, ObligationKind::Postcondition, ensures_effect),
    ] {
        m.proof_obligations.push(
            ProofObligation::new(
                ProofId::new(id),
                kind,
                ProofStatus::Discharged,
                format!("clause row {id} of 'b2_bump_into'"),
            )
            .with_function(f)
            .with_formula(clause),
        );
        m.proof_certificates.push(ProofCertificate {
            obligation: ProofId::new(id),
            prover: "stand-in".into(),
            evidence: ProofEvidence::SmtProof(b"(proof)".to_vec()),
            assurance: None,
        });
    }
    (m, r)
}

fn b2_bump_summary(m: &mut Module) -> &mut FunctionSummary {
    m.functions[0].summary.as_mut().expect("summary")
}

/// `b2.gap.unbindable_clause_still_earns_proved` — STILL OPEN (GAP ratchet,
/// roadmap §2.4). Both ensures clauses of `b2_bump_into` stripped to EMPTY
/// bindings with `proved` kept still validate: `empty = UNBINDABLE` is a
/// consumer duty no entry point enforces. This is the `proved`-only half of
/// WS1.2, deferred because it also refuses the published `composition`
/// conformance fixture; it flips with that half. Asserts the current outcome
/// EXACTLY, so any change of shape fails here first.
///
/// WS1.3 keeps the restating rows in step: `proved` is per-clause, so a row
/// backs only the clause its `formula` EQUALS (bindings included), and the
/// stripped clause is backed only by a row stripped the same way. Stripping
/// the summary alone is refused by that rule — asserted too, so the GAP below
/// is measured on the unbindable half alone.
#[test]
fn b2_gap_unbindable_clause_still_earns_proved() {
    let (base, _) = b2_bump_into();
    assert_eq!(stand_in_errors(&base), vec![], "baseline must validate");
    let mut m = base;
    for clause in b2_bump_summary(&mut m).ensures.iter_mut() {
        clause.bindings.clear();
    }
    let summary_only = stand_in_errors(&m);
    assert_eq!(summary_only.len(), 2, "{summary_only:?}");
    assert!(summary_only.iter().all(|e| matches!(
        e,
        ValidationError::InvalidFunctionSummary { detail, .. }
            if detail.contains("has no Discharged/Certified Postcondition row")
    )));
    for row in m.proof_obligations.iter_mut().skip(1) {
        row.formula
            .as_mut()
            .expect("restating row")
            .bindings
            .clear();
    }
    assert_eq!(
        stand_in_errors(&m),
        vec![],
        "GAP: an unbindable proved clause is still accepted"
    );
}

/// `b2.gap.clause_sort_unchecked_against_ir_type` — was: the u64 parameter
/// `x` re-sorted as BitVec(8) / Bool / Float{11,53} / RoundingMode, and the
/// u64 result and SSA value re-sorted as Bool, all six validated (the sort was
/// never read). Now each is ONE named refusal per carrier; the restating
/// obligation is kept in step so the sort is the only change, and since WS4.4
/// validates obligation bindings too, the row is refused by name beside the
/// summary.
#[test]
fn b2_gap_clause_sort_unchecked_against_ir_type() {
    let (base, r) = b2_bump_into();
    for sort in [
        ClauseSort::BitVec(8),
        ClauseSort::Bool,
        ClauseSort::Float { eb: 11, sb: 53 },
        ClauseSort::RoundingMode,
    ] {
        let mut m = base.clone();
        b2_bump_summary(&mut m).requires[0].bindings[0].1.sort = sort.clone();
        m.proof_obligations[0].formula.as_mut().unwrap().bindings[0]
            .1
            .sort = sort.clone();
        assert_summary_and_row_refusal(
            &stand_in_errors(&m),
            0,
            &format!("requires clause 0 binding 'x' has sort {sort:?} but Param 0 is u64"),
            0,
            &format!("binding \"x\" has sort {sort:?} but Param 0 is u64"),
        );
    }
    for (binding, needle, row_needle) in [
        (
            1usize,
            "ensures clause 0 binding 'result' has sort Bool but ResultSlot 0 is u64".to_string(),
            "binding \"result\" has sort Bool but ResultSlot 0 is u64".to_string(),
        ),
        (
            2,
            format!(
                "ensures clause 0 binding 'sum' has sort Bool but SSA value v{} is u64",
                r.index()
            ),
            format!(
                "binding \"sum\" has sort Bool but SSA value v{} is u64",
                r.index()
            ),
        ),
    ] {
        let mut m = base.clone();
        b2_bump_summary(&mut m).ensures[0].bindings[binding].1.sort = ClauseSort::Bool;
        m.proof_obligations[1].formula.as_mut().unwrap().bindings[binding]
            .1
            .sort = ClauseSort::Bool;
        assert_summary_and_row_refusal(&stand_in_errors(&m), 0, &needle, 1, &row_needle);
    }
}

/// `b2.gap.mut_param_exit_on_by_value_param_accepted` — was: `MutParamExit
/// { index: 0 }` naming the by-value `x: u64` (not the `*mut` at index 1)
/// validated; only `index < params.len()` was checked. Now it is refused by
/// name, while the baseline's `MutParamExit { index: 1 }` over `*mut u64`
/// keeps validating.
#[test]
fn b2_gap_mut_param_exit_on_by_value_param_accepted() {
    let (base, _) = b2_bump_into();
    assert_eq!(stand_in_errors(&base), vec![], "baseline must validate");
    let mut m = base;
    b2_bump_summary(&mut m).ensures[1].bindings[0].1.place = ClausePlace::MutParamExit { index: 0 };
    m.proof_obligations[2].formula.as_mut().unwrap().bindings[0]
        .1
        .place = ClausePlace::MutParamExit { index: 0 };
    assert_summary_and_row_refusal(
        &stand_in_errors(&m),
        0,
        "ensures clause 1 binding 'out_exit' uses MutParamExit on parameter 0 of type u64",
        2,
        "binding \"out_exit\" uses MutParamExit on parameter 0 of type u64",
    );
}

/// `b5.gap.clause_sort_bitvec64_accepted_on_nat_param` — was: `BitVec(64)`
/// bound to a `handle<Nat>` Param / ResultSlot ("Nat silently u64" on the
/// contract surface) validated. Now both bindings are refused; and so is the
/// `Int` reading the b5 PASS row carried (`Ty::Handle` admits NO sort at this
/// version — an opaque runtime word has no machine sort), so the handle
/// contract is refused on every sort rather than on the wrong one only.
#[test]
fn b5_gap_clause_sort_bitvec64_accepted_on_nat_param() {
    for sort in [BV64, ClauseSort::Int] {
        let (m, f) = nat_module(sort.clone());
        let errors = validate_module(&m);
        assert_eq!(errors.len(), 2, "{sort:?}: {errors:?}");
        assert!(
            errors.iter().all(|e| matches!(
                e,
                ValidationError::InvalidFunctionSummary { function, detail }
                    if *function == f && detail.contains(&format!("has sort {sort:?} but "))
            )),
            "{sort:?}: {errors:?}"
        );
    }
    // Mutation control: without the summary the handle module is clean, so
    // the refusals above are the binding rule's alone.
    let (mut m, _) = nat_module(BV64);
    for func in &mut m.functions {
        func.summary = None;
    }
    assert_eq!(validate_module(&m), vec![]);
}

// ---------------------------------------------------------------------------
// WS1.2 adversarial review — shapes the implementer's fixtures did not reach
// ---------------------------------------------------------------------------

/// `fn probe(p0: params[0], ..)` — a body that only returns — under an
/// UNPROVED summary with the given clauses, so the always-on typing rule is
/// the only thing that can speak. `target` is the module's `target_info`.
fn ws1_2_probe(
    params: Vec<Ty>,
    target: Option<TargetInfo>,
    requires: Vec<ProofFormula>,
    ensures: Vec<ProofFormula>,
    decreases: Vec<ProofFormula>,
) -> Module {
    let mut mb = match target {
        Some(target) => ModuleBuilder::new_with_target_info("ws1_2_probe", target),
        None => ModuleBuilder::new("ws1_2_probe"),
    };
    let ft = mb.add_func_type(params.clone(), vec![]);
    let mut fb = mb.function("probe", ft);
    fb.set_producer(Producer::TRust);
    let entry = fb.create_block();
    for ty in &params {
        let _ = fb.add_block_param(entry, ty.clone());
    }
    fb.switch_to_block(entry);
    fb.ret(vec![]);
    fb.build();
    let mut m = mb.build().expect("ModuleBuilder::build: test fixture");
    let mut summary =
        FunctionSummary::new().with_params((0..params.len()).map(|i| format!("p{i}")).collect());
    summary.requires = requires;
    summary.ensures = ensures;
    summary.decreases = decreases;
    m.functions[0].summary = Some(summary);
    m
}

fn ws1_2_param(sort: ClauseSort, index: u32) -> ProofFormula {
    formula("(= p p)", vec![("p", sort, ClausePlace::Param { index })])
}

fn ws1_2_exit(sort: ClauseSort, index: u32) -> ProofFormula {
    formula(
        "(= q q)",
        vec![("q", sort, ClausePlace::MutParamExit { index })],
    )
}

fn target_with_pointer_size(pointer_size: u32) -> TargetInfo {
    TargetInfo {
        pointer_size,
        ..aarch64()
    }
}

/// Adversarial 1: a pointer-width integer has no width without `target_info`,
/// so `BitVec(64)` on `usize` is refused BY THAT NAME there; with a target it
/// must match the target's pointer width EXACTLY (a 32-bit target refuses
/// `BitVec(64)` and admits `BitVec(32)`); `Int` needs no width at all.
#[test]
fn ws1_2_adversarial_pointer_width_ints_bind_only_at_the_target_width() {
    let params = || vec![Ty::Usize, Ty::Isize];
    let probe = |target: Option<TargetInfo>, clause: ProofFormula| {
        validate_module(&ws1_2_probe(params(), target, vec![clause], vec![], vec![]))
    };

    assert_only_summary_refusal(
        &probe(None, ws1_2_param(BV64, 0)),
        0,
        "requires clause 0 binding 'p' has sort BitVec(64) but Param 0 is usize, whose width is \
         unknown without target_info",
    );
    assert_eq!(probe(None, ws1_2_param(ClauseSort::Int, 0)), vec![]);
    assert_eq!(probe(None, ws1_2_param(ClauseSort::Int, 1)), vec![]);

    assert_eq!(probe(Some(aarch64()), ws1_2_param(BV64, 0)), vec![]);
    assert_eq!(probe(Some(aarch64()), ws1_2_param(BV64, 1)), vec![]);

    let thirty_two = || Some(target_with_pointer_size(4));
    assert_only_summary_refusal(
        &probe(thirty_two(), ws1_2_param(BV64, 1)),
        0,
        "requires clause 0 binding 'p' has sort BitVec(64) but Param 1 is isize",
    );
    assert_eq!(
        probe(thirty_two(), ws1_2_param(ClauseSort::BitVec(32), 1)),
        vec![]
    );
}

/// Adversarial 2: `MutParamExit` reads the POINTEE of a `&mut` / `*mut`, and
/// only of those. A shared `&T` or `*const T` has no exit value; the exit of
/// `&mut &mut u64` is itself a reference (no sort); the exit of `&mut u64` is
/// a u64 and is width-checked like any u64; and the `&mut` itself, read at
/// `Param`, is pointer-like and admits no sort.
#[test]
fn ws1_2_adversarial_mut_param_exit_reads_only_a_mutable_pointee() {
    let params = || {
        vec![
            Ty::Ref(Box::new(Ty::U64)),
            Ty::RefMut(Box::new(Ty::U64)),
            Ty::RefMut(Box::new(Ty::RefMut(Box::new(Ty::U64)))),
            Ty::PtrConst(Box::new(Ty::U64)),
            Ty::PtrMut(Box::new(Ty::I8)),
        ]
    };
    let ensures = |clause: ProofFormula| {
        validate_module(&ws1_2_probe(params(), None, vec![], vec![clause], vec![]))
    };

    assert_eq!(ensures(ws1_2_exit(BV64, 1)), vec![]);
    assert_eq!(ensures(ws1_2_exit(ClauseSort::Int, 1)), vec![]);
    assert_eq!(ensures(ws1_2_exit(ClauseSort::BitVec(8), 4)), vec![]);

    assert_only_summary_refusal(
        &ensures(ws1_2_exit(ClauseSort::Int, 0)),
        0,
        "ensures clause 0 binding 'q' uses MutParamExit on parameter 0 of type &u64, which is not \
         a &mut / *mut",
    );
    assert_only_summary_refusal(
        &ensures(ws1_2_exit(ClauseSort::Int, 3)),
        0,
        "ensures clause 0 binding 'q' uses MutParamExit on parameter 3 of type ",
    );
    assert_only_summary_refusal(
        &ensures(ws1_2_exit(ClauseSort::BitVec(32), 1)),
        0,
        "ensures clause 0 binding 'q' has sort BitVec(32) but MutParamExit 1 is u64",
    );
    assert_only_summary_refusal(
        &ensures(ws1_2_exit(ClauseSort::Int, 2)),
        0,
        "ensures clause 0 binding 'q' has sort Int but MutParamExit 2 is ",
    );
    assert_only_summary_refusal(
        &ensures(ws1_2_exit(ClauseSort::BitVec(64), 4)),
        0,
        "ensures clause 0 binding 'q' has sort BitVec(64) but MutParamExit 4 is i8",
    );
    assert_only_summary_refusal(
        &ensures(ws1_2_param(ClauseSort::Int, 1)),
        0,
        "ensures clause 0 binding 'p' has sort Int but Param 1 is ",
    );
}

/// Adversarial 3: the rule covers EVERY clause list — a `decreases` measure
/// and a `requires` clause on an unproved summary are typed exactly like an
/// ensures clause — and every ill-typed binding is its own refusal (none is
/// masked by an earlier one).
#[test]
fn ws1_2_adversarial_every_clause_list_is_typed_and_nothing_is_masked() {
    let m = ws1_2_probe(
        vec![Ty::U64, Ty::Bool],
        None,
        vec![ws1_2_param(ClauseSort::Bool, 0)],
        vec![ws1_2_param(ClauseSort::Int, 1)],
        vec![ws1_2_param(ClauseSort::BitVec(8), 0)],
    );
    let errors = validate_module(&m);
    assert_eq!(errors.len(), 3, "{errors:?}");
    for needle in [
        "requires clause 0 binding 'p' has sort Bool but Param 0 is u64",
        "ensures clause 0 binding 'p' has sort Int but Param 1 is bool",
        "decreases clause 0 binding 'p' has sort BitVec(8) but Param 0 is u64",
    ] {
        assert!(
            errors.iter().any(|e| matches!(
                e,
                ValidationError::InvalidFunctionSummary { function: 0, detail }
                    if detail.contains(needle)
            )),
            "{needle}: {errors:?}"
        );
    }

    // Mutation control: the faithful sorts on the same three lists validate.
    let honest = ws1_2_probe(
        vec![Ty::U64, Ty::Bool],
        None,
        vec![ws1_2_param(BV64, 0)],
        vec![ws1_2_param(ClauseSort::Bool, 1)],
        vec![ws1_2_param(ClauseSort::Int, 0)],
    );
    assert_eq!(validate_module(&honest), vec![]);
}

/// Adversarial 4: `char` and the three IEEE formats bind exactly per the
/// table — `char` is `Int` or a 32-bit vector, never 8; each float format
/// admits only its own `(eb, sb)`, and a float admits no integer sort.
#[test]
fn ws1_2_adversarial_char_and_float_rows_are_exact() {
    let params = || vec![Ty::Char, Ty::F16, Ty::F32, Ty::F64];
    let probe = |clause: ProofFormula| {
        validate_module(&ws1_2_probe(params(), None, vec![clause], vec![], vec![]))
    };
    for legal in [
        ws1_2_param(ClauseSort::Int, 0),
        ws1_2_param(ClauseSort::BitVec(32), 0),
        ws1_2_param(ClauseSort::Float { eb: 5, sb: 11 }, 1),
        ws1_2_param(ClauseSort::Float { eb: 8, sb: 24 }, 2),
        ws1_2_param(ClauseSort::Float { eb: 11, sb: 53 }, 3),
    ] {
        assert_eq!(probe(legal.clone()), vec![], "{legal:?}");
    }
    for (clause, needle) in [
        (
            ws1_2_param(ClauseSort::BitVec(8), 0),
            "has sort BitVec(8) but Param 0 is char",
        ),
        (
            ws1_2_param(ClauseSort::Float { eb: 11, sb: 53 }, 2),
            "has sort Float { eb: 11, sb: 53 } but Param 2 is f32",
        ),
        (
            ws1_2_param(ClauseSort::Float { eb: 8, sb: 24 }, 1),
            "has sort Float { eb: 8, sb: 24 } but Param 1 is f16",
        ),
        (
            ws1_2_param(ClauseSort::Int, 3),
            "has sort Int but Param 3 is f64",
        ),
        (
            ws1_2_param(BV64, 3),
            "has sort BitVec(64) but Param 3 is f64",
        ),
    ] {
        assert_only_summary_refusal(&probe(clause), 0, needle);
    }
}

/// Adversarial 5: a `Value` place on a MULTI-RESULT instruction is typed per
/// result — the overflow flag of `add_overflow` is a `bool`, its sum a u64 —
/// so reading the flag as a machine word (or the sum as a boolean) is refused.
#[test]
fn ws1_2_adversarial_value_places_type_each_result_of_a_multi_result_node() {
    use trust_ir::inst::OverflowOp;
    let module_with = |bindings: Vec<(&str, ClauseSort, ClausePlace)>| {
        let mut mb = ModuleBuilder::new("ws1_2_overflow");
        let ft = mb.add_func_type(vec![Ty::U64], vec![Ty::U64]);
        let mut fb = mb.function("checked_bump", ft);
        fb.set_producer(Producer::TRust);
        let entry = fb.create_block();
        let x = fb.add_block_param(entry, Ty::U64);
        fb.switch_to_block(entry);
        let one = fb.uconst(Ty::U64, 1);
        let (sum, flag) = fb.overflow(OverflowOp::AddOverflow, Ty::U64, x, one);
        fb.ret(vec![sum]);
        fb.build();
        let mut m = mb.build().expect("ModuleBuilder::build: test fixture");
        let bindings = bindings
            .into_iter()
            .map(|(name, sort, place)| {
                let place = match place {
                    ClausePlace::Value(v) if v.index() == 0 => ClausePlace::Value(sum),
                    ClausePlace::Value(_) => ClausePlace::Value(flag),
                    other => other,
                };
                (name, sort, place)
            })
            .collect();
        m.functions[0].summary = Some(
            FunctionSummary::new()
                .with_params(vec!["x".into()])
                .ensuring(formula("(= s s)", bindings)),
        );
        (m, sum, flag)
    };
    let sum_place = ClausePlace::Value(ValueId::new(0));
    let flag_place = ClausePlace::Value(ValueId::new(1));

    let (honest, ..) = module_with(vec![
        ("s", BV64, sum_place),
        ("o", ClauseSort::Bool, flag_place),
    ]);
    assert_eq!(validate_module(&honest), vec![]);

    let (m, _, flag) = module_with(vec![("o", BV64, flag_place)]);
    assert_only_summary_refusal(
        &validate_module(&m),
        0,
        &format!(
            "ensures clause 0 binding 'o' has sort BitVec(64) but SSA value v{} is bool",
            flag.index()
        ),
    );
    let (m, sum, _) = module_with(vec![("s", ClauseSort::Bool, sum_place)]);
    assert_only_summary_refusal(
        &validate_module(&m),
        0,
        &format!(
            "ensures clause 0 binding 's' has sort Bool but SSA value v{} is u64",
            sum.index()
        ),
    );
}
