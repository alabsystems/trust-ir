// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0
//
// Coverage is a verdict the CONSUMER derives from evidence it re-checks
// itself — `coverage_establishment_report`. No producer-written row is a
// source of coverage.
//
// THE TWO DEFECTS THIS PINS. (1) False provenance: the legacy rule
// (`coverage_assurance_report`, now deprecated) derived a bound from a
// request's MODE, so an `Unbounded` row citing a pending CHC request with no
// evidence at all "agreed" (`ws1_11_an_unbounded_record_on_a_chc_request_agrees`
// in coverage_assurance.rs). (2) A kernel-certified contract certificate — the
// only thing Trust ships — had no route to coverage at all: the old report
// records 0 rows for it, and every consumer rejected it as unrecorded.
//
// THE TWO BASES. K, per CERTIFICATE: the consumer's own kernel replay of
// exactly that certificate, of a classified claim family. R, per OBLIGATION: a
// sealed attestation row, outside every digest, whose citations the consumer
// recomputes — the solved bundle's whole REPLAY CONTEXT among them, on the
// solved and the admitted side — and whose result a
// `NativeCoverageResultReplay` re-verifies. A basis-R verdict names no
// certificate and vouches for none, and its bound exists only when the cited
// request's options mean exactly the obligation's machine semantics.
//
// ROUND 2 (the adversarial verdict on 355a9e9d). P1: the M1 -> M2 transfer
// compared executable content and the obligation's own claim only, so a
// result that rests on an assumed Precondition of M1 stayed Established on an
// M2 that dropped it (`context_drift_dropped_assumption_is_refused`). P2/P3:
// the solved-module Failed branch and both wire-identity branches had no
// committed negative control. P4: a row labelled ANY certificate of the
// obligation with the result, a `Trusted` one included
// (`solver_result_vouches_for_no_certificate`). P5: the bound ignored request
// options that change what a result means (`*_derives_no_bound`).
//
// ROUND 3 (the adversarial verdict on 8958b24a). P-A: the REQUEST's replay
// atoms were an unbound premise — an `Assumption` atom the module never
// states, or an `Assertion` atom whose formula is not its obligation's claim,
// ESTABLISHED (`request_replay_*`). P-D: a clean-expr `Goal` on a body node
// was in no digest (`goal_annotation_*`), and the context was an enumerated
// list, so every field nobody listed was unbound by omission; the default is
// now REVERSED (`replay_context_binds_*`). P-E: a result that rests on other
// obligations did not say so, and an assumed precondition that was `Failed`
// stayed Established (`*premise*`). P-B/P-C/P-F: the unindexable-context
// refusals, the refusal-wins merge, obligation renumbering, the evidence's
// request match and a relabelled row had no committed negative control.
//
// ROUND 4 (the adversarial verdict on 89957e87). An UNDETERMINED reason
// ended the row before later checks that could REFUSE it: a clean-expr `Goal`
// on an unrelated function of either bundle hid a forged solved context, an
// invalid or refuted result, a failed premise and a mode/strength mismatch,
// so `refusals()` was empty and the bundle was admitted; `ObligationNotModeled`
// hid the mode check the same way. Now every check that can still run does,
// and the first undetermined reason is the verdict only when none refuses
// (`*_masks_no_*`, `an_unbound_goal_is_the_first_undetermined_reason`).
//
// ROUND 5 (the verdicts on 794227ad). ONE FORMULA: the contract replay
// grounded an obligation's `smtlib` rendering whatever its schema, so a true
// rendering was kernel-certified and admitted for a FALSE `smtlib2` payload,
// and an opaque payload was grounded as SMT-LIB
// (`a_replay_grounds_only_the_obligations_one_formula_text`,
// `two_formula_texts_are_refused_by_both_validators`). GOALDRIFT: a Goal on
// an unrelated function still masked a context DRIFT, and with a Goal on the
// solved side the row's cited context digest was checked against nothing
// (`a_goal_masks_no_context_drift`, `a_goal_leaves_no_cited_context_digest_unchecked`).
// FEATURELESS: a build without the optional `coverage-attestation` feature
// could not recompute the claim or context digest, so a forgery of either
// was not refused; the feature is gone
// (`every_build_refuses_a_forged_claim_or_context_digest`).
//
// ROUND 6 (the verdict on 794601e2). ONE FORMULA held only an obligation's
// formula: a summary clause, a spec carrier, a temporal formula and a replay
// atom could still state two texts past both validators
// (`every_formula_a_module_states_is_held_to_one_text`); the free-name nonneg
// family had no committed control
// (`the_nonneg_family_grounds_only_the_one_formula_text`).
//
// Every forgery negative below is ONE mutation of a fixture that establishes,
// and asserts its SPECIFIC refusal. The basis-R replayer here is
// `TestOnlyDigestCheckingReplayer`: it re-hashes the attachment bytes against
// the evidence descriptors and reads a toy invariant model; it exists only in
// this test target and must never be linked into a consumer.

// The deprecated legacy rule is exercised on purpose: the A/B tests show it
// agreeing where the replacement refuses.
#![allow(deprecated)]
// The fixtures are shared by the kernel and kernel-less builds; each build
// compiles only the tests it can run.
#![cfg_attr(not(feature = "clean-tv-anchor"), allow(dead_code, unused_imports))]

use trust_ir::inst::Inst;
use trust_ir::node::InstrNode;
use trust_ir::proof::{
    CoverageAssurance, CoverageBound, KernelClaimFamily, ObligationKind, ProofCertificate,
    ProofCertificateRef, ProofDigest, ProofEvidence, ProofFormula, ProofLineageId,
    ProofLineageManifest, ProofLineageNode, ProofObligation, ProofObligationSourceIdentity,
    ProofObligationSourceRange, ProofReplayIdentity, ProofStatus, ProofTransform,
    ProofTransformStage, PublicObligationIdentity,
};
use trust_ir::request::{
    NativeAdapterInput, NativeAssertionId, NativeBundleProducer, NativeCoverageAttestation,
    NativeCoverageAttestationRow, NativeCoverageReplayInconclusive, NativeCoverageReplayRefusal,
    NativeCoverageResultReplay, NativeEvidenceArtifact, NativeEvidenceArtifactAttachment,
    NativeEvidenceArtifactKind, NativeEvidenceBundle, NativeObligationCause,
    NativeObligationSource, NativeReplayAtom, NativeReplayAtomId, NativeReplayAtomKind,
    NativeReplayContextUnavailable, NativeReplayedResult, NativeReplayedStrength, NativeRequestId,
    NativeRequestProvenance, NativeSourceLanguage, NativeToolIdentity, NativeUnsupportedMode,
    NativeUnsupportedModeReason, NativeVerificationBundle, NativeVerificationRequest,
    NativeVerifierSuite, TrustMcArithmeticModel, TrustMcBmcOptions, TrustMcChcEngine,
    TrustMcChcOptions, TrustMcInvariantSource, TrustMcMemoryModel, TrustMcNativeRequest,
    TrustMcPdrGeneralization, TrustMcPdrOptions, TrustMcRequestOptions, TrustMcSlicingMode,
    TrustMcVerificationMode, TrustVcNativeRequest, TrustVcVerificationMode, TrustWpFramePolicy,
    TrustWpHeapModel, TrustWpLoopStrategy, TrustWpNativeRequest, TrustWpPanicSemantics,
    TrustWpRequestOptions, TrustWpVerificationMode,
};
use trust_ir::ty::FuncTy;
use trust_ir::value::{BlockId, FuncId, ProofId};
use trust_ir::{Block, Function, Module, Producer, SourceSpan};
use trust_ir_build::validate::ValidationError;
use trust_ir_build::{
    CertificateCoverage, CoverageBasis, CoverageEstablishmentReport, CoverageInputs,
    CoverageUndeterminedReason, MachineSemanticsDivergence, ObligationCoverage,
    VerifiedSolverResult, bound_established_by_kernel_claim, bound_established_by_replayed_result,
    coverage_assurance_report, coverage_establishment_report, request_machine_semantics_divergence,
};

// ===========================================================================
// fixtures: one module, two obligations
// ===========================================================================

/// #0: a kernel-certifiable ground contract, `(>= 5 0)` — the shape of Trust's
/// `kernel_certified_native_bundle_module`. #1: a panic-freedom obligation a
/// TrustMc request is asked about.
const CONTRACT: u32 = 0;
const PANIC: u32 = 1;
const PROVER_VC: &str = "trust_vc-clean-kernel";
const PROVER_MC: &str = "trust-mc";

fn digest(seed: u8) -> ProofDigest {
    ProofDigest::sha256([seed; 32])
}

fn public_id(index: u32) -> String {
    format!("vc:kernel_checked:coverage:{index}")
}

fn obligation(
    index: u32,
    kind: ObligationKind,
    status: ProofStatus,
    formula: &str,
    file: u32,
) -> ProofObligation {
    ProofObligation::new(
        ProofId::new(index),
        kind,
        status,
        format!("obligation {index}"),
    )
    .with_formula(ProofFormula::smtlib2(formula, "Bool"))
    .with_function(FuncId::new(0))
    .with_source(
        ProofObligationSourceIdentity::new(
            format!("coverage:source:{index}"),
            format!("coverage:assertion:{index}"),
        )
        .with_range(ProofObligationSourceRange {
            file,
            start_line: 10 + index,
            start_col: 1,
            end_line: 10 + index,
            end_col: 2,
        })
        .with_public(PublicObligationIdentity {
            obligation_id: public_id(index),
            semantic_digest: ProofDigest::sha256_domain(
                "coverage_establishment.public",
                &index.to_le_bytes(),
            ),
        }),
    )
}

/// The module WITHOUT any certificate.
fn bare_module() -> Module {
    let mut module = Module::new("coverage_establishment");
    let file = module
        .intern_file("src/kernel_checked.rs")
        .expect("Module::intern_file: test fixture");
    let ft = module
        .add_func_type(FuncTy {
            params: Vec::new(),
            returns: Vec::new(),
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let function = Function::new(FuncId::new(0), "kernel_checked", ft, BlockId::new(0))
        .with_producer(Producer::TRust);
    let mut function = function;
    function.blocks.push(Block {
        id: BlockId::new(0),
        params: Vec::new(),
        body: vec![InstrNode::new(Inst::Return { values: Vec::new() })],
    });
    module
        .try_add_function(function)
        .expect("Module::try_add_function: test fixture");
    module.proof_obligations.push(obligation(
        CONTRACT,
        ObligationKind::Postcondition,
        ProofStatus::Discharged,
        "(>= 5 0)",
        file,
    ));
    module.proof_obligations.push(obligation(
        PANIC,
        ObligationKind::PanicFreedom,
        ProofStatus::Pending,
        "true",
        file,
    ));
    module
}

/// The canonical proof term of a ground contract goal:
/// `@Eq.refl Bool Bool.true`, in the shared Clean Expr codec. Pinned as bytes
/// so the KERNEL-LESS build carries the very certificate the kernel build
/// establishes; `pinned_contract_term_is_the_minted_one` holds it to the
/// minter.
const REFL_TRUE_TERM: &[u8] = &[
    4, 0, 0, 0, 4, 0, 0, 0, 3, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0,
    69, 113, 4, 0, 0, 0, 0, 0, 0, 0, 114, 101, 102, 108, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0,
    0, 0, 3, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 66, 111, 111, 108, 0, 0, 0,
    0, 0, 0, 0, 0, 3, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 66, 111,
    111, 108, 4, 0, 0, 0, 0, 0, 0, 0, 116, 114, 117, 101, 0, 0, 0, 0, 0, 0, 0, 0,
];

fn contract_term() -> Vec<u8> {
    #[cfg(feature = "clean-tv-anchor")]
    {
        let module = bare_module();
        let minted = trust_ir::clean_expr_lowering::contract::contract_clean_cic_certificate(
            &module.proof_obligations[CONTRACT as usize],
            PROVER_VC,
        )
        .expect("(>= 5 0) is a kernel-dischargeable ground contract");
        let ProofEvidence::CleanCic { term, .. } = minted.evidence else {
            panic!("the contract minter produces CleanCic");
        };
        term
    }
    #[cfg(not(feature = "clean-tv-anchor"))]
    {
        REFL_TRUE_TERM.to_vec()
    }
}

/// The contract certificate for #0, built field by field (so the kernel-less
/// build can carry it too): the pinned term under #0's own lineage.
fn contract_certificate(module: &Module) -> ProofCertificate {
    let obligation = &module.proof_obligations[CONTRACT as usize];
    ProofCertificate {
        obligation: obligation.id,
        prover: PROVER_VC.to_string(),
        evidence: ProofEvidence::CleanCic {
            term: contract_term(),
            context: Vec::new(),
            lineage: trust_ir::proof::clean_cic_lineage_digest(obligation),
            kernel_recheck: None,
        },
        assurance: None,
    }
}

/// The certificate trust-mc's result is written back as, for #1.
fn solver_certificate() -> ProofCertificate {
    ProofCertificate {
        obligation: ProofId::new(PANIC),
        prover: PROVER_MC.to_string(),
        evidence: ProofEvidence::SmtProof(b"(trust-mc chc valid)".to_vec()),
        assurance: None,
    }
}

fn replay(tool: &str, command: &str, seed: &[u8]) -> ProofReplayIdentity {
    ProofReplayIdentity::new(tool, command).with_transcript_digest(ProofDigest::sha256_domain(
        "coverage_establishment.replay",
        seed,
    ))
}

fn trust_vc_import(certificates: Vec<ProofCertificateRef>) -> NativeVerificationRequest {
    NativeVerificationRequest::TrustVc(TrustVcNativeRequest {
        id: NativeRequestId::new(0),
        mode: TrustVcVerificationMode::ImportProofCertificates,
        obligations: vec![ProofId::new(CONTRACT)],
        certificates,
        lineage_roots: vec![ProofLineageId::new(0)],
        options: Default::default(),
        diagnostics: Default::default(),
        provenance: NativeRequestProvenance::new(
            NativeVerifierSuite::TrustVc,
            NativeToolIdentity::new("trust_vc").with_version("semantics-v1"),
        )
        .with_solver(NativeToolIdentity::new("clean-kernel").with_version("0.9.0"))
        .with_replay(replay("trust_vc", "trust_vc import", b"vc")),
        function: None,
    })
}

fn trust_mc_request_with(
    id: u32,
    mode: TrustMcVerificationMode,
    unwind_limit: u32,
    obligations: &[u32],
    transcript: ProofDigest,
) -> NativeVerificationRequest {
    NativeVerificationRequest::TrustMc(TrustMcNativeRequest {
        id: NativeRequestId::new(id),
        mode,
        function: FuncId::new(0),
        obligations: obligations.iter().map(|o| ProofId::new(*o)).collect(),
        lineage_roots: vec![ProofLineageId::new(0)],
        options: TrustMcRequestOptions {
            bmc: TrustMcBmcOptions {
                unwind_limit,
                unwinding_assertions: true,
            },
            chc: TrustMcChcOptions {
                emit_horn_clauses: mode != TrustMcVerificationMode::BoundedModelCheck,
                ..TrustMcChcOptions::default()
            },
            ..TrustMcRequestOptions::default()
        },
        diagnostics: Default::default(),
        provenance: NativeRequestProvenance::new(
            NativeVerifierSuite::TrustMc,
            NativeToolIdentity::new("trust_mc").with_version("chc-v1"),
        )
        .with_solver(NativeToolIdentity::new("ay-chc").with_version("1"))
        .with_replay(
            ProofReplayIdentity::new("trust_mc", "trust_mc --chc kernel_checked")
                .with_transcript_digest(transcript),
        ),
    })
}

fn trust_mc_request(mode: TrustMcVerificationMode, unwind_limit: u32) -> NativeVerificationRequest {
    trust_mc_request_with(
        1,
        mode,
        unwind_limit,
        &[PANIC],
        ProofDigest::sha256_domain("coverage_establishment.replay", b"mc"),
    )
}

fn chc_request() -> NativeVerificationRequest {
    trust_mc_request(TrustMcVerificationMode::Chc, 1)
}

/// A native bundle bound to `module`: lineage, provenance and obligation
/// sources as the validator requires, plus `requests`. No evidence.
fn bundle_for(
    module: Module,
    requests: Vec<NativeVerificationRequest>,
) -> NativeVerificationBundle {
    let module_digest = module.stable_digest();
    let source = ProofDigest::sha256_domain("coverage_establishment.source", b"kernel_checked");
    let mut node = ProofLineageNode::new(
        ProofLineageId::new(0),
        ProofTransform::new(
            ProofTransformStage::Frontend,
            "rustc-mir-to-trust_ir",
            "tRust",
            "native-request-schema-v1",
        ),
        source,
        module_digest,
    );
    node.obligations = module.proof_obligations.iter().map(|o| o.id).collect();
    for request in &requests {
        if let NativeVerificationRequest::TrustVc(request) = request {
            node.certificates
                .extend(request.certificates.iter().cloned());
        }
    }
    node.replay = Some(replay(
        "trust-full-verify",
        "trust verify --emit-trust_ir-bundle",
        b"frontend",
    ));
    let lineage = ProofLineageManifest {
        schema_version: ProofLineageManifest::SCHEMA_VERSION,
        nodes: vec![node],
        roots: vec![ProofLineageId::new(0)],
    };
    let obligation_sources: Vec<NativeObligationSource> = module
        .proof_obligations
        .iter()
        .map(|obligation| NativeObligationSource {
            obligation: obligation.id,
            public_obligation_id: public_id(obligation.id.index()),
            function: Some(FuncId::new(0)),
            span: Some(SourceSpan {
                file: 0,
                line: 10 + obligation.id.index(),
                col: 1,
            }),
            assertion_id: Some(NativeAssertionId::new(obligation.id.index())),
            cause: if obligation.id.index() == CONTRACT {
                NativeObligationCause::Postcondition
            } else {
                NativeObligationCause::Panic
            },
            monomorphization: None,
            facts: Vec::new(),
        })
        .collect();
    let mut bundle = NativeVerificationBundle::new(
        NativeBundleProducer::TRust,
        NativeAdapterInput::RustMir {
            body_digest: source,
        },
        module_digest,
        module,
        lineage,
    );
    bundle.provenance.source_language = NativeSourceLanguage::Rust;
    bundle.provenance.source_languages = [NativeSourceLanguage::Rust].into_iter().collect();
    bundle.compiler_facts.obligation_sources = obligation_sources;
    bundle.requests = requests;
    bundle
}

/// Basis K's fixture: #0 carries the kernel-replayable contract certificate,
/// imported by a TrustVc request; #1 is asked of TrustMc (pending).
fn kernel_module() -> Module {
    let mut module = bare_module();
    let certificate = contract_certificate(&module);
    module.proof_certificates.push(certificate);
    module
}

fn kernel_bundle(module: Module) -> NativeVerificationBundle {
    let contract = module.proof_certificates[0].lineage_ref();
    bundle_for(module, vec![trust_vc_import(vec![contract]), chc_request()])
}

fn contract_ref(module: &Module) -> ProofCertificateRef {
    module
        .proof_certificates
        .iter()
        .find(|c| c.obligation == ProofId::new(CONTRACT) && c.prover == PROVER_VC)
        .expect("the fixture carries the contract certificate")
        .lineage_ref()
}

fn report(bundle: &NativeVerificationBundle) -> CoverageEstablishmentReport {
    coverage_establishment_report(bundle, CoverageInputs::default())
}

fn undetermined(reason: CoverageUndeterminedReason) -> CertificateCoverage {
    CertificateCoverage::Undetermined { reason }
}

/// "Nothing establishes this certificate": `NoBasis` where the kernel could
/// have replayed it and did not, `KernelUnavailable` in a kernel-less build.
fn no_basis() -> CertificateCoverage {
    undetermined(if NativeVerificationBundle::kernel_replay_available() {
        CoverageUndeterminedReason::NoBasis
    } else {
        CoverageUndeterminedReason::KernelUnavailable
    })
}

// ===========================================================================
// fixture sanity
// ===========================================================================

#[test]
fn fixtures_validate() {
    let carried = bundle_for(kernel_module(), vec![chc_request()]);
    assert_eq!(carried.validate(), Ok(()), "{:#?}", carried.validate());
    // An imported CleanCic certificate validates only where the kernel can
    // replay it (see `kernel_less_build_establishes_nothing`).
    let imported = kernel_bundle(kernel_module());
    assert_eq!(
        imported.validate().is_ok(),
        NativeVerificationBundle::kernel_replay_available(),
        "{:#?}",
        imported.validate()
    );
}

// ===========================================================================
// basis K — a kernel-replayed claim of a classified family
// ===========================================================================

/// A/B. Pre-fix there is no API for this, and the ONLY coverage rule records
/// nothing for a certificate with no in-module row (0 recorded, 0 agreed), so
/// every consumer rejected Trust's kernel-certified contract as unrecorded.
#[cfg(feature = "clean-tv-anchor")]
#[test]
fn kernel_replayed_contract_certificate_is_established_unbounded_without_a_row() {
    let module = kernel_module();
    assert!(
        module
            .proof_certificates
            .iter()
            .all(|c| c.assurance.is_none()),
        "no in-module row anywhere"
    );
    let certificate = contract_ref(&module);
    let bundle = kernel_bundle(module);

    let legacy = coverage_assurance_report(&bundle.module, Some(&bundle));
    assert!(legacy.is_checked());
    assert_eq!(
        (legacy.recorded(), legacy.agreed()),
        (0, 0),
        "pre-fix: nothing"
    );

    let report = report(&bundle);
    assert!(report.is_checked(), "{}", report.summary());
    assert_eq!(report.refusals(), &[] as &[ValidationError]);
    assert_eq!(
        report.for_certificate(&certificate),
        CertificateCoverage::Established {
            bound: CoverageBound::Unbounded,
            basis: CoverageBasis::KernelReplayedClaim {
                certificate: certificate.clone(),
                family: KernelClaimFamily::ContractGroundDecision,
            },
        }
    );
    assert!(
        report
            .summary()
            .contains("1 established by a kernel-replayed claim"),
        "{}",
        report.summary()
    );
}

/// Negative control: a flipped byte in the proof term. The lineage still binds
/// (it is over the OBLIGATION), so only the kernel can tell — and it does.
#[cfg(feature = "clean-tv-anchor")]
#[test]
fn tampered_contract_term_is_not_established() {
    let mut module = kernel_module();
    let ProofEvidence::CleanCic { term, .. } = &mut module.proof_certificates[0].evidence else {
        panic!("contract certificate is CleanCic");
    };
    *term.last_mut().expect("non-empty term") ^= 0x01;
    let tampered = contract_ref(&module);

    // Imported by TrustVc: the bundle itself refuses an unreplayed import, so
    // the report is UNCHECKED and establishes nothing.
    let imported = kernel_bundle(module.clone());
    assert!(imported.validate().is_err());
    let report_imported = report(&imported);
    assert!(!report_imported.is_checked());
    assert_eq!(
        report_imported.for_certificate(&tampered),
        undetermined(CoverageUndeterminedReason::ReportUnchecked)
    );

    // Merely carried (the bundle validates): not replayed, no basis.
    let carried = bundle_for(module, vec![chc_request()]);
    assert_eq!(carried.validate(), Ok(()));
    assert!(carried.kernel_replayed_certificates().is_empty());
    let report_carried = report(&carried);
    assert!(report_carried.is_checked());
    assert_eq!(report_carried.for_certificate(&tampered), no_basis());
}

fn with_directive(anchor: &str, directive_module: &str) -> Module {
    let mut module = kernel_module();
    let ProofEvidence::CleanCic { kernel_recheck, .. } = &mut module.proof_certificates[0].evidence
    else {
        panic!("contract certificate is CleanCic");
    };
    *kernel_recheck = Some(trust_ir::proof::CleanCicKernelRecheck {
        module: directive_module.to_string(),
        theorems: Vec::new(),
        anchor: anchor.to_string(),
        allowed_axioms: Vec::new(),
        binding: None,
    });
    module
}

/// Negative control: the SAME term, labelled with another anchor. The native
/// authority replays it against the contract goal (the bundle validates), but
/// what its producer claimed to prove is not what was replayed: unclassified,
/// so no coverage. The canonical contract anchor is the control.
#[cfg(feature = "clean-tv-anchor")]
#[test]
fn unclassified_anchor_family_is_undetermined() {
    let farkas = with_directive(
        trust_ir::proof::KERNEL_ANCHOR_FARKAS_CONSTRUCTIVE,
        "NNVerify",
    );
    let certificate = contract_ref(&farkas);
    let bundle = kernel_bundle(farkas);
    assert_eq!(
        bundle.validate(),
        Ok(()),
        "replayed, so the import validates"
    );
    assert_eq!(
        bundle.kernel_replayed_certificates().get(&certificate),
        Some(&None),
        "replayed in the kernel, family unclassified"
    );
    let unclassified = report(&bundle);
    assert_eq!(
        unclassified.for_certificate(&certificate),
        undetermined(CoverageUndeterminedReason::ClaimFamilyUnclassified)
    );
    assert!(unclassified.refusals().is_empty());

    let contract = with_directive(
        trust_ir::proof::KERNEL_ANCHOR_TRUST_IR_CONTRACT,
        trust_ir::proof::KERNEL_ANCHOR_TRUST_IR_CONTRACT_MODULE,
    );
    let certificate = contract_ref(&contract);
    let bundle = kernel_bundle(contract);
    assert!(matches!(
        report(&bundle).for_certificate(&certificate),
        CertificateCoverage::Established {
            bound: CoverageBound::Unbounded,
            basis: CoverageBasis::KernelReplayedClaim {
                family: KernelClaimFamily::ContractGroundDecision,
                ..
            },
        }
    ));
}

#[test]
fn kernel_claim_table_maps_only_the_contract_family() {
    assert_eq!(
        bound_established_by_kernel_claim(KernelClaimFamily::ContractGroundDecision),
        Some(CoverageBound::Unbounded)
    );
}

/// The kernel-less build (`--no-default-features`: no `clean-expr`) carries
/// the very certificate the kernel build establishes, and establishes nothing.
#[cfg(not(feature = "clean-tv-anchor"))]
#[test]
fn kernel_less_build_establishes_nothing() {
    assert!(!NativeVerificationBundle::kernel_replay_available());
    let module = kernel_module();
    let certificate = contract_ref(&module);

    let imported = kernel_bundle(module.clone());
    assert!(imported.kernel_replayed_certificates().is_empty());
    let unchecked = report(&imported);
    assert!(
        !unchecked.is_checked(),
        "an unreplayable import does not validate"
    );
    assert_eq!(
        unchecked.for_certificate(&certificate),
        undetermined(CoverageUndeterminedReason::ReportUnchecked)
    );

    let carried = bundle_for(module, vec![chc_request()]);
    assert_eq!(carried.validate(), Ok(()));
    let checked = report(&carried);
    assert!(checked.is_checked());
    assert_eq!(
        checked.for_certificate(&certificate),
        undetermined(CoverageUndeterminedReason::KernelUnavailable)
    );
    assert!(checked.refusals().is_empty());
}

/// The kernel-less test is only as strong as its certificate: the pinned term
/// IS the one the minter produces.
#[cfg(feature = "clean-tv-anchor")]
#[test]
fn pinned_contract_term_is_the_minted_one() {
    assert!(NativeVerificationBundle::kernel_replay_available());
    assert_eq!(contract_term(), REFL_TRUE_TERM);
}

fn sibling(prover: &str, evidence: ProofEvidence) -> ProofCertificate {
    ProofCertificate {
        obligation: ProofId::new(CONTRACT),
        prover: prover.to_string(),
        evidence,
        assurance: None,
    }
}

/// Negative control: an SMT and a `Trusted` certificate on the SAME obligation
/// as the replayed CleanCic. Coverage is per certificate: they gain nothing.
#[cfg(feature = "clean-tv-anchor")]
#[test]
fn sibling_certificate_cannot_borrow_kernel_basis() {
    let mut module = kernel_module();
    let smt = sibling("z3", ProofEvidence::SmtProof(b"(proof)".to_vec()));
    let trusted = sibling("auditor", ProofEvidence::Trusted("reviewed".to_string()));
    module.proof_certificates.push(smt.clone());
    module.proof_certificates.push(trusted.clone());
    let certificate = contract_ref(&module);
    let bundle = kernel_bundle(module);
    assert_eq!(bundle.validate(), Ok(()));
    assert_eq!(
        bundle
            .kernel_replayed_certificates()
            .keys()
            .collect::<Vec<_>>(),
        vec![&certificate],
        "only the CleanCic certificate itself was replayed"
    );
    let report = report(&bundle);
    assert!(matches!(
        report.for_certificate(&certificate),
        CertificateCoverage::Established { .. }
    ));
    for borrower in [smt, trusted] {
        assert_eq!(
            report.for_certificate(&borrower.lineage_ref()),
            undetermined(CoverageUndeterminedReason::NotTheReplayedCertificate)
        );
    }
    assert!(report.refusals().is_empty());
}

/// Negative control: the in-module row is non-authoritative. `Some(Unbounded)`
/// on a certificate with no basis refuses the bundle; on a certificate whose
/// derived bound meets it, and as `Unrecorded` anywhere, it is ignored.
#[cfg(feature = "clean-tv-anchor")]
#[test]
fn in_module_row_exceeding_derived_is_refused() {
    let cited = chc_request().stable_digest();
    let row = |bound| {
        Some(CoverageAssurance {
            bound,
            request_digest: cited,
        })
    };
    let mut module = kernel_module();
    module.proof_certificates[0].assurance = row(CoverageBound::Unbounded);
    let mut liar = sibling("z3", ProofEvidence::SmtProof(b"(proof)".to_vec()));
    liar.assurance = row(CoverageBound::Unbounded);
    let mut modest = sibling("auditor", ProofEvidence::Trusted("reviewed".to_string()));
    modest.assurance = row(CoverageBound::Unrecorded);
    module.proof_certificates.push(liar.clone());
    module.proof_certificates.push(modest.clone());
    let certificate = contract_ref(&module);
    let bundle = kernel_bundle(module);
    assert_eq!(bundle.validate(), Ok(()));

    let report = report(&bundle);
    let refusal = ValidationError::CoverageRowExceedsEstablished {
        obligation: CONTRACT,
        recorded: "Unbounded".to_string(),
        established: "nothing established".to_string(),
    };
    assert_eq!(
        report.for_certificate(&liar.lineage_ref()),
        CertificateCoverage::Refused(refusal.clone())
    );
    assert_eq!(report.refusals(), &[refusal]);
    assert!(matches!(
        report.for_certificate(&certificate),
        CertificateCoverage::Established {
            bound: CoverageBound::Unbounded,
            ..
        }
    ));
    assert_eq!(
        report.for_certificate(&modest.lineage_ref()),
        undetermined(CoverageUndeterminedReason::NotTheReplayedCertificate)
    );
}

// ===========================================================================
// basis R — a verified solver result cited by a sealed attestation
// ===========================================================================

const HORN: &[u8] =
    b"(declare-fun inv (Int) Bool)\n(assert (forall ((x Int)) (=> (inv x) (>= x 0))))\n";
const MODEL_VALID: &[u8] = b"(define-fun inv ((x Int)) Bool (>= x 0))\n";
const MODEL_BROKEN: &[u8] = b"(define-fun inv ((x Int)) Bool (< x 0))\n";

fn artifact_for(
    name: &str,
    kind: NativeEvidenceArtifactKind,
    bytes: &[u8],
) -> NativeEvidenceArtifact {
    NativeEvidenceArtifact::new(
        name,
        kind,
        NativeEvidenceArtifactAttachment::digest_for_bytes(
            trust_ir::proof::ProofDigestAlgorithm::Sha256,
            bytes,
        ),
    )
}

/// What the TEST replayer answers once the result bytes check out.
#[derive(Clone, Copy)]
enum Answer {
    Strength(NativeReplayedStrength),
    Refute,
    Inconclusive,
    /// A result at `strength` whose modelled obligations omit the row's.
    OmitObligation(NativeReplayedStrength),
}

/// TEST-ONLY replayer (this target is `cfg(test)` by construction). It is a
/// stand-in for trust-mc's `NativeTrustIrCoverageReplayer`: it checks that the
/// evidence is the cited request's, re-hashes every attachment against the
/// evidence descriptors, requires the invariant model to be the one toy model
/// that satisfies the toy Horn clauses (anything else is INVALID), and then
/// answers as configured. It must never be linked into a consumer.
struct TestOnlyDigestCheckingReplayer {
    answer: Answer,
}

fn replayer(answer: Answer) -> TestOnlyDigestCheckingReplayer {
    TestOnlyDigestCheckingReplayer { answer }
}

impl NativeCoverageResultReplay for TestOnlyDigestCheckingReplayer {
    fn replay(
        &self,
        solved: &NativeVerificationBundle,
        request: &NativeVerificationRequest,
        evidence: &NativeEvidenceBundle,
        attachments: &[NativeEvidenceArtifactAttachment],
    ) -> Result<NativeReplayedResult, NativeCoverageReplayRefusal> {
        let invalid = |detail: &str| {
            Err(NativeCoverageReplayRefusal::Invalid {
                detail: detail.to_string(),
            })
        };
        if evidence.request() != request.id()
            || evidence.request_digest() != request.stable_digest()
            || evidence.trust_ir_module_digest() != solved.trust_ir_module_digest
        {
            return invalid("the evidence is not the cited request's");
        }
        for attachment in attachments {
            let actual = NativeEvidenceArtifactAttachment::digest_for_bytes(
                attachment.key.digest_algorithm,
                &attachment.bytes,
            );
            if actual != attachment.key.digest
                || !evidence
                    .artifacts()
                    .iter()
                    .any(|a| a.kind == attachment.key.kind && a.digest == actual)
            {
                return invalid("an attachment does not hash to an evidence descriptor");
            }
        }
        let Some(model) = attachments
            .iter()
            .find(|a| a.key.kind == NativeEvidenceArtifactKind::TrustMcModel)
        else {
            return Err(NativeCoverageReplayRefusal::Inconclusive {
                reason: NativeCoverageReplayInconclusive::Unsupported,
                detail: "no invariant model to replay".to_string(),
            });
        };
        if model.bytes != MODEL_VALID {
            return invalid("the invariant model does not satisfy the Horn clauses");
        }
        let obligations = request.obligations().to_vec();
        match self.answer {
            Answer::Strength(strength) => Ok(NativeReplayedResult::new(obligations, strength)),
            Answer::Refute => Err(NativeCoverageReplayRefusal::Refuted {
                obligations,
                detail: "counterexample re-checked".to_string(),
            }),
            Answer::Inconclusive => Err(NativeCoverageReplayRefusal::Inconclusive {
                reason: NativeCoverageReplayInconclusive::Budget,
                detail: "replay budget exhausted".to_string(),
            }),
            Answer::OmitObligation(strength) => Ok(NativeReplayedResult::new(Vec::new(), strength)),
        }
    }
}

/// `Module::obligation_digest` of `obligation`.
fn claim_digest(module: &Module, obligation: u32) -> ProofDigest {
    module
        .obligation_digest(ProofId::new(obligation))
        .expect("fixture obligations are addressable")
        .0
}

/// What a producer writes as the row's replay-context digest: the solved
/// bundle's — also when a `Goal` outside every wire image leaves it
/// untransferable, since the digest binds everything else and is checked —
/// or, when it has none (an unindexable obligation table), a digest no
/// bundle recomputes.
fn row_context_digest(bundle: &NativeVerificationBundle) -> ProofDigest {
    bundle
        .coverage_replay_context_digest()
        .map_or(digest(0x35), |context| context.digest)
}

/// `NativeVerificationBundle::coverage_replay_context_digest` of a fixture
/// whose obligation table is indexable.
fn context_digest(bundle: &NativeVerificationBundle) -> ProofDigest {
    bundle
        .coverage_replay_context_digest()
        .expect("fixture obligation tables are indexable")
        .digest
}

/// A solve and its write-back. `solved` is M1 plus the request and its result
/// evidence; `admitted` is M2 = the bare module plus trust-mc's certificate for
/// #1, with the same request and NO evidence (the attestation carries the
/// citation).
struct SolvedFixture {
    request: NativeVerificationRequest,
    solved: NativeVerificationBundle,
    admitted: NativeVerificationBundle,
    attachments: Vec<NativeEvidenceArtifactAttachment>,
    row: NativeCoverageAttestationRow,
}

impl SolvedFixture {
    fn new(
        request: NativeVerificationRequest,
        extra_requests: Vec<NativeVerificationRequest>,
        model: &[u8],
        edit_admitted: impl FnOnce(&mut Module),
    ) -> Self {
        Self::editing_both(request, extra_requests, model, |_| {}, edit_admitted)
    }

    /// [`Self::new`], with M1 (the SOLVED module) edited too; M2 starts from
    /// the unedited bare module.
    fn editing_both(
        request: NativeVerificationRequest,
        extra_requests: Vec<NativeVerificationRequest>,
        model: &[u8],
        edit_solved: impl FnOnce(&mut Module),
        edit_admitted: impl FnOnce(&mut Module),
    ) -> Self {
        let mut m1 = bare_module();
        edit_solved(&mut m1);
        let mut requests = vec![request.clone()];
        requests.extend(extra_requests);
        let mut solved = bundle_for(m1.clone(), requests.clone());
        let bounded = matches!(
            &request,
            NativeVerificationRequest::TrustMc(r) if r.mode == TrustMcVerificationMode::BoundedModelCheck
        );
        let mut artifacts = Vec::new();
        let mut bytes: Vec<&[u8]> = Vec::new();
        if !bounded {
            artifacts.push(artifact_for(
                "kernel_checked.horn.smt2",
                NativeEvidenceArtifactKind::TrustMcHornClauses,
                HORN,
            ));
            bytes.push(HORN);
        }
        artifacts.push(artifact_for(
            "kernel_checked.invariant.smt2",
            NativeEvidenceArtifactKind::TrustMcModel,
            model,
        ));
        bytes.push(model);
        let evidence = solved
            .evidence_bundle_for_request(&request, artifacts.clone())
            .expect("the request carries a replay identity");
        solved.evidence_bundles.push(evidence.clone());
        assert_eq!(solved.validate(), Ok(()), "{:#?}", solved.validate());

        let mut m2 = bare_module();
        m2.proof_certificates.push(solver_certificate());
        edit_admitted(&mut m2);
        let admitted = bundle_for(m2, requests);

        let attachments = artifacts
            .iter()
            .zip(bytes)
            .map(|(artifact, bytes)| {
                NativeEvidenceArtifactAttachment::for_artifact(
                    request.id(),
                    NativeVerifierSuite::TrustMc,
                    artifact,
                    "trust-mc:coverage-establishment-test",
                    bytes.to_vec(),
                )
            })
            .collect();
        let row = NativeCoverageAttestationRow {
            obligation: ProofId::new(PANIC),
            obligation_digest: claim_digest(&m1, PANIC),
            solved_module_digest: solved.trust_ir_module_digest,
            solved_executable_content_digest: m1.executable_content_digest_v1(),
            solved_replay_context_digest: row_context_digest(&solved),
            solved_bundle_digest: solved.stable_digest(),
            request_digest: request.stable_digest(),
            evidence_bundle_digest: evidence.stable_digest(),
            result_artifacts: artifacts,
        };
        SolvedFixture {
            request,
            solved,
            admitted,
            attachments,
            row,
        }
    }

    fn chc() -> Self {
        Self::new(chc_request(), Vec::new(), MODEL_VALID, |_| {})
    }

    /// The certificate trust-mc's result is written back as.
    fn certificate(&self) -> ProofCertificateRef {
        solver_certificate().lineage_ref()
    }

    /// The obligation the fixture's result is about.
    fn obligation(&self) -> ProofId {
        ProofId::new(PANIC)
    }

    fn report_with(
        &self,
        rows: Vec<NativeCoverageAttestationRow>,
        replay: Option<&dyn NativeCoverageResultReplay>,
    ) -> CoverageEstablishmentReport {
        self.report_on(&self.admitted, NativeCoverageAttestation::new(rows), replay)
    }

    fn report_on(
        &self,
        admitted: &NativeVerificationBundle,
        attestation: NativeCoverageAttestation,
        replay: Option<&dyn NativeCoverageResultReplay>,
    ) -> CoverageEstablishmentReport {
        let solved = [&self.solved];
        coverage_establishment_report(
            admitted,
            CoverageInputs {
                attestation: Some(&attestation),
                solved_bundles: &solved,
                attachments: &self.attachments,
                replay,
            },
        )
    }

    /// Only `refusal`, attached to the obligation; the written-back
    /// certificate is untouched by it (basis R names no certificate).
    fn assert_refused(&self, report: &CoverageEstablishmentReport, refusal: ValidationError) {
        assert!(report.is_checked(), "{}", report.summary());
        assert_eq!(report.refusals(), std::slice::from_ref(&refusal));
        assert_eq!(
            report.for_obligation(self.obligation()),
            ObligationCoverage::Refused(refusal)
        );
        assert_eq!(report.for_certificate(&self.certificate()), no_basis());
    }

    /// The obligation's basis-R verdict is `Established` at `bound`.
    fn assert_established(&self, report: &CoverageEstablishmentReport, bound: CoverageBound) {
        assert!(report.is_checked(), "{}", report.summary());
        assert!(report.refusals().is_empty(), "{:?}", report.refusals());
        match report.for_obligation(self.obligation()) {
            ObligationCoverage::Established {
                bound: established,
                basis,
            } => {
                assert_eq!(established, bound);
                assert_eq!(basis.obligation, self.obligation());
            }
            other => panic!("expected Established {bound:?}, got {other:?}"),
        }
    }
}

fn obligation_undetermined(reason: CoverageUndeterminedReason) -> ObligationCoverage {
    ObligationCoverage::Undetermined { reason }
}

fn chc_valid() -> TestOnlyDigestCheckingReplayer {
    replayer(Answer::Strength(NativeReplayedStrength::ChcValidity))
}

/// The positive the negatives are one mutation away from. Basis R is PER
/// OBLIGATION: the verdict names the obligation, the replay context and the
/// result — and no certificate.
#[test]
fn verified_chc_result_is_established_unbounded() {
    let fixture = SolvedFixture::chc();
    assert_eq!(fixture.admitted.validate(), Ok(()));
    assert!(fixture.admitted.evidence_bundles.is_empty());
    let report = fixture.report_with(vec![fixture.row.clone()], Some(&chc_valid()));
    assert!(report.is_checked());
    assert_eq!(report.refusals(), &[] as &[ValidationError]);
    assert_eq!(
        report.for_obligation(fixture.obligation()),
        ObligationCoverage::Established {
            bound: CoverageBound::Unbounded,
            basis: VerifiedSolverResult {
                obligation: fixture.obligation(),
                row_digest: fixture.row.stable_digest(),
                solved_bundle_digest: fixture.row.solved_bundle_digest,
                request_digest: fixture.row.request_digest,
                evidence_bundle_digest: fixture.row.evidence_bundle_digest,
                replay_context_digest: fixture.row.solved_replay_context_digest,
                strength: NativeReplayedStrength::ChcValidity,
                premises: Vec::new(),
            },
        }
    );
    assert!(
        report
            .summary()
            .contains("1 established by a verified solver result"),
        "{}",
        report.summary()
    );
    assert_eq!(
        report.for_certificate(&fixture.certificate()),
        no_basis(),
        "the written-back certificate borrows nothing from its obligation's result"
    );
}

/// A/B. Inverts `ws1_11_an_unbounded_record_on_a_chc_request_agrees`: the
/// legacy rule AGREES with an `Unbounded` row citing a PENDING CHC request
/// that has no evidence at all. The replacement refuses the row, and refuses
/// the same citation moved into an attestation.
#[test]
fn pending_chc_request_without_evidence_is_not_established() {
    let request = chc_request();
    let mut module = bare_module();
    let mut certificate = solver_certificate();
    certificate.assurance = Some(CoverageAssurance {
        bound: CoverageBound::Unbounded,
        request_digest: request.stable_digest(),
    });
    module.proof_certificates.push(certificate.clone());
    let bundle = bundle_for(module.clone(), vec![request.clone()]);
    assert_eq!(bundle.validate(), Ok(()));
    assert!(bundle.evidence_bundles.is_empty(), "the request is PENDING");

    // Pre-fix: a request read as a result.
    let legacy = coverage_assurance_report(&bundle.module, Some(&bundle));
    assert_eq!(
        (legacy.recorded(), legacy.agreed(), legacy.undetermined()),
        (1, 1, 0)
    );
    assert!(legacy.errors().is_empty());

    // The row alone: it claims what nothing established.
    let row_refusal = ValidationError::CoverageRowExceedsEstablished {
        obligation: PANIC,
        recorded: "Unbounded".to_string(),
        established: "nothing established".to_string(),
    };
    let row_only = report(&bundle);
    assert_eq!(
        row_only.for_certificate(&certificate.lineage_ref()),
        CertificateCoverage::Refused(row_refusal.clone())
    );

    // The same citation as an attestation row (the admitted bundle is the
    // solved one): the request has no result evidence to cite.
    let row = NativeCoverageAttestationRow {
        obligation: ProofId::new(PANIC),
        obligation_digest: claim_digest(&module, PANIC),
        solved_module_digest: bundle.trust_ir_module_digest,
        solved_executable_content_digest: module.executable_content_digest_v1(),
        solved_replay_context_digest: context_digest(&bundle),
        solved_bundle_digest: bundle.stable_digest(),
        request_digest: request.stable_digest(),
        evidence_bundle_digest: digest(0x44),
        result_artifacts: Vec::new(),
    };
    let attestation = NativeCoverageAttestation::new(vec![row]);
    let replay = chc_valid();
    let cited = coverage_establishment_report(
        &bundle,
        CoverageInputs {
            attestation: Some(&attestation),
            replay: Some(&replay),
            ..CoverageInputs::default()
        },
    );
    let refusal = ValidationError::CoverageEvidenceMissing {
        obligation: PANIC,
        request: 1,
    };
    assert_eq!(cited.refusals(), &[refusal.clone(), row_refusal]);
    assert_eq!(
        cited.for_obligation(ProofId::new(PANIC)),
        ObligationCoverage::Refused(refusal)
    );
}

#[test]
fn request_of_another_bundle_is_refused() {
    let fixture = SolvedFixture::chc();
    let foreign = trust_mc_request_with(
        1,
        TrustMcVerificationMode::Chc,
        1,
        &[PANIC],
        ProofDigest::sha256_domain("coverage_establishment.replay", b"another bundle"),
    );
    let mut row = fixture.row.clone();
    row.request_digest = foreign.stable_digest();
    let report = fixture.report_with(vec![row], Some(&chc_valid()));
    fixture.assert_refused(
        &report,
        ValidationError::CoverageAssuranceRequestUnknown {
            obligation: PANIC,
            recorded: foreign.stable_digest(),
            bundle_requests: 1,
        },
    );
}

#[test]
fn request_omitting_obligation_is_refused() {
    let about_contract = trust_mc_request_with(
        2,
        TrustMcVerificationMode::Chc,
        1,
        &[CONTRACT],
        ProofDigest::sha256_domain("coverage_establishment.replay", b"contract"),
    );
    let fixture = SolvedFixture::new(
        chc_request(),
        vec![about_contract.clone()],
        MODEL_VALID,
        |_| {},
    );
    let mut row = fixture.row.clone();
    row.request_digest = about_contract.stable_digest();
    let report = fixture.report_with(vec![row], Some(&chc_valid()));
    fixture.assert_refused(
        &report,
        ValidationError::CoverageAssuranceObligationNotRequested {
            obligation: PANIC,
            request: 2,
            request_obligations: vec![CONTRACT],
        },
    );
}

/// P-F, the r2 verifier's surviving mutant M11. The cited evidence must be
/// the cited REQUEST's, by the consumer's own match. Requests 2 and 1 both
/// list #1 in the same suite; the solved bundle carries result evidence for
/// request 2 only. The row as written (request 2, its evidence) establishes;
/// relabelled to request 1 it is refused as evidence-missing. With the
/// `evidence.request() == request.id()` conjunct dropped, the consumer
/// resolved request 2's evidence for request 1 and only a later check caught
/// it, under another name.
#[test]
fn evidence_of_another_request_is_refused() {
    let second = trust_mc_request_with(
        2,
        TrustMcVerificationMode::Chc,
        1,
        &[PANIC],
        ProofDigest::sha256_domain("coverage_establishment.replay", b"mc-second"),
    );
    let fixture = SolvedFixture::new(second, vec![chc_request()], MODEL_VALID, |_| {});
    assert_eq!(fixture.solved.validate(), Ok(()));
    assert_eq!(fixture.admitted.validate(), Ok(()));
    let report = fixture.report_with(vec![fixture.row.clone()], Some(&chc_valid()));
    fixture.assert_established(&report, CoverageBound::Unbounded);

    let mut row = fixture.row.clone();
    row.request_digest = chc_request().stable_digest();
    let report = fixture.report_with(vec![row], Some(&chc_valid()));
    fixture.assert_refused(
        &report,
        ValidationError::CoverageEvidenceMissing {
            obligation: PANIC,
            request: 1,
        },
    );
}

/// The r2 verifier's ADV-R2-6 and ADV-R2-7, committed: a row is about the
/// obligation it NAMES, and relabelling a valid row cannot move its result.
/// (a) To an obligation neither module states (#7) and (b) to the sibling #0,
/// neither of which the cited request lists; (c) to #0 under a request that
/// lists both, the row keeping #1's claim digest. Each is refused by name and
/// nothing is established.
#[test]
fn relabelled_row_is_refused() {
    let fixture = SolvedFixture::chc();
    for (label, relabelled) in [("absent #7", 7), ("unrequested sibling #0", CONTRACT)] {
        let mut row = fixture.row.clone();
        row.obligation = ProofId::new(relabelled);
        let report = fixture.report_with(vec![row], Some(&chc_valid()));
        assert_eq!(
            report.refusals(),
            &[ValidationError::CoverageAssuranceObligationNotRequested {
                obligation: relabelled,
                request: 1,
                request_obligations: vec![PANIC],
            }],
            "{label}"
        );
        assert!(
            report
                .obligations()
                .all(|(_, verdict)| !matches!(verdict, ObligationCoverage::Established { .. })),
            "{label}"
        );
    }

    let both = trust_mc_request_with(
        1,
        TrustMcVerificationMode::Chc,
        1,
        &[CONTRACT, PANIC],
        ProofDigest::sha256_domain("coverage_establishment.replay", b"mc"),
    );
    let fixture = SolvedFixture::new(both, Vec::new(), MODEL_VALID, |_| {});
    let mut row = fixture.row.clone();
    row.obligation = ProofId::new(CONTRACT);
    let report = fixture.report_with(vec![row], Some(&chc_valid()));
    let refusal = ValidationError::CoverageSolvedBundleDigestMismatch {
        obligation: CONTRACT,
        field: "obligation_digest",
        recorded: fixture.row.obligation_digest,
        actual: claim_digest(&fixture.solved.module, CONTRACT),
    };
    assert_eq!(report.refusals(), std::slice::from_ref(&refusal));
    assert_eq!(
        report.for_obligation(ProofId::new(CONTRACT)),
        ObligationCoverage::Refused(refusal)
    );
    assert_eq!(
        report.for_obligation(ProofId::new(PANIC)),
        obligation_undetermined(CoverageUndeterminedReason::NoBasis)
    );
}

#[test]
fn evidence_digest_not_recomputing_is_refused() {
    let fixture = SolvedFixture::chc();
    let mut row = fixture.row.clone();
    row.evidence_bundle_digest = digest(0x77);
    let report = fixture.report_with(vec![row], Some(&chc_valid()));
    fixture.assert_refused(
        &report,
        ValidationError::CoverageEvidenceDigestMismatch {
            obligation: PANIC,
            request: 1,
            recorded: digest(0x77),
        },
    );
}

#[test]
fn artifact_bytes_not_hashing_is_refused() {
    // (a) The model bytes are swapped under the SAME key.
    let mut fixture = SolvedFixture::chc();
    let model = fixture
        .attachments
        .iter_mut()
        .find(|a| a.key.kind == NativeEvidenceArtifactKind::TrustMcModel)
        .expect("fixture attaches the model");
    model.bytes = MODEL_BROKEN.to_vec();
    let report = fixture.report_with(vec![fixture.row.clone()], Some(&chc_valid()));
    fixture.assert_refused(
        &report,
        ValidationError::CoverageResultArtifactUnresolved {
            obligation: PANIC,
            artifact: "kernel_checked.invariant.smt2".to_string(),
            reason: "digest_mismatch".to_string(),
        },
    );

    // (b) A cited artifact that is not a descriptor of the cited evidence.
    let fixture = SolvedFixture::chc();
    let mut row = fixture.row.clone();
    row.result_artifacts.push(artifact_for(
        "smuggled.smt2",
        NativeEvidenceArtifactKind::TrustMcModel,
        MODEL_VALID,
    ));
    let report = fixture.report_with(vec![row], Some(&chc_valid()));
    fixture.assert_refused(
        &report,
        ValidationError::CoverageResultArtifactUnresolved {
            obligation: PANIC,
            artifact: "smuggled.smt2".to_string(),
            reason: "not_a_descriptor_of_the_cited_evidence".to_string(),
        },
    );

    // (c) The bytes were never attached.
    let mut fixture = SolvedFixture::chc();
    fixture.attachments.clear();
    let report = fixture.report_with(vec![fixture.row.clone()], Some(&chc_valid()));
    fixture.assert_refused(
        &report,
        ValidationError::CoverageResultArtifactUnresolved {
            obligation: PANIC,
            artifact: "kernel_checked.horn.smt2".to_string(),
            reason: "missing_attachment".to_string(),
        },
    );
}

/// Every digest recomputes; the RESULT is wrong (the model violates the Horn
/// clauses). Only the replay can tell.
#[test]
fn replayer_invalid_result_is_refused() {
    let fixture = SolvedFixture::new(chc_request(), Vec::new(), MODEL_BROKEN, |_| {});
    let report = fixture.report_with(vec![fixture.row.clone()], Some(&chc_valid()));
    fixture.assert_refused(
        &report,
        ValidationError::CoverageResultReplayInvalid {
            obligation: PANIC,
            detail: "the invariant model does not satisfy the Horn clauses".to_string(),
        },
    );
}

/// No replayer linked: an honest row is UNDETERMINED — but a forged one is
/// still refused, because every digest is recomputed before the replay.
#[test]
fn no_replayer_is_undetermined() {
    let fixture = SolvedFixture::chc();
    let honest = fixture.report_with(vec![fixture.row.clone()], None);
    assert!(honest.is_checked());
    assert!(honest.refusals().is_empty());
    assert_eq!(
        honest.for_obligation(fixture.obligation()),
        obligation_undetermined(CoverageUndeterminedReason::NoReplayer)
    );

    let mut forged = fixture.row.clone();
    forged.evidence_bundle_digest = digest(0x78);
    let refused = fixture.report_with(vec![forged], None);
    assert!(matches!(
        refused.refusals(),
        [ValidationError::CoverageEvidenceDigestMismatch { .. }]
    ));
}

#[test]
fn inconclusive_or_unmodeled_replay_is_undetermined() {
    let fixture = SolvedFixture::chc();
    let budget = fixture.report_with(
        vec![fixture.row.clone()],
        Some(&replayer(Answer::Inconclusive)),
    );
    assert!(budget.refusals().is_empty());
    assert_eq!(
        budget.for_obligation(fixture.obligation()),
        obligation_undetermined(CoverageUndeterminedReason::ReplayInconclusive {
            reason: NativeCoverageReplayInconclusive::Budget,
            detail: "replay budget exhausted".to_string(),
        })
    );
    let unmodeled = fixture.report_with(
        vec![fixture.row.clone()],
        Some(&replayer(Answer::OmitObligation(
            NativeReplayedStrength::ChcValidity,
        ))),
    );
    assert!(unmodeled.refusals().is_empty());
    assert_eq!(
        unmodeled.for_obligation(fixture.obligation()),
        obligation_undetermined(CoverageUndeterminedReason::ObligationNotModeled)
    );
    // R4 A/B: modelling another obligation does not excuse a strength the
    // request's mode contradicts (on 89957e87 `ObligationNotModeled` returned
    // before the mode was compared).
    let contradicting = fixture.report_with(
        vec![fixture.row.clone()],
        Some(&replayer(Answer::OmitObligation(
            NativeReplayedStrength::BoundedUnwind { depth: 1 },
        ))),
    );
    fixture.assert_refused(
        &contradicting,
        ValidationError::CoverageModeStrengthMismatch {
            obligation: PANIC,
            request: 1,
            mode: "trust_mc Chc".to_string(),
            strength: "bounded_unwind:1".to_string(),
        },
    );
}

fn bmc_fixture(edit_admitted: impl FnOnce(&mut Module)) -> SolvedFixture {
    SolvedFixture::new(
        trust_mc_request(TrustMcVerificationMode::BoundedModelCheck, 4),
        Vec::new(),
        MODEL_VALID,
        edit_admitted,
    )
}

/// A depth-4 bounded check establishes `UnwindBounded { depth: 4 }` for the
/// OBLIGATION — never `Unbounded` — and the written-back certificate's
/// in-module row cannot borrow even that: the result vouches for no
/// certificate, so any row above `Unrecorded` on it claims more than its own
/// (basis K) bound.
#[test]
fn bmc_result_is_bounded_not_unbounded() {
    let depth4 = replayer(Answer::Strength(NativeReplayedStrength::BoundedUnwind {
        depth: 4,
    }));
    let fixture = bmc_fixture(|_| {});
    let report = fixture.report_with(vec![fixture.row.clone()], Some(&depth4));
    fixture.assert_established(&report, CoverageBound::UnwindBounded { depth: 4 });
    let ObligationCoverage::Established { basis, .. } = report.for_obligation(fixture.obligation())
    else {
        unreachable!("asserted above");
    };
    assert_eq!(
        basis.strength,
        NativeReplayedStrength::BoundedUnwind { depth: 4 }
    );

    let claims = |bound| {
        move |m2: &mut Module| {
            let request_digest = digest(0x10);
            m2.proof_certificates.last_mut().unwrap().assurance = Some(CoverageAssurance {
                bound,
                request_digest,
            });
        }
    };
    for bound in [
        CoverageBound::Unbounded,
        CoverageBound::UnwindBounded { depth: 4 },
    ] {
        let borrowing = bmc_fixture(claims(bound));
        let refused = borrowing.report_with(vec![borrowing.row.clone()], Some(&depth4));
        let refusal = ValidationError::CoverageRowExceedsEstablished {
            obligation: PANIC,
            recorded: format!("{bound:?}"),
            established: "nothing established".to_string(),
        };
        assert_eq!(
            refused.refusals(),
            std::slice::from_ref(&refusal),
            "{bound:?}"
        );
        assert_eq!(
            refused.for_certificate(&borrowing.certificate()),
            CertificateCoverage::Refused(refusal)
        );
    }
    // ...and an `Unrecorded` row is ignored.
    let modest = bmc_fixture(claims(CoverageBound::Unrecorded));
    let fine = modest.report_with(vec![modest.row.clone()], Some(&depth4));
    assert!(fine.refusals().is_empty());
}

#[test]
fn mode_strength_mismatch_is_refused() {
    // A CHC request "answered" by a bounded check.
    let fixture = SolvedFixture::chc();
    let bounded = replayer(Answer::Strength(NativeReplayedStrength::BoundedUnwind {
        depth: 1,
    }));
    let report = fixture.report_with(vec![fixture.row.clone()], Some(&bounded));
    fixture.assert_refused(
        &report,
        ValidationError::CoverageModeStrengthMismatch {
            obligation: PANIC,
            request: 1,
            mode: "trust_mc Chc".to_string(),
            strength: "bounded_unwind:1".to_string(),
        },
    );
    // A BMC request at unwind 4 "answered" at depth 3.
    let fixture = bmc_fixture(|_| {});
    let shallow = replayer(Answer::Strength(NativeReplayedStrength::BoundedUnwind {
        depth: 3,
    }));
    let report = fixture.report_with(vec![fixture.row.clone()], Some(&shallow));
    fixture.assert_refused(
        &report,
        ValidationError::CoverageModeStrengthMismatch {
            obligation: PANIC,
            request: 1,
            mode: "trust_mc BoundedModelCheck unwind_limit=4".to_string(),
            strength: "bounded_unwind:3".to_string(),
        },
    );
}

/// A WP request whose options mean exactly the obligation's machine
/// semantics (the heap is TrustIr memory, panics are required absent, nothing
/// is abduced), then `edit`ed.
fn wp_request_with(
    frame_policy: TrustWpFramePolicy,
    mode: TrustWpVerificationMode,
    edit: impl FnOnce(&mut TrustWpRequestOptions),
) -> NativeVerificationRequest {
    let mut options = TrustWpRequestOptions {
        heap_model: TrustWpHeapModel::TrustIrMemory,
        frame_policy,
        loop_strategy: TrustWpLoopStrategy::RequireInvariants,
        panic_semantics: TrustWpPanicSemantics::PanicFreeRequired,
        max_abduced_preconditions: 0,
        ..TrustWpRequestOptions::default()
    };
    edit(&mut options);
    NativeVerificationRequest::TrustWp(TrustWpNativeRequest {
        id: NativeRequestId::new(3),
        mode,
        function: FuncId::new(0),
        obligations: vec![ProofId::new(PANIC)],
        lineage_roots: Vec::new(),
        options,
        diagnostics: Default::default(),
        provenance: Default::default(),
    })
}

fn wp_request(
    frame_policy: TrustWpFramePolicy,
    mode: TrustWpVerificationMode,
) -> NativeVerificationRequest {
    wp_request_with(frame_policy, mode, |_| {})
}

/// The mode x strength table, arm by arm, where no fixture reaches it.
#[test]
fn replayed_result_table_requires_mode_and_strength_to_agree() {
    use NativeReplayedStrength::{
        BoundedUnwind, ChcValidity, PdrInvariant, WeakestPreconditionFullHeap,
    };
    let pdr = trust_mc_request(TrustMcVerificationMode::Pdr, 1);
    let bmc = trust_mc_request(TrustMcVerificationMode::BoundedModelCheck, 7);
    for strength in [ChcValidity, PdrInvariant] {
        assert_eq!(
            bound_established_by_replayed_result(&chc_request(), strength),
            Ok(Some(CoverageBound::Unbounded))
        );
        assert_eq!(
            bound_established_by_replayed_result(&pdr, strength),
            Ok(Some(CoverageBound::Unbounded))
        );
        assert!(bound_established_by_replayed_result(&bmc, strength).is_err());
    }
    assert_eq!(
        bound_established_by_replayed_result(&bmc, BoundedUnwind { depth: 7 }),
        Ok(Some(CoverageBound::UnwindBounded { depth: 7 }))
    );
    assert!(bound_established_by_replayed_result(&bmc, BoundedUnwind { depth: 8 }).is_err());
    let full = wp_request(
        TrustWpFramePolicy::FullHeap,
        TrustWpVerificationMode::WeakestPrecondition,
    );
    assert_eq!(
        bound_established_by_replayed_result(&full, WeakestPreconditionFullHeap),
        Ok(Some(CoverageBound::Unbounded))
    );
    assert!(bound_established_by_replayed_result(&full, ChcValidity).is_err());
    for partial in [
        TrustWpFramePolicy::Minimal,
        TrustWpFramePolicy::BorrowRegions,
    ] {
        let request = wp_request(partial, TrustWpVerificationMode::WeakestPrecondition);
        assert!(
            bound_established_by_replayed_result(&request, WeakestPreconditionFullHeap).is_err(),
            "a partial frame may assume a written location unchanged"
        );
    }
    for mode in [
        TrustWpVerificationMode::StrongestPostcondition,
        TrustWpVerificationMode::Abduction,
    ] {
        let request = wp_request(TrustWpFramePolicy::FullHeap, mode);
        assert!(
            bound_established_by_replayed_result(&request, WeakestPreconditionFullHeap).is_err()
        );
    }
    let import = trust_vc_import(Vec::new());
    for strength in [
        ChcValidity,
        PdrInvariant,
        WeakestPreconditionFullHeap,
        BoundedUnwind { depth: 1 },
    ] {
        assert!(
            bound_established_by_replayed_result(&import, strength).is_err(),
            "a TrustVc import is basis K's business"
        );
    }
}

// ---------------------------------------------------------------------------
// P5: request options that change what a result MEANS
// ---------------------------------------------------------------------------

/// A TrustMc request of `mode` (unwind limit 4) with its options edited.
fn mc_request_with(
    mode: TrustMcVerificationMode,
    edit: impl FnOnce(&mut TrustMcRequestOptions),
) -> NativeVerificationRequest {
    let mut request = trust_mc_request(mode, 4);
    let NativeVerificationRequest::TrustMc(inner) = &mut request else {
        unreachable!("trust_mc_request builds a TrustMc request");
    };
    edit(&mut inner.options);
    request
}

/// What a verified result of `strength` establishes on `request`, where mode
/// and strength agree.
fn replayed_bound(
    request: &NativeVerificationRequest,
    strength: NativeReplayedStrength,
) -> Option<CoverageBound> {
    bound_established_by_replayed_result(request, strength)
        .expect("the fixture pairs each mode with a strength it admits")
}

/// Assert that `request` derives `bound` iff `exact`, and names the divergent
/// `option` otherwise.
fn assert_machine_semantics(
    label: &str,
    request: &NativeVerificationRequest,
    strength: NativeReplayedStrength,
    bound: CoverageBound,
    exact: bool,
    option: &'static str,
    value: String,
) {
    if exact {
        assert_eq!(replayed_bound(request, strength), Some(bound), "{label}");
        assert_eq!(
            request_machine_semantics_divergence(request),
            None,
            "{label}"
        );
    } else {
        assert_eq!(replayed_bound(request, strength), None, "{label}");
        assert_eq!(
            request_machine_semantics_divergence(request),
            Some(MachineSemanticsDivergence { option, value }),
            "{label}"
        );
    }
}

/// The baseline every per-option test below mutates one field of: the
/// fixture requests' options mean exactly the machine semantics and derive a
/// bound in every mode.
#[test]
fn machine_semantics_baseline_derives_the_bound() {
    for (mode, strength, bound) in [
        (
            TrustMcVerificationMode::Chc,
            NativeReplayedStrength::ChcValidity,
            CoverageBound::Unbounded,
        ),
        (
            TrustMcVerificationMode::Pdr,
            NativeReplayedStrength::PdrInvariant,
            CoverageBound::Unbounded,
        ),
        (
            TrustMcVerificationMode::BoundedModelCheck,
            NativeReplayedStrength::BoundedUnwind { depth: 4 },
            CoverageBound::UnwindBounded { depth: 4 },
        ),
    ] {
        let request = mc_request_with(mode, |_| {});
        assert_eq!(request_machine_semantics_divergence(&request), None);
        assert_eq!(replayed_bound(&request, strength), Some(bound), "{mode:?}");
    }
    let wp = wp_request(
        TrustWpFramePolicy::FullHeap,
        TrustWpVerificationMode::WeakestPrecondition,
    );
    assert_eq!(request_machine_semantics_divergence(&wp), None);
    assert_eq!(
        replayed_bound(&wp, NativeReplayedStrength::WeakestPreconditionFullHeap),
        Some(CoverageBound::Unbounded)
    );
}

#[test]
fn trust_mc_memory_model_other_than_trust_ir_places_derives_no_bound() {
    for (model, exact) in [
        (TrustMcMemoryModel::TrustIrPlaces, true),
        (TrustMcMemoryModel::FlatArrays, false),
        (TrustMcMemoryModel::StackedBorrows, false),
    ] {
        for (mode, strength, bound) in [
            (
                TrustMcVerificationMode::Chc,
                NativeReplayedStrength::ChcValidity,
                CoverageBound::Unbounded,
            ),
            (
                TrustMcVerificationMode::BoundedModelCheck,
                NativeReplayedStrength::BoundedUnwind { depth: 4 },
                CoverageBound::UnwindBounded { depth: 4 },
            ),
        ] {
            let request = mc_request_with(mode, |o| o.memory_model = model);
            assert_machine_semantics(
                &format!("{mode:?} {model:?}"),
                &request,
                strength,
                bound,
                exact,
                "trust_mc.options.memory_model",
                format!("{model:?}"),
            );
        }
    }
}

/// `MathematicalIntegers` has no wrap-around, `RustChecked` imposes Rust's
/// overflow checks the IR makes explicit itself: a result under either is not
/// about the machine the obligation runs on.
#[test]
fn trust_mc_arithmetic_model_other_than_fixed_width_derives_no_bound() {
    for (model, exact) in [
        (TrustMcArithmeticModel::FixedWidthBitvectors, true),
        (TrustMcArithmeticModel::MathematicalIntegers, false),
        (TrustMcArithmeticModel::RustChecked, false),
    ] {
        for (mode, strength, bound) in [
            (
                TrustMcVerificationMode::Chc,
                NativeReplayedStrength::ChcValidity,
                CoverageBound::Unbounded,
            ),
            (
                TrustMcVerificationMode::Pdr,
                NativeReplayedStrength::PdrInvariant,
                CoverageBound::Unbounded,
            ),
            (
                TrustMcVerificationMode::BoundedModelCheck,
                NativeReplayedStrength::BoundedUnwind { depth: 4 },
                CoverageBound::UnwindBounded { depth: 4 },
            ),
        ] {
            let request = mc_request_with(mode, |o| o.arithmetic_model = model);
            assert_machine_semantics(
                &format!("{mode:?} {model:?}"),
                &request,
                strength,
                bound,
                exact,
                "trust_mc.options.arithmetic_model",
                format!("{model:?}"),
            );
        }
    }
    // Options decide the BOUND, never whether a disagreement is caught: a
    // bounded strength for a CHC request is still a mismatch under them.
    let integers = mc_request_with(TrustMcVerificationMode::Chc, |o| {
        o.arithmetic_model = TrustMcArithmeticModel::MathematicalIntegers
    });
    assert!(
        bound_established_by_replayed_result(
            &integers,
            NativeReplayedStrength::BoundedUnwind { depth: 4 }
        )
        .is_err()
    );
}

/// An invariant from TrustWp, TrustVc or the user comes from outside the
/// module and its replay context: the result may rest on an assumption
/// nobody re-checks here.
#[test]
fn trust_mc_external_invariant_source_derives_no_bound() {
    for (source, exact) in [
        (TrustMcInvariantSource::None, true),
        (TrustMcInvariantSource::TrustIrProofObligations, true),
        (TrustMcInvariantSource::TrustWp, false),
        (TrustMcInvariantSource::TrustVc, false),
        (TrustMcInvariantSource::UserSupplied, false),
    ] {
        for (mode, strength, bound) in [
            (
                TrustMcVerificationMode::Chc,
                NativeReplayedStrength::ChcValidity,
                CoverageBound::Unbounded,
            ),
            (
                TrustMcVerificationMode::Pdr,
                NativeReplayedStrength::PdrInvariant,
                CoverageBound::Unbounded,
            ),
        ] {
            let request = mc_request_with(mode, |o| o.chc.invariant_source = source);
            assert_machine_semantics(
                &format!("{mode:?} {source:?}"),
                &request,
                strength,
                bound,
                exact,
                "trust_mc.options.chc.invariant_source",
                format!("{source:?}"),
            );
        }
    }
}

/// `false` cuts every path at the unwind limit; `true` also asserts the
/// limit is never exceeded. The depth-4 claim holds under both, and the
/// completeness `true` would license is NOT derived — `BoundedUnwind` does not
/// attest that the unwinding assertions were re-checked — so neither value
/// ever reaches `Unbounded`.
#[test]
fn trust_mc_bmc_unwinding_assertions_never_upgrade_the_depth_bound() {
    for unwinding_assertions in [false, true] {
        let request = mc_request_with(TrustMcVerificationMode::BoundedModelCheck, |o| {
            o.bmc.unwinding_assertions = unwinding_assertions
        });
        assert_eq!(
            request_machine_semantics_divergence(&request),
            None,
            "{unwinding_assertions}"
        );
        assert_eq!(
            replayed_bound(&request, NativeReplayedStrength::BoundedUnwind { depth: 4 }),
            Some(CoverageBound::UnwindBounded { depth: 4 }),
            "unwinding_assertions={unwinding_assertions}"
        );
        for complete in [
            NativeReplayedStrength::ChcValidity,
            NativeReplayedStrength::PdrInvariant,
        ] {
            assert!(
                bound_established_by_replayed_result(&request, complete).is_err(),
                "unwinding_assertions={unwinding_assertions}: a BMC request is never complete"
            );
        }
    }
}

/// Solver strategy does not change what a REPLAYED result means: the engine,
/// the PDR settings, Horn-clause emission and slicing all keep the bound.
#[test]
fn trust_mc_solver_strategy_options_keep_the_bound() {
    type Edit = Box<dyn Fn(&mut TrustMcRequestOptions)>;
    let edits: Vec<(String, Edit)> = [
        TrustMcChcEngine::Z3Fixedpoint,
        TrustMcChcEngine::Spacer,
        TrustMcChcEngine::NativePdr,
    ]
    .into_iter()
    .map(|engine| {
        (
            format!("engine {engine:?}"),
            Box::new(move |o: &mut TrustMcRequestOptions| o.chc.engine = engine) as Edit,
        )
    })
    .chain(
        [
            TrustMcPdrGeneralization::None,
            TrustMcPdrGeneralization::Cubes,
            TrustMcPdrGeneralization::Interpolants,
        ]
        .into_iter()
        .map(|generalization| {
            (
                format!("generalization {generalization:?}"),
                Box::new(move |o: &mut TrustMcRequestOptions| {
                    o.chc.pdr.generalization = generalization
                }) as Edit,
            )
        }),
    )
    .chain(
        [
            TrustMcSlicingMode::None,
            TrustMcSlicingMode::ObligationBackwardSlice,
            TrustMcSlicingMode::ConstraintIndependence,
        ]
        .into_iter()
        .map(|slicing| {
            (
                format!("slicing {slicing:?}"),
                Box::new(move |o: &mut TrustMcRequestOptions| o.slicing = slicing) as Edit,
            )
        }),
    )
    .chain([
        (
            "pdr enabled, 3 frames".to_string(),
            Box::new(|o: &mut TrustMcRequestOptions| {
                o.chc.pdr = TrustMcPdrOptions {
                    enabled: true,
                    max_frames: Some(3),
                    generalization: TrustMcPdrGeneralization::Cubes,
                }
            }) as Edit,
        ),
        (
            "emit_horn_clauses flipped".to_string(),
            Box::new(|o: &mut TrustMcRequestOptions| {
                o.chc.emit_horn_clauses = !o.chc.emit_horn_clauses
            }) as Edit,
        ),
    ])
    .collect();
    for (label, edit) in edits {
        let request = mc_request_with(TrustMcVerificationMode::Chc, |o| edit(o));
        assert_eq!(
            request_machine_semantics_divergence(&request),
            None,
            "{label}"
        );
        assert_eq!(
            replayed_bound(&request, NativeReplayedStrength::ChcValidity),
            Some(CoverageBound::Unbounded),
            "{label}"
        );
    }
}

/// `RustBorrowGraph` assumes the borrow discipline; `SeparationLogic` is a
/// logic nobody has shown equal to the IR's memory.
#[test]
fn trust_wp_heap_model_other_than_trust_ir_memory_derives_no_bound() {
    for (model, exact) in [
        (TrustWpHeapModel::TrustIrMemory, true),
        (TrustWpHeapModel::RustBorrowGraph, false),
        (TrustWpHeapModel::SeparationLogic, false),
    ] {
        let request = wp_request_with(
            TrustWpFramePolicy::FullHeap,
            TrustWpVerificationMode::WeakestPrecondition,
            |o| o.heap_model = model,
        );
        assert_machine_semantics(
            &format!("{model:?}"),
            &request,
            NativeReplayedStrength::WeakestPreconditionFullHeap,
            CoverageBound::Unbounded,
            exact,
            "trust_wp.options.heap_model",
            format!("{model:?}"),
        );
    }
}

/// `Unwind` lets a panic leave without the obligation; `EncodePanicsAsErrors`
/// proves the obligation of an error-encoded program.
#[test]
fn trust_wp_panic_semantics_other_than_panic_free_derives_no_bound() {
    for (semantics, exact) in [
        (TrustWpPanicSemantics::PanicFreeRequired, true),
        (TrustWpPanicSemantics::EncodePanicsAsErrors, false),
        (TrustWpPanicSemantics::Unwind, false),
    ] {
        let request = wp_request_with(
            TrustWpFramePolicy::FullHeap,
            TrustWpVerificationMode::WeakestPrecondition,
            |o| o.panic_semantics = semantics,
        );
        assert_machine_semantics(
            &format!("{semantics:?}"),
            &request,
            NativeReplayedStrength::WeakestPreconditionFullHeap,
            CoverageBound::Unbounded,
            exact,
            "trust_wp.options.panic_semantics",
            format!("{semantics:?}"),
        );
    }
}

/// An abduced precondition is an assumption the result may rest on, and
/// nothing here re-checks it at the callers.
#[test]
fn trust_wp_abduced_preconditions_derive_no_bound() {
    for (limit, exact) in [(0, true), (1, false), (8, false)] {
        let request = wp_request_with(
            TrustWpFramePolicy::FullHeap,
            TrustWpVerificationMode::WeakestPrecondition,
            |o| o.max_abduced_preconditions = limit,
        );
        assert_machine_semantics(
            &format!("max_abduced_preconditions={limit}"),
            &request,
            NativeReplayedStrength::WeakestPreconditionFullHeap,
            CoverageBound::Unbounded,
            exact,
            "trust_wp.options.max_abduced_preconditions",
            format!("{limit:?}"),
        );
    }
}

/// Every loop strategy is sound (required and inferred invariants are
/// checked, `Havoc` over-approximates) and VC emission is output: all keep
/// the bound.
#[test]
fn trust_wp_loop_strategy_and_vc_emission_keep_the_bound() {
    for loop_strategy in [
        TrustWpLoopStrategy::RequireInvariants,
        TrustWpLoopStrategy::InferInvariants,
        TrustWpLoopStrategy::Havoc,
    ] {
        for emit in [false, true] {
            let request = wp_request_with(
                TrustWpFramePolicy::FullHeap,
                TrustWpVerificationMode::WeakestPrecondition,
                |o| {
                    o.loop_strategy = loop_strategy;
                    o.emit_verification_conditions = emit;
                },
            );
            assert_eq!(request_machine_semantics_divergence(&request), None);
            assert_eq!(
                replayed_bound(
                    &request,
                    NativeReplayedStrength::WeakestPreconditionFullHeap
                ),
                Some(CoverageBound::Unbounded),
                "{loop_strategy:?} emit={emit}"
            );
        }
    }
}

/// End to end: a VALID result for a CHC request under mathematical integers
/// is replayed, every citation recomputes — and the obligation stays
/// UNDETERMINED, naming the option. A WRONG result under the same options is
/// still refused: options decide the bound, never whether a forgery is caught.
#[test]
fn non_machine_request_options_leave_a_valid_result_undetermined() {
    let integers = || {
        mc_request_with(TrustMcVerificationMode::Chc, |o| {
            o.arithmetic_model = TrustMcArithmeticModel::MathematicalIntegers
        })
    };
    let fixture = SolvedFixture::new(integers(), Vec::new(), MODEL_VALID, |_| {});
    let report = fixture.report_with(vec![fixture.row.clone()], Some(&chc_valid()));
    assert!(report.refusals().is_empty(), "{:?}", report.refusals());
    assert_eq!(
        report.for_obligation(fixture.obligation()),
        obligation_undetermined(CoverageUndeterminedReason::RequestNotMachineSemantics {
            divergence: MachineSemanticsDivergence {
                option: "trust_mc.options.arithmetic_model",
                value: "MathematicalIntegers".to_string(),
            },
        })
    );

    let broken = SolvedFixture::new(integers(), Vec::new(), MODEL_BROKEN, |_| {});
    let report = broken.report_with(vec![broken.row.clone()], Some(&chc_valid()));
    broken.assert_refused(
        &report,
        ValidationError::CoverageResultReplayInvalid {
            obligation: PANIC,
            detail: "the invariant model does not satisfy the Horn clauses".to_string(),
        },
    );
}

/// The admitted module is not the code that was solved.
#[test]
fn code_drift_m1_m2_is_refused() {
    let fixture = SolvedFixture::new(chc_request(), Vec::new(), MODEL_VALID, |m2| {
        m2.functions[0].name = "kernel_checked_v2".to_string();
    });
    assert_eq!(fixture.admitted.validate(), Ok(()));
    let admitted = fixture.admitted.module.executable_content_digest_v1();
    assert_ne!(admitted, fixture.row.solved_executable_content_digest);
    let report = fixture.report_with(vec![fixture.row.clone()], Some(&chc_valid()));
    fixture.assert_refused(
        &report,
        ValidationError::CoverageSubjectCodeDrift {
            obligation: PANIC,
            solved: fixture.row.solved_executable_content_digest,
            admitted,
        },
    );
}

/// The admitted module states a different claim for the obligation: same
/// code, so only the claim digest can tell.
#[test]
fn claim_drift_is_refused() {
    let fixture = SolvedFixture::new(chc_request(), Vec::new(), MODEL_VALID, |m2| {
        m2.proof_obligations[PANIC as usize].formula =
            Some(ProofFormula::smtlib2("(= 1 1)", "Bool"));
    });
    assert_eq!(fixture.admitted.validate(), Ok(()));
    assert_eq!(
        fixture.admitted.module.executable_content_digest_v1(),
        fixture.row.solved_executable_content_digest,
        "the code is unchanged"
    );
    let report = fixture.report_with(vec![fixture.row.clone()], Some(&chc_valid()));
    assert!(matches!(
        report.refusals(),
        [ValidationError::CoverageClaimDrift {
            obligation: PANIC,
            ..
        }]
    ));
    assert!(matches!(
        report.for_obligation(fixture.obligation()),
        ObligationCoverage::Refused(ValidationError::CoverageClaimDrift { .. })
    ));
}

// ---------------------------------------------------------------------------
// P1: the transfer binds the WHOLE replay context
// ---------------------------------------------------------------------------

/// A replayer that honours the soundness contract — it establishes from the
/// replay context only — and whose re-translation (freshly, from `solved`)
/// ASSUMES the solved module's `Precondition` obligations of the requested
/// function: trust-ir's own reading of that kind (assumed, not proved), and a
/// claim the replay context binds. It NAMES them as the result's premises
/// (clause 6). The toy panic site is unreachable only under `(< 1 100)`.
/// Test-only, like `TestOnlyDigestCheckingReplayer`.
struct TestOnlyPreconditionAssumingReplayer;

impl NativeCoverageResultReplay for TestOnlyPreconditionAssumingReplayer {
    fn replay(
        &self,
        solved: &NativeVerificationBundle,
        request: &NativeVerificationRequest,
        _evidence: &NativeEvidenceBundle,
        _attachments: &[NativeEvidenceArtifactAttachment],
    ) -> Result<NativeReplayedResult, NativeCoverageReplayRefusal> {
        let assumed: Vec<ProofId> = solved
            .module
            .proof_obligations
            .iter()
            .filter(|o| {
                o.kind == ObligationKind::Precondition
                    && o.function == Some(FuncId::new(0))
                    && o.formula.as_ref().map(|f| f.payload.as_str()) == Some("(< 1 100)")
            })
            .map(|o| o.id)
            .collect();
        if !assumed.is_empty() {
            // Contract clause 6: it NAMES the claims it assumed.
            Ok(NativeReplayedResult::new(
                request.obligations().to_vec(),
                NativeReplayedStrength::ChcValidity,
            )
            .assuming(assumed))
        } else {
            Err(NativeCoverageReplayRefusal::Invalid {
                detail: "without the precondition the panic site is reachable".to_string(),
            })
        }
    }
}

/// Precondition #`index` of function 0, stating `formula`.
fn precondition(index: u32, formula: &str) -> ProofObligation {
    obligation(
        index,
        ObligationKind::Precondition,
        ProofStatus::Pending,
        formula,
        0,
    )
}

/// P1 A/B (the verifier's ADV-1). The result was solved in M1's whole
/// obligation context; M2 drops an assumed `Precondition` of the solved
/// function. Executable content excludes the obligation table and
/// `obligation_digest(#1)` covers only #1 and its function, so on 355a9e9d
/// the report ESTABLISHED #1 on M2 — while the very same replayer, run on M2,
/// finds the result invalid. Now: the admitted bundle does not recompute the
/// row's replay context, and the refusal names the dropped obligation.
#[test]
fn context_drift_dropped_assumption_is_refused() {
    let assumed = |m1: &mut Module| m1.proof_obligations.push(precondition(2, "(< 1 100)"));
    let fixture =
        SolvedFixture::editing_both(chc_request(), Vec::new(), MODEL_VALID, assumed, |_| {});
    assert_eq!(fixture.solved.validate(), Ok(()));
    assert_eq!(fixture.admitted.validate(), Ok(()));
    assert_eq!(
        fixture.solved.module.executable_content_digest_v1(),
        fixture.admitted.module.executable_content_digest_v1(),
        "the obligation table is outside executable content"
    );
    assert_eq!(
        claim_digest(&fixture.solved.module, PANIC),
        claim_digest(&fixture.admitted.module, PANIC),
        "#1's own claim did not move"
    );
    let replay = TestOnlyPreconditionAssumingReplayer;
    assert!(matches!(
        replay.replay(
            &fixture.admitted,
            &fixture.request,
            &fixture.solved.evidence_bundles[0],
            &fixture.attachments,
        ),
        Err(NativeCoverageReplayRefusal::Invalid { .. })
    ));
    let report = fixture.report_with(vec![fixture.row.clone()], Some(&replay));
    assert!(
        matches!(
            report.refusals(),
            [ValidationError::CoverageClaimDrift { obligation: PANIC, detail }]
                if detail.starts_with("the replay context drifted")
                    && detail.contains("obligation #2")
                    && detail.contains("the admitted module has no such obligation")
        ),
        "{:?}",
        report.refusals()
    );
    assert!(matches!(
        report.for_obligation(fixture.obligation()),
        ObligationCoverage::Refused(ValidationError::CoverageClaimDrift { .. })
    ));

    // Control: the same context carried over by an honest write-back (status
    // and certificates only) is NOT refused, and the same replayer re-verifies
    // the result. It rests on #2, which it names, and a `Discharged` status
    // establishes nothing, so the result waits on its premise (P-E; the
    // `*premise*` tests establish it once #2 is itself established).
    let honest =
        SolvedFixture::editing_both(chc_request(), Vec::new(), MODEL_VALID, assumed, |m2| {
            let mut discharged = precondition(2, "(< 1 100)");
            discharged.status = ProofStatus::Discharged;
            m2.proof_obligations.push(discharged);
            m2.proof_obligations[PANIC as usize].status = ProofStatus::Discharged;
        });
    let report = honest.report_with(vec![honest.row.clone()], Some(&replay));
    assert!(report.refusals().is_empty(), "{:?}", report.refusals());
    assert_eq!(
        report.for_obligation(honest.obligation()),
        obligation_undetermined(CoverageUndeterminedReason::PremiseNotEstablished {
            premise: ProofId::new(2)
        })
    );
}

/// Every part of the replay context is bound, in both directions: an
/// obligation that APPEARS in M2, another obligation's claim WEAKENED under
/// the same id, and a compiler fact that changed. Each keeps executable
/// content and #1's claim; each is refused by name.
#[test]
fn context_drift_is_refused_in_every_part_of_the_context() {
    let assumed = |m: &mut Module| m.proof_obligations.push(precondition(2, "(< 1 100)"));
    let appeared = SolvedFixture::new(chc_request(), Vec::new(), MODEL_VALID, assumed);
    let weakened =
        SolvedFixture::editing_both(chc_request(), Vec::new(), MODEL_VALID, assumed, |m2| {
            m2.proof_obligations.push(precondition(2, "(< 1 1000)"))
        });
    for (label, fixture, solved_side) in [
        (
            "appeared",
            appeared,
            "a context that has no such obligation",
        ),
        ("weakened", weakened, "a context that states claim"),
    ] {
        assert_eq!(fixture.admitted.validate(), Ok(()), "{label}");
        assert_eq!(
            fixture.admitted.module.executable_content_digest_v1(),
            fixture.row.solved_executable_content_digest,
            "{label}"
        );
        assert_eq!(
            claim_digest(&fixture.admitted.module, PANIC),
            fixture.row.obligation_digest,
            "{label}"
        );
        let report = fixture.report_with(vec![fixture.row.clone()], Some(&chc_valid()));
        assert!(
            matches!(
                report.refusals(),
                [ValidationError::CoverageClaimDrift { obligation: PANIC, detail }]
                    if detail.starts_with("the replay context drifted")
                        && detail.contains("obligation #2")
                        && detail.contains(solved_side)
                        && detail.contains("the admitted module states claim")
            ),
            "{label}: {:?}",
            report.refusals()
        );
    }

    let mut facts = SolvedFixture::chc();
    let source = facts
        .admitted
        .compiler_facts
        .obligation_sources
        .iter_mut()
        .find(|source| source.obligation == ProofId::new(PANIC))
        .expect("the fixture maps #1's source");
    source.cause = NativeObligationCause::Other;
    assert_eq!(facts.admitted.validate(), Ok(()));
    let report = facts.report_with(vec![facts.row.clone()], Some(&chc_valid()));
    assert!(
        matches!(
            report.refusals(),
            [ValidationError::CoverageClaimDrift { obligation: PANIC, detail }]
                if detail.starts_with("the replay context drifted")
                    && detail.contains("compiler facts")
        ),
        "{:?}",
        report.refusals()
    );
}

/// The context excludes exactly what an honest write-back rewrites — the
/// WHOLE allowlist: statuses, the certificate table, the diagnostics sidecar,
/// and the carriers bound to the module digest (the lineage manifest, the
/// requests, the evidence bundles) — so a write-back touching every one of
/// them keeps the digest and still establishes: the rule costs an honest
/// producer nothing.
#[test]
fn honest_write_back_keeps_the_replay_context() {
    let mut fixture = SolvedFixture::new(chc_request(), Vec::new(), MODEL_VALID, |m2| {
        m2.proof_obligations[PANIC as usize].status = ProofStatus::Discharged;
        m2.proof_obligations[CONTRACT as usize].status = ProofStatus::Pending;
        m2.obligation_diagnostics
            .push(trust_ir::proof::ObligationDiagnostic::note(
                ProofId::new(PANIC),
                "discharged by trust-mc (chc valid)",
            ));
    });
    // The admitted bundle is re-emitted for M2: its lineage names M2's digest,
    // it routes one more request, and it carries result evidence bound to M2.
    let extra = trust_mc_request_with(
        2,
        TrustMcVerificationMode::Chc,
        1,
        &[CONTRACT],
        ProofDigest::sha256_domain("coverage_establishment.replay", b"mc-extra"),
    );
    let mut admitted = bundle_for(fixture.admitted.module.clone(), vec![chc_request(), extra]);
    let evidence = admitted
        .evidence_bundle_for_request(&chc_request(), fixture.row.result_artifacts.clone())
        .expect("the request carries a replay identity");
    admitted.evidence_bundles.push(evidence);
    fixture.admitted = admitted;
    assert_eq!(fixture.admitted.validate(), Ok(()));
    assert_ne!(
        fixture.admitted.module.stable_digest(),
        fixture.solved.module.stable_digest(),
        "the write-back moved the module"
    );
    assert_ne!(fixture.admitted.lineage, fixture.solved.lineage);
    assert_ne!(fixture.admitted.requests, fixture.solved.requests);
    assert_ne!(
        fixture.admitted.evidence_bundles,
        fixture.solved.evidence_bundles
    );
    assert_eq!(
        context_digest(&fixture.admitted),
        fixture.row.solved_replay_context_digest,
        "...but not its replay context"
    );
    let report = fixture.report_with(vec![fixture.row.clone()], Some(&chc_valid()));
    fixture.assert_established(&report, CoverageBound::Unbounded);
}

// ---------------------------------------------------------------------------
// P4: a solver result is the obligation's, never a certificate's
// ---------------------------------------------------------------------------

/// P4 A/B (the verifier's ADV-7). On 355a9e9d a row NAMED a certificate and
/// the verified result then established THAT certificate — any certificate of
/// the obligation: a `Trusted` one "reviewed by nobody", or a z3 sibling (the
/// old `row_for_another_certificate_is_refused` case (c) asserted exactly
/// that). Now the row names none, the verdict is the obligation's, and every
/// certificate of the obligation stays what basis K makes it — here nothing.
#[test]
fn solver_result_vouches_for_no_certificate() {
    let trusted = ProofCertificate {
        obligation: ProofId::new(PANIC),
        prover: "auditor".to_string(),
        evidence: ProofEvidence::Trusted("reviewed by nobody".to_string()),
        assurance: None,
    };
    let z3 = ProofCertificate {
        obligation: ProofId::new(PANIC),
        prover: "z3".to_string(),
        evidence: ProofEvidence::SmtProof(b"(proof)".to_vec()),
        assurance: None,
    };
    let (carried_trusted, carried_z3) = (trusted.clone(), z3.clone());
    let fixture = SolvedFixture::new(chc_request(), Vec::new(), MODEL_VALID, move |m2| {
        m2.proof_certificates.push(carried_trusted);
        m2.proof_certificates.push(carried_z3);
    });
    assert_eq!(fixture.admitted.validate(), Ok(()));
    let report = fixture.report_with(vec![fixture.row.clone()], Some(&chc_valid()));
    fixture.assert_established(&report, CoverageBound::Unbounded);
    for certificate in [
        fixture.certificate(),
        trusted.lineage_ref(),
        z3.lineage_ref(),
    ] {
        assert_eq!(
            report.for_certificate(&certificate),
            no_basis(),
            "{}",
            certificate.prover
        );
    }
    assert_eq!(report.certificates().count(), 3);
    assert!(
        report
            .certificates()
            .all(|(_, verdict)| !matches!(verdict, CertificateCoverage::Established { .. })),
        "no certificate verdict is established by the obligation's result"
    );
}

// ---------------------------------------------------------------------------
// P2 / P3: the refusals that had no committed negative control
// ---------------------------------------------------------------------------

/// P2. Negative control for the SOLVED half of "Failed status for o": M1 says
/// #1 FAILED, M2 says Pending. Status is outside executable content, the
/// claim digest and the replay context, so only this branch refuses (with it
/// disabled every other test stays green and this one is Established).
#[test]
fn solved_module_failed_status_contradicts() {
    let fixture = SolvedFixture::editing_both(
        chc_request(),
        Vec::new(),
        MODEL_VALID,
        |m1| m1.proof_obligations[PANIC as usize].status = ProofStatus::Failed,
        |_| {},
    );
    assert_eq!(fixture.solved.validate(), Ok(()));
    assert_eq!(
        context_digest(&fixture.admitted),
        fixture.row.solved_replay_context_digest,
        "status is not context: only the status branch can see this"
    );
    let report = fixture.report_with(vec![fixture.row.clone()], Some(&chc_valid()));
    fixture.assert_refused(
        &report,
        ValidationError::CoverageContradicted {
            obligation: PANIC,
            detail: "the obligation is Failed in the solved module".to_string(),
        },
    );
}

/// P3. Negative control for the wire-identity refusals: a module no binary
/// version encodes (a completeness claim; its digests PANIC) is refused by
/// name, as the admitted bundle and as a supplied solved bundle — never a
/// panic, never Established.
#[test]
fn module_without_wire_identity_is_refused() {
    let mut fixture = SolvedFixture::chc();
    fixture.admitted.module.completeness = Some(trust_ir::ModuleCompleteness::Complete);
    let blocker = trust_ir_build::wire_identity_blocker(&fixture.admitted.module)
        .expect("a completeness claim has no wire identity");
    assert!(matches!(
        blocker,
        ValidationError::ModuleHasNoWireIdentity { .. }
    ));
    let report = fixture.report_with(vec![fixture.row.clone()], Some(&chc_valid()));
    assert!(!report.is_checked());
    assert_eq!(report.refusals(), std::slice::from_ref(&blocker));
    assert_eq!(
        report.for_obligation(fixture.obligation()),
        obligation_undetermined(CoverageUndeterminedReason::ReportUnchecked)
    );
    assert_eq!(
        report.for_certificate(&fixture.certificate()),
        undetermined(CoverageUndeterminedReason::ReportUnchecked)
    );

    let mut fixture = SolvedFixture::chc();
    fixture.solved.module.completeness = Some(trust_ir::ModuleCompleteness::Complete);
    assert_eq!(
        fixture.solved.stable_digest(),
        fixture.row.solved_bundle_digest,
        "the bundle digest reads the recorded module digest, so the row still resolves"
    );
    let blocker = trust_ir_build::wire_identity_blocker(&fixture.solved.module)
        .expect("a completeness claim has no wire identity");
    let report = fixture.report_with(vec![fixture.row.clone()], Some(&chc_valid()));
    // Refused BY NAME for the missing wire identity, before anything digests
    // or validates the solved module — not by whatever `validate` says next.
    fixture.assert_refused(
        &report,
        ValidationError::CoverageSolvedBundleInvalid {
            obligation: PANIC,
            detail: blocker.to_string(),
        },
    );
}

#[test]
fn duplicate_rows_are_refused() {
    let fixture = SolvedFixture::chc();
    let report = fixture.report_with(
        vec![fixture.row.clone(), fixture.row.clone()],
        Some(&chc_valid()),
    );
    assert_eq!(
        report.refusals(),
        &[ValidationError::CoverageAttestationRowDuplicate {
            obligation: PANIC,
            solved_bundle: fixture.row.solved_bundle_digest,
            request: fixture.row.request_digest,
        }]
    );
    assert_eq!(
        report.for_obligation(fixture.obligation()),
        obligation_undetermined(CoverageUndeterminedReason::NoBasis),
        "a malformed attestation is not read at all"
    );
}

#[test]
fn replayed_refutation_contradicts() {
    let fixture = SolvedFixture::chc();
    let report = fixture.report_with(vec![fixture.row.clone()], Some(&replayer(Answer::Refute)));
    fixture.assert_refused(
        &report,
        ValidationError::CoverageContradicted {
            obligation: PANIC,
            detail: "the replay re-established a refutation of obligation(s) [1]: \
                     counterexample re-checked"
                .to_string(),
        },
    );
    // The admitted module itself says the obligation FAILED.
    let fixture = SolvedFixture::new(chc_request(), Vec::new(), MODEL_VALID, |m2| {
        m2.proof_obligations[PANIC as usize].status = ProofStatus::Failed;
    });
    let report = fixture.report_with(vec![fixture.row.clone()], Some(&chc_valid()));
    fixture.assert_refused(
        &report,
        ValidationError::CoverageContradicted {
            obligation: PANIC,
            detail: "the obligation is Failed in the admitted module".to_string(),
        },
    );
}

/// Schema 1 (rows naming a certificate, no replay context) is refused as
/// stale, as is any other number; a legacy stable checksum is no citation.
#[test]
fn attestation_schema_mismatch_is_refused() {
    let fixture = SolvedFixture::chc();
    for stale in [1, 3] {
        let mut attestation = NativeCoverageAttestation::new(vec![fixture.row.clone()]);
        attestation.schema_version = stale;
        let report = fixture.report_on(&fixture.admitted, attestation, Some(&chc_valid()));
        assert!(
            matches!(
                report.refusals(),
                [ValidationError::CoverageAttestationSchemaUnsupported { detail }]
                    if detail.contains(&format!("version {stale}"))
            ),
            "{stale}: {:?}",
            report.refusals()
        );
        assert_eq!(
            report.for_obligation(fixture.obligation()),
            obligation_undetermined(CoverageUndeterminedReason::NoBasis)
        );
    }
    let mut row = fixture.row.clone();
    row.request_digest = ProofDigest::trust_ir_stable("legacy", b"request");
    let report = fixture.report_with(vec![row], Some(&chc_valid()));
    assert!(matches!(
        report.refusals(),
        [ValidationError::CoverageAttestationSchemaUnsupported { detail }] if detail.contains("request_digest")
    ));
}

/// One field edit of an otherwise-valid attestation row.
type RowEdit = fn(&mut NativeCoverageAttestationRow);

#[test]
fn solved_bundle_citations_must_resolve_and_recompute() {
    // Not supplied.
    let fixture = SolvedFixture::chc();
    let attestation = NativeCoverageAttestation::new(vec![fixture.row.clone()]);
    let replay = chc_valid();
    let report = coverage_establishment_report(
        &fixture.admitted,
        CoverageInputs {
            attestation: Some(&attestation),
            attachments: &fixture.attachments,
            replay: Some(&replay),
            ..CoverageInputs::default()
        },
    );
    fixture.assert_refused(
        &report,
        ValidationError::CoverageSolvedBundleMissing {
            obligation: PANIC,
            recorded: fixture.row.solved_bundle_digest,
            supplied: 0,
        },
    );

    // Supplied, but invalid (and cited by its own digest).
    let mut fixture = SolvedFixture::chc();
    fixture.solved.schema_version = 7;
    let mut row = fixture.row.clone();
    row.solved_bundle_digest = fixture.solved.stable_digest();
    let report = fixture.report_with(vec![row], Some(&chc_valid()));
    assert!(matches!(
        report.refusals(),
        [ValidationError::CoverageSolvedBundleInvalid {
            obligation: PANIC,
            ..
        }]
    ));

    // A recorded identity that does not recompute, field by field — the
    // replay context among them: a row cannot lie about the context it was
    // solved in any more than about its module.
    let fixture = SolvedFixture::chc();
    let edits: [(&str, RowEdit); 4] = [
        ("solved_module_digest", |row| {
            row.solved_module_digest = digest(0x61)
        }),
        ("solved_executable_content_digest", |row| {
            row.solved_executable_content_digest = digest(0x62)
        }),
        ("obligation_digest", |row| {
            row.obligation_digest = digest(0x63)
        }),
        ("solved_replay_context_digest", |row| {
            row.solved_replay_context_digest = digest(0x64)
        }),
    ];
    for (field, edit) in edits {
        let mut row = fixture.row.clone();
        edit(&mut row);
        let report = fixture.report_with(vec![row], Some(&chc_valid()));
        assert!(
            matches!(
                report.refusals(),
                [ValidationError::CoverageSolvedBundleDigestMismatch { field: f, .. }] if *f == field
            ),
            "{field}: {:?}",
            report.refusals()
        );
    }
}

/// FEATURELESS (R10 A/B). Every build recomputes EVERY digest a row cites.
/// On 794227ad the claim and context digests were compiled only under the
/// optional `coverage-attestation` feature, and a build without it — whose
/// doc said "forgeries refused" — could recompute neither: a row forging
/// either was `Undetermined{ClaimDigestUnavailable}` with `refusals()` EMPTY.
/// The feature is gone (its `trust-ir/fmt` is a plain dependency), so both
/// forgeries are refused in the default and the `--no-default-features`
/// build alike.
#[test]
fn every_build_refuses_a_forged_claim_or_context_digest() {
    let fixture = SolvedFixture::chc();
    let mut wrong = Vec::new();
    for (field, forge) in [
        (
            "obligation_digest",
            (|row: &mut NativeCoverageAttestationRow| row.obligation_digest = digest(0x66))
                as fn(&mut NativeCoverageAttestationRow),
        ),
        ("solved_replay_context_digest", |row| {
            row.solved_replay_context_digest = digest(0x66)
        }),
    ] {
        let mut row = fixture.row.clone();
        forge(&mut row);
        let report = fixture.report_with(vec![row], Some(&chc_valid()));
        let refused = matches!(
            report.refusals(),
            [ValidationError::CoverageSolvedBundleDigestMismatch { field: f, .. }] if *f == field
        ) && matches!(
            report.for_obligation(fixture.obligation()),
            ObligationCoverage::Refused(ValidationError::CoverageSolvedBundleDigestMismatch { .. })
        );
        if !refused {
            wrong.push(format!(
                "forged {field}: refusals {:?}, verdict {:?}",
                report.refusals(),
                report.for_obligation(fixture.obligation())
            ));
        }
    }
    assert!(wrong.is_empty(), "not refused:\n{}", wrong.join("\n"));
}

// ===========================================================================
// acyclicity
// ===========================================================================

fn every_digest(fixture: &SolvedFixture) -> Vec<ProofDigest> {
    let mut digests = Vec::new();
    for bundle in [&fixture.solved, &fixture.admitted] {
        digests.push(bundle.module.stable_digest());
        digests.push(bundle.module.executable_content_digest_v1());
        digests.push(bundle.stable_digest());
        digests.extend(
            bundle
                .requests
                .iter()
                .map(NativeVerificationRequest::stable_digest),
        );
        digests.extend(
            bundle
                .evidence_bundles
                .iter()
                .map(NativeEvidenceBundle::stable_digest),
        );
    }
    digests
}

/// The attestation is read by nothing earlier in the chain: mutating it moves
/// its own digest and nothing else.
#[test]
fn attestation_is_outside_every_digest() {
    let fixture = SolvedFixture::chc();
    let before = every_digest(&fixture);
    let sealed = NativeCoverageAttestation::new(vec![fixture.row.clone()]);
    let mut mutated = sealed.clone();
    mutated.rows[0].result_artifacts.pop();
    mutated.rows[0].evidence_bundle_digest = digest(0x5A);
    mutated.rows.push(fixture.row.clone());
    assert_ne!(sealed.stable_digest(), mutated.stable_digest());
    assert_ne!(
        sealed.rows[0].stable_digest(),
        mutated.rows[0].stable_digest()
    );
    for attestation in [sealed, mutated] {
        let _ = fixture.report_on(&fixture.admitted, attestation, Some(&chc_valid()));
        assert_eq!(
            every_digest(&fixture),
            before,
            "no digest reads the attestation"
        );
    }
    assert_eq!(
        fixture.request.stable_digest(),
        fixture.row.request_digest,
        "the row cites the request without being cited by it"
    );
}

/// A request whose replay transcript binds the module digest — exactly how
/// Trust's bridge builds one (transcript = H(suite, source, module digest,
/// obligations)).
fn module_bound_request(module: &Module) -> NativeVerificationRequest {
    let mut transcript = Vec::new();
    transcript.extend_from_slice(b"trust_mc");
    transcript.extend_from_slice(&module.stable_digest().bytes);
    transcript.extend_from_slice(&PANIC.to_le_bytes());
    trust_mc_request_with(
        1,
        TrustMcVerificationMode::Chc,
        1,
        &[PANIC],
        ProofDigest::sha256_domain("coverage_establishment.transcript", &transcript),
    )
}

/// WHY the row left the module. Seal the row to cite the module-bound request,
/// recompute the request the sealed module induces, repeat: the citation never
/// resolves, because row → module digest → transcript → request digest → row
/// has no fixed point.
#[test]
fn in_module_row_citing_module_bound_request_has_no_fixed_point() {
    let mut module = bare_module();
    module.proof_certificates.push(solver_certificate());
    let identity = module.proof_certificates[0].lineage_ref();
    for round in 0..3 {
        let cited = module_bound_request(&module).stable_digest();
        module.proof_certificates[0].assurance = Some(CoverageAssurance {
            bound: CoverageBound::Unbounded,
            request_digest: cited,
        });
        let induced = module_bound_request(&module);
        assert_ne!(
            induced.stable_digest(),
            cited,
            "round {round}: sealing the row did not move the request — a fixed point"
        );
        let bundle = bundle_for(module.clone(), vec![induced]);
        assert_eq!(bundle.validate(), Ok(()));
        let legacy = coverage_assurance_report(&bundle.module, Some(&bundle));
        assert_eq!(
            legacy.errors(),
            &[ValidationError::CoverageAssuranceRequestUnknown {
                obligation: PANIC,
                recorded: cited,
                bundle_requests: 1,
            }],
            "round {round}: the honest bundle cannot resolve its own row"
        );
    }
    assert_eq!(
        module.proof_certificates[0].lineage_ref(),
        identity,
        "a certificate's identity excludes the row, so an attestation can name it"
    );
}

// ===========================================================================
// Round 3: a replay may assume NOTHING the consumer does not bind and check
// ===========================================================================

// ---------------------------------------------------------------------------
// P-A: the REQUEST's replay atoms are neither premises nor goals
// ---------------------------------------------------------------------------

/// A replayer that honours the contract as r2 WROTE it — it translates
/// "freshly from `solved` and `request`" and establishes only from the replay
/// context and the digest-bound request — and whose translation assumes the
/// request's own `Assumption` replay atoms (the type's doc: "one typed formula
/// atom used by verifier replay or VC generation"). The toy panic site is
/// unreachable only under `(< 1 100)`. Test-only.
struct TestOnlyRequestAtomAssumingReplayer;

impl NativeCoverageResultReplay for TestOnlyRequestAtomAssumingReplayer {
    fn replay(
        &self,
        _solved: &NativeVerificationBundle,
        request: &NativeVerificationRequest,
        _evidence: &NativeEvidenceBundle,
        _attachments: &[NativeEvidenceArtifactAttachment],
    ) -> Result<NativeReplayedResult, NativeCoverageReplayRefusal> {
        let assumed = request
            .provenance()
            .replay_context()
            .atoms
            .iter()
            .any(|atom| {
                atom.kind == NativeReplayAtomKind::Assumption && atom.formula.payload == "(< 1 100)"
            });
        if assumed {
            Ok(NativeReplayedResult::new(
                request.obligations().to_vec(),
                NativeReplayedStrength::ChcValidity,
            ))
        } else {
            Err(NativeCoverageReplayRefusal::Invalid {
                detail: "without the assumption the panic site is reachable".to_string(),
            })
        }
    }
}

/// A replayer that takes its GOAL for #1 from the request's `Assertion` atom
/// bound to #1 and proves it when it is `true`. Test-only.
struct TestOnlyRequestAssertionGoalReplayer;

impl NativeCoverageResultReplay for TestOnlyRequestAssertionGoalReplayer {
    fn replay(
        &self,
        _solved: &NativeVerificationBundle,
        request: &NativeVerificationRequest,
        _evidence: &NativeEvidenceBundle,
        _attachments: &[NativeEvidenceArtifactAttachment],
    ) -> Result<NativeReplayedResult, NativeCoverageReplayRefusal> {
        let goal = request
            .provenance()
            .replay_context()
            .atoms
            .iter()
            .find(|atom| {
                atom.kind == NativeReplayAtomKind::Assertion
                    && atom.obligation == Some(ProofId::new(PANIC))
            });
        match goal {
            Some(atom) if atom.formula.payload == "true" => Ok(NativeReplayedResult::new(
                vec![ProofId::new(PANIC)],
                NativeReplayedStrength::ChcValidity,
            )),
            _ => Err(NativeCoverageReplayRefusal::Invalid {
                detail: "the goal does not hold".to_string(),
            }),
        }
    }
}

fn with_replay_atom(
    mut request: NativeVerificationRequest,
    atom: NativeReplayAtom,
) -> NativeVerificationRequest {
    match &mut request {
        NativeVerificationRequest::TrustMc(inner) => {
            inner.provenance.replay_context.atoms.push(atom)
        }
        NativeVerificationRequest::TrustWp(inner) => {
            inner.provenance.replay_context.atoms.push(atom)
        }
        NativeVerificationRequest::TrustVc(inner) => {
            inner.provenance.replay_context.atoms.push(atom)
        }
    }
    request
}

fn assumption(formula: &str) -> NativeReplayAtom {
    NativeReplayAtom::assumption(
        NativeReplayAtomId::new(0),
        ProofFormula::smtlib2(formula, "Bool"),
    )
}

/// An `Assertion` atom citing obligation `obligation`, stating `formula`.
fn assertion_for(atom: u32, obligation: u32, formula: &str) -> NativeReplayAtom {
    NativeReplayAtom::assertion(
        NativeReplayAtomId::new(atom),
        ProofFormula::smtlib2(formula, "Bool"),
    )
    .with_obligation(ProofId::new(obligation))
    .with_assertion_id(NativeAssertionId::new(obligation))
}

/// P-A A/B (the verifier's ADV-R2-1). The REQUEST carries an `Assumption` the
/// admitted module never states. The replay context binds the bundle, not
/// the request, and the request was a premise the r2 contract allowed, so on
/// 8958b24a the report ESTABLISHED #1 — while the same replayer on the same
/// request minus the atom finds the result invalid. Now: a request-carried
/// assumption (and an unsupported-mode entry) is a divergence from the
/// obligation's machine semantics, at the table and in the report.
#[test]
fn request_replay_assumption_atom_derives_no_bound() {
    let request = with_replay_atom(chc_request(), assumption("(< 1 100)"));
    assert_eq!(
        request_machine_semantics_divergence(&request),
        Some(MachineSemanticsDivergence {
            option: "trust_mc.provenance.replay_context.atoms",
            value: "Assumption #0 \"(< 1 100)\"".to_string(),
        })
    );
    assert_eq!(
        bound_established_by_replayed_result(&request, NativeReplayedStrength::ChcValidity),
        Ok(None)
    );
    let wp = with_replay_atom(
        wp_request(
            TrustWpFramePolicy::FullHeap,
            TrustWpVerificationMode::WeakestPrecondition,
        ),
        assumption("(< 1 100)"),
    );
    assert_eq!(
        bound_established_by_replayed_result(
            &wp,
            NativeReplayedStrength::WeakestPreconditionFullHeap
        ),
        Ok(None)
    );
    let mut unsupported = chc_request();
    if let NativeVerificationRequest::TrustMc(inner) = &mut unsupported {
        inner
            .provenance
            .replay_context
            .unsupported_modes
            .push(NativeUnsupportedMode::new(
                NativeUnsupportedModeReason::UnsupportedCompilerFact,
                "a fact the replay cannot model",
            ));
    }
    assert!(matches!(
        request_machine_semantics_divergence(&unsupported),
        Some(MachineSemanticsDivergence {
            option: "trust_mc.provenance.replay_context.unsupported_modes",
            ..
        })
    ));
    // An `Assertion` atom is not a divergence of the request alone.
    assert_eq!(
        request_machine_semantics_divergence(&with_replay_atom(
            chc_request(),
            assertion_for(1, PANIC, "true")
        )),
        None
    );

    let fixture = SolvedFixture::new(request.clone(), Vec::new(), MODEL_VALID, |_| {});
    assert_eq!(fixture.solved.validate(), Ok(()));
    assert_eq!(fixture.admitted.validate(), Ok(()));
    assert_eq!(
        context_digest(&fixture.admitted),
        fixture.row.solved_replay_context_digest
    );
    let replay = TestOnlyRequestAtomAssumingReplayer;
    assert!(matches!(
        replay.replay(
            &fixture.solved,
            &chc_request(),
            &fixture.solved.evidence_bundles[0],
            &fixture.attachments,
        ),
        Err(NativeCoverageReplayRefusal::Invalid { .. })
    ));
    let report = fixture.report_with(vec![fixture.row.clone()], Some(&replay));
    assert!(report.refusals().is_empty(), "{:?}", report.refusals());
    assert_eq!(
        report.for_obligation(fixture.obligation()),
        obligation_undetermined(CoverageUndeterminedReason::RequestNotMachineSemantics {
            divergence: MachineSemanticsDivergence {
                option: "trust_mc.provenance.replay_context.atoms",
                value: "Assumption #0 \"(< 1 100)\"".to_string(),
            }
        })
    );
}

/// P-A A/B (the verifier's ADV-R2-2). The request's `Assertion` atom for #1
/// validates (obligation, assertion id) but states `true` where #1 claims
/// `(= 1 2)`; `validate` never compares an atom's formula with its
/// obligation's, so on 8958b24a a replay that took its goal from the request
/// ESTABLISHED #1. Now the bundle is REFUSED — for #1's own atom and for a
/// SIBLING's (a sibling assertion can be assumed after it is "checked") —
/// and an atom stating exactly its obligation's claim still establishes.
#[test]
fn request_replay_assertion_atom_must_state_the_claim() {
    let falsify = |m: &mut Module| {
        m.proof_obligations[PANIC as usize].formula =
            Some(ProofFormula::smtlib2("(= 1 2)", "Bool"));
    };
    let request = with_replay_atom(chc_request(), assertion_for(1, PANIC, "true"));
    let fixture = SolvedFixture::editing_both(request, Vec::new(), MODEL_VALID, falsify, falsify);
    assert_eq!(fixture.solved.validate(), Ok(()));
    assert_eq!(fixture.admitted.validate(), Ok(()));
    let report = fixture.report_with(
        vec![fixture.row.clone()],
        Some(&TestOnlyRequestAssertionGoalReplayer),
    );
    assert!(
        matches!(
            report.refusals(),
            [ValidationError::CoverageClaimDrift { obligation: PANIC, detail }]
                if detail.starts_with("the request's Assertion atom #1 states \"true\" for \
                                       obligation #1, whose claim is \"(= 1 2)\"")
        ),
        "{:?}",
        report.refusals()
    );
    assert!(matches!(
        report.for_obligation(fixture.obligation()),
        ObligationCoverage::Refused(ValidationError::CoverageClaimDrift { .. })
    ));

    // A SIBLING's assertion atom: the request lists #0 and #1, #0's atom says
    // `true`, #0 claims `(>= 5 0)`.
    let both = trust_mc_request_with(
        1,
        TrustMcVerificationMode::Chc,
        1,
        &[CONTRACT, PANIC],
        ProofDigest::sha256_domain("coverage_establishment.replay", b"mc"),
    );
    let sibling = with_replay_atom(both, assertion_for(0, CONTRACT, "true"));
    let fixture = SolvedFixture::new(sibling, Vec::new(), MODEL_VALID, |_| {});
    assert_eq!(fixture.solved.validate(), Ok(()));
    let report = fixture.report_with(vec![fixture.row.clone()], Some(&chc_valid()));
    assert!(
        matches!(
            report.refusals(),
            [ValidationError::CoverageClaimDrift { obligation: PANIC, detail }]
                if detail.contains("for obligation #0, whose claim is \"(>= 5 0)\"")
        ),
        "{:?}",
        report.refusals()
    );

    // Control: an atom stating exactly its obligation's claim keeps the bound.
    let faithful = with_replay_atom(chc_request(), assertion_for(1, PANIC, "true"));
    let fixture = SolvedFixture::new(faithful, Vec::new(), MODEL_VALID, |_| {});
    let report = fixture.report_with(vec![fixture.row.clone()], Some(&chc_valid()));
    fixture.assert_established(&report, CoverageBound::Unbounded);
}

// ---------------------------------------------------------------------------
// P-D: the replay context is the whole bundle but an explicit allowlist
// ---------------------------------------------------------------------------

/// P-D A/B, the REVERSED DEFAULT. Fields nobody listed in the v1 context —
/// the license of a function no obligation is scoped to (outside executable
/// content and outside every claim digest), the bundle's provenance, its
/// diagnostics policy — were unbound by omission, so on 8958b24a an admitted
/// bundle that changed any of them after the solve still ESTABLISHED. The v2
/// context is the whole bundle but the write-back allowlist, so each moves it
/// and is refused by name; `honest_write_back_keeps_the_replay_context` is
/// the other half (every allowlisted field changed, still established).
#[test]
fn replay_context_binds_everything_but_the_write_back_allowlist() {
    fn with_helper(gate: Option<trust_ir::BodyGate>) -> impl FnOnce(&mut Module) {
        move |m: &mut Module| {
            let mut helper =
                Function::new(FuncId::new(1), "helper", m.functions[0].ty, BlockId::new(0))
                    .with_producer(Producer::TRust);
            helper.blocks.push(Block {
                id: BlockId::new(0),
                params: Vec::new(),
                body: vec![InstrNode::new(Inst::Return { values: Vec::new() })],
            });
            helper.body_gate = gate;
            m.try_add_function(helper)
                .expect("Module::try_add_function: test fixture");
        }
    }
    let license = SolvedFixture::editing_both(
        chc_request(),
        Vec::new(),
        MODEL_VALID,
        with_helper(None),
        with_helper(Some(trust_ir::BodyGate::Gated {
            authority: "someone".to_string(),
            evidence: None,
        })),
    );
    let mut provenance = SolvedFixture::chc();
    provenance.admitted.provenance.producer_version = "trust-other".to_string();
    let mut policy = SolvedFixture::chc();
    policy.admitted.diagnostics.emit_counterexamples =
        !policy.admitted.diagnostics.emit_counterexamples;
    for (label, fixture) in [
        ("license of an unscoped function", license),
        ("provenance", provenance),
        ("diagnostics policy", policy),
    ] {
        assert_eq!(fixture.admitted.validate(), Ok(()), "{label}");
        assert_eq!(
            fixture.admitted.module.executable_content_digest_v1(),
            fixture.row.solved_executable_content_digest,
            "{label}: outside executable content"
        );
        assert_eq!(
            claim_digest(&fixture.admitted.module, PANIC),
            fixture.row.obligation_digest,
            "{label}: outside #1's claim"
        );
        let report = fixture.report_with(vec![fixture.row.clone()], Some(&chc_valid()));
        assert!(
            matches!(
                report.refusals(),
                [ValidationError::CoverageClaimDrift { obligation: PANIC, detail }]
                    if detail.starts_with("the replay context drifted")
                        && detail.contains("outside the write-back allowlist")
            ),
            "{label}: {:?}",
            report.refusals()
        );
    }
}

/// A replayer that reads the node's clean-expr `Goal` (the fusion carrier:
/// the goal IS the node's data) and proves the panic site only when it is the
/// trivial one. Test-only.
#[cfg(feature = "clean-tv-anchor")]
struct TestOnlyGoalReadingReplayer;

#[cfg(feature = "clean-tv-anchor")]
impl NativeCoverageResultReplay for TestOnlyGoalReadingReplayer {
    fn replay(
        &self,
        solved: &NativeVerificationBundle,
        request: &NativeVerificationRequest,
        _evidence: &NativeEvidenceBundle,
        _attachments: &[NativeEvidenceArtifactAttachment],
    ) -> Result<NativeReplayedResult, NativeCoverageReplayRefusal> {
        let trivial = solved.module.functions[0].blocks[0].body[0]
            .proofs
            .iter()
            .any(|proof| {
                matches!(
                    proof,
                    trust_ir::proof::ProofAnnotation::Goal(goal)
                        if goal.goal == clean_kernel::Expr::bvar(0)
                )
            });
        if trivial {
            Ok(NativeReplayedResult::new(
                request.obligations().to_vec(),
                NativeReplayedStrength::ChcValidity,
            ))
        } else {
            Err(NativeCoverageReplayRefusal::Invalid {
                detail: "the goal is not the trivial one".to_string(),
            })
        }
    }
}

/// `m`'s return node carries the clean-expr goal `goal`.
#[cfg(feature = "clean-tv-anchor")]
fn goal_on_return(goal: clean_kernel::Expr) -> impl Fn(&mut Module) {
    move |m: &mut Module| {
        m.functions[0].blocks[0].body[0].proofs = vec![trust_ir::proof::ProofAnnotation::Goal(
            Box::new(trust_ir::proof::ExprObligation::new(goal.clone())),
        )];
    }
}

/// P-D A/B (the verifier's ADV-R2-9). A clean-expr `ProofAnnotation::Goal`
/// on a body node is excluded from every wire image — `Module::stable_digest`
/// is the same with and without it — and the canonical text shows only
/// `goal(N hyps)`, so no digest can bind its content. On 8958b24a M1 and M2
/// carried DIFFERENT goals, the replay context agreed, and a replayer that
/// reads the goal ESTABLISHED #1 on M2 (while failing on M2). Now nothing
/// replayed in a context carrying a Goal transfers: UNDETERMINED, even when
/// both sides carry the same goal (the context digest, which excludes the
/// Goal, is still held to the row).
#[cfg(feature = "clean-tv-anchor")]
#[test]
fn goal_annotation_leaves_the_replay_context_undetermined() {
    let trivial = goal_on_return(clean_kernel::Expr::bvar(0));
    let other = goal_on_return(clean_kernel::Expr::bvar(7));
    let mut plain = bare_module();
    let bare_digest = plain.stable_digest();
    trivial(&mut plain);
    assert_eq!(
        plain.stable_digest(),
        bare_digest,
        "a Goal is outside the module's wire image"
    );

    let cases: [(&str, SolvedFixture); 2] = [
        (
            "different goals",
            SolvedFixture::editing_both(chc_request(), Vec::new(), MODEL_VALID, &trivial, &other),
        ),
        (
            "the same goal",
            SolvedFixture::editing_both(chc_request(), Vec::new(), MODEL_VALID, &trivial, &trivial),
        ),
    ];
    for (label, fixture) in cases {
        assert_eq!(fixture.solved.validate(), Ok(()), "{label}");
        assert_eq!(fixture.admitted.validate(), Ok(()), "{label}");
        for bundle in [&fixture.solved, &fixture.admitted] {
            let context = bundle
                .coverage_replay_context_digest()
                .expect("an indexable context has a digest, Goal or not");
            assert_eq!(
                context.transferable(),
                Err(FuncId::new(0)),
                "{label}: nothing transfers on a context carrying a Goal"
            );
        }
        // The Goal is outside the digest: different goals, one digest (so
        // the digest can neither bind nor excuse the goal's content).
        assert_eq!(
            context_digest(&fixture.solved),
            context_digest(&fixture.admitted),
            "{label}"
        );
        assert_eq!(
            claim_digest(&fixture.admitted.module, PANIC),
            fixture.row.obligation_digest,
            "{label}: the canonical text marks a goal's presence, not its content"
        );
        let report = fixture.report_with(
            vec![fixture.row.clone()],
            Some(&TestOnlyGoalReadingReplayer),
        );
        assert!(
            report.refusals().is_empty(),
            "{label}: {:?}",
            report.refusals()
        );
        assert_eq!(
            report.for_obligation(fixture.obligation()),
            obligation_undetermined(CoverageUndeterminedReason::GoalAnnotationUnbound {
                function: FuncId::new(0)
            }),
            "{label}"
        );
    }
    // A goal that APPEARS after the solve moves the canonical text of #1's
    // function, so the claim digest already refuses it.
    let appeared =
        SolvedFixture::editing_both(chc_request(), Vec::new(), MODEL_VALID, |_| {}, &other);
    let report = appeared.report_with(
        vec![appeared.row.clone()],
        Some(&TestOnlyGoalReadingReplayer),
    );
    assert!(
        matches!(
            report.refusals(),
            [ValidationError::CoverageClaimDrift {
                obligation: PANIC,
                ..
            }]
        ),
        "{:?}",
        report.refusals()
    );
}

/// P-F T5. Renumbering a SIBLING obligation between the solve and the
/// admission — the same claim, the order kept, the compiler facts naming
/// neither id — moves the replay context: a replayer may read obligations by
/// id (a call-site proof context names callee claims by `ProofId`). Refused;
/// the control (same id) establishes. With the ids erased from the context
/// image this test is the only one that turns red.
#[test]
fn renumbered_sibling_obligation_is_refused() {
    fn sibling(id: u32) -> impl FnOnce(&mut Module) {
        move |m: &mut Module| {
            let mut o = obligation(
                2,
                ObligationKind::ArithmeticSafety,
                ProofStatus::Pending,
                "(< 1 100)",
                0,
            );
            o.id = ProofId::new(id);
            m.proof_obligations.push(o);
        }
    }
    for (label, renamed) in [("renamed", 3), ("control", 2)] {
        let mut fixture = SolvedFixture::editing_both(
            chc_request(),
            Vec::new(),
            MODEL_VALID,
            sibling(2),
            sibling(renamed),
        );
        for bundle in [&mut fixture.solved, &mut fixture.admitted] {
            bundle
                .compiler_facts
                .obligation_sources
                .retain(|source| source.obligation.index() < 2);
        }
        fixture.row.solved_bundle_digest = fixture.solved.stable_digest();
        fixture.row.solved_replay_context_digest = context_digest(&fixture.solved);
        assert_eq!(fixture.solved.validate(), Ok(()), "{label}");
        assert_eq!(fixture.admitted.validate(), Ok(()), "{label}");
        assert_eq!(
            claim_digest(&fixture.solved.module, 2),
            claim_digest(&fixture.admitted.module, renamed),
            "{label}: only the sibling's id moves"
        );
        let report = fixture.report_with(vec![fixture.row.clone()], Some(&chc_valid()));
        if renamed == 2 {
            fixture.assert_established(&report, CoverageBound::Unbounded);
        } else {
            assert!(
                matches!(
                    report.refusals(),
                    [ValidationError::CoverageClaimDrift { obligation: PANIC, detail }]
                        if detail.starts_with("the replay context drifted")
                ),
                "{label}: {:?}",
                report.refusals()
            );
        }
    }
}

// ---------------------------------------------------------------------------
// P-B / P-C: the unindexable context and the merge order
// ---------------------------------------------------------------------------

/// Re-seal a fixture's solved bundle around `m1` (evidence and row re-cited).
fn rebind_solved(
    fixture: &SolvedFixture,
    m1: Module,
) -> (NativeVerificationBundle, NativeCoverageAttestationRow) {
    let mut solved = bundle_for(m1.clone(), fixture.solved.requests.clone());
    let artifacts = fixture.row.result_artifacts.clone();
    let evidence = solved
        .evidence_bundle_for_request(&fixture.request, artifacts)
        .expect("the request carries a replay identity");
    solved.evidence_bundles.push(evidence.clone());
    let mut row = fixture.row.clone();
    row.obligation_digest = claim_digest(&m1, PANIC);
    row.solved_module_digest = solved.trust_ir_module_digest;
    row.solved_executable_content_digest = m1.executable_content_digest_v1();
    row.solved_bundle_digest = solved.stable_digest();
    row.evidence_bundle_digest = evidence.stable_digest();
    (solved, row)
}

/// P-B. Negative control for the two UNINDEXABLE-context refusals.
/// `NativeVerificationBundle::validate` does not check obligation sites, so a
/// validating bundle can carry a dangling one and have no replay context.
/// (a) The SOLVED context is unindexable and the row cites the admitted
/// bundle's; (b) the ADMITTED context is unindexable. Each is refused by
/// name; with either arm read as "the row's digest", each is Established.
#[test]
fn unindexable_replay_context_is_refused() {
    fn dangle_contract(m: &mut Module) {
        m.proof_obligations[CONTRACT as usize].site = Some(trust_ir::proof::ObligationSite {
            function: FuncId::new(0),
            block: BlockId::new(0),
            inst_index: 9,
        });
    }
    // (a) M1 dangles #0; M2 does not; the row cites M2's context.
    let mut solved_side = SolvedFixture::chc();
    let mut m1 = solved_side.solved.module.clone();
    dangle_contract(&mut m1);
    let (solved, row) = rebind_solved(&solved_side, m1);
    solved_side.solved = solved;
    solved_side.row = row;
    solved_side.row.solved_replay_context_digest = context_digest(&solved_side.admitted);
    assert_eq!(solved_side.solved.validate(), Ok(()));
    assert_eq!(
        solved_side.solved.coverage_replay_context_digest(),
        Err(NativeReplayContextUnavailable::Unindexable)
    );
    let report = solved_side.report_with(vec![solved_side.row.clone()], Some(&chc_valid()));
    assert!(
        matches!(
            report.refusals(),
            [ValidationError::CoverageClaimDrift { obligation: PANIC, detail }]
                if detail.contains("the replay context of the solved bundle cannot be computed")
        ),
        "{:?}",
        report.refusals()
    );

    // (b) M2 dangles #0; the row cites M1's context.
    let admitted_side = SolvedFixture::new(chc_request(), Vec::new(), MODEL_VALID, dangle_contract);
    assert_eq!(admitted_side.admitted.validate(), Ok(()));
    assert_eq!(
        admitted_side.admitted.coverage_replay_context_digest(),
        Err(NativeReplayContextUnavailable::Unindexable)
    );
    let report = admitted_side.report_with(vec![admitted_side.row.clone()], Some(&chc_valid()));
    assert!(
        matches!(
            report.refusals(),
            [ValidationError::CoverageClaimDrift { obligation: PANIC, detail }]
                if detail.contains("the replay context of the admitted bundle cannot be computed")
        ),
        "{:?}",
        report.refusals()
    );
}

/// P-C. Negative control for the merge: a refused row wins over an
/// established row for the same obligation in EITHER order (the attestation
/// itself is valid: the two rows cite different solved bundles).
#[test]
fn refusal_wins_whatever_the_row_order() {
    let fixture = SolvedFixture::chc();
    let mut forged = fixture.row.clone();
    forged.solved_bundle_digest = digest(0x79);
    for rows in [
        vec![fixture.row.clone(), forged.clone()],
        vec![forged.clone(), fixture.row.clone()],
    ] {
        let report = fixture.report_with(rows, Some(&chc_valid()));
        assert_eq!(report.refusals().len(), 1, "{:?}", report.refusals());
        assert!(
            matches!(
                report.for_obligation(fixture.obligation()),
                ObligationCoverage::Refused(ValidationError::CoverageSolvedBundleMissing { .. })
            ),
            "{:?}",
            report.for_obligation(fixture.obligation())
        );
    }
}

// ---------------------------------------------------------------------------
// P-E: a result that rests on other obligations names them, and is
// established only when they are
// ---------------------------------------------------------------------------

/// The precondition #2 the premise tests share.
const PREMISE: u32 = 2;

/// A replayer that NAMES, per request id, the premises its result rests on,
/// and answers `BoundedUnwind` to the request's depth for a BMC request. It
/// checks nothing else (the consumer has recomputed every digest before it
/// runs). Test-only.
#[derive(Clone)]
struct TestOnlyPremiseNamingReplayer {
    premises: Vec<(u32, Vec<u32>)>,
}

impl NativeCoverageResultReplay for TestOnlyPremiseNamingReplayer {
    fn replay(
        &self,
        _solved: &NativeVerificationBundle,
        request: &NativeVerificationRequest,
        _evidence: &NativeEvidenceBundle,
        _attachments: &[NativeEvidenceArtifactAttachment],
    ) -> Result<NativeReplayedResult, NativeCoverageReplayRefusal> {
        let strength = match request {
            NativeVerificationRequest::TrustMc(mc)
                if mc.mode == TrustMcVerificationMode::BoundedModelCheck =>
            {
                NativeReplayedStrength::BoundedUnwind {
                    depth: u64::from(mc.options.bmc.unwind_limit),
                }
            }
            _ => NativeReplayedStrength::ChcValidity,
        };
        let premises = self
            .premises
            .iter()
            .find(|(id, _)| *id == request.id().index())
            .map(|(_, premises)| premises.iter().map(|p| ProofId::new(*p)).collect())
            .unwrap_or_default();
        Ok(NativeReplayedResult::new(request.obligations().to_vec(), strength).assuming(premises))
    }
}

fn naming(premises: &[(u32, &[u32])]) -> TestOnlyPremiseNamingReplayer {
    TestOnlyPremiseNamingReplayer {
        premises: premises
            .iter()
            .map(|(id, premises)| (*id, premises.to_vec()))
            .collect(),
    }
}

/// Two results solved in ONE bundle: request 1 for #1 (CHC) and request 2 for
/// the precondition #2 (`second`: CHC, or BMC to depth 4), each with its
/// evidence and its attestation row. M2 is M1 plus trust-mc's certificate.
struct PremiseFixture {
    solved: NativeVerificationBundle,
    admitted: NativeVerificationBundle,
    attachments: Vec<NativeEvidenceArtifactAttachment>,
    /// The rows for #1 and for #2.
    rows: [NativeCoverageAttestationRow; 2],
}

impl PremiseFixture {
    fn new(
        second: TrustMcVerificationMode,
        edit_solved: impl FnOnce(&mut Module),
        edit_admitted: impl FnOnce(&mut Module),
    ) -> Self {
        let with_premise =
            |m: &mut Module| m.proof_obligations.push(precondition(PREMISE, "(< 1 100)"));
        let mut m1 = bare_module();
        with_premise(&mut m1);
        edit_solved(&mut m1);
        let requests = vec![
            chc_request(),
            trust_mc_request_with(
                2,
                second,
                4,
                &[PREMISE],
                ProofDigest::sha256_domain("coverage_establishment.replay", b"mc-premise"),
            ),
        ];
        let mut solved = bundle_for(m1.clone(), requests.clone());
        let model = artifact_for(
            "kernel_checked.invariant.smt2",
            NativeEvidenceArtifactKind::TrustMcModel,
            MODEL_VALID,
        );
        let horn = artifact_for(
            "kernel_checked.horn.smt2",
            NativeEvidenceArtifactKind::TrustMcHornClauses,
            HORN,
        );
        let mut attachments = Vec::new();
        let mut evidences = Vec::new();
        let mut cited = Vec::new();
        for request in &requests {
            let bounded = matches!(
                request,
                NativeVerificationRequest::TrustMc(r)
                    if r.mode == TrustMcVerificationMode::BoundedModelCheck
            );
            let artifacts: Vec<(NativeEvidenceArtifact, &[u8])> = if bounded {
                vec![(model.clone(), MODEL_VALID)]
            } else {
                vec![(horn.clone(), HORN), (model.clone(), MODEL_VALID)]
            };
            let evidence = solved
                .evidence_bundle_for_request(
                    request,
                    artifacts.iter().map(|(a, _)| a.clone()).collect(),
                )
                .expect("the request carries a replay identity");
            solved.evidence_bundles.push(evidence.clone());
            evidences.push(evidence);
            cited.push(artifacts.iter().map(|(a, _)| a.clone()).collect::<Vec<_>>());
            for (artifact, bytes) in artifacts {
                attachments.push(NativeEvidenceArtifactAttachment::for_artifact(
                    request.id(),
                    NativeVerifierSuite::TrustMc,
                    &artifact,
                    "trust-mc:coverage-establishment-test",
                    bytes.to_vec(),
                ));
            }
        }
        assert_eq!(solved.validate(), Ok(()), "{:#?}", solved.validate());
        let mut m2 = bare_module();
        with_premise(&mut m2);
        m2.proof_certificates.push(solver_certificate());
        edit_admitted(&mut m2);
        let admitted = bundle_for(m2, requests.clone());
        let row = |index: usize, obligation: u32| NativeCoverageAttestationRow {
            obligation: ProofId::new(obligation),
            obligation_digest: claim_digest(&m1, obligation),
            solved_module_digest: solved.trust_ir_module_digest,
            solved_executable_content_digest: m1.executable_content_digest_v1(),
            solved_replay_context_digest: row_context_digest(&solved),
            solved_bundle_digest: solved.stable_digest(),
            request_digest: requests[index].stable_digest(),
            evidence_bundle_digest: evidences[index].stable_digest(),
            result_artifacts: cited[index].clone(),
        };
        let rows = [row(0, PANIC), row(1, PREMISE)];
        PremiseFixture {
            solved,
            admitted,
            attachments,
            rows,
        }
    }

    fn chc() -> Self {
        Self::new(TrustMcVerificationMode::Chc, |_| {}, |_| {})
    }

    fn report(
        &self,
        rows: Vec<NativeCoverageAttestationRow>,
        replay: &TestOnlyPremiseNamingReplayer,
    ) -> CoverageEstablishmentReport {
        let attestation = NativeCoverageAttestation::new(rows);
        let solved = [&self.solved];
        coverage_establishment_report(
            &self.admitted,
            CoverageInputs {
                attestation: Some(&attestation),
                solved_bundles: &solved,
                attachments: &self.attachments,
                replay: Some(replay),
            },
        )
    }
}

/// P-E. #1's result rests on the precondition #2 and NAMES it; it is
/// established only once #2 is — here by #2's own verified result, in the
/// same report, in either row order — and its verdict names the premise.
#[test]
fn premise_established_in_the_same_report_grounds_the_result() {
    let fixture = PremiseFixture::chc();
    let replay = naming(&[(1, &[PREMISE]), (2, &[])]);
    let [first, second] = fixture.rows.clone();
    for rows in [
        vec![first.clone(), second.clone()],
        vec![second.clone(), first.clone()],
    ] {
        let report = fixture.report(rows, &replay);
        assert!(report.refusals().is_empty(), "{:?}", report.refusals());
        match report.for_obligation(ProofId::new(PANIC)) {
            ObligationCoverage::Established {
                bound: CoverageBound::Unbounded,
                basis,
            } => assert_eq!(basis.premises, vec![ProofId::new(PREMISE)]),
            other => panic!("expected #1 Established, got {other:?}"),
        }
        assert!(matches!(
            report.for_obligation(ProofId::new(PREMISE)),
            ObligationCoverage::Established {
                bound: CoverageBound::Unbounded,
                ..
            }
        ));
    }
}

/// P-E. The premise is established by a KERNEL-REPLAYED certificate (basis
/// K): #1's result rests on the ground contract #0, which the admitted bundle
/// carries Trust's kernel certificate for. In a kernel-less build nothing
/// establishes #0, so #1 waits on it.
#[test]
fn kernel_established_premise_grounds_the_result() {
    let mut fixture = PremiseFixture::chc();
    let mut m2 = fixture.admitted.module.clone();
    let certificate = contract_certificate(&m2);
    let contract = certificate.lineage_ref();
    m2.proof_certificates.push(certificate);
    fixture.admitted = bundle_for(
        m2,
        vec![
            trust_vc_import(vec![contract.clone()]),
            fixture.solved.requests[0].clone(),
            fixture.solved.requests[1].clone(),
        ],
    );
    let replay = naming(&[(1, &[CONTRACT])]);
    let report = fixture.report(vec![fixture.rows[0].clone()], &replay);
    if NativeVerificationBundle::kernel_replay_available() {
        assert!(report.refusals().is_empty(), "{:?}", report.refusals());
        assert!(matches!(
            report.for_certificate(&contract),
            CertificateCoverage::Established {
                bound: CoverageBound::Unbounded,
                ..
            }
        ));
        assert!(
            matches!(
                report.for_obligation(ProofId::new(PANIC)),
                ObligationCoverage::Established {
                    bound: CoverageBound::Unbounded,
                    ..
                }
            ),
            "{:?}",
            report.for_obligation(ProofId::new(PANIC))
        );
    } else {
        // Kernel-less: the imported CleanCic certificate does not validate,
        // so nothing is derived at all.
        assert!(!report.is_checked());
    }
}

/// P-E. A named premise that nothing establishes `Unbounded` leaves the
/// result UNDETERMINED: no row for #2 at all, or #2 established only to a
/// bounded depth.
#[test]
fn premise_not_established_leaves_the_result_undetermined() {
    let waiting = obligation_undetermined(CoverageUndeterminedReason::PremiseNotEstablished {
        premise: ProofId::new(PREMISE),
    });
    let fixture = PremiseFixture::chc();
    let replay = naming(&[(1, &[PREMISE])]);
    let report = fixture.report(vec![fixture.rows[0].clone()], &replay);
    assert!(report.refusals().is_empty(), "{:?}", report.refusals());
    assert_eq!(report.for_obligation(ProofId::new(PANIC)), waiting);

    let bounded = PremiseFixture::new(TrustMcVerificationMode::BoundedModelCheck, |_| {}, |_| {});
    let report = bounded.report(bounded.rows.to_vec(), &replay);
    assert!(report.refusals().is_empty(), "{:?}", report.refusals());
    assert!(matches!(
        report.for_obligation(ProofId::new(PREMISE)),
        ObligationCoverage::Established {
            bound: CoverageBound::UnwindBounded { depth: 4 },
            ..
        }
    ));
    assert_eq!(report.for_obligation(ProofId::new(PANIC)), waiting);
}

/// P-E. An assumption CYCLE establishes nothing, whatever the row order: #1
/// rests on #2 and #2 on #1; and #1 resting on itself.
#[test]
fn assumption_cycle_is_undetermined_whatever_the_row_order() {
    let fixture = PremiseFixture::chc();
    let cycle = naming(&[(1, &[PREMISE]), (2, &[PANIC])]);
    let [first, second] = fixture.rows.clone();
    for rows in [
        vec![first.clone(), second.clone()],
        vec![second.clone(), first.clone()],
    ] {
        let report = fixture.report(rows, &cycle);
        assert!(report.refusals().is_empty(), "{:?}", report.refusals());
        assert_eq!(
            report.for_obligation(ProofId::new(PANIC)),
            obligation_undetermined(CoverageUndeterminedReason::PremiseNotEstablished {
                premise: ProofId::new(PREMISE)
            })
        );
        assert_eq!(
            report.for_obligation(ProofId::new(PREMISE)),
            obligation_undetermined(CoverageUndeterminedReason::PremiseNotEstablished {
                premise: ProofId::new(PANIC)
            })
        );
    }
    let itself = naming(&[(1, &[PANIC])]);
    let report = fixture.report(vec![first], &itself);
    assert_eq!(
        report.for_obligation(ProofId::new(PANIC)),
        obligation_undetermined(CoverageUndeterminedReason::PremiseNotEstablished {
            premise: ProofId::new(PANIC)
        })
    );
}

/// P-E A/B (the verifier's ADV-R2-3). The precondition #1's result rests on
/// is FAILED; on 8958b24a only #1's own status was checked and #1 stayed
/// Established. Now a named premise that is `Failed` in the solved or in the
/// admitted module refuses the bundle, and so does a premise the module does
/// not state at all.
#[test]
fn failed_or_unstated_premise_is_refused() {
    let fail = |m: &mut Module| {
        m.proof_obligations[PREMISE as usize].status = ProofStatus::Failed;
    };
    let replay = naming(&[(1, &[PREMISE])]);
    for (label, fixture, side) in [
        (
            "both",
            PremiseFixture::new(TrustMcVerificationMode::Chc, fail, fail),
            "solved",
        ),
        (
            "solved only",
            PremiseFixture::new(TrustMcVerificationMode::Chc, fail, |_| {}),
            "solved",
        ),
        (
            "admitted only",
            PremiseFixture::new(TrustMcVerificationMode::Chc, |_| {}, fail),
            "admitted",
        ),
    ] {
        let report = fixture.report(vec![fixture.rows[0].clone()], &replay);
        let refusal = ValidationError::CoverageContradicted {
            obligation: PANIC,
            detail: format!(
                "the result rests on premise #{PREMISE}, which is Failed in the {side} module"
            ),
        };
        assert_eq!(report.refusals(), std::slice::from_ref(&refusal), "{label}");
        assert_eq!(
            report.for_obligation(ProofId::new(PANIC)),
            ObligationCoverage::Refused(refusal),
            "{label}"
        );
    }

    let fixture = PremiseFixture::chc();
    let report = fixture.report(vec![fixture.rows[0].clone()], &naming(&[(1, &[9])]));
    assert_eq!(
        report.refusals(),
        &[ValidationError::CoverageResultReplayInvalid {
            obligation: PANIC,
            detail: "the replay names premise #9, which the solved module does not state"
                .to_string(),
        }]
    );
}

/// P-E with P-C: a premise whose own row is REFUSED grounds nothing — the
/// refusal wins for #2 and #1 waits on it — whatever the row order, and
/// whether #2's valid row rests on nothing or on an ungrounded premise of
/// its own (the refusal is not overwritten by `PremiseNotEstablished`).
#[test]
fn refused_premise_grounds_nothing() {
    let fixture = PremiseFixture::chc();
    let [first, second] = fixture.rows.clone();
    let mut forged = second.clone();
    forged.solved_bundle_digest = digest(0x79);
    for (replay, rows) in [
        naming(&[(1, &[PREMISE]), (2, &[])]),
        naming(&[(1, &[PREMISE]), (2, &[PANIC])]),
    ]
    .into_iter()
    .flat_map(|replay| {
        [
            vec![first.clone(), second.clone(), forged.clone()],
            vec![forged.clone(), second.clone(), first.clone()],
        ]
        .map(|rows| (replay.clone(), rows))
    }) {
        let report = fixture.report(rows, &replay);
        assert_eq!(report.refusals().len(), 1, "{:?}", report.refusals());
        assert!(matches!(
            report.for_obligation(ProofId::new(PREMISE)),
            ObligationCoverage::Refused(ValidationError::CoverageSolvedBundleMissing { .. })
        ));
        assert_eq!(
            report.for_obligation(ProofId::new(PANIC)),
            obligation_undetermined(CoverageUndeterminedReason::PremiseNotEstablished {
                premise: ProofId::new(PREMISE)
            })
        );
    }
}

/// Every row is judged against ITS solved bundle, however many rows cite that
/// bundle and in whatever order: the consumer digests each candidate bundle
/// once and must serve each row that bundle's own digests. Two rows (for #1
/// and #2) cite one solved bundle and the admitted bundle drifted — (a) its
/// module states an obligation #3 the solve never saw (context drift), (b) it
/// has one more function (code drift) — so each row is refused for the
/// drift, and neither is judged as if the admitted bundle's digest were the
/// solved one's.
#[test]
fn drift_refuses_every_row_that_cites_the_solved_bundle() {
    fn appeared(m: &mut Module) {
        m.proof_obligations.push(obligation(
            3,
            ObligationKind::ArithmeticSafety,
            ProofStatus::Pending,
            "(< 2 100)",
            0,
        ));
    }
    fn helper(m: &mut Module) {
        let mut helper =
            Function::new(FuncId::new(1), "helper", m.functions[0].ty, BlockId::new(0))
                .with_producer(Producer::TRust);
        helper.blocks.push(Block {
            id: BlockId::new(0),
            params: Vec::new(),
            body: vec![InstrNode::new(Inst::Return { values: Vec::new() })],
        });
        m.try_add_function(helper)
            .expect("Module::try_add_function: test fixture");
    }
    let context_drift = |refusal: &ValidationError| match refusal {
        ValidationError::CoverageClaimDrift { obligation, detail }
            if detail.starts_with(
                "the replay context drifted: obligation #3: the result was solved in a \
                 context that has no such obligation",
            ) =>
        {
            Some(*obligation)
        }
        _ => None,
    };
    let code_drift = |refusal: &ValidationError| match refusal {
        ValidationError::CoverageSubjectCodeDrift { obligation, .. } => Some(*obligation),
        _ => None,
    };
    /// A label, the admitted-module edit, and which refusal it must draw.
    type Case<'a> = (
        &'a str,
        fn(&mut Module),
        &'a dyn Fn(&ValidationError) -> Option<u32>,
    );
    let cases: [Case<'_>; 2] = [
        ("an obligation appeared", appeared, &context_drift),
        ("a function appeared", helper, &code_drift),
    ];
    for (label, edit, expected) in cases {
        let fixture = PremiseFixture::new(TrustMcVerificationMode::Chc, |_| {}, edit);
        assert_eq!(fixture.admitted.validate(), Ok(()), "{label}");
        let [first, second] = fixture.rows.clone();
        for rows in [
            vec![first.clone(), second.clone()],
            vec![second.clone(), first.clone()],
        ] {
            let report = fixture.report(rows, &naming(&[]));
            let mut drifted: Vec<u32> = report
                .refusals()
                .iter()
                .map(|refusal| {
                    expected(refusal).unwrap_or_else(|| panic!("{label}: got {refusal:?}"))
                })
                .collect();
            drifted.sort_unstable();
            assert_eq!(drifted, vec![PANIC, PREMISE], "{label}");
        }
    }
}

// ---------------------------------------------------------------------------
// ROUND 4: an undetermined reason never masks a refusal
// ---------------------------------------------------------------------------

/// `m` gains function #1, `unrelated` — no obligation is scoped to it, so no
/// claim digest reads it — whose return node carries a clean-expr `Goal` when
/// `goal`.
#[cfg(feature = "clean-tv-anchor")]
fn unrelated_function(goal: bool) -> impl Fn(&mut Module) {
    move |m: &mut Module| {
        let mut unrelated = Function::new(
            FuncId::new(1),
            "unrelated",
            m.functions[0].ty,
            BlockId::new(0),
        )
        .with_producer(Producer::TRust);
        let mut node = InstrNode::new(Inst::Return { values: Vec::new() });
        if goal {
            node.proofs = vec![trust_ir::proof::ProofAnnotation::Goal(Box::new(
                trust_ir::proof::ExprObligation::new(clean_kernel::Expr::bvar(0)),
            ))];
        }
        unrelated.blocks.push(Block {
            id: BlockId::new(0),
            params: Vec::new(),
            body: vec![node],
        });
        m.try_add_function(unrelated)
            .expect("Module::try_add_function: test fixture");
    }
}

/// Where the unrelated function's Goal sits: (label, solved side, admitted
/// side). The first is the control every other one differs from.
#[cfg(feature = "clean-tv-anchor")]
const GOAL_PLACEMENTS: [(&str, bool, bool); 4] = [
    ("no Goal", false, false),
    ("a Goal on the admitted side", false, true),
    ("a Goal on the solved side", true, false),
    ("a Goal on both sides", true, true),
];

/// What a Goal on the unrelated function leaves an otherwise establishing row.
#[cfg(feature = "clean-tv-anchor")]
fn unrelated_goal_unbound() -> ObligationCoverage {
    obligation_undetermined(CoverageUndeterminedReason::GoalAnnotationUnbound {
        function: FuncId::new(1),
    })
}

/// R4 A/B (the verdict on 89957e87, GOALFORGE). The ADMITTED bundle carries a
/// Goal on an UNRELATED function — no claim digest moves — and Trust's
/// kernel-replayable contract certificate for #0, and the row FORGES the
/// solved replay context. On 89957e87 the admitted side's
/// `GoalAnnotationUnbound` returned before the solved side was compared:
/// `refusals()` was EMPTY, #1 Undetermined, and the bundle was admitted on
/// its basis-K certificate. The solved context recomputes, so the forgery is
/// refused whatever the admitted side carries; the honest row is still
/// Undetermined (Established without the Goal).
#[cfg(feature = "clean-tv-anchor")]
#[test]
fn goal_on_the_admitted_side_masks_no_forged_solved_context() {
    for admitted_goal in [false, true] {
        let mut fixture = SolvedFixture::editing_both(
            chc_request(),
            Vec::new(),
            MODEL_VALID,
            unrelated_function(false),
            unrelated_function(admitted_goal),
        );
        let mut m2 = fixture.admitted.module.clone();
        let certificate = contract_certificate(&m2);
        let contract = certificate.lineage_ref();
        m2.proof_certificates.push(certificate);
        fixture.admitted = bundle_for(
            m2,
            vec![trust_vc_import(vec![contract.clone()]), chc_request()],
        );
        assert_eq!(fixture.admitted.validate(), Ok(()), "{admitted_goal}");
        assert_eq!(
            fixture
                .admitted
                .coverage_replay_context_digest()
                .map(|context| context.transferable().is_err()),
            Ok(admitted_goal)
        );
        let solved_context = context_digest(&fixture.solved);

        let honest = fixture.report_with(vec![fixture.row.clone()], Some(&chc_valid()));
        assert!(honest.refusals().is_empty(), "{:?}", honest.refusals());
        assert!(matches!(
            honest.for_certificate(&contract),
            CertificateCoverage::Established {
                bound: CoverageBound::Unbounded,
                ..
            }
        ));
        if admitted_goal {
            assert_eq!(
                honest.for_obligation(fixture.obligation()),
                unrelated_goal_unbound()
            );
        } else {
            fixture.assert_established(&honest, CoverageBound::Unbounded);
        }

        fixture.row.solved_replay_context_digest = digest(0x77);
        let forged = fixture.report_with(vec![fixture.row.clone()], Some(&chc_valid()));
        let refusal = ValidationError::CoverageSolvedBundleDigestMismatch {
            obligation: PANIC,
            field: "solved_replay_context_digest",
            recorded: digest(0x77),
            actual: solved_context,
        };
        assert_eq!(
            forged.refusals(),
            std::slice::from_ref(&refusal),
            "admitted Goal: {admitted_goal}"
        );
        assert_eq!(
            forged.for_obligation(fixture.obligation()),
            ObligationCoverage::Refused(refusal)
        );
    }
}

/// R4 A/B (GOALFORGE-2, and the solved-side twin the verdict read but did not
/// run). Every digest is honest; the REPLAY refuses the result — it is
/// invalid, a refutation is re-established, or its strength contradicts the
/// request's mode (also when it models some other obligation). On 89957e87 a
/// Goal on an unrelated function, on EITHER side, returned
/// `GoalAnnotationUnbound` before the replay ran, so each was Undetermined
/// with no refusal; and a result that did not model the obligation returned
/// `ObligationNotModeled` before the mode was compared. The replay runs on the
/// solved bundle, whatever the transfer can carry, so each is refused in
/// every placement, exactly as without the Goal.
#[cfg(feature = "clean-tv-anchor")]
#[test]
fn an_undetermined_reason_masks_no_replay_refusal() {
    let invalid = ValidationError::CoverageResultReplayInvalid {
        obligation: PANIC,
        detail: "the invariant model does not satisfy the Horn clauses".to_string(),
    };
    let refuted = ValidationError::CoverageContradicted {
        obligation: PANIC,
        detail: "the replay re-established a refutation of obligation(s) [1]: \
                 counterexample re-checked"
            .to_string(),
    };
    let bounded = NativeReplayedStrength::BoundedUnwind { depth: 1 };
    let mismatch = ValidationError::CoverageModeStrengthMismatch {
        obligation: PANIC,
        request: 1,
        mode: "trust_mc Chc".to_string(),
        strength: "bounded_unwind:1".to_string(),
    };
    let chc_validity = Answer::Strength(NativeReplayedStrength::ChcValidity);
    let cases: [(&str, &[u8], Answer, &ValidationError); 4] = [
        ("an invalid result", MODEL_BROKEN, chc_validity, &invalid),
        ("a refutation", MODEL_VALID, Answer::Refute, &refuted),
        (
            "a contradicting strength",
            MODEL_VALID,
            Answer::Strength(bounded),
            &mismatch,
        ),
        (
            "the same, unmodelled",
            MODEL_VALID,
            Answer::OmitObligation(bounded),
            &mismatch,
        ),
    ];
    // Every masked case is listed, not just the first.
    let mut masked = Vec::new();
    for (placement, solved_goal, admitted_goal) in GOAL_PLACEMENTS {
        for (case, model, answer, refusal) in &cases {
            let fixture = SolvedFixture::editing_both(
                chc_request(),
                Vec::new(),
                model,
                unrelated_function(solved_goal),
                unrelated_function(admitted_goal),
            );
            assert_eq!(fixture.solved.validate(), Ok(()), "{placement}");
            assert_eq!(fixture.admitted.validate(), Ok(()), "{placement}");
            let report = fixture.report_with(vec![fixture.row.clone()], Some(&replayer(*answer)));
            let verdict = report.for_obligation(fixture.obligation());
            if report.refusals() != std::slice::from_ref(*refusal)
                || verdict != ObligationCoverage::Refused((*refusal).clone())
            {
                masked.push(format!(
                    "{placement}, {case}: refusals {:?}, verdict {verdict:?}",
                    report.refusals()
                ));
            }
        }
    }
    assert!(masked.is_empty(), "masked refusals:\n{}", masked.join("\n"));
}

/// R4 A/B: the premise checks run whatever the transfer can carry. #1's
/// result names the precondition #2, which is `Failed` in the admitted module,
/// or names #9, which no module states; on 89957e87 a Goal on an unrelated
/// function, on either side, left both Undetermined with no refusal.
#[cfg(feature = "clean-tv-anchor")]
#[test]
fn an_unbound_goal_masks_no_premise_refusal() {
    let fail = |m: &mut Module| {
        m.proof_obligations[PREMISE as usize].status = ProofStatus::Failed;
    };
    let failed_premise = ValidationError::CoverageContradicted {
        obligation: PANIC,
        detail: format!(
            "the result rests on premise #{PREMISE}, which is Failed in the admitted module"
        ),
    };
    let unstated_premise = ValidationError::CoverageResultReplayInvalid {
        obligation: PANIC,
        detail: "the replay names premise #9, which the solved module does not state".to_string(),
    };
    // Every masked case is listed, not just the first.
    let mut masked = Vec::new();
    for (placement, solved_goal, admitted_goal) in GOAL_PLACEMENTS {
        let cases = [
            (
                "a Failed premise",
                PremiseFixture::new(
                    TrustMcVerificationMode::Chc,
                    unrelated_function(solved_goal),
                    |m: &mut Module| {
                        unrelated_function(admitted_goal)(m);
                        fail(m);
                    },
                ),
                naming(&[(1, &[PREMISE])]),
                &failed_premise,
            ),
            (
                "an unstated premise",
                PremiseFixture::new(
                    TrustMcVerificationMode::Chc,
                    unrelated_function(solved_goal),
                    unrelated_function(admitted_goal),
                ),
                naming(&[(1, &[9])]),
                &unstated_premise,
            ),
        ];
        for (case, fixture, replay, refusal) in cases {
            let report = fixture.report(vec![fixture.rows[0].clone()], &replay);
            let verdict = report.for_obligation(ProofId::new(PANIC));
            if report.refusals() != std::slice::from_ref(refusal)
                || verdict != ObligationCoverage::Refused(refusal.clone())
            {
                masked.push(format!(
                    "{placement}, {case}: refusals {:?}, verdict {verdict:?}",
                    report.refusals()
                ));
            }
        }
    }
    assert!(masked.is_empty(), "masked refusals:\n{}", masked.join("\n"));
}

/// R4 control: deferring the Goal changes no verdict that is not a refusal.
/// With a Goal on either side the row is `GoalAnnotationUnbound` — never
/// Established — whether the replayer is missing, inconclusive, answers for
/// another obligation, or re-establishes the result; without it, each keeps
/// its own reason. The first undetermined reason found is the verdict.
#[cfg(feature = "clean-tv-anchor")]
#[test]
fn an_unbound_goal_is_the_first_undetermined_reason() {
    // (case, the replayer's answer, the verdict without the Goal: `None` is
    // Established `Unbounded`).
    let cases: [(&str, Option<Answer>, Option<CoverageUndeterminedReason>); 4] = [
        (
            "no replayer",
            None,
            Some(CoverageUndeterminedReason::NoReplayer),
        ),
        (
            "an inconclusive replay",
            Some(Answer::Inconclusive),
            Some(CoverageUndeterminedReason::ReplayInconclusive {
                reason: NativeCoverageReplayInconclusive::Budget,
                detail: "replay budget exhausted".to_string(),
            }),
        ),
        (
            "a result for another obligation",
            Some(Answer::OmitObligation(NativeReplayedStrength::ChcValidity)),
            Some(CoverageUndeterminedReason::ObligationNotModeled),
        ),
        (
            "a re-established result",
            Some(Answer::Strength(NativeReplayedStrength::ChcValidity)),
            None,
        ),
    ];
    for (placement, solved_goal, admitted_goal) in GOAL_PLACEMENTS {
        for (case, answer, without_goal) in &cases {
            let fixture = SolvedFixture::editing_both(
                chc_request(),
                Vec::new(),
                MODEL_VALID,
                unrelated_function(solved_goal),
                unrelated_function(admitted_goal),
            );
            let replay = answer.map(replayer);
            let report = fixture.report_with(
                vec![fixture.row.clone()],
                replay
                    .as_ref()
                    .map(|replay| replay as &dyn NativeCoverageResultReplay),
            );
            assert!(
                report.refusals().is_empty(),
                "{placement}, {case}: {:?}",
                report.refusals()
            );
            let verdict = report.for_obligation(fixture.obligation());
            match (solved_goal || admitted_goal, without_goal) {
                (true, _) => assert_eq!(verdict, unrelated_goal_unbound(), "{placement}, {case}"),
                (false, Some(reason)) => assert_eq!(
                    verdict,
                    obligation_undetermined(reason.clone()),
                    "{placement}, {case}"
                ),
                (false, None) => fixture.assert_established(&report, CoverageBound::Unbounded),
            }
        }
    }
}

// ---------------------------------------------------------------------------
// ROUND 5: one formula text, and every cited digest checked
// ---------------------------------------------------------------------------

/// Admitted gains Trust's kernel-replayable contract certificate for #0 (basis
/// K), so a report with EMPTY `refusals()` admits the bundle on it.
#[cfg(feature = "clean-tv-anchor")]
fn with_contract_certificate(fixture: &mut SolvedFixture) -> ProofCertificateRef {
    let mut m2 = fixture.admitted.module.clone();
    let certificate = contract_certificate(&m2);
    let contract = certificate.lineage_ref();
    m2.proof_certificates.push(certificate);
    let compiler_facts = fixture.admitted.compiler_facts.clone();
    fixture.admitted = bundle_for(
        m2,
        vec![trust_vc_import(vec![contract.clone()]), chc_request()],
    );
    fixture.admitted.compiler_facts = compiler_facts;
    contract
}

/// GOALDRIFT (R10 A/B, the verdict on 794227ad). A clean-expr `Goal` on an
/// UNRELATED function — on the admitted side, the solved side or both —
/// masked a replay-context DRIFT: the admitted module drops the solved
/// context's assumed precondition #2 (P1/ADV-1), or the admitted compiler
/// facts moved. Without the Goal each is `CoverageClaimDrift`; on 794227ad a
/// Goal left it `GoalAnnotationUnbound` with `refusals()` EMPTY, so the bundle
/// was admitted on Trust's kernel-replayable contract certificate (the same on
/// 89957e87; b13f9d76 refused all six). The context digest binds everything
/// but the Goals and is now always computed, so both sides are held to the
/// row before a Goal can withhold the transfer: the drift is refused in every
/// placement, and an honest write-back in none (Established without a Goal,
/// `GoalAnnotationUnbound` with one).
#[cfg(feature = "clean-tv-anchor")]
#[test]
fn a_goal_masks_no_context_drift() {
    // Every wrong case is listed, not just the first.
    let mut wrong = Vec::new();
    for (placement, solved_goal, admitted_goal) in GOAL_PLACEMENTS {
        for (case, keep_assumption, facts_drift) in [
            ("an honest write-back", true, false),
            ("a dropped assumption", false, false),
            ("drifted compiler facts", true, true),
        ] {
            let mut fixture = SolvedFixture::editing_both(
                chc_request(),
                Vec::new(),
                MODEL_VALID,
                move |m: &mut Module| {
                    m.proof_obligations.push(precondition(2, "(< 1 100)"));
                    unrelated_function(solved_goal)(m);
                },
                move |m: &mut Module| {
                    if keep_assumption {
                        let mut discharged = precondition(2, "(< 1 100)");
                        discharged.status = ProofStatus::Discharged;
                        m.proof_obligations.push(discharged);
                    }
                    unrelated_function(admitted_goal)(m);
                },
            );
            let contract = with_contract_certificate(&mut fixture);
            if facts_drift {
                let source = fixture
                    .admitted
                    .compiler_facts
                    .obligation_sources
                    .iter_mut()
                    .find(|source| source.obligation == ProofId::new(PANIC))
                    .expect("the fixture maps #1's source");
                source.cause = NativeObligationCause::Other;
            }
            assert_eq!(fixture.solved.validate(), Ok(()), "{placement}, {case}");
            assert_eq!(fixture.admitted.validate(), Ok(()), "{placement}, {case}");

            let report = fixture.report_with(vec![fixture.row.clone()], Some(&chc_valid()));
            assert!(
                matches!(
                    report.for_certificate(&contract),
                    CertificateCoverage::Established {
                        bound: CoverageBound::Unbounded,
                        ..
                    }
                ),
                "{placement}, {case}: the bundle carries a basis-K certificate"
            );
            let verdict = report.for_obligation(fixture.obligation());
            let right = if keep_assumption && !facts_drift {
                report.refusals().is_empty()
                    && if solved_goal || admitted_goal {
                        verdict == unrelated_goal_unbound()
                    } else {
                        matches!(
                            verdict,
                            ObligationCoverage::Established {
                                bound: CoverageBound::Unbounded,
                                ..
                            }
                        )
                    }
            } else {
                matches!(
                    report.refusals(),
                    [ValidationError::CoverageClaimDrift { obligation: PANIC, detail }]
                        if detail.starts_with("the replay context drifted")
                ) && matches!(
                    verdict,
                    ObligationCoverage::Refused(ValidationError::CoverageClaimDrift { .. })
                )
            };
            if !right {
                wrong.push(format!(
                    "{placement}, {case}: refusals {:?}, verdict {verdict:?}",
                    report.refusals()
                ));
            }
        }
    }
    assert!(wrong.is_empty(), "masked or wrong:\n{}", wrong.join("\n"));
}

/// GOALDRIFT, the solved side (R10 A/B). With a `Goal` on the SOLVED side the
/// context had no digest on 794227ad, so `row.solved_replay_context_digest`
/// was checked against nothing and the honest producer cited "a digest no
/// bundle recomputes": a FORGED citation left `refusals()` EMPTY and the
/// bundle was admitted on its basis-K certificate (an acknowledged left-open
/// item of round 4). The digest of everything but the Goals is the citation
/// now, in every placement: the honest row cites it (Undetermined with a
/// Goal, Established without), and a forgery is refused.
#[cfg(feature = "clean-tv-anchor")]
#[test]
fn a_goal_leaves_no_cited_context_digest_unchecked() {
    let mut wrong = Vec::new();
    for (placement, solved_goal, admitted_goal) in GOAL_PLACEMENTS {
        let mut fixture = SolvedFixture::editing_both(
            chc_request(),
            Vec::new(),
            MODEL_VALID,
            unrelated_function(solved_goal),
            unrelated_function(admitted_goal),
        );
        let contract = with_contract_certificate(&mut fixture);
        let honest_citation = fixture.row.solved_replay_context_digest;

        let honest = fixture.report_with(vec![fixture.row.clone()], Some(&chc_valid()));
        let honest_verdict = honest.for_obligation(fixture.obligation());
        let honest_right = honest.refusals().is_empty()
            && if solved_goal || admitted_goal {
                honest_verdict == unrelated_goal_unbound()
            } else {
                matches!(
                    honest_verdict,
                    ObligationCoverage::Established {
                        bound: CoverageBound::Unbounded,
                        ..
                    }
                )
            };
        if !honest_right {
            wrong.push(format!(
                "{placement}, honest: refusals {:?}, verdict {honest_verdict:?}",
                honest.refusals()
            ));
        }

        fixture.row.solved_replay_context_digest = digest(0x77);
        let forged = fixture.report_with(vec![fixture.row.clone()], Some(&chc_valid()));
        let refusal = ValidationError::CoverageSolvedBundleDigestMismatch {
            obligation: PANIC,
            field: "solved_replay_context_digest",
            recorded: digest(0x77),
            actual: honest_citation,
        };
        let forged_right = forged.refusals() == std::slice::from_ref(&refusal)
            && forged.for_obligation(fixture.obligation()) == ObligationCoverage::Refused(refusal)
            && matches!(
                forged.for_certificate(&contract),
                CertificateCoverage::Established { .. }
            );
        if !forged_right {
            wrong.push(format!(
                "{placement}, forged: refusals {:?}, verdict {:?}",
                forged.refusals(),
                forged.for_obligation(fixture.obligation())
            ));
        }
    }
    assert!(
        wrong.is_empty(),
        "unchecked or wrong:\n{}",
        wrong.join("\n")
    );
}

/// #0 of the kernel fixture with `formula` in place of `(>= 5 0)`, and a
/// contract certificate carrying the kernel-accepted `Eq.refl true` term
/// under #0's recomputed lineage — every identity resealed, exactly as the
/// r9 coverage-vc verifier built it.
#[cfg(feature = "clean-tv-anchor")]
fn kernel_bundle_stating(formula: ProofFormula) -> (NativeVerificationBundle, ProofCertificateRef) {
    let mut module = bare_module();
    module.proof_obligations[CONTRACT as usize].formula = Some(formula);
    let certificate = contract_certificate(&module);
    let reference = certificate.lineage_ref();
    module.proof_certificates.push(certificate);
    (kernel_bundle(module), reference)
}

/// ONE FORMULA (R10 A/B, the r9 coverage-vc verdict on trust-vc 59cf71c8 +
/// trust-ir 794227ad). The contract replay grounded `smtlib` whenever it was
/// present, whatever the schema, so:
///
/// * P1: an `smtlib2` obligation whose payload `(>= 0 5)` is FALSE and whose
///   `smtlib` rendering `(>= 5 0)` is true was kernel-replayed, reported by
///   `kernel_replayed_certificates` as `ContractGroundDecision`, and
///   `Established{Unbounded}` — release-admitted downstream;
/// * P2: an opaque-schema payload (`trust-types.Formula@1`, `(>= 5 0)`, no
///   rendering) was grounded as SMT-LIB and admitted the same way.
///
/// The replay now grounds only the obligation's ONE SMT-LIB text (an
/// `smtlib2` payload whose rendering, if any, is that payload), the minter
/// refuses the rest, and `kernel_replayed_certificates` lists a replay only
/// for an obligation that states one text. Controls: the payload-only and the
/// identical-rendering `smtlib2` spellings still establish.
#[cfg(feature = "clean-tv-anchor")]
#[test]
fn a_replay_grounds_only_the_obligations_one_formula_text() {
    let mut two_texts = ProofFormula::smtlib2("(>= 0 5)", "Bool");
    two_texts.smtlib = Some("(>= 5 0)".to_string());
    let opaque = ProofFormula::new("trust-types.Formula@1", "(>= 5 0)");
    let mut opaque_rendered = ProofFormula::new("trust-types.Formula@1", "{\"formula\":\"x\"}");
    opaque_rendered.smtlib = Some("(>= 5 0)".to_string());
    let mut payload_only = ProofFormula::smtlib2("(>= 5 0)", "Bool");
    payload_only.smtlib = None;

    let mut wrong = Vec::new();
    for (case, formula, establishes) in [
        (
            "P1: false smtlib2 payload, true rendering",
            two_texts,
            false,
        ),
        ("P2: opaque payload, no rendering", opaque, false),
        ("opaque payload, true rendering", opaque_rendered, false),
        (
            "control: smtlib2 payload, identical rendering",
            ProofFormula::smtlib2("(>= 5 0)", "Bool"),
            true,
        ),
        ("control: smtlib2 payload, no rendering", payload_only, true),
    ] {
        let (bundle, certificate) = kernel_bundle_stating(formula.clone());
        let obligation = &bundle.module.proof_obligations[CONTRACT as usize];
        let minted = trust_ir::clean_expr_lowering::contract::contract_clean_cic_certificate(
            obligation, PROVER_VC,
        )
        .is_some();
        let replayed = bundle
            .kernel_replayed_certificates()
            .get(&certificate)
            .copied();
        let report = coverage_establishment_report(&bundle, CoverageInputs::default());
        let verdict = report.for_certificate(&certificate);
        let established = matches!(
            verdict,
            CertificateCoverage::Established {
                bound: CoverageBound::Unbounded,
                basis: CoverageBasis::KernelReplayedClaim {
                    family: KernelClaimFamily::ContractGroundDecision,
                    ..
                },
            }
        );
        let right = if establishes {
            minted
                && replayed == Some(Some(KernelClaimFamily::ContractGroundDecision))
                && established
                && report.refusals().is_empty()
        } else {
            !minted && replayed.is_none() && !established
        };
        if !right {
            wrong.push(format!(
                "{case}: minted {minted}, replayed {replayed:?}, verdict {verdict:?}, \
                 validate {:?}",
                bundle.validate().map_err(|errors| errors.len())
            ));
        }
    }
    assert!(
        wrong.is_empty(),
        "a text the obligation does not state:\n{}",
        wrong.join("\n")
    );
}

/// ONE FORMULA, the validators. An `smtlib2` formula whose `smtlib` rendering
/// differs from its payload states two formulas: `validate_module` refuses it
/// (`FormulaTextsDisagree`; must-refuse corpus row
/// `refuse/formula_smtlib_rendering_disagrees`) and so does the bundle's own
/// validation, whatever the status — so the coverage report over it is
/// UNCHECKED and establishes nothing. An opaque schema's rendering is not
/// comparable with its payload: never a disagreement, never grounded.
#[test]
fn two_formula_texts_are_refused_by_both_validators() {
    let mut two_texts = ProofFormula::smtlib2("(>= 0 5)", "Bool");
    two_texts.smtlib = Some("(>= 5 0)".to_string());
    let no_predicates = trust_ir::PredTable::new(&[], &[]);
    assert!(two_texts.states_two_texts(&no_predicates));
    assert_eq!(two_texts.smtlib_text(), None);
    let mut opaque = ProofFormula::new("trust-types.Formula@1", "{}");
    opaque.smtlib = Some("(>= 5 0)".to_string());
    assert!(!opaque.states_two_texts(&no_predicates));
    assert_eq!(opaque.smtlib_text(), None);
    assert_eq!(
        ProofFormula::smtlib2("(>= 5 0)", "Bool").smtlib_text(),
        Some("(>= 5 0)")
    );

    for status in [ProofStatus::Pending, ProofStatus::Discharged] {
        let mut module = bare_module();
        module.proof_obligations[CONTRACT as usize].status = status;
        module.proof_obligations[CONTRACT as usize].formula = Some(two_texts.clone());
        let site = trust_ir::proof::FormulaSite::Obligation(ProofId::new(CONTRACT));
        assert!(
            trust_ir_build::validate::validate_module(&module)
                .contains(&ValidationError::FormulaTextsDisagree { site: site.clone() }),
            "{status:?}"
        );
        let bundle = bundle_for(module, vec![chc_request()]);
        let errors = bundle.validate().expect_err("two formula texts");
        assert!(
            errors.contains(
                &trust_ir::request::NativeVerificationBundleError::FormulaTextsDisagree { site }
            ),
            "{status:?}: {errors:?}"
        );
        let report = coverage_establishment_report(&bundle, CoverageInputs::default());
        assert!(!report.is_checked(), "{status:?}");
    }
}

/// ONE FORMULA, everywhere a module states one (the R10 verifier's residual on
/// 794601e2). r5 held an OBLIGATION's formula to one text and nothing else: a
/// summary `requires`/`ensures`/`decreases` clause, a spec machine's typed
/// invariant carrier or temporal formula, and a request's replay atom could
/// each state an `smtlib2` payload `(>= 0 5)` beside a different `smtlib`
/// rendering `(>= 5 0)`, and `validate_module` and
/// `NativeVerificationBundle::validate` both accepted them. Now
/// `Module::stated_formulas` is the one walk both validators run, each site
/// refused by name (`FormulaTextsDisagree`) and exactly once; a replay atom is
/// refused as `InvalidReplayAtom { field: "formula.smtlib" }`. Controls: the
/// same sites with one text (identical rendering, payload only) and with an
/// opaque schema under any rendering are never a disagreement.
#[test]
fn every_formula_a_module_states_is_held_to_one_text() {
    use trust_ir::proof::{ClauseBinding, ClausePlace, ClauseSort, FormulaSite};
    use trust_ir::request::NativeVerificationBundleError;
    use trust_ir::{
        FunctionSummary, SpecInvariant, SpecModule, SpecTemporal, SpecVar, TemporalForm,
    };

    let two_texts = || {
        let mut formula = ProofFormula::smtlib2("(>= 0 5)", "Bool");
        formula.smtlib = Some("(>= 5 0)".to_string());
        formula
    };
    let mut payload_only = ProofFormula::smtlib2("(>= 5 0)", "Bool");
    payload_only.smtlib = None;
    let mut opaque_rendered = ProofFormula::new("trust-types.Formula@1", "{\"ge\":[0,5]}");
    opaque_rendered.smtlib = Some("(>= 5 0)".to_string());
    let one_text = [
        ProofFormula::smtlib2("(>= 5 0)", "Bool"),
        payload_only,
        opaque_rendered,
    ];
    // A DesignOnly machine over `seq: Int` whose typed invariant carrier and/or
    // `Always` leaf is `invariant` / `temporal`, bound over `seq`.
    fn machine(invariant: Option<ProofFormula>, temporal: Option<ProofFormula>) -> SpecModule {
        let over_seq = |mut formula: ProofFormula| {
            formula.bindings = vec![(
                "seq".to_string(),
                ClauseBinding {
                    sort: ClauseSort::Int,
                    place: ClausePlace::SpecVar { index: 0 },
                },
            )];
            formula
        };
        let mut spec = SpecModule::design_only("ring");
        spec.vars = vec![SpecVar::new("seq", "Int").with_sort(ClauseSort::Int)];
        if let Some(typed) = invariant {
            spec.invariants =
                vec![SpecInvariant::new("Bounded", "(>= 5 0)").with_typed(over_seq(typed))];
        }
        if let Some(leaf) = temporal {
            spec.temporal = vec![SpecTemporal::new(
                "AlwaysBounded",
                TemporalForm::Always(over_seq(leaf)),
            )];
        }
        spec
    }
    type Place = fn(&mut Module, ProofFormula);
    let sites: [(FormulaSite, Place); 6] = [
        (FormulaSite::Obligation(ProofId::new(CONTRACT)), |m, f| {
            m.proof_obligations[CONTRACT as usize].formula = Some(f)
        }),
        (
            FormulaSite::SummaryClause {
                function: FuncId::new(0),
                clause: "requires",
                index: 0,
            },
            |m, f| m.functions[0].summary = Some(FunctionSummary::new().requiring(f)),
        ),
        (
            FormulaSite::SummaryClause {
                function: FuncId::new(0),
                clause: "ensures",
                index: 1,
            },
            |m, f| {
                m.functions[0].summary = Some(
                    FunctionSummary::new()
                        .ensuring(ProofFormula::smtlib2("true", "Bool"))
                        .ensuring(f),
                )
            },
        ),
        (
            FormulaSite::SummaryClause {
                function: FuncId::new(0),
                clause: "decreases",
                index: 0,
            },
            |m, f| {
                let mut summary = FunctionSummary::new();
                summary.decreases = vec![f];
                m.functions[0].summary = Some(summary);
            },
        ),
        (
            FormulaSite::SpecInvariant {
                machine: "ring".to_string(),
                invariant: "Bounded".to_string(),
            },
            |m, f| m.spec_modules = vec![machine(Some(f), None)],
        ),
        (
            FormulaSite::SpecTemporal {
                machine: "ring".to_string(),
                property: "AlwaysBounded".to_string(),
            },
            |m, f| m.spec_modules = vec![machine(None, Some(f))],
        ),
    ];

    let refused_sites = |module: &Module| {
        let validated: Vec<FormulaSite> = trust_ir_build::validate::validate_module(module)
            .into_iter()
            .filter_map(|error| match error {
                ValidationError::FormulaTextsDisagree { site } => Some(site),
                _ => None,
            })
            .collect();
        let bundled: Vec<FormulaSite> = bundle_for(module.clone(), vec![chc_request()])
            .validate()
            .err()
            .unwrap_or_default()
            .into_iter()
            .filter_map(|error| match error {
                NativeVerificationBundleError::FormulaTextsDisagree { site } => Some(site),
                _ => None,
            })
            .collect();
        (validated, bundled)
    };

    let mut wrong = Vec::new();
    for (site, place) in &sites {
        let mut module = bare_module();
        place(&mut module, two_texts());
        let (validated, bundled) = refused_sites(&module);
        if validated != std::slice::from_ref(site) || bundled != std::slice::from_ref(site) {
            wrong.push(format!(
                "{site}, two texts: validate_module refused {validated:?}, bundle refused \
                 {bundled:?}"
            ));
        }
        for formula in &one_text {
            let mut module = bare_module();
            place(&mut module, formula.clone());
            let (validated, bundled) = refused_sites(&module);
            if !validated.is_empty() || !bundled.is_empty() {
                wrong.push(format!(
                    "{site}, control {formula:?}: validate_module refused {validated:?}, bundle \
                     refused {bundled:?}"
                ));
            }
        }
    }

    // A request's replay atom: a premise a verifier would read.
    let atom_refusal = |formula: ProofFormula| {
        let atom = NativeReplayAtom::assumption(NativeReplayAtomId::new(0), formula);
        bundle_for(bare_module(), vec![with_replay_atom(chc_request(), atom)])
            .validate()
            .err()
            .unwrap_or_default()
            .contains(&NativeVerificationBundleError::InvalidReplayAtom {
                request: NativeRequestId::new(1),
                atom: NativeReplayAtomId::new(0),
                field: "formula.smtlib",
            })
    };
    if !atom_refusal(two_texts()) {
        wrong.push("replay atom, two texts: not refused".to_string());
    }
    for formula in &one_text {
        if atom_refusal(formula.clone()) {
            wrong.push(format!("replay atom, control {formula:?}: refused"));
        }
    }
    assert!(
        wrong.is_empty(),
        "a stated formula's texts:\n{}",
        wrong.join("\n")
    );
}

/// #0 of `bare_module` re-scoped to `kernel_checked(s: u64)` and stating
/// `formula` over `s`, with a CleanCic certificate carrying the
/// kernel-accepted nonneg term (minted for the HONEST clause `(>= s 0)`) under
/// the recomputed lineage of the obligation as stated. Also returns whether
/// the minter mints for the obligation as stated.
#[cfg(feature = "clean-tv-anchor")]
fn nonneg_bundle_stating(
    formula: ProofFormula,
) -> (NativeVerificationBundle, ProofCertificateRef, bool) {
    nonneg_bundle_binding(formula, "s")
}

/// [`nonneg_bundle_stating`] with the clause's one binding named `symbol`.
#[cfg(feature = "clean-tv-anchor")]
fn nonneg_bundle_binding(
    formula: ProofFormula,
    symbol: &str,
) -> (NativeVerificationBundle, ProofCertificateRef, bool) {
    use trust_ir::proof::{ClauseBinding, ClausePlace, ClauseSort};
    let bind = |mut f: ProofFormula, symbol: &str| {
        f.bindings = vec![(
            symbol.to_string(),
            ClauseBinding {
                sort: ClauseSort::Int,
                place: ClausePlace::Param { index: 0 },
            },
        )];
        f
    };
    let mut module = bare_module();
    let ft = module
        .add_func_type(FuncTy {
            params: vec![trust_ir::ty::Ty::U64],
            returns: Vec::new(),
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    module.functions[0].ty = ft;
    module.functions[0].blocks[0].params =
        vec![(trust_ir::value::ValueId::new(0), trust_ir::ty::Ty::U64)];
    // The honest term is the one closed nonneg proof, whatever the symbol.
    module.proof_obligations[CONTRACT as usize].formula =
        Some(bind(ProofFormula::smtlib2("(>= s 0)", "Bool"), "s"));
    let honest = trust_ir::clean_expr_lowering::contract::contract_clean_cic_certificate_in(
        &module,
        &module.proof_obligations[CONTRACT as usize],
        PROVER_VC,
    )
    .expect("the honest nonneg clause bound to a u64 param mints");
    let ProofEvidence::CleanCic { term, .. } = honest.evidence else {
        panic!("the contract minter mints CleanCic evidence");
    };
    module.proof_obligations[CONTRACT as usize].formula = Some(bind(formula, symbol));
    let minted = trust_ir::clean_expr_lowering::contract::contract_clean_cic_certificate_in(
        &module,
        &module.proof_obligations[CONTRACT as usize],
        PROVER_VC,
    )
    .is_some();
    let obligation = &module.proof_obligations[CONTRACT as usize];
    let certificate = ProofCertificate {
        obligation: obligation.id,
        prover: PROVER_VC.to_string(),
        evidence: ProofEvidence::CleanCic {
            term,
            context: Vec::new(),
            lineage: trust_ir::proof::clean_cic_lineage_digest(obligation),
            kernel_recheck: None,
        },
        assurance: None,
    };
    let reference = certificate.lineage_ref();
    module.proof_certificates.push(certificate);
    (kernel_bundle(module), reference, minted)
}

/// ONE FORMULA on the FREE-NAME nonneg family (the R10 verifier's probe; the
/// r5 tests cover only the literal family). The nonneg grounding
/// (`is_nat_nonneg_shape`, `bind_nat_nonneg`, the minter) reads the same one
/// text, so none of these is minted, replayed or Established — on 794227ad
/// each was Established{Unbounded} with `validate` Ok: N1 an `smtlib2`
/// payload `(>= s 5)` (FALSE at s = 0) with the tautology rendering
/// `(>= s 0)`, N2 an opaque payload with that rendering, N3 an opaque payload
/// `(>= s 0)` with no rendering. Controls: the one-text spellings establish.
#[cfg(feature = "clean-tv-anchor")]
#[test]
fn the_nonneg_family_grounds_only_the_one_formula_text() {
    let mut n1 = ProofFormula::smtlib2("(>= s 5)", "Bool");
    n1.smtlib = Some("(>= s 0)".to_string());
    let mut n2 = ProofFormula::new("trust-types.Formula@1", "{\"ge\":[\"s\",5]}");
    n2.smtlib = Some("(>= s 0)".to_string());
    let n3 = ProofFormula::new("trust-types.Formula@1", "(>= s 0)");
    let mut payload_only = ProofFormula::smtlib2("(>= s 0)", "Bool");
    payload_only.smtlib = None;
    let mut wrong = Vec::new();
    for (case, formula, establishes) in [
        (
            "N1: smtlib2 payload (>= s 5), rendering (>= s 0)",
            n1,
            false,
        ),
        ("N2: opaque payload, rendering (>= s 0)", n2, false),
        ("N3: opaque payload (>= s 0), no rendering", n3, false),
        (
            "control: smtlib2 (>= s 0), identical rendering",
            ProofFormula::smtlib2("(>= s 0)", "Bool"),
            true,
        ),
        (
            "control: smtlib2 (>= s 0), no rendering",
            payload_only,
            true,
        ),
    ] {
        let (bundle, certificate, minted) = nonneg_bundle_stating(formula);
        let replayed = bundle
            .kernel_replayed_certificates()
            .get(&certificate)
            .copied();
        let report = coverage_establishment_report(&bundle, CoverageInputs::default());
        let verdict = report.for_certificate(&certificate);
        let established = matches!(
            verdict,
            CertificateCoverage::Established {
                bound: CoverageBound::Unbounded,
                ..
            }
        );
        let right = if establishes {
            minted && replayed.is_some() && established && report.refusals().is_empty()
        } else {
            !minted && replayed.is_none() && !established
        };
        if !right {
            wrong.push(format!(
                "{case}: minted {minted}, replayed {replayed:?}, verdict {verdict:?}, validate {:?}",
                bundle.validate().map_err(|errors| errors.len())
            ));
        }
    }
    assert!(
        wrong.is_empty(),
        "a nonneg text the obligation does not state:\n{}",
        wrong.join("\n")
    );
}

/// The one-formula rule holds for EVERY schema trust-ir owns
/// (`OwnedFormulaSchema`), at every place a module states a formula, in both
/// validators and a request's replay atoms — not only for `smtlib2`.
///
/// `trust-ir.Pred@1` is owned: its payload `pred.N` cites the module's own
/// predicate table, whose rendering trust-ir computes. A `pred.0` citation of
/// `(and (<= 1 self) (<= self 8))` beside the rendering `true` validated
/// exactly like its honest twin in both validators (measured, r10 verifier),
/// and so did a citation of no predicate at all beside a rendering. The claim
/// schemas (bit-blast goal, SAT refutation, lineage binding) state no SMT-LIB
/// text, so any rendering beside one is a second formula. An opaque schema's
/// rendering stays uncompared (the control).
#[test]
fn every_owned_schema_is_held_to_its_one_text() {
    use trust_ir::proof::satres::satres_formula;
    use trust_ir::proof::{
        BVBLAST_GOAL_SCHEMA, FormulaSite, LINEAGE_TRANSFORM_BINDING_SCHEMA, OwnedFormulaSchema,
    };
    use trust_ir::request::NativeVerificationBundleError;
    use trust_ir::value::{PredId, UnivId};
    use trust_ir::{
        FunctionSummary, Pred, PredTable, Space, SpecInvariant, SpecModule, SpecTemporal,
        TemporalForm, Universe,
    };

    let with_predicates = |mut module: Module| {
        module.universes = vec![Universe::IntRange { lo: 1, hi: 8 }];
        module.predicates = vec![Pred::InUniverse(UnivId::new(0), Space::Member)];
        module
    };
    let pred0 = PredTable::new(
        &[Pred::InUniverse(UnivId::new(0), Space::Member)],
        &[Universe::IntRange { lo: 1, hi: 8 }],
    )
    .proof_formula(PredId::new(0))
    .expect("pred.0 renders");
    assert_eq!(
        pred0.smtlib.as_deref(),
        Some("(and (<= 1 self) (<= self 8))")
    );
    let rendered = |mut formula: ProofFormula, rendering: &str| {
        formula.smtlib = Some(rendering.to_string());
        formula
    };
    let unrendered = |mut formula: ProofFormula| {
        formula.smtlib = None;
        formula
    };
    let cited = |payload: &str, rendering: Option<&str>| {
        let mut formula = pred0.clone();
        formula.payload = payload.to_string();
        formula.smtlib = rendering.map(str::to_string);
        formula
    };
    let goal_claim = ProofFormula::new(
        BVBLAST_GOAL_SCHEMA,
        format!("site=0:0:0\nkind=BoundsCheck\ngoal={}", "a".repeat(64)),
    );
    let satres_claim =
        satres_formula("lower.add", &[vec![(0, false)], vec![(0, true)]]).expect("a satres claim");
    let lineage_claim = ProofFormula::new(
        LINEAGE_TRANSFORM_BINDING_SCHEMA,
        format!("sha256:{}", "ab".repeat(32)),
    );
    // (label, schema, formula, states two texts)
    let cases: Vec<(&str, Option<OwnedFormulaSchema>, ProofFormula, bool)> = vec![
        (
            "pred.0 as rendered",
            Some(OwnedFormulaSchema::Pred),
            pred0.clone(),
            false,
        ),
        (
            "pred.0, no rendering",
            Some(OwnedFormulaSchema::Pred),
            unrendered(pred0.clone()),
            false,
        ),
        (
            "pred.0 beside `true`",
            Some(OwnedFormulaSchema::Pred),
            rendered(pred0.clone(), "true"),
            true,
        ),
        (
            "pred.0 beside pred.0's rendering respaced",
            Some(OwnedFormulaSchema::Pred),
            rendered(pred0.clone(), "(and (<= 1 self)  (<= self 8))"),
            true,
        ),
        (
            "pred.7 (no such predicate) beside pred.0's rendering",
            Some(OwnedFormulaSchema::Pred),
            cited("pred.7", pred0.smtlib.as_deref()),
            true,
        ),
        (
            "pred.00 (not the citation spelling) beside pred.0's rendering",
            Some(OwnedFormulaSchema::Pred),
            cited("pred.00", pred0.smtlib.as_deref()),
            true,
        ),
        (
            "bit-blast goal claim",
            Some(OwnedFormulaSchema::BvBlastGoal),
            goal_claim.clone(),
            false,
        ),
        (
            "bit-blast goal claim beside `true`",
            Some(OwnedFormulaSchema::BvBlastGoal),
            rendered(goal_claim, "true"),
            true,
        ),
        (
            "SAT-refutation claim",
            Some(OwnedFormulaSchema::SatRes),
            satres_claim.clone(),
            false,
        ),
        (
            "SAT-refutation claim beside `false`",
            Some(OwnedFormulaSchema::SatRes),
            rendered(satres_claim, "false"),
            true,
        ),
        (
            "lineage binding",
            Some(OwnedFormulaSchema::LineageTransformBinding),
            lineage_claim.clone(),
            false,
        ),
        (
            "lineage binding beside `true`",
            Some(OwnedFormulaSchema::LineageTransformBinding),
            rendered(lineage_claim, "true"),
            true,
        ),
        (
            "smtlib2 (>= 0 5) beside (>= 5 0)",
            Some(OwnedFormulaSchema::Smtlib2),
            rendered(ProofFormula::smtlib2("(>= 0 5)", "Bool"), "(>= 5 0)"),
            true,
        ),
        (
            "opaque payload beside a rendering (not owned: never compared)",
            None,
            rendered(
                ProofFormula::new("trust-types.Formula@1", "{\"ge\":[5,0]}"),
                "true",
            ),
            false,
        ),
    ];
    // Every owned schema has a two-text case and an honest one.
    for owned in OwnedFormulaSchema::ALL {
        for two in [false, true] {
            assert!(
                owned == OwnedFormulaSchema::Smtlib2
                    || cases
                        .iter()
                        .any(|(_, schema, _, t)| *schema == Some(owned) && *t == two),
                "{owned:?} has no case stating {} text(s)",
                if two { "two" } else { "one" }
            );
        }
    }

    fn machine(invariant: Option<ProofFormula>, temporal: Option<ProofFormula>) -> SpecModule {
        let mut spec = SpecModule::design_only("ring");
        if let Some(typed) = invariant {
            spec.invariants = vec![SpecInvariant::new("Bounded", "(>= 5 0)").with_typed(typed)];
        }
        if let Some(leaf) = temporal {
            spec.temporal = vec![SpecTemporal::new(
                "AlwaysBounded",
                TemporalForm::Always(leaf),
            )];
        }
        spec
    }
    type Place = fn(&mut Module, ProofFormula);
    let sites: [(FormulaSite, Place); 4] = [
        (FormulaSite::Obligation(ProofId::new(CONTRACT)), |m, f| {
            m.proof_obligations[CONTRACT as usize].kind = ObligationKind::RefinementType;
            m.proof_obligations[CONTRACT as usize].status = ProofStatus::Pending;
            m.proof_obligations[CONTRACT as usize].formula = Some(f);
        }),
        (
            FormulaSite::SummaryClause {
                function: FuncId::new(0),
                clause: "ensures",
                index: 0,
            },
            |m, f| m.functions[0].summary = Some(FunctionSummary::new().ensuring(f)),
        ),
        (
            FormulaSite::SpecInvariant {
                machine: "ring".to_string(),
                invariant: "Bounded".to_string(),
            },
            |m, f| m.spec_modules = vec![machine(Some(f), None)],
        ),
        (
            FormulaSite::SpecTemporal {
                machine: "ring".to_string(),
                property: "AlwaysBounded".to_string(),
            },
            |m, f| m.spec_modules = vec![machine(None, Some(f))],
        ),
    ];
    let refused_sites = |module: &Module| {
        let validated: Vec<FormulaSite> = trust_ir_build::validate::validate_module(module)
            .into_iter()
            .filter_map(|error| match error {
                ValidationError::FormulaTextsDisagree { site } => Some(site),
                _ => None,
            })
            .collect();
        let bundled: Vec<FormulaSite> = bundle_for(module.clone(), vec![chc_request()])
            .validate()
            .err()
            .unwrap_or_default()
            .into_iter()
            .filter_map(|error| match error {
                NativeVerificationBundleError::FormulaTextsDisagree { site } => Some(site),
                _ => None,
            })
            .collect();
        (validated, bundled)
    };
    let atom_refused = |formula: ProofFormula| {
        let atom = NativeReplayAtom::assumption(NativeReplayAtomId::new(0), formula);
        bundle_for(
            with_predicates(bare_module()),
            vec![with_replay_atom(chc_request(), atom)],
        )
        .validate()
        .err()
        .unwrap_or_default()
        .contains(&NativeVerificationBundleError::InvalidReplayAtom {
            request: NativeRequestId::new(1),
            atom: NativeReplayAtomId::new(0),
            field: "formula.smtlib",
        })
    };

    let mut wrong = Vec::new();
    for (label, _, formula, two) in &cases {
        for (site, place) in &sites {
            let mut module = with_predicates(bare_module());
            place(&mut module, formula.clone());
            let (validated, bundled) = refused_sites(&module);
            let expected: &[FormulaSite] = if *two {
                std::slice::from_ref(site)
            } else {
                &[]
            };
            if validated != expected || bundled != expected {
                wrong.push(format!(
                    "{label} at {site}: validate_module refused {validated:?}, bundle refused \
                     {bundled:?}, expected {expected:?}"
                ));
            }
        }
        if atom_refused(formula.clone()) != *two {
            wrong.push(format!(
                "{label} as a replay atom: refused {}, expected {two}",
                !*two
            ));
        }
    }
    // A function checked WITHOUT its module has no predicate table: every
    // citation dangles, so an honest rendered `pred.0` clause is refused there
    // (fail-closed) while its module accepts it.
    let mut module = with_predicates(bare_module());
    module.functions[0].summary = Some(FunctionSummary::new().ensuring(pred0.clone()));
    if module.first_formula_stating_two_texts().is_some()
        || module.functions[0]
            .first_formula_stating_two_texts()
            .is_none()
    {
        wrong.push(format!(
            "pred.0 as rendered, on a summary: module-level {:?}, detached function {:?}",
            module.first_formula_stating_two_texts(),
            module.functions[0].first_formula_stating_two_texts()
        ));
    }
    assert!(
        wrong.is_empty(),
        "an owned schema's formula texts:\n{}",
        wrong.join("\n")
    );
}

/// A kernel replay grounds only SMT-LIB2 SOURCE: the contract grounder reads
/// the one text through trust-ir's one SMT-LIB2 reader
/// (`trust_ir::proof::read_smtlib_term`). It used to tokenize on its own,
/// splitting on Rust `char::is_whitespace` and taking any other run of
/// characters as an atom, so each text below was grounded as the text it
/// resembles, kernel-replayed and Established{Unbounded} (measured on
/// dcc5b9a3; the primed case end to end through trust-vc by its r10
/// reverifier), although no SMT-LIB2 reader reads it that way — z3 answers
/// `(declare-const x' Int)` with "unexpected character" and drops the
/// assertion. Controls: SMT-LIB2's own whitespace still reads.
#[cfg(feature = "clean-tv-anchor")]
#[test]
fn a_replay_grounds_only_smtlib2_source() {
    let established = |bundle: &NativeVerificationBundle, certificate: &ProofCertificateRef| {
        let replayed = bundle
            .kernel_replayed_certificates()
            .contains_key(certificate);
        let verdict = coverage_establishment_report(bundle, CoverageInputs::default())
            .for_certificate(certificate);
        (replayed, verdict)
    };
    let mut wrong = Vec::new();
    // The literal family: #0 restated, the ground `(>= 5 0)` term re-bound to
    // it under its recomputed lineage.
    for (case, text, establishes) in [
        ("ideographic spaces", "(>=\u{3000}5\u{3000}0)", false),
        ("vertical tab and form feed", "(>=\u{0b}5\u{0c}0)", false),
        ("no-break space", "(>=\u{a0}5 0)", false),
        ("next line", "(>=\u{85}5 0)", false),
        ("a leading-zero numeral", "(>= 5 00)", false),
        ("control: tab, CR, LF", "(>=\t5\r\n0)", true),
        ("control: plain", "(>= 5 0)", true),
    ] {
        let mut module = bare_module();
        module.proof_obligations[CONTRACT as usize].formula =
            Some(ProofFormula::smtlib2(text, "Bool"));
        let certificate = contract_certificate(&module);
        let reference = certificate.lineage_ref();
        module.proof_certificates.push(certificate);
        let bundle = kernel_bundle(module);
        let (replayed, verdict) = established(&bundle, &reference);
        let is_established = matches!(verdict, CertificateCoverage::Established { .. });
        if replayed != establishes || is_established != establishes {
            wrong.push(format!(
                "{case} {text:?}: replayed {replayed}, verdict {verdict:?}, expected {establishes}"
            ));
        }
    }
    // The free-name nonneg family: `(>= x' 0)` bound `x'` -> a u64 param.
    for (case, text, symbol, establishes) in [
        ("a primed name", "(>= x' 0)", "x'", false),
        ("a primed name, mirrored", "(<= 0 r'')", "r''", false),
        ("an apostrophe inside a name", "(>= a'b 0)", "a'b", false),
        (
            "an SMT-LIB2 reserved word as the name",
            "(>= par 0)",
            "par",
            false,
        ),
        ("control: a plain name", "(>= x_exit 0)", "x_exit", true),
    ] {
        let (bundle, certificate, minted) =
            nonneg_bundle_binding(ProofFormula::smtlib2(text, "Bool"), symbol);
        let (replayed, verdict) = established(&bundle, &certificate);
        let is_established = matches!(verdict, CertificateCoverage::Established { .. });
        if minted != establishes || replayed != establishes || is_established != establishes {
            wrong.push(format!(
                "{case} {text:?}: minted {minted}, replayed {replayed}, verdict {verdict:?}, \
                 expected {establishes}"
            ));
        }
    }
    // `()` has no head: grounding it indexed `items[1..]` of an empty list and
    // aborted the process. It is a refusal.
    for text in ["()", "(())", "(not ())"] {
        let formula = ProofFormula::smtlib2(text, "Bool");
        let goal = std::panic::catch_unwind(|| {
            trust_ir::clean_expr_lowering::contract::contract_goal(
                &ObligationKind::Postcondition,
                Some(&formula),
            )
            .is_ok()
        });
        if !matches!(goal, Ok(false)) {
            wrong.push(format!(
                "{text:?}: contract_goal {}",
                match goal {
                    Ok(true) => "grounded it",
                    _ => "PANICKED",
                }
            ));
        }
    }
    assert!(
        wrong.is_empty(),
        "a replay of a text that is not SMT-LIB2 source:\n{}",
        wrong.join("\n")
    );
}

/// Whether a contract certificate for #0 stating `formula` is kernel-replayed,
/// and whether its coverage is established.
#[cfg(feature = "clean-tv-anchor")]
fn ground_contract_verdict(formula: ProofFormula) -> (bool, bool) {
    let mut module = bare_module();
    module.proof_obligations[CONTRACT as usize].formula = Some(formula);
    let certificate = contract_certificate(&module);
    let reference = certificate.lineage_ref();
    module.proof_certificates.push(certificate);
    let bundle = kernel_bundle(module);
    let replayed = bundle
        .kernel_replayed_certificates()
        .contains_key(&reference);
    let established = matches!(
        coverage_establishment_report(&bundle, CoverageInputs::default())
            .for_certificate(&reference),
        CertificateCoverage::Established { .. }
    );
    (replayed, established)
}

/// A nonneg clause's name is a name trust-ir's one reader reads as a
/// variable. An SMT-LIB2 theory function symbol is none: the Linked spec
/// surface refuses each as a variable (`linked_var_name_problem`), and z3
/// refuses `(declare-const and Int)` ("invalid declaration, builtin symbol").
/// The contract grounder took any simple symbol, so `(>= and 0)` bound `and`
/// -> a u64 param was minted, kernel-replayed and its coverage ESTABLISHED —
/// every theory symbol below was, before. Each row is now minted, replayed
/// and established exactly when the one reader reads it over its binding.
#[cfg(feature = "clean-tv-anchor")]
#[test]
fn a_clause_name_is_a_name_the_one_reader_reads() {
    let mut wrong = Vec::new();
    for name in [
        "and", "or", "xor", "not", "ite", "distinct", "div", "mod", "abs", "bvadd", "bvnot",
        "concat", "x_exit",
    ] {
        let text = format!("(>= {name} 0)");
        let (bundle, certificate, minted) =
            nonneg_bundle_binding(ProofFormula::smtlib2(&text, "Bool"), name);
        let replayed = bundle
            .kernel_replayed_certificates()
            .contains_key(&certificate);
        let established = matches!(
            coverage_establishment_report(&bundle, CoverageInputs::default())
                .for_certificate(&certificate),
            CertificateCoverage::Established { .. }
        );
        let read = trust_ir::spec_surface::check_linked_invariant(
            &text,
            &trust_ir::spec_surface::linked_var_env([(name, "Int")]),
        )
        .is_ok();
        let expected = name == "x_exit";
        if [read, minted, replayed, established] != [expected; 4] {
            wrong.push(format!(
                "{text}: read {read}, minted {minted}, replayed {replayed}, established \
                 {established}, expected {expected}"
            ));
        }
    }
    assert!(wrong.is_empty(), "{}", wrong.join("\n"));
}

/// A formula declared of a sort other than `Bool` states no predicate. The
/// ground `(>= 5 0)` declared of sort `Int` or `(_ BitVec 8)` was grounded as
/// the Bool decision `Nat.ble 0 5` all the same, so its certificate was
/// kernel-replayed and its coverage ESTABLISHED for an obligation that states
/// no predicate. (trust-vc's coverage rule 5 already refuses such a sort.)
#[cfg(feature = "clean-tv-anchor")]
#[test]
fn a_formula_of_another_sort_grounds_nothing() {
    let mut wrong = Vec::new();
    for (sort, expected) in [
        ("Bool", true),
        ("Int", false),
        ("(_ BitVec 8)", false),
        ("bool", false),
    ] {
        let (replayed, established) =
            ground_contract_verdict(ProofFormula::smtlib2("(>= 5 0)", sort));
        if [replayed, established] != [expected; 2] {
            wrong.push(format!(
                "sort {sort:?}: replayed {replayed}, established {established}, expected \
                 {expected}"
            ));
        }
    }
    assert!(wrong.is_empty(), "{}", wrong.join("\n"));
}

/// `and` / `or` take two or more arguments (SMT-LIB2 Core declares both
/// `:left-assoc`), and trust-ir's one reader refuses fewer. The grounder read
/// `(and (>= 5 0))` as `(>= 5 0)`, so the ground contract's certificate was
/// kernel-replayed and its coverage ESTABLISHED for a text no strict SMT-LIB2
/// reader reads. Each row is now replayed and established exactly when the
/// one reader reads it.
#[cfg(feature = "clean-tv-anchor")]
#[test]
fn a_connective_of_one_argument_grounds_nothing() {
    let mut wrong = Vec::new();
    for (text, expected) in [
        ("(and (>= 5 0))", false),
        ("(or (>= 5 0))", false),
        ("(and (>= 5 0) (>= 6 0))", true),
        ("(or (>= 5 0) (>= 0 6))", true),
    ] {
        let read = trust_ir::spec_surface::check_linked_invariant(
            text,
            &trust_ir::spec_surface::linked_var_env(std::iter::empty::<(&str, &str)>()),
        )
        .is_ok();
        let (replayed, established) = ground_contract_verdict(ProofFormula::smtlib2(text, "Bool"));
        if [read, replayed, established] != [expected; 3] {
            wrong.push(format!(
                "{text}: read {read}, replayed {replayed}, established {established}, expected \
                 {expected}"
            ));
        }
    }
    assert!(wrong.is_empty(), "{}", wrong.join("\n"));
}
