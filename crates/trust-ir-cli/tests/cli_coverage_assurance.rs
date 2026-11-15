// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Integration tests for `trust-ir validate --bundle` — the consumer side of
//! `ProofCertificate::assurance`.
//!
//! The row carries a `CoverageBound` plus the `request_digest` of the evidence
//! bundle it was projected FROM, so that the projection is checkable rather
//! than a second source of truth. These tests pin the shipped binary as the
//! reachable entry point for that check: a faithful projection passes, each of
//! the three ways a citation can be wrong exits 1 with a named refusal, and
//! WITHOUT the flag the recorded row is reported UNCHECKED — never as
//! agreement.

mod common;

use std::fs;
use std::path::{Path, PathBuf};

use common::{build_valid_module, trust_ir_cmd};
use tempfile::tempdir;
use trust_ir::Module;
use trust_ir::proof::{
    CoverageAssurance, CoverageBound, ObligationKind, ProofCertificate, ProofDigest, ProofEvidence,
    ProofLineageManifest, ProofObligation, ProofStatus,
};
use trust_ir::request::{
    NativeAdapterInput, NativeBundleProducer, NativeRequestId, NativeVerificationBundle,
    NativeVerificationRequest, TrustMcBmcOptions, TrustMcNativeRequest, TrustMcRequestOptions,
    TrustMcVerificationMode, TrustWpNativeRequest, TrustWpVerificationMode,
};
use trust_ir::value::{FuncId, ProofId};

/// A well-formed module whose single certificate projects `bound` from a
/// TrustMc bounded-model-check request, citing `digest`.
fn fixture(bound: CoverageBound, cite: Option<ProofDigest>) -> (Module, NativeVerificationBundle) {
    let mut module = build_valid_module();
    // An assurance row is a v41 feature, so this module is written as a v41
    // blob — and a v41-or-later producer MUST make a `body_gate` claim for
    // every bodied function (`validate` refuses a tag-0 body by name,
    // `ProducerOmittedBodyGate`). No gate ran on this fixture: say so.
    module.functions[0].body_gate = Some(trust_ir::BodyGate::Ungated);
    let id = ProofId::new(
        module
            .proof_obligations
            .iter()
            .map(|o| o.id.index() + 1)
            .max()
            .unwrap_or(0),
    );
    module.proof_obligations.push(ProofObligation::new(
        id,
        ObligationKind::PanicFreedom,
        ProofStatus::Pending,
        "add must not overflow",
    ));
    let request = NativeVerificationRequest::TrustMc(TrustMcNativeRequest {
        id: NativeRequestId::new(0),
        mode: TrustMcVerificationMode::BoundedModelCheck,
        function: FuncId::new(0),
        obligations: vec![id],
        lineage_roots: Vec::new(),
        options: TrustMcRequestOptions {
            bmc: TrustMcBmcOptions {
                unwind_limit: 1,
                unwinding_assertions: true,
            },
            ..TrustMcRequestOptions::default()
        },
        diagnostics: Default::default(),
        provenance: Default::default(),
    });
    module.proof_certificates.push(ProofCertificate {
        obligation: id,
        prover: "trust-mc".to_string(),
        evidence: ProofEvidence::Trusted("fixture".to_string()),
        assurance: Some(CoverageAssurance {
            bound,
            request_digest: cite.unwrap_or_else(|| request.stable_digest()),
        }),
    });
    let mut bundle = NativeVerificationBundle::new(
        NativeBundleProducer::TrustIr,
        NativeAdapterInput::TrustIrModule,
        module.stable_digest(),
        module.clone(),
        ProofLineageManifest::new(),
    );
    bundle.requests = vec![request];
    (module, bundle)
}

fn write(dir: &Path, module: &Module, bundle: &NativeVerificationBundle) -> (PathBuf, PathBuf) {
    let module_path = dir.join("module.tmbc");
    fs::write(
        &module_path,
        trust_ir::binary::serialize_module(module).expect("serialize_module: test fixture"),
    )
    .expect("write module");
    let bundle_path = dir.join("bundle.json");
    fs::write(
        &bundle_path,
        serde_json::to_vec(bundle).expect("serialize bundle"),
    )
    .expect("write bundle");
    (module_path, bundle_path)
}

/// Run `validate` with the bundle, returning (success, stdout, stderr).
fn run(
    module: &Module,
    bundle: &NativeVerificationBundle,
    with_flag: bool,
) -> (bool, String, String) {
    let dir = tempdir().expect("tempdir");
    let (module_path, bundle_path) = write(dir.path(), module, bundle);
    let mut cmd = trust_ir_cmd();
    cmd.arg("validate");
    if with_flag {
        cmd.arg("--bundle").arg(&bundle_path);
    }
    let output = cmd.arg(&module_path).output().expect("run trust-ir");
    (
        output.status.success(),
        String::from_utf8_lossy(&output.stdout).to_string(),
        String::from_utf8_lossy(&output.stderr).to_string(),
    )
}

/// The adversarial-review scenario, through the shipped binary. The bundle is
/// this module's and holds TWO requests for the same obligation: the depth-1
/// BMC that was run, and a deductive TrustWp request. The certificate claims
/// `Unbounded` and cites the WP one, whose fields determine no bound.
///
/// Exit 0 is correct — nothing is refused, because an honest projection of a
/// method-recording request is not a violation. The OUTPUT is what must not
/// lie: before the fix this printed "1 of 1 recorded row re-derived against
/// the bundle" while holding a bundle that records a depth-1 bounded check for
/// that very obligation.
#[test]
fn an_underived_bound_is_printed_as_undetermined_not_as_re_derived() {
    let (mut module, mut bundle) = fixture(CoverageBound::Unbounded, None);
    let obligation = module.proof_certificates[0].obligation;
    let wp = NativeVerificationRequest::TrustWp(TrustWpNativeRequest {
        id: NativeRequestId::new(1),
        mode: TrustWpVerificationMode::WeakestPrecondition,
        function: FuncId::new(0),
        obligations: vec![obligation],
        lineage_roots: Vec::new(),
        options: Default::default(),
        diagnostics: Default::default(),
        provenance: Default::default(),
    });
    // The producer moves its citation onto the sibling that determines nothing.
    module.proof_certificates[0]
        .assurance
        .as_mut()
        .expect("assurance row")
        .request_digest = wp.stable_digest();
    bundle.requests.push(wp);
    // Re-bind the bundle: rewriting the certificate moved the module digest.
    bundle.trust_ir_module_digest = module.stable_digest();
    bundle.module = module.clone();

    let (ok, stdout, stderr) = run(&module, &bundle, true);
    assert!(ok, "stdout: {stdout}\nstderr: {stderr}");
    assert!(
        stdout.contains("coverage assurance: 0 of 1"),
        "stdout: {stdout}"
    );
    assert!(stdout.contains("1 left UNDETERMINED"), "stdout: {stdout}");
    assert!(stdout.contains("not agreement"), "stdout: {stdout}");
    assert!(
        !stdout.contains("1 of 1 recorded row re-derived"),
        "stdout: {stdout}"
    );
}

#[test]
fn a_faithful_projection_passes_and_reports_the_re_derivation() {
    let (module, bundle) = fixture(CoverageBound::UnwindBounded { depth: 1 }, None);
    let (ok, stdout, stderr) = run(&module, &bundle, true);
    assert!(ok, "stdout: {stdout}\nstderr: {stderr}");
    assert!(
        stdout.contains("coverage assurance: 1 of 1"),
        "stdout: {stdout}"
    );
}

#[test]
fn without_the_flag_a_recorded_row_is_reported_unchecked() {
    // The None-is-not-a-wildcard rule, at the CLI. `Unbounded` here is backed
    // by nothing; the exit code stays 0 because a module separated from its
    // bundle is the normal case, and the OUTPUT is what refuses to call that
    // agreement.
    let (module, bundle) = fixture(CoverageBound::Unbounded, None);
    let (ok, stdout, stderr) = run(&module, &bundle, false);
    assert!(ok, "stdout: {stdout}\nstderr: {stderr}");
    assert!(stdout.contains("UNCHECKED"), "stdout: {stdout}");
    assert!(
        stdout.contains("must not be read as agreement"),
        "stdout: {stdout}"
    );
}

#[test]
fn a_bound_the_cited_request_contradicts_exits_one() {
    let (module, bundle) = fixture(CoverageBound::Unbounded, None);
    let (ok, stdout, stderr) = run(&module, &bundle, true);
    assert!(!ok, "a depth-1 BMC projected as unbounded must fail");
    assert!(
        stderr.contains("coverage assurance failed"),
        "stdout: {stdout}\nstderr: {stderr}"
    );
    assert!(stderr.contains("UnwindBounded { depth: 1 }"), "{stderr}");
}

#[test]
fn a_digest_that_resolves_to_no_request_exits_one() {
    let (module, bundle) = fixture(
        CoverageBound::UnwindBounded { depth: 1 },
        Some(ProofDigest::sha256([3u8; 32])),
    );
    let (ok, _stdout, stderr) = run(&module, &bundle, true);
    assert!(!ok);
    assert!(stderr.contains("matches none of the bundle's"), "{stderr}");
}

#[test]
fn a_bundle_for_another_module_exits_one_and_checks_nothing() {
    let (module, mut bundle) = fixture(CoverageBound::UnwindBounded { depth: 1 }, None);
    bundle.trust_ir_module_digest = ProofDigest::sha256([0x5a; 32]);
    let (ok, _stdout, stderr) = run(&module, &bundle, true);
    assert!(!ok);
    assert!(
        stderr.contains("is not this module's"),
        "the refusal must name what went wrong: {stderr}"
    );
}

#[test]
fn a_citation_about_another_obligation_exits_one() {
    let (mut module, mut bundle) = fixture(CoverageBound::UnwindBounded { depth: 1 }, None);
    // Re-point the bundle's only request at an obligation the certificate does
    // not discharge. The digest still resolves; only the obligation binding
    // catches it.
    let other = ProofId::new(99);
    module.proof_obligations.push(ProofObligation::new(
        other,
        ObligationKind::PanicFreedom,
        ProofStatus::Pending,
        "a different check",
    ));
    if let NativeVerificationRequest::TrustMc(request) = &mut bundle.requests[0] {
        request.obligations = vec![other];
    }
    let cited = bundle.requests[0].stable_digest();
    module.proof_certificates[0].assurance = Some(CoverageAssurance {
        bound: CoverageBound::UnwindBounded { depth: 1 },
        request_digest: cited,
    });
    bundle.trust_ir_module_digest = module.stable_digest();
    let (ok, _stdout, stderr) = run(&module, &bundle, true);
    assert!(!ok);
    assert!(stderr.contains("not this one"), "{stderr}");
}

#[test]
fn a_bundle_path_that_is_not_json_is_an_io_error() {
    let dir = tempdir().expect("tempdir");
    let (module, bundle) = fixture(CoverageBound::UnwindBounded { depth: 1 }, None);
    let (module_path, bundle_path) = write(dir.path(), &module, &bundle);
    fs::write(&bundle_path, b"not a bundle").expect("clobber bundle");
    let output = trust_ir_cmd()
        .arg("validate")
        .arg("--bundle")
        .arg(&bundle_path)
        .arg(&module_path)
        .output()
        .expect("run trust-ir");
    assert!(!output.status.success());
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(stderr.contains("is not valid JSON"), "{stderr}");
}

#[test]
fn a_module_with_no_assurance_rows_and_no_flag_says_nothing() {
    let module = build_valid_module();
    let bundle = NativeVerificationBundle::new(
        NativeBundleProducer::TrustIr,
        NativeAdapterInput::TrustIrModule,
        module.stable_digest(),
        module.clone(),
        ProofLineageManifest::new(),
    );
    let (ok, stdout, stderr) = run(&module, &bundle, false);
    assert!(ok, "stdout: {stdout}\nstderr: {stderr}");
    assert!(
        !stdout.contains("coverage assurance"),
        "no rows and no bundle is not a finding: {stdout}"
    );
}
