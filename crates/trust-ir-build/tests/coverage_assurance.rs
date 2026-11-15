// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0
//
// `ProofCertificate::assurance` / `CoverageAssurance::request_digest` is a
// digest SOMEBODY now re-derives.
//
// The row's own rustdoc states the contract it shipped without: "a consumer
// holding the bundle re-derives the bound and refuses on mismatch, while a
// consumer SEPARATED from its bundle still reads an honest 'depth-1 BMC'
// instead of nothing at all", and `CoverageBound::Unrecorded` adds "an import
// must not gain unbounded standing by omission". Before this rule nothing in
// the repo read `request_digest` outside the codec and one round-trip test, so
// an `UnwindBounded { depth: 1 }` certificate and an `Unbounded` one were
// operationally indistinguishable.
//
// The negatives are the point: a recorded digest that does not re-derive, a
// bundle that is absent (UNCHECKED, and the report says so in words), and an
// assurance citing a request about a DIFFERENT obligation.
//
// `coverage_assurance_report` is DEPRECATED (false provenance: a request's
// mode is not a verified result — see coverage_establishment.rs, whose
// `pending_chc_request_without_evidence_is_not_established` inverts
// `ws1_11_an_unbounded_record_on_a_chc_request_agrees` below). These tests pin
// the legacy rule's behaviour until it is deleted with its last caller.
#![allow(deprecated)]

use trust_ir::inst::Inst;
use trust_ir::node::InstrNode;
use trust_ir::proof::{
    CoverageAssurance, CoverageBound, ObligationKind, ProofCertificate, ProofDigest, ProofEvidence,
    ProofLineageManifest, ProofObligation, ProofStatus,
};
use trust_ir::request::{
    NativeAdapterInput, NativeBundleProducer, NativeRequestId, NativeVerificationBundle,
    NativeVerificationRequest, TrustMcBmcOptions, TrustMcChcOptions, TrustMcNativeRequest,
    TrustMcPdrOptions, TrustMcRequestOptions, TrustMcVerificationMode, TrustVcNativeRequest,
    TrustVcVerificationMode, TrustWpFramePolicy, TrustWpLoopStrategy, TrustWpNativeRequest,
    TrustWpRequestOptions, TrustWpVerificationMode,
};
use trust_ir::ty::FuncTy;
use trust_ir::value::{BlockId, FuncId, ProofId};
use trust_ir::{Block, Function, Module};
use trust_ir_build::validate::{
    ValidationError, coverage_assurance_report, validate_module, validate_module_with_bundle,
};

// ---------------------------------------------------------------------------
// fixtures
// ---------------------------------------------------------------------------

/// A structurally clean module carrying `obligations` panic-freedom rows and
/// one nullary function, so `validate_module_with_bundle` can be measured
/// without unrelated structural noise.
fn module_with(obligations: u32) -> Module {
    let mut module = Module::new("assurance");
    let ft = module
        .add_func_type(FuncTy {
            params: vec![],
            returns: vec![],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut func = Function::new(FuncId::new(0), "f", ft, BlockId::new(0));
    let mut block = Block::new(BlockId::new(0));
    block
        .body
        .push(InstrNode::new(Inst::Return { values: vec![] }));
    func.blocks.push(block);
    module
        .try_add_function(func)
        .expect("Module::try_add_function: test fixture");
    for id in 0..obligations {
        module.proof_obligations.push(ProofObligation::new(
            ProofId::new(id),
            ObligationKind::PanicFreedom,
            ProofStatus::Pending,
            "k",
        ));
    }
    module
}

fn certificate(obligation: u32, assurance: Option<CoverageAssurance>) -> ProofCertificate {
    ProofCertificate {
        obligation: ProofId::new(obligation),
        prover: "trust-mc".to_string(),
        evidence: ProofEvidence::Trusted("fixture".to_string()),
        assurance,
    }
}

/// A TrustMc bounded-model-check request: the ONE request shape whose own
/// fields determine a coverage bound (`unwind_limit`).
fn bmc_request(id: u32, obligations: &[u32], unwind_limit: u32) -> NativeVerificationRequest {
    NativeVerificationRequest::TrustMc(TrustMcNativeRequest {
        id: NativeRequestId::new(id),
        mode: TrustMcVerificationMode::BoundedModelCheck,
        function: FuncId::new(0),
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

/// A deductive TrustWp request under the DEFAULT options — frame policy
/// `BorrowRegions` — a shape whose coverage is NOT determined by the request:
/// that frame may assume a written location unchanged, so the rule leaves it
/// undetermined (WS1.11's fail-closed qualifier). The `FullHeap` shapes that
/// DO determine a bound are built by [`wp_request_with`].
fn wp_request(id: u32, obligations: &[u32]) -> NativeVerificationRequest {
    NativeVerificationRequest::TrustWp(TrustWpNativeRequest {
        id: NativeRequestId::new(id),
        mode: TrustWpVerificationMode::WeakestPrecondition,
        function: FuncId::new(0),
        obligations: obligations.iter().map(|o| ProofId::new(*o)).collect(),
        lineage_roots: Vec::new(),
        options: Default::default(),
        diagnostics: Default::default(),
        provenance: Default::default(),
    })
}

/// A bundle bound to `module` by its stable digest — the precondition every
/// re-derivation rests on.
fn bundle_for(
    module: &Module,
    requests: Vec<NativeVerificationRequest>,
) -> NativeVerificationBundle {
    let mut bundle = NativeVerificationBundle::new(
        NativeBundleProducer::TrustIr,
        NativeAdapterInput::TrustIrModule,
        module.stable_digest(),
        module.clone(),
        ProofLineageManifest::default(),
    );
    bundle.requests = requests;
    bundle
}

// ---------------------------------------------------------------------------
// the positive: a faithful projection re-derives
// ---------------------------------------------------------------------------

#[test]
fn a_faithful_projection_re_derives_and_agrees() {
    let mut module = module_with(1);
    let request = bmc_request(0, &[0], 1);
    module.proof_certificates.push(certificate(
        0,
        Some(CoverageAssurance {
            bound: CoverageBound::UnwindBounded { depth: 1 },
            request_digest: request.stable_digest(),
        }),
    ));
    let bundle = bundle_for(&module, vec![request]);
    let report = coverage_assurance_report(&module, Some(&bundle));
    assert!(report.is_checked());
    assert_eq!((report.recorded(), report.agreed()), (1, 1));
    assert_eq!(report.errors(), Vec::new().as_slice());
    assert!(report.summary().contains("1 of 1"), "{}", report.summary());
}

// ---------------------------------------------------------------------------
// negative 1: recorded digest != re-derived digest
// ---------------------------------------------------------------------------

#[test]
fn a_recorded_digest_that_does_not_re_derive_is_refused() {
    let mut module = module_with(1);
    let request = bmc_request(0, &[0], 1);
    module.proof_certificates.push(certificate(
        0,
        Some(CoverageAssurance {
            bound: CoverageBound::UnwindBounded { depth: 1 },
            request_digest: ProofDigest::sha256([7u8; 32]),
        }),
    ));
    let bundle = bundle_for(&module, vec![request]);
    let report = coverage_assurance_report(&module, Some(&bundle));
    assert!(report.is_checked());
    assert_eq!(report.agreed(), 0);
    assert_eq!(
        report.errors(),
        vec![ValidationError::CoverageAssuranceRequestUnknown {
            obligation: 0,
            recorded: ProofDigest::sha256([7u8; 32]),
            bundle_requests: 1,
        }]
        .as_slice()
    );
}

#[test]
fn a_request_whose_fields_moved_no_longer_re_derives() {
    // The digest is over the request's CONTENT, so a bundle whose request was
    // edited after the projection was stamped stops matching. This is the
    // realistic shape of the failure, as opposed to a garbage digest.
    let mut module = module_with(1);
    let stamped = bmc_request(0, &[0], 1);
    module.proof_certificates.push(certificate(
        0,
        Some(CoverageAssurance {
            bound: CoverageBound::UnwindBounded { depth: 1 },
            request_digest: stamped.stable_digest(),
        }),
    ));
    let shipped = bmc_request(0, &[0], 4);
    assert_ne!(stamped.stable_digest(), shipped.stable_digest());
    let bundle = bundle_for(&module, vec![shipped]);
    let report = coverage_assurance_report(&module, Some(&bundle));
    assert!(matches!(
        report.errors(),
        [ValidationError::CoverageAssuranceRequestUnknown { obligation: 0, .. }]
    ));
}

// ---------------------------------------------------------------------------
// negative 2: no bundle — UNCHECKED, and the report says so
// ---------------------------------------------------------------------------

#[test]
fn an_absent_bundle_leaves_the_assurance_unchecked_and_says_so() {
    let mut module = module_with(1);
    module.proof_certificates.push(certificate(
        0,
        Some(CoverageAssurance {
            // A bound no bundle backs. With no bundle to re-derive against,
            // this is neither confirmed nor refuted — and must not be read as
            // agreement.
            bound: CoverageBound::Unbounded,
            request_digest: ProofDigest::sha256([9u8; 32]),
        }),
    ));
    let report = coverage_assurance_report(&module, None);
    assert!(!report.is_checked(), "no bundle means nothing was checked");
    assert_eq!(report.recorded(), 1);
    assert_eq!(
        report.agreed(),
        0,
        "an unchecked row must never be counted as agreeing"
    );
    assert_eq!(report.errors(), Vec::new().as_slice());
    let summary = report.summary();
    assert!(summary.contains("UNCHECKED"), "{summary}");
    assert!(
        summary.contains("must not be read as agreement"),
        "{summary}"
    );
    // And the structural pass stays silent about it: a module carrying an
    // assurance row is well-formed, which is the whole reason the check needs
    // a bundle-bearing entry point.
    assert_eq!(validate_module(&module), Vec::new());
}

#[test]
fn a_bundle_for_a_different_module_is_refused_and_checks_nothing() {
    let mut module = module_with(1);
    let request = bmc_request(0, &[0], 1);
    module.proof_certificates.push(certificate(
        0,
        Some(CoverageAssurance {
            bound: CoverageBound::UnwindBounded { depth: 1 },
            request_digest: request.stable_digest(),
        }),
    ));
    let other = module_with(0);
    let mut bundle = bundle_for(&other, vec![request]);
    bundle.module = module.clone();
    let report = coverage_assurance_report(&module, Some(&bundle));
    assert!(
        !report.is_checked(),
        "a bundle about another module checks nothing"
    );
    assert_eq!(report.agreed(), 0);
    assert!(matches!(
        report.errors(),
        [ValidationError::NativeBundleNotForThisModule { .. }]
    ));
}

// ---------------------------------------------------------------------------
// negative 3: the assurance cites a bundle request for a DIFFERENT obligation
// ---------------------------------------------------------------------------

#[test]
fn an_assurance_citing_another_obligations_request_is_refused() {
    let mut module = module_with(2);
    // Two requests in one bundle, as a real handoff has. Obligation 1's
    // certificate projects its bound from obligation 0's request.
    let zero = bmc_request(0, &[0], 1);
    let one = bmc_request(1, &[1], 1);
    module.proof_certificates.push(certificate(
        1,
        Some(CoverageAssurance {
            bound: CoverageBound::UnwindBounded { depth: 1 },
            request_digest: zero.stable_digest(),
        }),
    ));
    let bundle = bundle_for(&module, vec![zero, one]);
    let report = coverage_assurance_report(&module, Some(&bundle));
    assert!(report.is_checked());
    assert_eq!(report.agreed(), 0);
    assert_eq!(
        report.errors(),
        vec![ValidationError::CoverageAssuranceObligationNotRequested {
            obligation: 1,
            request: 0,
            request_obligations: vec![0],
        }]
        .as_slice(),
        "the digest alone resolves; only the obligation binding catches this"
    );
}

// ---------------------------------------------------------------------------
// the bound itself
// ---------------------------------------------------------------------------

#[test]
fn a_bound_the_cited_request_contradicts_is_refused() {
    // The sentence from the rustdoc, as a test: a depth-1 BMC and an unbounded
    // proof must stop being indistinguishable.
    let mut module = module_with(1);
    let request = bmc_request(0, &[0], 1);
    module.proof_certificates.push(certificate(
        0,
        Some(CoverageAssurance {
            bound: CoverageBound::Unbounded,
            request_digest: request.stable_digest(),
        }),
    ));
    let bundle = bundle_for(&module, vec![request]);
    let report = coverage_assurance_report(&module, Some(&bundle));
    assert_eq!(
        report.errors(),
        vec![ValidationError::CoverageAssuranceBoundMismatch {
            obligation: 0,
            recorded: "Unbounded".to_string(),
            derived: "UnwindBounded { depth: 1 }".to_string(),
        }]
        .as_slice()
    );
}

#[test]
fn unrecorded_is_not_a_wildcard_against_a_request_that_states_a_depth() {
    // `Unrecorded` is an honest reading for a row that never projected
    // anything. It is NOT an honest reading for a row whose entire purpose is
    // to project a bundle that states `unwind_limit`.
    let mut module = module_with(1);
    let request = bmc_request(0, &[0], 3);
    module.proof_certificates.push(certificate(
        0,
        Some(CoverageAssurance {
            bound: CoverageBound::Unrecorded,
            request_digest: request.stable_digest(),
        }),
    ));
    let bundle = bundle_for(&module, vec![request]);
    assert!(matches!(
        coverage_assurance_report(&module, Some(&bundle)).errors(),
        [ValidationError::CoverageAssuranceBoundMismatch { .. }]
    ));
}

#[test]
fn a_depth_that_disagrees_with_the_requests_unwind_limit_is_refused() {
    let mut module = module_with(1);
    let request = bmc_request(0, &[0], 8);
    module.proof_certificates.push(certificate(
        0,
        Some(CoverageAssurance {
            bound: CoverageBound::UnwindBounded { depth: 7 },
            request_digest: request.stable_digest(),
        }),
    ));
    let bundle = bundle_for(&module, vec![request]);
    let errors = coverage_assurance_report(&module, Some(&bundle)).into_errors();
    assert!(matches!(
        errors.as_slice(),
        [ValidationError::CoverageAssuranceBoundMismatch { .. }]
    ));
    assert!(errors[0].to_string().contains("depth: 8"), "{}", errors[0]);
}

#[test]
fn a_request_shape_that_determines_no_bound_leaves_the_bound_unchecked() {
    // TrustWp is deductive: the bundle records a METHOD, not a bound. The
    // citation and the obligation binding are still checked — only the bound
    // is left alone, deliberately, because refusing an honest under-claim is
    // the wrong direction for a fail-closed rule.
    //
    // And "left alone" is reported as itself. `agreed()` is 0 and
    // `undetermined()` is 1 for EVERY bound, including the four mutually
    // contradictory ones below: if an underived bound counted as agreement,
    // this loop would report all four as re-derived against the same request,
    // which is arithmetically impossible and is exactly the conflation
    // `is_checked()` refuses at table granularity.
    for bound in [
        CoverageBound::Unbounded,
        CoverageBound::UnwindBounded { depth: 1 },
        CoverageBound::Unrecorded,
        CoverageBound::ModelBounded { size: 12 },
    ] {
        let mut module = module_with(1);
        let request = wp_request(0, &[0]);
        module.proof_certificates.push(certificate(
            0,
            Some(CoverageAssurance {
                bound,
                request_digest: request.stable_digest(),
            }),
        ));
        let bundle = bundle_for(&module, vec![request]);
        let report = coverage_assurance_report(&module, Some(&bundle));
        assert_eq!(report.errors(), Vec::new().as_slice(), "{bound:?}");
        assert_eq!(
            (report.recorded(), report.agreed(), report.undetermined()),
            (1, 0, 1),
            "{bound:?}"
        );
        // The printed line must not claim a derivation that did not happen.
        let summary = report.summary();
        assert!(summary.contains("0 of 1"), "{bound:?}: {summary}");
        assert!(
            summary.contains("1 left UNDETERMINED"),
            "{bound:?}: {summary}"
        );
    }
}

#[test]
fn a_wp_request_is_still_bound_to_its_own_obligation() {
    let mut module = module_with(2);
    let zero = wp_request(0, &[0]);
    let one = wp_request(1, &[1]);
    module.proof_certificates.push(certificate(
        1,
        Some(CoverageAssurance {
            bound: CoverageBound::Unbounded,
            request_digest: zero.stable_digest(),
        }),
    ));
    let bundle = bundle_for(&module, vec![zero, one]);
    assert!(matches!(
        coverage_assurance_report(&module, Some(&bundle)).errors(),
        [ValidationError::CoverageAssuranceObligationNotRequested { .. }]
    ));
}

// ---------------------------------------------------------------------------
// reachability and composition
// ---------------------------------------------------------------------------

#[test]
fn validate_module_with_bundle_composes_structure_then_assurance() {
    let mut module = module_with(1);
    let request = bmc_request(0, &[0], 1);
    module.proof_certificates.push(certificate(
        0,
        Some(CoverageAssurance {
            bound: CoverageBound::Unbounded,
            request_digest: request.stable_digest(),
        }),
    ));
    let bundle = bundle_for(&module, vec![request]);
    // Structurally clean...
    assert_eq!(validate_module(&module), Vec::new());
    // ...and refused once its bundle is in hand. This is the reachability the
    // residual ledger required: the rule runs from an entry point a consumer
    // holding the bundle actually calls, not a helper nobody calls.
    assert_eq!(
        validate_module_with_bundle(&module, &bundle),
        vec![ValidationError::CoverageAssuranceBoundMismatch {
            obligation: 0,
            recorded: "Unbounded".to_string(),
            derived: "UnwindBounded { depth: 1 }".to_string(),
        }]
    );
}

#[test]
fn certificates_without_an_assurance_row_are_neither_counted_nor_checked() {
    let mut module = module_with(1);
    module.proof_certificates.push(certificate(0, None));
    let bundle = bundle_for(&module, vec![bmc_request(0, &[0], 1)]);
    let report = coverage_assurance_report(&module, Some(&bundle));
    assert_eq!((report.recorded(), report.agreed()), (0, 0));
    assert_eq!(report.errors(), Vec::new().as_slice());
    // `None` = NOT RECORDED. It is not a violation to omit the row; it is a
    // violation to read the omission as unbounded standing, which is what
    // `recorded() == 0` plus `is_checked()` lets a caller see.
    assert!(report.is_checked());
    assert!(report.summary().contains("0 of 0"), "{}", report.summary());
}

#[test]
fn every_offending_row_is_reported_once_in_module_order() {
    let mut module = module_with(3);
    let zero = bmc_request(0, &[0], 1);
    module.proof_certificates.push(certificate(
        0,
        Some(CoverageAssurance {
            bound: CoverageBound::UnwindBounded { depth: 1 },
            request_digest: zero.stable_digest(),
        }),
    ));
    module.proof_certificates.push(certificate(
        1,
        Some(CoverageAssurance {
            bound: CoverageBound::Unbounded,
            request_digest: ProofDigest::sha256([1u8; 32]),
        }),
    ));
    module.proof_certificates.push(certificate(
        2,
        Some(CoverageAssurance {
            bound: CoverageBound::Unbounded,
            request_digest: zero.stable_digest(),
        }),
    ));
    let bundle = bundle_for(&module, vec![zero]);
    let report = coverage_assurance_report(&module, Some(&bundle));
    assert_eq!((report.recorded(), report.agreed()), (3, 1));
    let offenders: Vec<u32> = report
        .errors()
        .iter()
        .map(|e| match e {
            ValidationError::CoverageAssuranceRequestUnknown { obligation, .. }
            | ValidationError::CoverageAssuranceObligationNotRequested { obligation, .. }
            | ValidationError::CoverageAssuranceBoundMismatch { obligation, .. } => *obligation,
            other => panic!("unexpected {other:?}"),
        })
        .collect();
    assert_eq!(offenders, vec![1, 2]);
}

// ---------------------------------------------------------------------------
// the row whose bound the bundle never establishes is NOT agreement
//
// Reported by adversarial review of the rule that landed in de03d78: the
// `bound_determined_by_request(..) == None` arm fell through to `agreed += 1`,
// so a row whose bound was never looked at was counted — and PRINTED — as
// "re-derived against the bundle". That reproduced, at row granularity, the
// exact absence-read-as-agreement conflation `is_checked()` exists to prevent
// at table granularity, and contradicted `agreed()`'s own documented contract.
//
// The narrowness of `bound_determined_by_request` is not the defect and was not
// changed by that fix. (WS1.11 later widened it by exactly the request shapes
// that NAME an unbounded procedure — see the section at the end of this file —
// and the default-options TrustWp request used below is deliberately still
// outside it.) Leaving such a row unchecked is right; leaving it invisible is
// not.
// ---------------------------------------------------------------------------

/// The review's scenario, at the level the CLI prints: the bundle is correctly
/// bound to this module and holds TWO requests for the SAME obligation — the
/// depth-1 BMC that was actually run, and a TrustWp request. The certificate
/// claims `Unbounded` and cites the WP one.
///
/// Every check the rule can make passes, so there is no refusal and there
/// should not be: the row is an honest projection of a request that determines
/// no bound. What must NOT happen is the operator being told it re-derived,
/// while the very bundle in hand records a depth-1 bounded check for that
/// obligation.
#[test]
fn a_sibling_citation_that_determines_no_bound_is_not_reported_as_re_derived() {
    let mut module = module_with(1);
    let bmc = bmc_request(0, &[0], 1);
    let wp = wp_request(1, &[0]);
    module.proof_certificates.push(certificate(
        0,
        Some(CoverageAssurance {
            bound: CoverageBound::Unbounded,
            request_digest: wp.stable_digest(),
        }),
    ));
    let bundle = bundle_for(&module, vec![bmc, wp]);

    let report = coverage_assurance_report(&module, Some(&bundle));
    assert!(report.is_checked());
    assert_eq!(report.errors(), Vec::new().as_slice());
    assert_eq!(
        (report.recorded(), report.agreed(), report.undetermined()),
        (1, 0, 1)
    );
    let summary = report.summary();
    assert!(
        summary.contains("0 of 1 recorded row re-derived against the bundle"),
        "{summary}"
    );
    assert!(summary.contains("1 left UNDETERMINED"), "{summary}");
    assert!(summary.contains("not agreement"), "{summary}");

    // The whole point: a consumer whose gate requires the bound to have been
    // ESTABLISHED refuses this artifact, while the refusal-list entry point
    // (correctly) reports nothing to refuse.
    assert!(validate_module_with_bundle(&module, &bundle).is_empty());
    assert!(!(report.is_checked() && report.errors().is_empty() && report.undetermined() == 0));
}

/// The same module, with the certificate citing the BMC request that was
/// actually run: now the over-claim is REFUSED. This is the pair that shows the
/// hazard is real rather than hypothetical — the producer chooses which
/// `request_digest` to record, and the only thing standing between the two
/// outcomes is that choice.
#[test]
fn citing_the_bmc_sibling_instead_refuses_the_same_over_claim() {
    let mut module = module_with(1);
    let bmc = bmc_request(0, &[0], 1);
    let wp = wp_request(1, &[0]);
    module.proof_certificates.push(certificate(
        0,
        Some(CoverageAssurance {
            bound: CoverageBound::Unbounded,
            request_digest: bmc.stable_digest(),
        }),
    ));
    let bundle = bundle_for(&module, vec![bmc, wp]);
    let report = coverage_assurance_report(&module, Some(&bundle));
    assert_eq!(
        (report.recorded(), report.agreed(), report.undetermined()),
        (1, 0, 0)
    );
    assert!(matches!(
        report.errors(),
        [ValidationError::CoverageAssuranceBoundMismatch { .. }]
    ));
}

/// Every recorded row takes exactly ONE of the per-row exits, so the three
/// counts plus the refusals account for all of them. Without this, a future
/// arm could be added that is counted twice or not at all — and a count that
/// does not add up is how the original defect hid: `agreed` silently absorbed
/// a fourth outcome.
#[test]
fn the_three_counts_and_the_refusals_partition_the_recorded_rows() {
    let mut module = module_with(4);
    let bmc = bmc_request(0, &[0, 1, 2, 3], 1);
    let wp = wp_request(1, &[0, 1, 2, 3]);
    // agreed
    module.proof_certificates.push(certificate(
        0,
        Some(CoverageAssurance {
            bound: CoverageBound::UnwindBounded { depth: 1 },
            request_digest: bmc.stable_digest(),
        }),
    ));
    // undetermined
    module.proof_certificates.push(certificate(
        1,
        Some(CoverageAssurance {
            bound: CoverageBound::Unbounded,
            request_digest: wp.stable_digest(),
        }),
    ));
    // refused (bound mismatch)
    module.proof_certificates.push(certificate(
        2,
        Some(CoverageAssurance {
            bound: CoverageBound::Unbounded,
            request_digest: bmc.stable_digest(),
        }),
    ));
    // refused (citation does not resolve)
    module.proof_certificates.push(certificate(
        3,
        Some(CoverageAssurance {
            bound: CoverageBound::Unbounded,
            request_digest: ProofDigest::sha256([7u8; 32]),
        }),
    ));
    // not recorded at all: counted by none of the three.
    module.proof_certificates.push(certificate(3, None));

    let bundle = bundle_for(&module, vec![bmc, wp]);
    let report = coverage_assurance_report(&module, Some(&bundle));
    assert_eq!(
        (report.recorded(), report.agreed(), report.undetermined()),
        (4, 1, 1)
    );
    assert_eq!(report.errors().len(), 2);
    assert_eq!(
        report.recorded(),
        report.agreed() + report.undetermined() + report.errors().len()
    );
    let summary = report.summary();
    assert!(summary.contains("1 of 4"), "{summary}");
    assert!(summary.contains("1 left UNDETERMINED"), "{summary}");
    assert!(summary.contains("2 refusals"), "{summary}");
}

/// `into_errors()` drops everything that is not a refusal, so an empty `Vec`
/// must never be reachable from a SUPPLIED bundle that checked nothing. It is
/// not: the one unchecked path under `Some(bundle)` is the module-digest
/// mismatch, which carries its own refusal.
#[test]
fn a_supplied_bundle_is_either_checked_or_carries_a_refusal() {
    let mut module = module_with(1);
    let request = bmc_request(0, &[0], 1);
    module.proof_certificates.push(certificate(
        0,
        Some(CoverageAssurance {
            bound: CoverageBound::UnwindBounded { depth: 1 },
            request_digest: request.stable_digest(),
        }),
    ));
    // Bound to this module: checked.
    let ours = bundle_for(&module, vec![request.clone()]);
    let report = coverage_assurance_report(&module, Some(&ours));
    assert!(report.is_checked() || !report.clone().into_errors().is_empty());

    // Bound to another module: UNCHECKED, and the reduction still carries the
    // refusal, so no caller can be handed a silently-empty list.
    let other = bundle_for(&module_with(2), vec![request]);
    let report = coverage_assurance_report(&module, Some(&other));
    assert!(!report.is_checked());
    assert_eq!((report.agreed(), report.undetermined()), (0, 0));
    assert!(report.is_checked() || !report.clone().into_errors().is_empty());
    assert!(matches!(
        report.into_errors().as_slice(),
        [ValidationError::NativeBundleNotForThisModule { .. }]
    ));
}

// ---------------------------------------------------------------------------
// WS1.11 — the coverage bound is re-derivable beyond TrustMc BMC
//
// `bound_determined_by_request` used to return `Some` for a TrustMc
// bounded-model-check request only, so an `Unbounded` row was never
// re-derivable: it was UNDETERMINED against every request that could honestly
// back it (proof program row `b2.gap.unbounded_coverage_claim_not_rederivable`,
// finding F-020). The rule now derives `Unbounded` from the request shapes that
// NAME an unbounded procedure — TrustMc CHC and PDR, and TrustWp weakest-
// precondition under a whole-heap frame — and nothing else.
//
// Every arm has its own test, because mislabelling a bounded procedure
// `Unbounded` is the unsound direction. The undetermined arms are tested as
// hard as the determined ones: each asserts `(recorded, agreed, undetermined)`
// = (1, 0, 1) with NO refusal, for every recorded bound.
// ---------------------------------------------------------------------------

/// Every coverage bound a row can record — the sweep the undetermined arms
/// are checked against, so no arm can be "undetermined for Unbounded only".
const EVERY_BOUND: [CoverageBound; 4] = [
    CoverageBound::Unbounded,
    CoverageBound::UnwindBounded { depth: 1 },
    CoverageBound::Unrecorded,
    CoverageBound::ModelBounded { size: 12 },
];

/// A TrustMc request in `mode` whose options are the ones
/// `NativeVerificationBundle::validate` requires of that mode (CHC and PDR
/// emit Horn clauses; PDR is enabled), with the PDR frame cap `max_frames`.
fn mc_request(
    id: u32,
    obligations: &[u32],
    mode: TrustMcVerificationMode,
    max_frames: Option<u32>,
) -> NativeVerificationRequest {
    NativeVerificationRequest::TrustMc(TrustMcNativeRequest {
        id: NativeRequestId::new(id),
        mode,
        function: FuncId::new(0),
        obligations: obligations.iter().map(|o| ProofId::new(*o)).collect(),
        lineage_roots: Vec::new(),
        options: TrustMcRequestOptions {
            chc: TrustMcChcOptions {
                pdr: TrustMcPdrOptions {
                    enabled: mode == TrustMcVerificationMode::Pdr,
                    max_frames,
                    ..TrustMcPdrOptions::default()
                },
                emit_horn_clauses: true,
                ..TrustMcChcOptions::default()
            },
            ..TrustMcRequestOptions::default()
        },
        diagnostics: Default::default(),
        provenance: Default::default(),
    })
}

/// A TrustWp request with an explicit mode, loop strategy and frame policy.
fn wp_request_with(
    id: u32,
    obligations: &[u32],
    mode: TrustWpVerificationMode,
    loop_strategy: TrustWpLoopStrategy,
    frame_policy: TrustWpFramePolicy,
) -> NativeVerificationRequest {
    NativeVerificationRequest::TrustWp(TrustWpNativeRequest {
        id: NativeRequestId::new(id),
        mode,
        function: FuncId::new(0),
        obligations: obligations.iter().map(|o| ProofId::new(*o)).collect(),
        lineage_roots: Vec::new(),
        options: TrustWpRequestOptions {
            loop_strategy,
            frame_policy,
            ..TrustWpRequestOptions::default()
        },
        diagnostics: Default::default(),
        provenance: Default::default(),
    })
}

/// A TrustVc request in `mode`.
fn vc_request(
    id: u32,
    obligations: &[u32],
    mode: TrustVcVerificationMode,
) -> NativeVerificationRequest {
    NativeVerificationRequest::TrustVc(TrustVcNativeRequest {
        id: NativeRequestId::new(id),
        mode,
        obligations: obligations.iter().map(|o| ProofId::new(*o)).collect(),
        certificates: Vec::new(),
        lineage_roots: Vec::new(),
        options: Default::default(),
        diagnostics: Default::default(),
        provenance: Default::default(),
        function: None,
    })
}

/// One module, one obligation, one certificate recording `bound` against
/// `request`, and the bundle holding `request`: the report over it.
fn report_for(
    bound: CoverageBound,
    request: NativeVerificationRequest,
) -> trust_ir_build::validate::CoverageAssuranceReport {
    let mut module = module_with(1);
    module.proof_certificates.push(certificate(
        0,
        Some(CoverageAssurance {
            bound,
            request_digest: request.stable_digest(),
        }),
    ));
    let bundle = bundle_for(&module, vec![request]);
    coverage_assurance_report(&module, Some(&bundle))
}

/// The row was re-derived and AGREES: checked, (1, 1, 0), no refusal.
fn assert_agrees(report: &trust_ir_build::validate::CoverageAssuranceReport, what: &str) {
    assert!(report.is_checked(), "{what}");
    assert_eq!(report.errors(), Vec::new().as_slice(), "{what}");
    assert_eq!(
        (report.recorded(), report.agreed(), report.undetermined()),
        (1, 1, 0),
        "{what}: {}",
        report.summary()
    );
    assert!(
        report.summary().contains("1 of 1"),
        "{what}: {}",
        report.summary()
    );
}

/// The row's bound was NOT re-derived: checked, (1, 0, 1), no refusal.
fn assert_undetermined(report: &trust_ir_build::validate::CoverageAssuranceReport, what: &str) {
    assert!(report.is_checked(), "{what}");
    assert_eq!(report.errors(), Vec::new().as_slice(), "{what}");
    assert_eq!(
        (report.recorded(), report.agreed(), report.undetermined()),
        (1, 0, 1),
        "{what}: {}",
        report.summary()
    );
}

/// The row was re-derived and REFUSED with the named mismatch, naming the
/// recorded bound and the one the request actually derives.
fn assert_mismatch(
    report: &trust_ir_build::validate::CoverageAssuranceReport,
    recorded: &str,
    derived: &str,
) {
    assert!(report.is_checked());
    assert_eq!(
        (report.recorded(), report.agreed(), report.undetermined()),
        (1, 0, 0)
    );
    assert_eq!(
        report.errors(),
        vec![ValidationError::CoverageAssuranceBoundMismatch {
            obligation: 0,
            recorded: recorded.to_string(),
            derived: derived.to_string(),
        }]
        .as_slice()
    );
}

// --- the positive, and one test per new `Unbounded` arm ---------------------

/// The increment's POSITIVE: an `Unbounded` record on a PDR request agrees. A
/// PDR/IC3 "safe" verdict is an inductive invariant — unreachability at every
/// depth.
#[test]
fn ws1_11_an_unbounded_record_on_a_pdr_request_agrees() {
    let report = report_for(
        CoverageBound::Unbounded,
        mc_request(0, &[0], TrustMcVerificationMode::Pdr, None),
    );
    assert_agrees(&report, "Unbounded on PDR");
}

/// A CHC "valid" verdict is a model of the Horn clauses: unbounded.
#[test]
fn ws1_11_an_unbounded_record_on_a_chc_request_agrees() {
    let report = report_for(
        CoverageBound::Unbounded,
        mc_request(0, &[0], TrustMcVerificationMode::Chc, None),
    );
    assert_agrees(&report, "Unbounded on CHC");
}

/// The frame cap bounds the SEARCH, not the verdict: a PDR run that hits
/// `max_frames` without a fixpoint returns unknown and discharges nothing, so a
/// discharge that DID come from a capped request is still an inductive
/// invariant. The cap must not turn the derivation into a depth.
#[test]
fn ws1_11_a_frame_capped_pdr_request_still_derives_unbounded() {
    for mode in [TrustMcVerificationMode::Pdr, TrustMcVerificationMode::Chc] {
        let report = report_for(CoverageBound::Unbounded, mc_request(0, &[0], mode, Some(8)));
        assert_agrees(
            &report,
            &format!("Unbounded on {mode:?} with max_frames = 8"),
        );
        let report = report_for(
            CoverageBound::UnwindBounded { depth: 8 },
            mc_request(0, &[0], mode, Some(8)),
        );
        assert_mismatch(&report, "UnwindBounded { depth: 8 }", "Unbounded");
    }
}

#[test]
fn ws1_11_wp_full_heap_require_invariants_derives_unbounded() {
    let report = report_for(
        CoverageBound::Unbounded,
        wp_request_with(
            0,
            &[0],
            TrustWpVerificationMode::WeakestPrecondition,
            TrustWpLoopStrategy::RequireInvariants,
            TrustWpFramePolicy::FullHeap,
        ),
    );
    assert_agrees(&report, "WP / RequireInvariants / FullHeap");
}

#[test]
fn ws1_11_wp_full_heap_infer_invariants_derives_unbounded() {
    let report = report_for(
        CoverageBound::Unbounded,
        wp_request_with(
            0,
            &[0],
            TrustWpVerificationMode::WeakestPrecondition,
            TrustWpLoopStrategy::InferInvariants,
            TrustWpFramePolicy::FullHeap,
        ),
    );
    assert_agrees(&report, "WP / InferInvariants / FullHeap");
}

/// Havoc over-approximates the loop by forgetting everything it may write —
/// and under a whole-heap frame "everything it may write" is everything.
#[test]
fn ws1_11_wp_full_heap_havoc_derives_unbounded() {
    let report = report_for(
        CoverageBound::Unbounded,
        wp_request_with(
            0,
            &[0],
            TrustWpVerificationMode::WeakestPrecondition,
            TrustWpLoopStrategy::Havoc,
            TrustWpFramePolicy::FullHeap,
        ),
    );
    assert_agrees(&report, "WP / Havoc / FullHeap");
}

// --- the negative twin ------------------------------------------------------

/// The increment's NEGATIVE TWIN: the positive's record, citing a BMC request
/// instead, is refused with the named mismatch — a depth-1 BMC is not an
/// unbounded proof, and the widening must not have made it one.
#[test]
fn ws1_11_an_unbounded_record_on_a_bmc_request_is_a_mismatch() {
    let report = report_for(CoverageBound::Unbounded, bmc_request(0, &[0], 1));
    assert_mismatch(&report, "Unbounded", "UnwindBounded { depth: 1 }");
}

/// Equality, not a partial order, on the new arms too: an unbounded procedure
/// is not projected as a bounded one, nor as `Unrecorded`, nor as a model
/// bound.
#[test]
fn ws1_11_a_non_unbounded_record_on_an_unbounded_request_is_a_mismatch() {
    let unbounded_requests = [
        mc_request(0, &[0], TrustMcVerificationMode::Pdr, None),
        mc_request(0, &[0], TrustMcVerificationMode::Chc, None),
        wp_request_with(
            0,
            &[0],
            TrustWpVerificationMode::WeakestPrecondition,
            TrustWpLoopStrategy::Havoc,
            TrustWpFramePolicy::FullHeap,
        ),
    ];
    for request in unbounded_requests {
        for bound in EVERY_BOUND {
            if bound == CoverageBound::Unbounded {
                continue;
            }
            let report = report_for(bound, request.clone());
            assert_mismatch(&report, &format!("{bound:?}"), "Unbounded");
        }
    }
}

// --- the mutation controls --------------------------------------------------

/// MUTATION CONTROL: the same `Unbounded` record, the same obligation, the
/// request mode flipped PDR → BMC and nothing else. The verdict flips from
/// agreement to the named refusal, so it is the MODE that the rule reads.
#[test]
fn ws1_11_flipping_the_request_mode_pdr_to_bmc_flips_the_verdict() {
    let pdr = mc_request(0, &[0], TrustMcVerificationMode::Pdr, None);
    let NativeVerificationRequest::TrustMc(mut flipped) = pdr.clone() else {
        unreachable!("mc_request builds a TrustMc request")
    };
    flipped.mode = TrustMcVerificationMode::BoundedModelCheck;
    let bmc = NativeVerificationRequest::TrustMc(flipped);
    assert_agrees(&report_for(CoverageBound::Unbounded, pdr), "PDR");
    // `mc_request` leaves `bmc.unwind_limit` at its default of 1.
    assert_mismatch(
        &report_for(CoverageBound::Unbounded, bmc),
        "Unbounded",
        "UnwindBounded { depth: 1 }",
    );
}

/// MUTATION CONTROL: every TrustVc mode stays UNDETERMINED for every recorded
/// bound — TrustVc imports, merges or discharges certificates somebody else
/// scoped, so its coverage is whatever that certificate claims, not a request
/// field.
#[test]
fn ws1_11_every_trust_vc_mode_stays_undetermined() {
    for mode in [
        TrustVcVerificationMode::ImportProofCertificates,
        TrustVcVerificationMode::MergeProofCertificates,
        TrustVcVerificationMode::DischargeProofObligations,
    ] {
        for bound in EVERY_BOUND {
            let report = report_for(bound, vc_request(0, &[0], mode));
            assert_undetermined(&report, &format!("TrustVc {mode:?} / {bound:?}"));
        }
    }
}

/// MUTATION CONTROL, the fail-closed qualifier: a WP/Havoc request under frame
/// `Minimal` stays UNDETERMINED, while the same request with only the frame
/// flipped to `FullHeap` agrees. A frame that may assume a written location
/// unchanged makes the WP proof partial, and labelling it `Unbounded` is the
/// unsound direction.
#[test]
fn ws1_11_wp_havoc_minimal_frame_stays_undetermined_while_full_heap_agrees() {
    let minimal = wp_request_with(
        0,
        &[0],
        TrustWpVerificationMode::WeakestPrecondition,
        TrustWpLoopStrategy::Havoc,
        TrustWpFramePolicy::Minimal,
    );
    let NativeVerificationRequest::TrustWp(mut flipped) = minimal.clone() else {
        unreachable!("wp_request_with builds a TrustWp request")
    };
    flipped.options.frame_policy = TrustWpFramePolicy::FullHeap;
    let full_heap = NativeVerificationRequest::TrustWp(flipped);
    assert_undetermined(
        &report_for(CoverageBound::Unbounded, minimal),
        "WP / Havoc / Minimal",
    );
    assert_agrees(
        &report_for(CoverageBound::Unbounded, full_heap),
        "WP / Havoc / FullHeap",
    );
}

/// `Minimal` and `BorrowRegions` stay undetermined under EVERY loop strategy
/// and for every recorded bound — no loop treatment rescues a partial frame.
#[test]
fn ws1_11_wp_minimal_and_borrow_regions_frames_stay_undetermined() {
    for frame in [
        TrustWpFramePolicy::Minimal,
        TrustWpFramePolicy::BorrowRegions,
    ] {
        for strategy in [
            TrustWpLoopStrategy::RequireInvariants,
            TrustWpLoopStrategy::InferInvariants,
            TrustWpLoopStrategy::Havoc,
        ] {
            for bound in EVERY_BOUND {
                let request = wp_request_with(
                    0,
                    &[0],
                    TrustWpVerificationMode::WeakestPrecondition,
                    strategy,
                    frame,
                );
                assert_undetermined(
                    &report_for(bound, request),
                    &format!("WP / {strategy:?} / {frame:?} / {bound:?}"),
                );
            }
        }
    }
}

/// Strongest-postcondition and abduction stay undetermined EVEN under a
/// whole-heap frame: the frame qualifier licenses only weakest-precondition.
#[test]
fn ws1_11_strongest_postcondition_stays_undetermined() {
    for bound in EVERY_BOUND {
        let request = wp_request_with(
            0,
            &[0],
            TrustWpVerificationMode::StrongestPostcondition,
            TrustWpLoopStrategy::RequireInvariants,
            TrustWpFramePolicy::FullHeap,
        );
        assert_undetermined(&report_for(bound, request), &format!("SP / {bound:?}"));
    }
}

#[test]
fn ws1_11_abduction_stays_undetermined() {
    for bound in EVERY_BOUND {
        let request = wp_request_with(
            0,
            &[0],
            TrustWpVerificationMode::Abduction,
            TrustWpLoopStrategy::RequireInvariants,
            TrustWpFramePolicy::FullHeap,
        );
        assert_undetermined(
            &report_for(bound, request),
            &format!("Abduction / {bound:?}"),
        );
    }
}

// --- the GAP row, ported ----------------------------------------------------

/// Port of proof-program row `b2.gap.unbounded_coverage_claim_not_rederivable`
/// (partb `b2_contracts_obligations.rs`, `b2_14` part (d)).
///
/// The archived row built four assurance rows — `Unbounded` citing a TrustWp
/// request, `UnwindBounded { depth: 1 }` citing a depth-1 BMC, `ModelBounded`
/// and `Unrecorded` citing TrustWp requests — and pinned the GAP as
/// `recorded 4 / agreed 1 / undetermined 3 / 0 errors`: only the BMC row was
/// ever re-derived, so an `Unbounded` claim could never be.
///
/// Flipped: with the deductive requests spelled as the shapes that NAME an
/// unbounded procedure (WP under a whole-heap frame, and PDR), the `Unbounded`
/// row is re-derived and agrees, and the rows that under-project an unbounded
/// procedure are refused by name instead of passing as undetermined.
///
/// The archived fixture's own requests used DEFAULT TrustWp options, whose
/// frame is `BorrowRegions`; that shape is deliberately STILL undetermined
/// (the fail-closed frame qualifier), and the second half pins it, so the
/// flip cannot be misread as "every deductive request now re-derives".
#[test]
fn b2_gap_unbounded_coverage_claim_not_rederivable() {
    let full_heap_wp = |id: u32, obligation: u32| {
        wp_request_with(
            id,
            &[obligation],
            TrustWpVerificationMode::WeakestPrecondition,
            TrustWpLoopStrategy::RequireInvariants,
            TrustWpFramePolicy::FullHeap,
        )
    };
    let requests = vec![
        full_heap_wp(0, 0),
        bmc_request(1, &[1], 1),
        full_heap_wp(2, 2),
        mc_request(3, &[3], TrustMcVerificationMode::Pdr, None),
    ];
    let rows = [
        CoverageBound::Unbounded,
        CoverageBound::UnwindBounded { depth: 1 },
        CoverageBound::ModelBounded { size: 4 },
        CoverageBound::Unrecorded,
    ];
    let mut module = module_with(4);
    for (index, (bound, request)) in rows.iter().zip(&requests).enumerate() {
        module.proof_certificates.push(certificate(
            index as u32,
            Some(CoverageAssurance {
                bound: *bound,
                request_digest: request.stable_digest(),
            }),
        ));
    }
    let bundle = bundle_for(&module, requests);
    let report = coverage_assurance_report(&module, Some(&bundle));
    assert!(report.is_checked());
    // GAP: (4, 1, 3) with no refusal. Flipped: the Unbounded row and the BMC
    // row agree; ModelBounded-on-WP and Unrecorded-on-PDR are refused.
    assert_eq!(
        (report.recorded(), report.agreed(), report.undetermined()),
        (4, 2, 0),
        "{}",
        report.summary()
    );
    assert_eq!(
        report.errors(),
        vec![
            ValidationError::CoverageAssuranceBoundMismatch {
                obligation: 2,
                recorded: "ModelBounded { size: 4 }".to_string(),
                derived: "Unbounded".to_string(),
            },
            ValidationError::CoverageAssuranceBoundMismatch {
                obligation: 3,
                recorded: "Unrecorded".to_string(),
                derived: "Unbounded".to_string(),
            },
        ]
        .as_slice()
    );

    // The archived fixture's DEFAULT-options WP request (frame BorrowRegions)
    // is still undetermined: the flip is exactly the named shapes, no wider.
    assert_undetermined(
        &report_for(CoverageBound::Unbounded, wp_request(0, &[0])),
        "default-options WP (BorrowRegions)",
    );
}

// --- WS1.11 review: a sibling that fixes a SHORTER bound contests the claim --
//
// The producer chooses which request a row cites, and the bundle records no
// per-obligation verdict. Before WS1.11 an `Unbounded` row citing a non-BMC
// sibling of a depth-1 BMC request was UNDETERMINED, so the strict admission
// gate (`undetermined() == 0`) refused it. Once CHC / PDR / whole-heap WP
// derive `Unbounded`, citing such a sibling would have moved the same
// over-claim into `agreed`. Check 4 keeps it undetermined; an under-claim,
// which holds whichever run discharged the obligation, still agrees.

/// One obligation (0), one certificate recording `bound` against the request
/// at `cited` in `requests`, and the bundle holding all of `requests`.
fn report_citing(
    bound: CoverageBound,
    requests: Vec<NativeVerificationRequest>,
    cited: usize,
) -> trust_ir_build::validate::CoverageAssuranceReport {
    let mut module = module_with(2);
    module.proof_certificates.push(certificate(
        0,
        Some(CoverageAssurance {
            bound,
            request_digest: requests[cited].stable_digest(),
        }),
    ));
    let bundle = bundle_for(&module, requests);
    coverage_assurance_report(&module, Some(&bundle))
}

fn full_heap_wp(id: u32, obligations: &[u32]) -> NativeVerificationRequest {
    wp_request_with(
        id,
        obligations,
        TrustWpVerificationMode::WeakestPrecondition,
        TrustWpLoopStrategy::Havoc,
        TrustWpFramePolicy::FullHeap,
    )
}

#[test]
fn ws1_11_review_unbounded_citing_pdr_beside_a_depth1_bmc_sibling_is_not_established() {
    let pdr = mc_request(1, &[0], TrustMcVerificationMode::Pdr, None);
    let report = report_citing(
        CoverageBound::Unbounded,
        vec![bmc_request(0, &[0], 1), pdr.clone()],
        1,
    );
    assert_undetermined(&report, "Unbounded on PDR beside a depth-1 BMC sibling");
    assert!(
        !(report.is_checked() && report.errors().is_empty() && report.undetermined() == 0),
        "the strict admission gate must refuse the over-claim"
    );
    // Mutation control: without the BMC sibling the same row is established.
    assert_agrees(
        &report_citing(CoverageBound::Unbounded, vec![pdr], 0),
        "Unbounded on PDR alone",
    );
}

#[test]
fn ws1_11_review_unbounded_citing_full_heap_wp_beside_a_bmc_sibling_is_not_established() {
    assert_undetermined(
        &report_citing(
            CoverageBound::Unbounded,
            vec![full_heap_wp(0, &[0]), bmc_request(1, &[0], 7)],
            0,
        ),
        "Unbounded on WP/FullHeap beside a depth-7 BMC sibling",
    );
    // A CHC sibling does not contest a CHC-grade claim.
    assert_agrees(
        &report_citing(
            CoverageBound::Unbounded,
            vec![
                full_heap_wp(0, &[0]),
                mc_request(1, &[0], TrustMcVerificationMode::Chc, None),
            ],
            0,
        ),
        "Unbounded on WP/FullHeap beside a CHC sibling",
    );
}

#[test]
fn ws1_11_review_an_under_claim_beside_an_unbounded_sibling_still_agrees() {
    // A depth-1 row is true whichever of the two runs discharged the
    // obligation, so an unbounded sibling must not demote it.
    assert_agrees(
        &report_citing(
            CoverageBound::UnwindBounded { depth: 1 },
            vec![
                bmc_request(0, &[0], 1),
                mc_request(1, &[0], TrustMcVerificationMode::Pdr, Some(4)),
            ],
            0,
        ),
        "depth-1 on BMC beside a PDR sibling",
    );
}

#[test]
fn ws1_11_review_a_deeper_bmc_claim_beside_a_shallower_bmc_sibling_is_not_established() {
    assert_undetermined(
        &report_citing(
            CoverageBound::UnwindBounded { depth: 10 },
            vec![bmc_request(0, &[0], 1), bmc_request(1, &[0], 10)],
            1,
        ),
        "depth-10 on BMC-10 beside BMC-1",
    );
    assert_agrees(
        &report_citing(
            CoverageBound::UnwindBounded { depth: 1 },
            vec![bmc_request(0, &[0], 1), bmc_request(1, &[0], 10)],
            0,
        ),
        "depth-1 on BMC-1 beside BMC-10",
    );
}

#[test]
fn ws1_11_review_a_sibling_about_another_obligation_does_not_contest() {
    assert_agrees(
        &report_citing(
            CoverageBound::Unbounded,
            vec![
                bmc_request(0, &[1], 1),
                mc_request(1, &[0], TrustMcVerificationMode::Pdr, None),
            ],
            1,
        ),
        "Unbounded on PDR beside a BMC request for obligation 1 only",
    );
}

#[test]
fn ws1_11_review_a_row_contradicting_its_own_citation_is_refused_not_contested() {
    // The refusal is about the row's own citation and comes first: an
    // Unbounded row citing the BMC request is refused even with a PDR sibling.
    assert_mismatch(
        &report_citing(
            CoverageBound::Unbounded,
            vec![
                bmc_request(0, &[0], 1),
                mc_request(1, &[0], TrustMcVerificationMode::Pdr, None),
            ],
            0,
        ),
        "Unbounded",
        "UnwindBounded { depth: 1 }",
    );
}
