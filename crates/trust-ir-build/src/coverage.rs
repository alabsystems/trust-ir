// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Consumer-derived input coverage: [`coverage_establishment_report`].
//!
//! # The principle
//!
//! Coverage is a verdict the CONSUMER derives from evidence it re-checks
//! itself. No producer-written row is a source of coverage. This replaces
//! [`crate::coverage_assurance_report`] (deprecated), which derived a bound
//! from a request's MODE alone — a request is a question, not an answer, so a
//! pending CHC request with no evidence "agreed" with an `Unbounded` row — and
//! whose rows, citing a module-bound request from inside the module digest,
//! had no fixed point.
//!
//! Coverage is derived from one of two bases, and they answer DIFFERENT
//! questions:
//!
//! * **Basis K — kernel-replayed claim, per CERTIFICATE**
//!   ([`CoverageEstablishmentReport::for_certificate`]). The certificate is
//!   one [`NativeVerificationBundle::kernel_replayed_certificates`] reports:
//!   this process re-checked it in the Clean kernel against the claim
//!   re-derived from its obligation, and the authority classified the claim's
//!   [`KernelClaimFamily`]. The certificate's own evidence WAS the replayed
//!   proof, so the verdict is about it. The bound is
//!   [`bound_established_by_kernel_claim`] of that family —
//!   `ContractGroundDecision` is `Unbounded`; every family whose
//!   quantification nobody has written down yet is `None`. Nothing is cited,
//!   so nothing can cycle.
//! * **Basis R — verified solver result, per OBLIGATION**
//!   ([`CoverageEstablishmentReport::for_obligation`]). A row of a sealed
//!   [`NativeCoverageAttestation`] cites a solver result for an obligation by
//!   digest. The consumer resolves and RECOMPUTES every digest, resolves the
//!   result bytes, requires the admitted bundle to recompute the solved
//!   bundle's executable content, the obligation's claim and the WHOLE replay
//!   context (`NativeVerificationBundle::coverage_replay_context_digest`),
//!   and has a [`NativeCoverageResultReplay`] implementation re-verify the
//!   result. The bound is [`bound_established_by_replayed_result`]: mode and
//!   replayed strength must agree, and only a request whose options mean
//!   exactly the obligation's machine semantics — and whose replay atoms add
//!   no assumption — maps to a bound. A result that rests on other
//!   obligations names them ([`VerifiedSolverResult::premises`]) and is
//!   established only when each of them is itself established `Unbounded` in
//!   the same report, with no cycle. The verdict vouches for NO certificate —
//!   nothing ties the result's bytes to any certificate's evidence — and a
//!   certificate verdict cannot carry it: [`CoverageBasis`] has no
//!   solver-result variant.
//!
//! The in-module `ProofCertificate::assurance` row establishes nothing. When it
//! claims more than its CERTIFICATE's derived bound (basis K; an obligation's
//! solver result is not the certificate's) the bundle is refused (a producer
//! over-stating what it cannot establish); otherwise it is ignored.
//!
//! # The three outcomes
//!
//! `Established` names its bound AND its basis; `Undetermined` names why
//! nothing was established (fail-closed: never read as coverage); `Refused` is
//! a forgery or a contradiction, and ANY refusal in a report is fatal for the
//! whole bundle ([`CoverageEstablishmentReport::refusals`]), because it means
//! a producer cited something false. An undetermined verdict does not block
//! its siblings.

use std::collections::{BTreeMap, BTreeSet};

use trust_ir::proof::{CoverageBound, KernelClaimFamily, ProofCertificateRef, ProofDigest};
use trust_ir::request::{
    NativeCoverageAttestation, NativeCoverageAttestationError, NativeCoverageAttestationRow,
    NativeCoverageReplayInconclusive, NativeCoverageReplayRefusal, NativeCoverageResultReplay,
    NativeEvidenceArtifactAttachment, NativeEvidenceArtifactAttachmentKey, NativeReplayAtomKind,
    NativeReplayContext, NativeReplayedStrength, NativeRequestProvenance, NativeVerificationBundle,
    NativeVerificationRequest, TrustMcArithmeticModel, TrustMcBmcOptions, TrustMcChcEngine,
    TrustMcChcOptions, TrustMcInvariantSource, TrustMcMemoryModel, TrustMcNativeRequest,
    TrustMcPdrGeneralization, TrustMcPdrOptions, TrustMcRequestOptions, TrustMcSlicingMode,
    TrustMcVerificationMode, TrustVcVerificationMode, TrustWpFramePolicy, TrustWpHeapModel,
    TrustWpLoopStrategy, TrustWpNativeRequest, TrustWpPanicSemantics, TrustWpRequestOptions,
    TrustWpVerificationMode,
};
use trust_ir::request::{NativeReplayContextDigest, NativeReplayContextUnavailable};
use trust_ir::value::FuncId;
use trust_ir::{ProofId, ProofStatus};

use crate::linked::coverage_supports;
use crate::validate::{ValidationError, wire_identity_blocker};

/// What a consumer supplies beyond the bundle it is admitting.
///
/// [`CoverageInputs::default`] supplies nothing, so only basis K can establish
/// coverage. An attestation with no `replay` leaves every row Undetermined
/// (after every digest it cites has still been recomputed and every forgery
/// refused).
#[derive(Clone, Copy, Default)]
pub struct CoverageInputs<'a> {
    /// The sealed basis-R citations, if any.
    pub attestation: Option<&'a NativeCoverageAttestation>,
    /// The bundles the cited results were SOLVED against. The admitted bundle
    /// itself is always a candidate too (no write-back).
    pub solved_bundles: &'a [&'a NativeVerificationBundle],
    /// Result-artifact bytes, resolved against the solved bundle by digest.
    pub attachments: &'a [NativeEvidenceArtifactAttachment],
    /// The replayer that re-verifies a cited result. Part of the consumer's
    /// trusted base: link only the verifier's own implementation.
    pub replay: Option<&'a dyn NativeCoverageResultReplay>,
}

/// Which evidence established a CERTIFICATE's coverage.
///
/// There is deliberately no solver-result variant: a verified solver result
/// is about an obligation's claim and names no certificate
/// ([`VerifiedSolverResult`], [`CoverageEstablishmentReport::for_obligation`]),
/// so a certificate verdict can never be read as vouched for by one.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub enum CoverageBasis {
    /// Basis K: this process replayed exactly `certificate` in the Clean
    /// kernel and the replayed claim is of `family`.
    KernelReplayedClaim {
        certificate: ProofCertificateRef,
        family: KernelClaimFamily,
    },
}

impl CoverageBasis {
    /// The certificate the basis is about — always the certificate the verdict
    /// is keyed by; an admission rule checks it anyway.
    #[must_use]
    pub fn certificate(&self) -> &ProofCertificateRef {
        match self {
            CoverageBasis::KernelReplayedClaim { certificate, .. } => certificate,
        }
    }
}

/// Basis R of an OBLIGATION's verdict: the attestation row `row_digest` cited
/// a solver result for `obligation`, every cited digest recomputed on the
/// solved AND the admitted side (the replay context among them), the
/// replayer re-established `strength`, and every obligation in `premises` —
/// the claims the result ASSUMED — is itself established `Unbounded` in the
/// same report.
///
/// It names no certificate and vouches for none: the result's bytes are bound
/// to the obligation's claim and its replay context, never to any
/// certificate's evidence.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct VerifiedSolverResult {
    pub obligation: ProofId,
    pub row_digest: ProofDigest,
    pub solved_bundle_digest: ProofDigest,
    pub request_digest: ProofDigest,
    pub evidence_bundle_digest: ProofDigest,
    pub replay_context_digest: ProofDigest,
    pub strength: NativeReplayedStrength,
    /// The other obligations whose claims the result rests on, sorted and
    /// deduplicated (empty when it rests on none). Each is established
    /// `Unbounded` in the same report, or this verdict is not `Established`.
    pub premises: Vec<ProofId>,
}

/// A request option whose value gives a result a meaning OTHER than the
/// obligation's machine semantics ([`request_machine_semantics_divergence`]).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MachineSemanticsDivergence {
    /// The option's path in the request, e.g. `trust_mc.options.arithmetic_model`.
    pub option: &'static str,
    /// The value the request states, as its `Debug` spelling.
    pub value: String,
}

/// Why no coverage was established. Never a wildcard for coverage.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub enum CoverageUndeterminedReason {
    /// The admitted bundle has no wire identity or does not validate, so
    /// nothing was derived ([`CoverageEstablishmentReport::is_checked`] is
    /// `false`).
    ReportUnchecked,
    /// The admitted module carries no such certificate.
    CertificateNotInModule,
    /// The admitted module states no such obligation.
    ObligationNotInModule,
    /// No basis: for a certificate, it was not kernel-replayed; for an
    /// obligation, no attestation row cites a result for it.
    NoBasis,
    /// This build cannot run the Clean kernel (no `clean-expr`), so nothing is
    /// kernel-replayed.
    KernelUnavailable,
    /// The certificate was kernel-replayed but its claim family is
    /// unclassified (or classified with no bound yet).
    ClaimFamilyUnclassified,
    /// A SIBLING certificate on the same obligation was kernel-replayed, not
    /// this one.
    NotTheReplayedCertificate,
    /// An attestation row cites a result for the obligation but no replayer
    /// is linked.
    NoReplayer,
    /// The replayer could not decide.
    ReplayInconclusive {
        reason: NativeCoverageReplayInconclusive,
        detail: String,
    },
    /// The replayed result does not model the obligation.
    ObligationNotModeled,
    /// The cited request's options give the (valid) result a meaning other
    /// than the obligation's machine semantics — mathematical integers, an
    /// externally supplied invariant, unwinding panics, … — so it covers
    /// nothing of the obligation as the machine runs it.
    RequestNotMachineSemantics {
        divergence: MachineSemanticsDivergence,
    },
    /// The solved or the admitted bundle carries a clean-expr
    /// `ProofAnnotation::Goal` (on `function`), which no wire image binds, so
    /// nothing a replay read from that context can transfer. It ends the row
    /// only after every check that can refuse it has run — both context
    /// digests against the row's citation (they bind everything but the
    /// Goals, so a Goal neither causes nor excuses a drift), the replay, the
    /// premises, mode and strength.
    GoalAnnotationUnbound { function: FuncId },
    /// The result rests on `premise`, which is not established `Unbounded` in
    /// this report — undetermined, only bounded, or part of an assumption
    /// cycle (an obligation that is, directly or through others, its own
    /// premise is never established by it).
    PremiseNotEstablished { premise: ProofId },
}

/// One certificate's verdict (basis K).
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CertificateCoverage {
    Established {
        bound: CoverageBound,
        basis: CoverageBasis,
    },
    Undetermined {
        reason: CoverageUndeterminedReason,
    },
    /// Fatal for the bundle: the same error is in
    /// [`CoverageEstablishmentReport::refusals`].
    Refused(ValidationError),
}

/// One obligation's verdict (basis R). Says nothing about any certificate.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ObligationCoverage {
    Established {
        bound: CoverageBound,
        basis: VerifiedSolverResult,
    },
    Undetermined {
        reason: CoverageUndeterminedReason,
    },
    /// Fatal for the bundle: the same error is in
    /// [`CoverageEstablishmentReport::refusals`].
    Refused(ValidationError),
}

/// What [`coverage_establishment_report`] derived: per certificate (basis K)
/// and per obligation (basis R).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CoverageEstablishmentReport {
    checked: bool,
    certificates: BTreeMap<ProofCertificateRef, CertificateCoverage>,
    obligations: BTreeMap<ProofId, ObligationCoverage>,
    refusals: Vec<ValidationError>,
    bundle_errors: usize,
}

impl CoverageEstablishmentReport {
    /// Did the derivation RUN? `false` when the admitted bundle has no wire
    /// identity or does not validate: then every verdict is
    /// [`CoverageUndeterminedReason::ReportUnchecked`].
    #[must_use]
    pub fn is_checked(&self) -> bool {
        self.checked
    }

    /// The verdict for one certificate (by its lineage reference, which
    /// excludes `assurance`): basis K only. A verified solver result for the
    /// certificate's obligation never appears here.
    #[must_use]
    pub fn for_certificate(&self, certificate: &ProofCertificateRef) -> CertificateCoverage {
        if !self.checked {
            return CertificateCoverage::Undetermined {
                reason: CoverageUndeterminedReason::ReportUnchecked,
            };
        }
        self.certificates
            .get(certificate)
            .cloned()
            .unwrap_or(CertificateCoverage::Undetermined {
                reason: CoverageUndeterminedReason::CertificateNotInModule,
            })
    }

    /// The verdict for one obligation's CLAIM from a verified solver result
    /// (basis R). It vouches for no certificate of the obligation: admitting a
    /// certificate still needs that certificate's own evidence judged.
    #[must_use]
    pub fn for_obligation(&self, obligation: ProofId) -> ObligationCoverage {
        if !self.checked {
            return ObligationCoverage::Undetermined {
                reason: CoverageUndeterminedReason::ReportUnchecked,
            };
        }
        self.obligations
            .get(&obligation)
            .cloned()
            .unwrap_or(ObligationCoverage::Undetermined {
                reason: CoverageUndeterminedReason::ObligationNotInModule,
            })
    }

    /// Every certificate of the admitted module and its verdict (empty when
    /// unchecked).
    pub fn certificates(
        &self,
    ) -> impl Iterator<Item = (&ProofCertificateRef, &CertificateCoverage)> {
        self.certificates.iter()
    }

    /// Every obligation of the admitted module and its basis-R verdict (empty
    /// when unchecked).
    pub fn obligations(&self) -> impl Iterator<Item = (&ProofId, &ObligationCoverage)> {
        self.obligations.iter()
    }

    /// Every refusal, including those not attached to a verdict (a row citing
    /// an obligation the admitted module does not state, a malformed
    /// attestation). ANY entry is fatal for the whole bundle.
    #[must_use]
    pub fn refusals(&self) -> &[ValidationError] {
        &self.refusals
    }

    /// How many `NativeVerificationBundle::validate` errors left the report
    /// unchecked (0 when checked).
    #[must_use]
    pub fn bundle_errors(&self) -> usize {
        self.bundle_errors
    }

    /// One line for a report or CLI. Says UNCHECKED out loud when nothing was
    /// derived, and counts the outcomes apart, certificates and obligations
    /// separately.
    #[must_use]
    pub fn summary(&self) -> String {
        if !self.checked {
            return format!(
                "coverage establishment: UNCHECKED — the admitted bundle did not validate \
                 ({} bundle error(s), {} refusal(s)); nothing is established",
                self.bundle_errors,
                self.refusals.len()
            );
        }
        let (mut kernel, mut certificate_undetermined, mut certificate_refused) = (0, 0, 0);
        for outcome in self.certificates.values() {
            match outcome {
                CertificateCoverage::Established { .. } => kernel += 1,
                CertificateCoverage::Undetermined { .. } => certificate_undetermined += 1,
                CertificateCoverage::Refused(_) => certificate_refused += 1,
            }
        }
        let (mut solver, mut obligation_undetermined, mut obligation_refused) = (0, 0, 0);
        for outcome in self.obligations.values() {
            match outcome {
                ObligationCoverage::Established { .. } => solver += 1,
                ObligationCoverage::Undetermined { .. } => obligation_undetermined += 1,
                ObligationCoverage::Refused(_) => obligation_refused += 1,
            }
        }
        format!(
            "coverage establishment: {} certificate(s): {} established by a kernel-replayed \
             claim, {} UNDETERMINED (not coverage), {} refused; {} obligation(s): {} \
             established by a verified solver result (vouching for no certificate), {} \
             UNDETERMINED, {} refused; {} refusal(s) in all{}",
            self.certificates.len(),
            kernel,
            certificate_undetermined,
            certificate_refused,
            self.obligations.len(),
            solver,
            obligation_undetermined,
            obligation_refused,
            self.refusals.len(),
            if self.refusals.is_empty() {
                ""
            } else {
                " — the bundle is refused"
            }
        )
    }
}

/// The bound a kernel-replayed claim of `family` establishes, or `None`.
///
/// THE soundness-critical table of basis K. `ContractGroundDecision` is a
/// closed ground decision or a `∀ x : Nat` nonneg tautology bound to an
/// unsigned place — universally closed, so `Unbounded` relative to the
/// obligation's formula. Every other family (give-back refinements, Farkas
/// bounds, SlackCertZ, clean-backend translation validation, trust-cg
/// lowering, fuel-quantified or `Done`-conditional statements) is `None` until
/// its quantification is written down and tested — and the wildcard makes a
/// family added upstream arrive here as `None`.
#[must_use]
pub fn bound_established_by_kernel_claim(family: KernelClaimFamily) -> Option<CoverageBound> {
    match family {
        KernelClaimFamily::ContractGroundDecision => Some(CoverageBound::Unbounded),
        _ => None,
    }
}

/// A replayed strength the cited request's mode does not admit.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ModeStrengthMismatch {
    /// The request's mode (and, for BMC, its unwind limit), for diagnostics.
    pub mode: String,
    /// The strength the replayer re-established.
    pub strength: NativeReplayedStrength,
}

/// The first option of `request` whose value gives a result a meaning OTHER
/// than the obligation's machine semantics, or `None` when every option means
/// exactly that.
///
/// Exhaustive over every option field (struct patterns with no `..`) and every
/// option enum (no wildcard), so a field or a value added upstream is a
/// compile error here until someone decides what it means. The decisions:
///
/// * **TrustMc.** `memory_model` must be `TrustIrPlaces` (`FlatArrays` is an
///   encoding nobody has shown exact; `StackedBorrows` adds aliasing UB the
///   IR does not have, so a proof under it assumes the program obeys it).
///   `arithmetic_model` must be `FixedWidthBitvectors` (`MathematicalIntegers`
///   has no wrap-around; `RustChecked` imposes Rust's overflow checks where
///   the IR makes its own checks explicit). `chc.invariant_source` must be
///   `None` or `TrustIrProofObligations` (an invariant from `TrustWp`,
///   `TrustVc` or the user comes from outside the module and its replay
///   context, so the result may rest on an assumption nobody re-checks here).
///   Solver strategy does not change what a replayed result means: `chc.engine`,
///   the `chc.pdr` settings, `chc.emit_horn_clauses` and `slicing` (a slice
///   the replay re-derives is the replayer's faithfulness obligation, like the
///   rest of its translation). `bmc.unwinding_assertions`: `false` cuts every
///   path at the unwind limit, `true` also ASSERTS the limit is never
///   exceeded; the depth-`unwind_limit` claim the bound states holds under
///   both (the assertion is an extra conjunct the result satisfies), and the
///   completeness `true` would license is not derived because
///   [`NativeReplayedStrength::BoundedUnwind`] does not attest that the
///   unwinding assertions were re-checked. `bmc.unwind_limit` is the depth
///   the mode table requires the strength to equal.
/// * **TrustWp.** `heap_model` must be `TrustIrMemory` (`RustBorrowGraph`
///   assumes the borrow discipline, `SeparationLogic` is a logic nobody has
///   shown equal to the IR's memory). `panic_semantics` must be
///   `PanicFreeRequired` (`EncodePanicsAsErrors` proves the obligation of an
///   error-encoded program, `Unwind` lets a panic leave without the
///   obligation). `max_abduced_preconditions` must be `0` (an abduced
///   precondition is an assumption the result may rest on, and nothing here
///   re-checks it at the callers). `loop_strategy` (every strategy is sound:
///   required invariants are checked, inferred ones are checked, `Havoc`
///   over-approximates) and `emit_verification_conditions` (output) keep the
///   meaning. `frame_policy` is the mode table's: a partial frame answered by
///   a whole-heap strength is a MISMATCH, not a divergence.
/// * **TrustVc.** No option set: every TrustVc mode is a mismatch (a
///   certificate import is basis K's business, not a solver result).
/// * **The request's replay atoms** (`provenance.replay_context`, every
///   suite). A replay may assume nothing the consumer does not bind and
///   check, and the consumer checks no request-carried formula against the
///   program: an `Assumption` atom is a premise the admitted module never
///   states, so any one of them is a divergence — and so is an
///   `unsupported_modes` entry (the producer itself says the request cannot
///   be admitted). An `Assertion` atom must state EXACTLY the claim of the
///   obligation it cites; that needs the module, so
///   `coverage_establishment_report` checks it per row and REFUSES a
///   mismatch.
///
/// The other request-level fields (`id`, `function`, `obligations`,
/// `lineage_roots`, `diagnostics`, and `provenance`'s suite, expected
/// verifier, solvers and replay identity) are identity and reporting, bound
/// by the request digest; they do not change what a result means.
#[must_use]
pub fn request_machine_semantics_divergence(
    request: &NativeVerificationRequest,
) -> Option<MachineSemanticsDivergence> {
    fn diverges(option: &'static str, value: impl core::fmt::Debug) -> MachineSemanticsDivergence {
        MachineSemanticsDivergence {
            option,
            value: format!("{value:?}"),
        }
    }
    match request {
        NativeVerificationRequest::TrustMc(request) => {
            let TrustMcNativeRequest {
                id: _,
                mode: _,
                function: _,
                obligations: _,
                lineage_roots: _,
                options,
                diagnostics: _,
                provenance,
            } = request;
            if let Some(divergence) = replay_context_divergence(
                provenance,
                "trust_mc.provenance.replay_context.atoms",
                "trust_mc.provenance.replay_context.unsupported_modes",
            ) {
                return Some(divergence);
            }
            let TrustMcRequestOptions {
                memory_model,
                arithmetic_model,
                bmc,
                chc,
                slicing,
            } = *options;
            let TrustMcBmcOptions {
                unwind_limit: _,
                unwinding_assertions: _,
            } = bmc;
            let TrustMcChcOptions {
                engine,
                invariant_source,
                pdr,
                emit_horn_clauses: _,
            } = chc;
            let TrustMcPdrOptions {
                enabled: _,
                max_frames: _,
                generalization,
            } = pdr;
            match memory_model {
                TrustMcMemoryModel::TrustIrPlaces => {}
                TrustMcMemoryModel::FlatArrays | TrustMcMemoryModel::StackedBorrows => {
                    return Some(diverges("trust_mc.options.memory_model", memory_model));
                }
            }
            match arithmetic_model {
                TrustMcArithmeticModel::FixedWidthBitvectors => {}
                TrustMcArithmeticModel::MathematicalIntegers
                | TrustMcArithmeticModel::RustChecked => {
                    return Some(diverges(
                        "trust_mc.options.arithmetic_model",
                        arithmetic_model,
                    ));
                }
            }
            match invariant_source {
                TrustMcInvariantSource::None | TrustMcInvariantSource::TrustIrProofObligations => {}
                TrustMcInvariantSource::TrustWp
                | TrustMcInvariantSource::TrustVc
                | TrustMcInvariantSource::UserSupplied => {
                    return Some(diverges(
                        "trust_mc.options.chc.invariant_source",
                        invariant_source,
                    ));
                }
            }
            match engine {
                TrustMcChcEngine::Z3Fixedpoint
                | TrustMcChcEngine::Spacer
                | TrustMcChcEngine::NativePdr => {}
            }
            match generalization {
                TrustMcPdrGeneralization::None
                | TrustMcPdrGeneralization::Cubes
                | TrustMcPdrGeneralization::Interpolants => {}
            }
            match slicing {
                TrustMcSlicingMode::None
                | TrustMcSlicingMode::ObligationBackwardSlice
                | TrustMcSlicingMode::ConstraintIndependence => {}
            }
            None
        }
        NativeVerificationRequest::TrustWp(request) => {
            let TrustWpNativeRequest {
                id: _,
                mode: _,
                function: _,
                obligations: _,
                lineage_roots: _,
                options,
                diagnostics: _,
                provenance,
            } = request;
            if let Some(divergence) = replay_context_divergence(
                provenance,
                "trust_wp.provenance.replay_context.atoms",
                "trust_wp.provenance.replay_context.unsupported_modes",
            ) {
                return Some(divergence);
            }
            let TrustWpRequestOptions {
                heap_model,
                loop_strategy,
                frame_policy: _,
                panic_semantics,
                max_abduced_preconditions,
                emit_verification_conditions: _,
            } = *options;
            match heap_model {
                TrustWpHeapModel::TrustIrMemory => {}
                TrustWpHeapModel::RustBorrowGraph | TrustWpHeapModel::SeparationLogic => {
                    return Some(diverges("trust_wp.options.heap_model", heap_model));
                }
            }
            match panic_semantics {
                TrustWpPanicSemantics::PanicFreeRequired => {}
                TrustWpPanicSemantics::EncodePanicsAsErrors | TrustWpPanicSemantics::Unwind => {
                    return Some(diverges(
                        "trust_wp.options.panic_semantics",
                        panic_semantics,
                    ));
                }
            }
            if max_abduced_preconditions != 0 {
                return Some(diverges(
                    "trust_wp.options.max_abduced_preconditions",
                    max_abduced_preconditions,
                ));
            }
            match loop_strategy {
                TrustWpLoopStrategy::RequireInvariants
                | TrustWpLoopStrategy::InferInvariants
                | TrustWpLoopStrategy::Havoc => {}
            }
            None
        }
        NativeVerificationRequest::TrustVc(request) => replay_context_divergence(
            &request.provenance,
            "trust_vc.provenance.replay_context.atoms",
            "trust_vc.provenance.replay_context.unsupported_modes",
        ),
    }
}

/// The request's replay context adds a premise: an `Assumption` atom, or an
/// unsupported-mode entry. Destructured with no `..`, so a field or an atom
/// kind added upstream is a compile error here until someone decides what it
/// means.
fn replay_context_divergence(
    provenance: &NativeRequestProvenance,
    atoms_option: &'static str,
    unsupported_option: &'static str,
) -> Option<MachineSemanticsDivergence> {
    let NativeRequestProvenance {
        verifier_suite: _,
        expected_verifier: _,
        solvers: _,
        replay: _,
        replay_context,
    } = provenance;
    let NativeReplayContext {
        atoms,
        unsupported_modes,
    } = replay_context;
    let assumption = atoms.iter().find(|atom| match atom.kind {
        NativeReplayAtomKind::Assumption => true,
        // Checked per row against the module (`assertion_atom_mismatch`).
        NativeReplayAtomKind::Assertion => false,
    });
    if let Some(atom) = assumption {
        return Some(MachineSemanticsDivergence {
            option: atoms_option,
            value: format!("Assumption #{} {:?}", atom.id.index(), atom.formula.payload),
        });
    }
    unsupported_modes
        .first()
        .map(|unsupported| MachineSemanticsDivergence {
            option: unsupported_option,
            value: format!("{unsupported:?}"),
        })
}

/// The first `Assertion` replay atom of `request` that does not state EXACTLY
/// the formula `module` gives the obligation it cites (or cites none): a
/// replay that took its goal from the request would have proved another
/// claim. Described for the refusal.
fn assertion_atom_mismatch(
    request: &NativeVerificationRequest,
    module: &trust_ir::Module,
) -> Option<String> {
    request
        .provenance()
        .replay_context()
        .atoms
        .iter()
        .filter(|atom| atom.kind == NativeReplayAtomKind::Assertion)
        .find_map(|atom| {
            let claim = atom
                .obligation
                .and_then(|id| module.proof_obligations.iter().find(|o| o.id == id))
                .and_then(|obligation| obligation.formula.as_ref());
            (claim != Some(&atom.formula)).then(|| {
                format!(
                    "the request's Assertion atom #{} states {:?} for {}, whose claim is {}; a \
                     replay whose goal is the request's would prove another claim",
                    atom.id.index(),
                    atom.formula.payload,
                    atom.obligation.map_or_else(
                        || "no obligation".to_string(),
                        |id| format!("obligation #{}", id.index())
                    ),
                    claim.map_or_else(
                        || "not stated".to_string(),
                        |formula| format!("{:?}", formula.payload)
                    ),
                )
            })
        })
}

/// The bound a verified solver result establishes for its obligation:
/// `Err` when the request's mode and the replayed strength disagree (a
/// refusal), `Ok(None)` when they agree but the request's options mean
/// something other than the obligation's machine semantics
/// ([`request_machine_semantics_divergence`]; undetermined), `Ok(Some(bound))`
/// otherwise.
///
/// * TrustMc `Chc` / `Pdr` with `ChcValidity` / `PdrInvariant` → `Unbounded`
///   (the query is unreachable from every state at every depth).
/// * TrustMc `BoundedModelCheck` with `BoundedUnwind { depth }`, `depth` EQUAL
///   to the request's `unwind_limit` → `UnwindBounded { depth }`, under either
///   `unwinding_assertions` value (never `Unbounded`).
/// * TrustWp `WeakestPrecondition` under a `FullHeap` frame, every loop
///   strategy, with `WeakestPreconditionFullHeap` → `Unbounded` (no WP
///   replayer exists yet, so in practice WP stays undetermined).
/// * Everything else is a mismatch: WP under a `Minimal` / `BorrowRegions`
///   frame (it may assume a written location unchanged), strongest
///   postcondition and abduction (not a discharge for all inputs), and every
///   TrustVc mode (a certificate import is basis K's business, not a solver
///   result).
///
/// Exhaustive over the request, mode, frame and loop enums with no wildcard,
/// so a new variant must pick its arm here; the strength enum is foreign and
/// `#[non_exhaustive]`, so each arm's strength match ends in a fail-closed
/// mismatch.
pub fn bound_established_by_replayed_result(
    request: &NativeVerificationRequest,
    strength: NativeReplayedStrength,
) -> Result<Option<CoverageBound>, ModeStrengthMismatch> {
    let bound = bound_of_mode_and_strength(request, strength)?;
    Ok(match request_machine_semantics_divergence(request) {
        None => Some(bound),
        Some(_) => None,
    })
}

fn bound_of_mode_and_strength(
    request: &NativeVerificationRequest,
    strength: NativeReplayedStrength,
) -> Result<CoverageBound, ModeStrengthMismatch> {
    let mismatch = |mode: String| Err(ModeStrengthMismatch { mode, strength });
    match request {
        NativeVerificationRequest::TrustMc(request) => match request.mode {
            TrustMcVerificationMode::BoundedModelCheck => {
                let limit = u64::from(request.options.bmc.unwind_limit);
                match strength {
                    NativeReplayedStrength::BoundedUnwind { depth } if depth == limit => {
                        Ok(CoverageBound::UnwindBounded { depth })
                    }
                    _ => mismatch(format!("trust_mc BoundedModelCheck unwind_limit={limit}")),
                }
            }
            TrustMcVerificationMode::Chc | TrustMcVerificationMode::Pdr => match strength {
                NativeReplayedStrength::ChcValidity | NativeReplayedStrength::PdrInvariant => {
                    Ok(CoverageBound::Unbounded)
                }
                _ => mismatch(format!("trust_mc {:?}", request.mode)),
            },
        },
        NativeVerificationRequest::TrustWp(request) => match request.mode {
            TrustWpVerificationMode::WeakestPrecondition => match request.options.frame_policy {
                TrustWpFramePolicy::FullHeap => match request.options.loop_strategy {
                    TrustWpLoopStrategy::RequireInvariants
                    | TrustWpLoopStrategy::InferInvariants
                    | TrustWpLoopStrategy::Havoc => match strength {
                        NativeReplayedStrength::WeakestPreconditionFullHeap => {
                            Ok(CoverageBound::Unbounded)
                        }
                        _ => mismatch(format!(
                            "trust_wp WeakestPrecondition FullHeap {:?}",
                            request.options.loop_strategy
                        )),
                    },
                },
                TrustWpFramePolicy::Minimal | TrustWpFramePolicy::BorrowRegions => {
                    mismatch(format!(
                        "trust_wp WeakestPrecondition under the partial frame {:?}",
                        request.options.frame_policy
                    ))
                }
            },
            TrustWpVerificationMode::StrongestPostcondition
            | TrustWpVerificationMode::Abduction => {
                mismatch(format!("trust_wp {:?}", request.mode))
            }
        },
        NativeVerificationRequest::TrustVc(request) => match request.mode {
            TrustVcVerificationMode::ImportProofCertificates
            | TrustVcVerificationMode::MergeProofCertificates
            | TrustVcVerificationMode::DischargeProofObligations => mismatch(format!(
                "trust_vc {:?} (a certificate import is basis K's, not a solver result)",
                request.mode
            )),
        },
    }
}

/// Derive input coverage for the bundle a consumer is ADMITTING, from
/// evidence the consumer re-checks itself: per certificate (basis K) and per
/// obligation (basis R).
///
/// # Order of work
///
/// 0. The admitted bundle must have a wire identity
///    ([`wire_identity_blocker`]; a refusal) and must validate
///    ([`NativeVerificationBundle::validate`]); otherwise the report is
///    UNCHECKED and establishes nothing.
/// 1. **Basis K** for every certificate of the admitted module (see
///    [`bound_established_by_kernel_claim`]).
/// 2. **Basis R** for every row of `inputs.attestation`, if it validates
///    (else its errors are refusals and no row is read). Per row, in order,
///    each failure a REFUSAL unless marked: the solved bundle is supplied
///    ([`ValidationError::CoverageSolvedBundleMissing`]) and validates
///    ([`ValidationError::CoverageSolvedBundleInvalid`]); its module and
///    executable-content digests recompute
///    ([`ValidationError::CoverageSolvedBundleDigestMismatch`]); the request
///    is in it ([`ValidationError::CoverageAssuranceRequestUnknown`]), lists
///    the obligation ([`ValidationError::CoverageAssuranceObligationNotRequested`])
///    and carries no `Assertion` replay atom stating anything but exactly the
///    formula of the obligation it cites ([`ValidationError::CoverageClaimDrift`]);
///    it has result evidence for the obligation
///    ([`ValidationError::CoverageEvidenceMissing`]) whose digest recomputes
///    ([`ValidationError::CoverageEvidenceDigestMismatch`]); every cited result
///    artifact is a descriptor of it and its bytes resolve
///    ([`ValidationError::CoverageResultArtifactUnresolved`]); the obligation
///    is `Failed` in neither module ([`ValidationError::CoverageContradicted`])
///    and the admitted module states it ([`ValidationError::CoverageClaimDrift`]);
///    the admitted module has the solved executable content
///    ([`ValidationError::CoverageSubjectCodeDrift`]), the same claim
///    ([`ValidationError::CoverageClaimDrift`]) and — both the solved and the
///    admitted bundle recomputing the row's digest of it, the whole bundle but
///    its write-back allowlist — the same replay context
///    ([`ValidationError::CoverageSolvedBundleDigestMismatch`],
///    [`ValidationError::CoverageClaimDrift`]; an unindexable context on either
///    side is refused; a clean-expr `Goal` on either side is UNDETERMINED, but
///    only after both context digests — which bind everything but the Goals —
///    have been held to the citation); a
///    replayer is linked (UNDETERMINED otherwise); the replay does not find
///    the result invalid ([`ValidationError::CoverageResultReplayInvalid`]) or
///    refuted ([`ValidationError::CoverageContradicted`]) — inconclusive is
///    UNDETERMINED; every premise the result names is an obligation both
///    modules state ([`ValidationError::CoverageResultReplayInvalid`]) and is
///    `Failed` in neither ([`ValidationError::CoverageContradicted`]); mode and
///    strength agree ([`ValidationError::CoverageModeStrengthMismatch`]); the
///    result models the obligation (UNDETERMINED otherwise); and the
///    request's options mean exactly the obligation's machine semantics and
///    its replay atoms carry no `Assumption` (UNDETERMINED otherwise). An
///    UNDETERMINED step never ends a row before a later check that can
///    refuse it: every check that can still run does (only a missing
///    replayer or an inconclusive replay leaves nothing to run), and the
///    first undetermined reason is the verdict only when none refuses.
///    Per obligation, a refusal wins whatever the row order; an established
///    row is only a CANDIDATE until step 3.
/// 3. **Premises**, over the whole report: a candidate is established only
///    when every premise it names is established `Unbounded` in this report —
///    by a kernel-replayed certificate (step 1) or another such candidate —
///    as a least fixed point, so an assumption cycle never is (UNDETERMINED:
///    [`CoverageUndeterminedReason::PremiseNotEstablished`]); of two
///    established bounds the stronger is kept.
/// 4. **The in-module row**: a certificate whose `assurance` claims more than
///    its own (basis K) bound is REFUSED
///    ([`ValidationError::CoverageRowExceedsEstablished`]); any other
///    `assurance` is ignored. Its obligation's solver result does not count:
///    it vouches for no certificate.
///
/// # Admitting on this report
///
/// Certificate `C` is covered only when `report.is_checked()`,
/// `report.refusals().is_empty()`, and `report.for_certificate(&C.lineage_ref())`
/// is `Established` with the bound the consumer needs and `basis.certificate()
/// == &C.lineage_ref()`. Obligation `o`'s CLAIM is covered by a verified
/// solver result only when the same two report-level conditions hold and
/// `report.for_obligation(o)` is `Established` with the bound the consumer
/// needs — which admits no certificate of `o`. `assurance` is never read as
/// coverage.
#[must_use]
pub fn coverage_establishment_report(
    bundle: &NativeVerificationBundle,
    inputs: CoverageInputs<'_>,
) -> CoverageEstablishmentReport {
    let module = &bundle.module;
    if let Some(error) = wire_identity_blocker(module) {
        return CoverageEstablishmentReport {
            checked: false,
            certificates: BTreeMap::new(),
            obligations: BTreeMap::new(),
            refusals: vec![error],
            bundle_errors: 0,
        };
    }
    if let Err(errors) = bundle.validate() {
        return CoverageEstablishmentReport {
            checked: false,
            certificates: BTreeMap::new(),
            obligations: BTreeMap::new(),
            refusals: Vec::new(),
            bundle_errors: errors.len(),
        };
    }

    // 1. Basis K, per certificate.
    let replayed = bundle.kernel_replayed_certificates();
    let mut certificates: BTreeMap<ProofCertificateRef, CertificateCoverage> = BTreeMap::new();
    for certificate in &module.proof_certificates {
        let reference = certificate.lineage_ref();
        let outcome = kernel_outcome(&reference, &replayed);
        certificates.entry(reference).or_insert(outcome);
    }

    // 2. Basis R, per obligation.
    let mut obligations: BTreeMap<ProofId, ObligationCoverage> = module
        .proof_obligations
        .iter()
        .map(|obligation| {
            (
                obligation.id,
                ObligationCoverage::Undetermined {
                    reason: CoverageUndeterminedReason::NoBasis,
                },
            )
        })
        .collect();
    let mut refusals = Vec::new();
    let mut candidates = Vec::new();
    if let Some(attestation) = inputs.attestation {
        match attestation.validate() {
            Err(errors) => refusals.extend(errors.into_iter().map(attestation_error)),
            Ok(()) => {
                let mut solved = SolvedCandidates::new(bundle, inputs.solved_bundles);
                for row in &attestation.rows {
                    let outcome = establish_row(bundle, row, &inputs, &mut solved);
                    merge_row(
                        &mut obligations,
                        &mut refusals,
                        &mut candidates,
                        row.obligation,
                        outcome,
                    );
                }
            }
        }
    }

    // 3. The premises: a result that rests on other obligations is
    // established only when each of them is, `Unbounded`, in THIS report.
    let kernel_established: BTreeSet<ProofId> = certificates
        .iter()
        .filter(|(_, outcome)| {
            matches!(
                outcome,
                CertificateCoverage::Established {
                    bound: CoverageBound::Unbounded,
                    ..
                }
            )
        })
        .map(|(reference, _)| reference.obligation)
        .collect();
    resolve_premises(&mut obligations, candidates, kernel_established);

    // 4. The in-module row: refused when it over-states its certificate's own
    // bound, ignored otherwise.
    for certificate in &module.proof_certificates {
        let Some(assurance) = certificate.assurance else {
            continue;
        };
        let Some(outcome) = certificates.get_mut(&certificate.lineage_ref()) else {
            continue;
        };
        let established = match outcome {
            CertificateCoverage::Established { bound, .. } => Some(*bound),
            CertificateCoverage::Undetermined { .. } => None,
            CertificateCoverage::Refused(_) => continue,
        };
        // No derived bound supplies nothing but `Unrecorded`, which is exactly
        // how `coverage_supports` reads an `Unrecorded` supply.
        let supply = established.unwrap_or(CoverageBound::Unrecorded);
        if coverage_supports(supply, assurance.bound) {
            continue;
        }
        let error = ValidationError::CoverageRowExceedsEstablished {
            obligation: certificate.obligation.index(),
            recorded: format!("{:?}", assurance.bound),
            established: established.map_or_else(
                || "nothing established".to_string(),
                |bound| format!("{bound:?}"),
            ),
        };
        refusals.push(error.clone());
        *outcome = CertificateCoverage::Refused(error);
    }

    CoverageEstablishmentReport {
        checked: true,
        certificates,
        obligations,
        refusals,
        bundle_errors: 0,
    }
}

fn kernel_outcome(
    reference: &ProofCertificateRef,
    replayed: &BTreeMap<ProofCertificateRef, Option<KernelClaimFamily>>,
) -> CertificateCoverage {
    let undetermined = |reason| CertificateCoverage::Undetermined { reason };
    match replayed.get(reference) {
        Some(Some(family)) => match bound_established_by_kernel_claim(*family) {
            Some(bound) => CertificateCoverage::Established {
                bound,
                basis: CoverageBasis::KernelReplayedClaim {
                    certificate: reference.clone(),
                    family: *family,
                },
            },
            None => undetermined(CoverageUndeterminedReason::ClaimFamilyUnclassified),
        },
        Some(None) => undetermined(CoverageUndeterminedReason::ClaimFamilyUnclassified),
        None if !NativeVerificationBundle::kernel_replay_available() => {
            undetermined(CoverageUndeterminedReason::KernelUnavailable)
        }
        None if replayed
            .keys()
            .any(|sibling| sibling.obligation == reference.obligation) =>
        {
            undetermined(CoverageUndeterminedReason::NotTheReplayedCertificate)
        }
        None => undetermined(CoverageUndeterminedReason::NoBasis),
    }
}

fn attestation_error(error: NativeCoverageAttestationError) -> ValidationError {
    match error {
        NativeCoverageAttestationError::DuplicateRow {
            obligation,
            solved_bundle_digest,
            request_digest,
        } => ValidationError::CoverageAttestationRowDuplicate {
            obligation: obligation.index(),
            solved_bundle: solved_bundle_digest,
            request: request_digest,
        },
        other => ValidationError::CoverageAttestationSchemaUnsupported {
            detail: other.to_string(),
        },
    }
}

/// The candidate solved bundles — the ADMITTED bundle first, then the
/// supplied ones — each digested, validated and (once validated) given its
/// executable-content and replay-context digests at most once. Both digest
/// the whole module (the context clones the whole bundle first), so
/// recomputing them per row made a report cost rows x bundle size.
struct SolvedCandidates<'a> {
    bundles: Vec<&'a NativeVerificationBundle>,
    digests: Vec<ProofDigest>,
    validated: Vec<Option<Result<(), String>>>,
    contents: Vec<Option<ProofDigest>>,
    contexts: Vec<Option<Result<NativeReplayContextDigest, NativeReplayContextUnavailable>>>,
    supplied: usize,
}

impl<'a> SolvedCandidates<'a> {
    /// The admitted bundle's index: it is always a candidate (no write-back).
    const ADMITTED: usize = 0;

    fn new(
        admitted: &'a NativeVerificationBundle,
        supplied: &[&'a NativeVerificationBundle],
    ) -> Self {
        let bundles: Vec<&'a NativeVerificationBundle> = std::iter::once(admitted)
            .chain(supplied.iter().copied())
            .collect();
        let digests = bundles
            .iter()
            .map(|bundle| bundle.stable_digest())
            .collect();
        let validated = vec![None; bundles.len()];
        Self {
            contents: vec![None; bundles.len()],
            contexts: vec![None; bundles.len()],
            bundles,
            digests,
            validated,
            supplied: supplied.len(),
        }
    }

    /// `Module::executable_content_digest_v1` of candidate `index`'s module,
    /// computed once. Like every module digest it panics on a module with no
    /// wire identity: call it (and [`Self::context`]) only on the admitted
    /// bundle, probed before anything is derived, or on a candidate
    /// [`Self::validated`] accepted.
    fn content(&mut self, index: usize) -> ProofDigest {
        if let Some(content) = self.contents[index] {
            return content;
        }
        let content = self.bundles[index].module.executable_content_digest_v1();
        self.contents[index] = Some(content);
        content
    }

    /// `coverage_replay_context_digest` of candidate `index`, computed once.
    fn context(
        &mut self,
        index: usize,
    ) -> Result<NativeReplayContextDigest, NativeReplayContextUnavailable> {
        if let Some(context) = self.contexts[index] {
            return context;
        }
        let context = self.bundles[index].coverage_replay_context_digest();
        self.contexts[index] = Some(context);
        context
    }

    fn find(&self, digest: ProofDigest) -> Option<usize> {
        self.digests
            .iter()
            .position(|candidate| *candidate == digest)
    }

    fn validated(&mut self, index: usize) -> Result<(), String> {
        if let Some(verdict) = &self.validated[index] {
            return verdict.clone();
        }
        let bundle = self.bundles[index];
        let verdict = if let Some(error) = wire_identity_blocker(&bundle.module) {
            Err(error.to_string())
        } else {
            bundle.validate().map_err(|errors| {
                let first = errors.first().map(ToString::to_string).unwrap_or_default();
                format!("{} validation error(s), first: {first}", errors.len())
            })
        };
        self.validated[index] = Some(verdict.clone());
        verdict
    }
}

enum RowOutcome {
    Established {
        bound: CoverageBound,
        basis: VerifiedSolverResult,
    },
    Undetermined(CoverageUndeterminedReason),
    Refused(ValidationError),
}

/// An established row, held until its premises are resolved (step 3).
struct Candidate {
    obligation: ProofId,
    bound: CoverageBound,
    basis: VerifiedSolverResult,
}

/// Step 2's per-row merge. A refusal wins, whatever the row order; an
/// undetermined reason replaces `NoBasis`; an established row becomes a
/// CANDIDATE, which step 3 turns into a verdict only once its premises are.
fn merge_row(
    obligations: &mut BTreeMap<ProofId, ObligationCoverage>,
    refusals: &mut Vec<ValidationError>,
    candidates: &mut Vec<Candidate>,
    obligation: ProofId,
    outcome: RowOutcome,
) {
    match outcome {
        RowOutcome::Refused(error) => {
            refusals.push(error.clone());
            if let Some(current) = obligations.get_mut(&obligation) {
                *current = ObligationCoverage::Refused(error);
            }
        }
        RowOutcome::Undetermined(reason) => {
            if let Some(current @ ObligationCoverage::Undetermined { .. }) =
                obligations.get_mut(&obligation)
            {
                *current = ObligationCoverage::Undetermined { reason };
            }
        }
        RowOutcome::Established { bound, basis } => candidates.push(Candidate {
            obligation,
            bound,
            basis,
        }),
    }
}

/// Step 3: turn the candidates into verdicts. A candidate is GROUNDED when
/// every premise it names is established `Unbounded` in this report — by a
/// kernel-replayed certificate (`kernel_established`) or by another grounded
/// candidate — computed as a LEAST fixed point, so an assumption cycle (an
/// obligation that is, directly or through others, its own premise) never
/// grounds, and the result does not depend on the row order. A refused
/// obligation grounds nothing and stays refused. Of an obligation's grounded
/// candidates the stronger bound is kept; with none grounded, the obligation
/// is `PremiseNotEstablished`.
fn resolve_premises(
    obligations: &mut BTreeMap<ProofId, ObligationCoverage>,
    candidates: Vec<Candidate>,
    kernel_established: BTreeSet<ProofId>,
) {
    let refused = |obligations: &BTreeMap<ProofId, ObligationCoverage>, id: &ProofId| {
        matches!(obligations.get(id), Some(ObligationCoverage::Refused(_)))
    };
    let mut unbounded = kernel_established;
    let mut grounded = vec![false; candidates.len()];
    loop {
        let mut progressed = false;
        for (index, candidate) in candidates.iter().enumerate() {
            if grounded[index] || refused(obligations, &candidate.obligation) {
                continue;
            }
            if candidate
                .basis
                .premises
                .iter()
                .all(|premise| unbounded.contains(premise))
            {
                grounded[index] = true;
                progressed = true;
                if candidate.bound == CoverageBound::Unbounded {
                    unbounded.insert(candidate.obligation);
                }
            }
        }
        if !progressed {
            break;
        }
    }
    for (candidate, grounded) in candidates.into_iter().zip(grounded) {
        let Candidate {
            obligation,
            bound,
            basis,
        } = candidate;
        let Some(current) = obligations.get_mut(&obligation) else {
            continue;
        };
        let replace = match current {
            ObligationCoverage::Refused(_) => false,
            ObligationCoverage::Undetermined { .. } => true,
            ObligationCoverage::Established { bound: kept, .. } => {
                grounded && !coverage_supports(*kept, bound)
            }
        };
        if !replace {
            continue;
        }
        if grounded {
            *current = ObligationCoverage::Established { bound, basis };
        } else if let Some(premise) = basis
            .premises
            .iter()
            .find(|premise| !unbounded.contains(premise))
        {
            *current = ObligationCoverage::Undetermined {
                reason: CoverageUndeterminedReason::PremiseNotEstablished { premise: *premise },
            };
        }
    }
}

fn establish_row(
    admitted: &NativeVerificationBundle,
    row: &NativeCoverageAttestationRow,
    inputs: &CoverageInputs<'_>,
    solved: &mut SolvedCandidates<'_>,
) -> RowOutcome {
    let obligation = row.obligation.index();
    let module = &admitted.module;
    let refuse = RowOutcome::Refused;
    let undetermined = RowOutcome::Undetermined;

    // (a) The solved bundle: supplied, and valid.
    let Some(index) = solved.find(row.solved_bundle_digest) else {
        return refuse(ValidationError::CoverageSolvedBundleMissing {
            obligation,
            recorded: row.solved_bundle_digest,
            supplied: solved.supplied,
        });
    };
    if let Err(detail) = solved.validated(index) {
        return refuse(ValidationError::CoverageSolvedBundleInvalid { obligation, detail });
    }
    let solved_bundle = solved.bundles[index];
    let solved_module = &solved_bundle.module;

    // (b) The solved module's identities recompute. `validate` has already
    // bound `trust_ir_module_digest` to the embedded module.
    if solved_bundle.trust_ir_module_digest != row.solved_module_digest {
        return refuse(ValidationError::CoverageSolvedBundleDigestMismatch {
            obligation,
            field: "solved_module_digest",
            recorded: row.solved_module_digest,
            actual: solved_bundle.trust_ir_module_digest,
        });
    }
    let solved_content = solved.content(index);
    if solved_content != row.solved_executable_content_digest {
        return refuse(ValidationError::CoverageSolvedBundleDigestMismatch {
            obligation,
            field: "solved_executable_content_digest",
            recorded: row.solved_executable_content_digest,
            actual: solved_content,
        });
    }

    // (c) The request: in the solved bundle, about this obligation.
    let Some(request) = solved_bundle
        .requests
        .iter()
        .find(|request| request.stable_digest() == row.request_digest)
    else {
        return refuse(ValidationError::CoverageAssuranceRequestUnknown {
            obligation,
            recorded: row.request_digest,
            bundle_requests: solved_bundle.requests.len(),
        });
    };
    let requested = request.obligations();
    if !requested.contains(&row.obligation) {
        return refuse(ValidationError::CoverageAssuranceObligationNotRequested {
            obligation,
            request: request.id().index(),
            request_obligations: requested.iter().map(|id| id.index()).collect(),
        });
    }
    // Each obligation's goal is its CLAIM in the context, never a formula the
    // request carries: an `Assertion` atom stating anything else is refused.
    // (An `Assumption` atom derives no bound: step (i).)
    if let Some(detail) = assertion_atom_mismatch(request, solved_module) {
        return refuse(ValidationError::CoverageClaimDrift { obligation, detail });
    }

    // (d) The result evidence: present for this obligation, digest recomputes.
    let Some(evidence) = solved_bundle.evidence_bundles.iter().find(|evidence| {
        evidence.request() == request.id()
            && evidence.verifier_suite() == request.verifier_suite()
            && evidence.obligations().contains(&row.obligation)
    }) else {
        return refuse(ValidationError::CoverageEvidenceMissing {
            obligation,
            request: request.id().index(),
        });
    };
    if evidence.stable_digest() != row.evidence_bundle_digest {
        return refuse(ValidationError::CoverageEvidenceDigestMismatch {
            obligation,
            request: request.id().index(),
            recorded: row.evidence_bundle_digest,
        });
    }

    // (e) The result bytes: each a descriptor of that evidence, each resolved.
    let mut resolved: Vec<NativeEvidenceArtifactAttachment> = Vec::new();
    for artifact in &row.result_artifacts {
        if !evidence.artifacts().contains(artifact) {
            return refuse(ValidationError::CoverageResultArtifactUnresolved {
                obligation,
                artifact: artifact.name.clone(),
                reason: "not_a_descriptor_of_the_cited_evidence".to_string(),
            });
        }
        let key = NativeEvidenceArtifactAttachmentKey::for_artifact(request.id(), artifact);
        let resolution =
            solved_bundle.resolve_evidence_artifact_attachment(key, inputs.attachments);
        if resolution.authoritative_bytes().is_none() {
            return refuse(ValidationError::CoverageResultArtifactUnresolved {
                obligation,
                artifact: artifact.name.clone(),
                reason: resolution.report.reason.code().to_string(),
            });
        }
        resolved.extend(
            inputs
                .attachments
                .iter()
                .filter(|attachment| attachment.key == key)
                .cloned(),
        );
    }

    // (f) Nothing the consumer holds contradicts the obligation, and the
    // admitted module states it.
    let status_of = |module: &trust_ir::Module, id: ProofId| {
        module
            .proof_obligations
            .iter()
            .find(|candidate| candidate.id == id)
            .map(|candidate| candidate.status)
    };
    if status_of(solved_module, row.obligation) == Some(ProofStatus::Failed) {
        return refuse(ValidationError::CoverageContradicted {
            obligation,
            detail: "the obligation is Failed in the solved module".to_string(),
        });
    }
    match status_of(module, row.obligation) {
        None => {
            return refuse(ValidationError::CoverageClaimDrift {
                obligation,
                detail: "the admitted module has no such obligation".to_string(),
            });
        }
        Some(ProofStatus::Failed) => {
            return refuse(ValidationError::CoverageContradicted {
                obligation,
                detail: "the obligation is Failed in the admitted module".to_string(),
            });
        }
        Some(_) => {}
    }

    // (g) The admitted bundle is about the same code, the same claim and the
    // same replay context.
    let admitted_content = solved.content(SolvedCandidates::ADMITTED);
    if admitted_content != row.solved_executable_content_digest {
        return refuse(ValidationError::CoverageSubjectCodeDrift {
            obligation,
            solved: row.solved_executable_content_digest,
            admitted: admitted_content,
        });
    }
    // A transfer that is UNDETERMINED (a Goal on any function of either
    // bundle) does not end the row: a refusal is fatal for the whole bundle,
    // so every check below that can still refuse the row runs first, and the
    // first undetermined reason is the verdict only at step (j).
    let transfer = match transfer_check(solved, index, row) {
        TransferCheck::Same(context) => Ok(context),
        TransferCheck::Undetermined(reason) => Err(reason),
        TransferCheck::Refused(error) => return refuse(error),
    };

    // (h) The replay, of the SOLVED bundle, whatever the transfer can carry.
    // With no replayer, or no decision, nothing below can run.
    let Some(replay) = inputs.replay else {
        return undetermined(
            transfer
                .err()
                .unwrap_or(CoverageUndeterminedReason::NoReplayer),
        );
    };
    let result = match replay.replay(solved_bundle, request, evidence, &resolved) {
        Ok(result) => result,
        Err(NativeCoverageReplayRefusal::Inconclusive { reason, detail }) => {
            return undetermined(
                transfer
                    .err()
                    .unwrap_or(CoverageUndeterminedReason::ReplayInconclusive { reason, detail }),
            );
        }
        Err(NativeCoverageReplayRefusal::Refuted {
            obligations,
            detail,
        }) => {
            return refuse(ValidationError::CoverageContradicted {
                obligation,
                detail: format!(
                    "the replay re-established a refutation of obligation(s) {:?}: {detail}",
                    obligations.iter().map(|id| id.index()).collect::<Vec<_>>()
                ),
            });
        }
        Err(NativeCoverageReplayRefusal::Invalid { detail }) => {
            return refuse(ValidationError::CoverageResultReplayInvalid { obligation, detail });
        }
        // A refusal this build cannot classify is read as the result being
        // wrong: never as coverage, and never silently.
        Err(other) => {
            return refuse(ValidationError::CoverageResultReplayInvalid {
                obligation,
                detail: format!("unclassified replay refusal: {other:?}"),
            });
        }
    };
    // (h') The premises the result names: each an obligation both modules
    // state (the context binds its claim), none of them Failed. Whether each
    // is ESTABLISHED is step 3's, over the whole report.
    let mut premises = result.premises.clone();
    premises.sort();
    premises.dedup();
    for premise in &premises {
        for (side, side_module) in [("solved", solved_module), ("admitted", module)] {
            match status_of(side_module, *premise) {
                None => {
                    return refuse(ValidationError::CoverageResultReplayInvalid {
                        obligation,
                        detail: format!(
                            "the replay names premise #{}, which the {side} module does not state",
                            premise.index()
                        ),
                    });
                }
                Some(ProofStatus::Failed) => {
                    return refuse(ValidationError::CoverageContradicted {
                        obligation,
                        detail: format!(
                            "the result rests on premise #{}, which is Failed in the {side} module",
                            premise.index()
                        ),
                    });
                }
                Some(_) => {}
            }
        }
    }

    // (i) Mode and strength must agree, whatever the result models.
    let bound = match bound_of_mode_and_strength(request, result.strength) {
        Ok(bound) => bound,
        Err(mismatch) => {
            return refuse(ValidationError::CoverageModeStrengthMismatch {
                obligation,
                request: request.id().index(),
                mode: mismatch.mode,
                strength: mismatch.strength.code(),
            });
        }
    };

    // (j) Nothing left can refuse the row: the first undetermined reason is
    // the verdict. The result must transfer, model the obligation, and have
    // been asked under the obligation's machine semantics.
    let replay_context_digest = match transfer {
        Ok(context) => context,
        Err(reason) => return undetermined(reason),
    };
    if !result.obligations.contains(&row.obligation) {
        return undetermined(CoverageUndeterminedReason::ObligationNotModeled);
    }
    if let Some(divergence) = request_machine_semantics_divergence(request) {
        return undetermined(CoverageUndeterminedReason::RequestNotMachineSemantics { divergence });
    }
    RowOutcome::Established {
        bound,
        basis: VerifiedSolverResult {
            obligation: row.obligation,
            row_digest: row.stable_digest(),
            solved_bundle_digest: row.solved_bundle_digest,
            request_digest: row.request_digest,
            evidence_bundle_digest: row.evidence_bundle_digest,
            replay_context_digest,
            strength: result.strength,
            premises,
        },
    }
}

enum TransferCheck {
    /// The claim and the whole replay context carry over; the context digest.
    Same(ProofDigest),
    Refused(ValidationError),
    /// Every digest the row cites was held to it and nothing drifted, but a
    /// clean-expr `Goal` (outside every wire image, so outside the context
    /// digest) leaves nothing to transfer. The row's verdict only if no later
    /// check refuses it.
    Undetermined(CoverageUndeterminedReason),
}

/// The cited result is about `row.obligation_digest`, solved in the replay
/// context `row.solved_replay_context_digest`. The SOLVED bundle must
/// recompute both (else the row lies about its own subject), and the ADMITTED
/// bundle must too (else the claim, or anything else outside the write-back
/// allowlist — an assumed precondition, a callee contract, a compiler fact, a
/// body annotation — drifted after the solve).
///
/// Every cited digest is checked whatever else is undetermined: the context
/// digest binds everything a wire image binds, so it exists also when a
/// clean-expr `Goal` (in no wire image) sits in either bundle, and both sides
/// are held to the citation before that Goal can leave the row undetermined.
/// A Goal therefore neither causes nor excuses a refusal: it only withholds
/// the transfer.
fn transfer_check(
    candidates: &mut SolvedCandidates<'_>,
    index: usize,
    row: &NativeCoverageAttestationRow,
) -> TransferCheck {
    let solved = candidates.bundles[index];
    let admitted = candidates.bundles[SolvedCandidates::ADMITTED];
    let obligation = row.obligation.index();
    match solved.module.obligation_digest(row.obligation) {
        Some(digest) if digest.0 == row.obligation_digest => {}
        Some(digest) => {
            return TransferCheck::Refused(ValidationError::CoverageSolvedBundleDigestMismatch {
                obligation,
                field: "obligation_digest",
                recorded: row.obligation_digest,
                actual: digest.0,
            });
        }
        None => {
            return TransferCheck::Refused(ValidationError::CoverageClaimDrift {
                obligation,
                detail: "the solved module's claim digest cannot be computed".to_string(),
            });
        }
    }
    match admitted.module.obligation_digest(row.obligation) {
        Some(digest) if digest.0 == row.obligation_digest => {}
        Some(digest) => {
            return TransferCheck::Refused(ValidationError::CoverageClaimDrift {
                obligation,
                detail: format!(
                    "the result is about claim {}, the admitted module states claim {}",
                    row.obligation_digest, digest.0
                ),
            });
        }
        None => {
            return TransferCheck::Refused(ValidationError::CoverageClaimDrift {
                obligation,
                detail: "the admitted module's claim digest cannot be computed".to_string(),
            });
        }
    }
    // An ambiguous context has no identity on either side: refused.
    let unavailable = |side: &str, reason: NativeReplayContextUnavailable| {
        let detail = match reason {
            NativeReplayContextUnavailable::Unindexable => format!(
                "the replay context of the {side} bundle cannot be computed (its obligation \
                 table cannot be indexed)"
            ),
            // A reason this build cannot classify refuses the row: never
            // coverage, and never silently.
            other => {
                format!("the replay context of the {side} bundle cannot be computed: {other}")
            }
        };
        TransferCheck::Refused(ValidationError::CoverageClaimDrift { obligation, detail })
    };
    let solved_context = match candidates.context(index) {
        Ok(context) => context,
        Err(reason) => return unavailable("solved", reason),
    };
    let admitted_context = match candidates.context(SolvedCandidates::ADMITTED) {
        Ok(context) => context,
        Err(reason) => return unavailable("admitted", reason),
    };
    // The row's citation of the SOLVED context is a forgery check, and the
    // admitted context must be the same one — whatever Goal either carries.
    if solved_context.digest != row.solved_replay_context_digest {
        return TransferCheck::Refused(ValidationError::CoverageSolvedBundleDigestMismatch {
            obligation,
            field: "solved_replay_context_digest",
            recorded: row.solved_replay_context_digest,
            actual: solved_context.digest,
        });
    }
    if admitted_context.digest != row.solved_replay_context_digest {
        return TransferCheck::Refused(ValidationError::CoverageClaimDrift {
            obligation,
            detail: format!(
                "the replay context drifted: {}; a result transfers only to a module stating \
                 every assumption it may rest on",
                describe_context_drift(solved, admitted)
            ),
        });
    }
    // Nothing drifted in what a digest binds; a Goal outside it withholds the
    // transfer.
    match solved_context
        .transferable()
        .and(admitted_context.transferable())
    {
        Ok(context) => TransferCheck::Same(context),
        Err(function) => {
            TransferCheck::Undetermined(CoverageUndeterminedReason::GoalAnnotationUnbound {
                function,
            })
        }
    }
}

/// Name the first part of the replay context that differs, for the refusal
/// message only (the verdict is the digest comparison).
fn describe_context_drift(
    solved: &NativeVerificationBundle,
    admitted: &NativeVerificationBundle,
) -> String {
    if let (Some(solved_index), Some(admitted_index)) = (
        solved.module.obligation_digest_index(),
        admitted.module.obligation_digest_index(),
    ) {
        let mut ids: Vec<ProofId> = solved
            .module
            .proof_obligations
            .iter()
            .chain(&admitted.module.proof_obligations)
            .map(|obligation| obligation.id)
            .collect();
        ids.sort();
        ids.dedup();
        for id in ids {
            let (was, is) = (solved_index.get(id), admitted_index.get(id));
            if was != is {
                let state = |digest: Option<trust_ir::ObligationDigest>| {
                    digest.map_or_else(
                        || "has no such obligation".to_string(),
                        |digest| format!("states claim {}", digest.0),
                    )
                };
                return format!(
                    "obligation #{}: the result was solved in a context that {}, the admitted \
                     module {}",
                    id.index(),
                    state(was),
                    state(is)
                );
            }
        }
    }
    if solved.compiler_facts.stable_digest() != admitted.compiler_facts.stable_digest() {
        return "the admitted bundle's compiler facts are not the ones the result was solved \
                with"
            .to_string();
    }
    "the admitted bundle differs from the solved one outside the write-back allowlist (a \
     body, a function field, an obligation's id or order, the adapter input, the producer, \
     the provenance or a policy)"
        .to_string()
}
