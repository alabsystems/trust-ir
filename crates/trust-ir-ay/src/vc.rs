// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Whole-function verification-condition (VC) generation.
//!
//! This module replaces the historical "batch stub" path
//! (docs/roadmap/integration-ay-vc.md): given a [`Function`], it walks the
//! body, binds every SSA value to a solver term through the symbol-binding
//! schema ([`crate::ay_symbol`] / [`crate::ay_sort`]), encodes each supported
//! instruction with the per-op encoders the adapter already owns
//! ([`crate::encode_binop`], [`crate::encode_icmp`], [`crate::MemoryModel`],
//! [`crate::BorrowModel`], [`crate::ArcModel`], …), and checks every VC
//! condition the body carries: `Inst::Assert` conditions plus the encodable
//! instruction-level proof annotations.
//!
//! # Scope — honest and fail-closed
//!
//! * **Straight-line bodies only (v1).** The whole-function walk covers a
//!   single entry block ending in `Return`. Control flow (`Br`/`CondBr`/
//!   `Switch`), calls, atomics, aggregates, and every other unencoded
//!   instruction abort the walk with [`AYError::UnsupportedOp`] /
//!   [`AYError::UnsupportedType`] — there is no silent havoc: an unencodable
//!   instruction is never approximated. Such a body (and every multi-block
//!   body) gets the SITED VC instead: one block-local, hypothesis-free
//!   condition per obligation site, which can lose proofs but never mint one
//!   (WS5.4 (2); the walk's refusal is kept in
//!   [`FunctionVc::whole_function_fallback`]).
//! * **Annotations.** Encodable annotations (`NoOverflow`/`NoWrap`,
//!   `DivNonZero`, `ShiftInRange`, `NotNull`, `Aligned`, and the borrow
//!   family) become solver-checked conditions over the node's actual operand
//!   terms. Claim-style hints with no operational obligation (`Wrapping`,
//!   memory-role/GPU hints, `ValueRange`, `KnownBits`, `BranchWeights`,
//!   `ProofRef`, `Custom`) are skipped, per the documented trust boundary.
//!   Obligation-bearing annotations the BV/FP encoding cannot express — the
//!   `DataRaceFree` concurrency class, NN bounds, liveness, dual-evaluation
//!   properties, `InBounds` (no length operand exists on the IR node) — are
//!   surfaced as structured [`VcVerdict::Unsupported`] entries, so a report
//!   containing one can never read as a full PASS.
//! * **Obligations (B4).** Module obligations scoped to the function
//!   (`ProofObligation::function == Some(id)`) are reported with an explicit
//!   [`VcObligationOutcome`]. An obligation is `ProvedByVc` only when the
//!   conditions generated at its site exist and all proved. A row sited on an
//!   assert-shaped node must be of an assert-class kind
//!   ([`trust_ir::proof::ASSERT_CLASS_OBLIGATION_KINDS`]); any other kind is
//!   `Unsupported` there (WS5.4 (1a)). A formula-carrying obligation is
//!   addressed only when its formula states the goal re-derived at its site
//!   ([`trust_ir::proof::formula_binds_site_goal`]); any other formula fails
//!   closed (`Unsupported`) because the adapter has no in-process SMT-LIB
//!   bridge (WS5.4 (1b)).
//! * **Counterexamples.** A refuting model is mapped back to
//!   `(ValueId, ModelValue)` pairs over the schema-bound symbols (the
//!   function's parameters), feeding the diagnostics counterexample payload
//!   (docs/roadmap/diagnostics-representation.md).
//!
//! Determinism: symbols come from [`crate::ay_symbol`] (a pure function of
//! ids), bindings/conditions are collected in body order in `Vec`s (no map
//! iteration), so the same module yields the same VC — and the same model
//! back-translation — on every machine.

use ay::{Model, ModelValue, Solver, Sort, Term};

use trust_ir::inst::{BinOp, Inst, OverflowOp};
use trust_ir::proof::{
    ObligationDiagnostic, ObligationKind, PRODUCER_FORMULA_DISAGREES, ProofAnnotation, ProofDigest,
    ProofObligation, ProofStatus, assert_class_kind_refusal, derive_site_goal,
    formula_binds_site_goal, is_assert_class_kind, is_assert_site_inst,
};
use trust_ir::ty::Ty;
use trust_ir::value::{BlockId, FuncId, ProofId, ValueId};
use trust_ir::{Constant, Function, InstrNode, Module};

use crate::{
    AYError, ArcModel, BorrowModel, MemoryModel, ProofCondition, ProofOperands, ay_sort, ay_symbol,
    create_fp_solver, encode_binop, encode_cast, encode_fcmp, encode_icmp, encode_overflow_check,
    encode_unop, encode_vector_binop, encode_vector_unop, verify_proof_obligation,
};

/// Where a VC condition came from.
#[derive(Debug, Clone, PartialEq)]
pub enum VcSource {
    /// An `Inst::Assert { cond }` in the body: the VC that `cond` always
    /// holds under the preceding `Assume`s and instruction semantics.
    Assert,
    /// An instruction-level proof annotation, checked over the node's actual
    /// operand terms.
    Annotation(ProofAnnotation),
    /// A SITED assert: the node at a [`trust_ir::ObligationSite`] is either an
    /// `Inst::Assert { cond }` (the direct lane's shape — the VC is that `cond`
    /// holds) or a lowered `CondBr` exactly one of whose successors diverges (a
    /// `core::panicking` arm ending `Unreachable` — the VC is that control never
    /// takes the diverging arm). Both are read by the one shared
    /// [`trust_ir::proof::lowered_assert_condition`].
    LoweredAssert {
        /// The module obligation whose `site` selected this node.
        obligation: ProofId,
        /// The value the condition must take to avoid the diverging arm.
        expected: bool,
    },
}

/// Verdict for a single VC condition.
#[derive(Debug, Clone, PartialEq)]
pub enum VcVerdict {
    /// The negated condition is UNSAT: the condition holds for all inputs
    /// (trusted via the `ay_sound_unsat` boundary, `AYBridge.lean`).
    Proved,
    /// The negated condition is SAT: the condition can be violated.
    /// `counterexample` is the witness ay vouches for, or why there is none.
    Refuted {
        /// A consumer-accepted model mapped back to source values, or the
        /// typed reason ay gave no such model. Never an empty stand-in for a
        /// missing model.
        counterexample: Counterexample,
    },
    /// The solver could not decide (timeout / resource limit), or the solver
    /// session could not be trusted to decide (a solver frame failed to open
    /// or close — see `reason`). Never `Proved`.
    Unknown {
        /// Why no verdict exists.
        reason: String,
    },
    /// Fail-closed: the annotation has no BV/FP encoding (the
    /// `DataRaceFree`-class fallthrough of [`verify_proof_obligation`]).
    /// Surfaced structurally so it can never be mistaken for a PASS.
    Unsupported {
        /// Why the condition could not be encoded.
        reason: String,
    },
}

/// The witness of a [`VcVerdict::Refuted`] condition.
///
/// ay answered SAT. What backs that answer is either a model ay itself
/// accepts for a consumer ([`Self::Model`]), or nothing it will vouch for
/// ([`Self::Unavailable`], with ay's typed reason). The two used to share one
/// spelling — an EMPTY assignment list — which presented "no model" as "a
/// model that assigns nothing".
#[derive(Debug, Clone, PartialEq)]
pub enum Counterexample {
    /// A consumer-accepted model projected onto the bound symbols, in
    /// binding (declaration) order. Empty only when the model assigns none of
    /// the bound symbols.
    Model(Vec<(ValueId, ModelValue)>),
    /// ay answered SAT but gave no consumer-accepted witness.
    Unavailable(WitnessUnavailable),
}

/// Why a SAT answer carries no consumer-accepted model.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum WitnessUnavailable {
    /// ay did not accept its own SAT model for a consumer
    /// (`SolverError::SatModelNotValidated`).
    NotValidated,
    /// Model generation failed; ay's message.
    GenerationFailed(String),
    /// The solver held no SAT result to take a model from
    /// (`SolverError::NoResult` / `SolverError::NotSat`).
    NoSatResult,
}

impl core::fmt::Display for WitnessUnavailable {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Self::NotValidated => f.write_str("ay did not validate its SAT model for a consumer"),
            Self::GenerationFailed(message) => write!(f, "model generation failed: {message}"),
            Self::NoSatResult => f.write_str("the solver holds no SAT result"),
        }
    }
}

/// The ONE place a SAT answer becomes a witness: ay's consumer-boundary model
/// (`Solver::try_get_model_for_consumer`, which requires the model to have
/// passed ay's own validation), projected onto `bindings`. Both solve paths
/// call it; neither falls back to the unvalidated `Solver::model()`.
fn sat_witness(solver: &Solver, bindings: &[(ValueId, String)]) -> Counterexample {
    match solver.try_get_model_for_consumer() {
        Ok(model) => Counterexample::Model(model_counterexample(model.model(), bindings)),
        Err(ay::SolverError::SatModelNotValidated) => {
            Counterexample::Unavailable(WitnessUnavailable::NotValidated)
        }
        Err(ay::SolverError::NoResult | ay::SolverError::NotSat) => {
            Counterexample::Unavailable(WitnessUnavailable::NoSatResult)
        }
        Err(other) => {
            Counterexample::Unavailable(WitnessUnavailable::GenerationFailed(other.to_string()))
        }
    }
}

/// One condition of a whole-function VC, tied to the body position that
/// produced it.
#[derive(Debug, Clone, PartialEq)]
pub struct VcCondition {
    /// Block containing the originating instruction.
    pub block: BlockId,
    /// Index of the originating instruction within the block body.
    pub inst_index: usize,
    /// What the condition asserts.
    pub source: VcSource,
    /// The solver's verdict.
    pub verdict: VcVerdict,
    /// The replayable UNSAT payload, present only when the verdict is `Proved`
    /// AND the payload passed an OFFLINE re-check at capture time. `None`
    /// otherwise — a bundle that does not replay is never attached, so this
    /// field cannot carry an unreplayable claim.
    pub evidence: Option<SmtReplayEvidence>,
}

/// A `Proved` verdict's replayable UNSAT proof, captured from ay and verified
/// to REPLAY before it is attached.
///
/// The distinction that matters: the in-solver acceptance path
/// (`UnsatProofArtifact::accept_for_consumer(Strict)`) can return `Ok` via a
/// "deferred-trust rescue" that RE-RUNS FRESH SOLVERS to discharge an opaque
/// `:rule trust` step. That is ay certifying its own proof, and accepting it
/// would put ay back inside the trusted base. The gate here is instead
/// `ay::re_check_bundle_strict`, which runs no solver, plus a hard
/// `trust_count == 0` requirement so not a single step is taken on faith.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SmtReplayEvidence {
    /// The exact ay revision that produced the payload. `ay.proofbundle/v2` is
    /// tied to the linked ay-core representation, not a stable cross-version
    /// format, so a certificate minted at one rev becomes unreplayable after a
    /// rev bump. Recording the rev makes that a visible event.
    pub ay_rev: &'static str,
    /// The bundle's own schema tag (`ay.proofbundle/v2`).
    pub bundle_schema: String,
    /// The serialized bundle (JSON).
    pub bundle_bytes: Vec<u8>,
    /// Canonical rendering of the term whose UNSAT the bundle certifies — the
    /// NEGATION of the obligation's condition. Carried so a consumer can see
    /// WHAT was proved without re-deriving it.
    pub goal_canonical: String,
    /// Steps in the replayed proof that were taken on trust. Always 0: a
    /// nonzero count means the payload was rejected and never attached.
    pub trust_count: u32,
}

/// The exact ay revision this adapter is pinned to (see `Cargo.toml`).
pub const AY_REV: &str = "12d411d420e27eea05099f8cd277eb288e8622c9";

/// Re-check a captured proof bundle OFFLINE — no solver run, no network, no
/// producer cooperation.
///
/// This is the honest gate for any status flip. Returns the replayed step
/// quality on success. A bundle whose replay reports ANY trust step is
/// rejected here even though ay's own strict verdict would accept it.
pub fn replay_bundle_offline(bundle_bytes: &[u8]) -> Result<u32, String> {
    let bundle: ay::SerializableProofBundle = serde_json::from_slice(bundle_bytes)
        .map_err(|e| format!("proof bundle does not deserialize: {e}"))?;
    if bundle.schema != ay::PROOF_BUNDLE_SCHEMA {
        return Err(format!(
            "proof bundle schema is {:?}, expected {:?}",
            bundle.schema,
            ay::PROOF_BUNDLE_SCHEMA
        ));
    }
    let recheck = ay::re_check_bundle_strict(&bundle)
        .map_err(|e| format!("offline re-check rejected the proof: {e:?}"))?;
    if recheck.quality.trust_count != 0 {
        return Err(format!(
            "offline re-check passed but the proof carries {} opaque trust step(s); \
             a trust step is a step NOT independently verified, so this payload is not \
             replayable evidence",
            recheck.quality.trust_count
        ));
    }
    if recheck.assume_terms.is_empty() {
        return Err(
            "offline re-check reports no assumed axioms; a refutation of nothing proves nothing"
                .to_string(),
        );
    }
    Ok(recheck.quality.trust_count)
}

/// Outcome for a module proof obligation scoped (B4) to the verified function.
#[derive(Debug, Clone, PartialEq)]
pub enum VcObligationOutcome {
    /// Every VC condition the body produced was proved (and there was at
    /// least one), so the in-process solver backs this obligation. This is a
    /// solver verdict, not discharge authority. AY can export a zero-trust
    /// replayable bundle for supported symbolic goals, but this generic path
    /// does not independently bind the replayed goal to the live IR; applying
    /// this outcome therefore leaves the public obligation status `Pending`.
    ProvedByVc,
    /// The VC does not back the obligation: no encodable conditions, or at
    /// least one condition failed to prove.
    NotDischarged {
        /// Why the obligation is not backed.
        reason: String,
    },
    /// Fail-closed: the obligation is outside what this VC can honestly
    /// address (formula payloads, out-of-scope kinds).
    Unsupported {
        /// Why the obligation is out of scope.
        reason: String,
    },
}

/// The result of whole-function VC generation for one function.
#[derive(Debug, Clone)]
pub struct FunctionVc {
    /// Digest of the exact module snapshot from which this VC was generated.
    /// Kept private so external callers cannot forge a cross-module apply.
    source_module_digest: ProofDigest,
    /// Sealed application inputs. Public report fields remain inspectable for
    /// compatibility, but mutating them cannot redirect proof-table updates.
    application_obligations: Vec<(ProofId, VcObligationOutcome)>,
    /// Refutations backed by a consumer-accepted model: the only ones that
    /// may mint `Failed` (see [`apply_vc_outcomes`]).
    application_refutations: Vec<VcCondition>,
    /// SAT answers ay would not vouch for ([`Counterexample::Unavailable`]):
    /// reported, never used to mint `Failed`.
    application_unwitnessed: Vec<VcCondition>,
    /// Sealed replay evidence per proved obligation. Sealed for the same reason
    /// the outcomes are: a caller must not be able to hand `apply_vc_outcomes`
    /// a payload the solver never produced.
    application_evidence: Vec<(ProofId, SmtReplayEvidence)>,
    /// The verified function.
    pub func: FuncId,
    /// Schema-bound symbols declared for this VC, in declaration order:
    /// `(value, ay_symbol(func, value))`. These are the names a refuting
    /// model assigns; [`model_counterexample`] maps them back.
    pub bindings: Vec<(ValueId, String)>,
    /// Every condition checked (or surfaced as unsupported), in body order.
    pub conditions: Vec<VcCondition>,
    /// Function-level proof annotations that carry an obligation the VC
    /// cannot encode, with the reason. Claim-style hints are not listed
    /// (they carry no obligation). A non-empty list means the function's
    /// own claims are NOT fully covered by this VC.
    pub unsupported_function_proofs: Vec<(ProofAnnotation, String)>,
    /// Outcome for each module obligation scoped to this function (B4),
    /// in module order.
    pub obligations: Vec<(ProofId, VcObligationOutcome)>,
    /// `Some(refusal)` when this single-block body's whole-function walk
    /// refused (`UnsupportedOp` / `UnsupportedType`) and the SITED VC was
    /// generated instead (WS5.4 (2)). The refusal is kept, typed and verbatim,
    /// so the fallback never hides WHY the stronger VC was unavailable. `None`
    /// for a whole-function VC and for a multi-block body (which only ever gets
    /// the sited VC).
    pub whole_function_fallback: Option<AYError>,
}

impl FunctionVc {
    /// Digest of the exact module snapshot from which this VC was generated.
    pub fn source_module_digest(&self) -> ProofDigest {
        self.source_module_digest
    }

    /// True iff every collected condition was proved. `Unsupported` and
    /// `Unknown` verdicts count as not proved (fail-closed). Note this is
    /// vacuously true for a body with no conditions; obligation outcomes
    /// guard against vacuous discharge separately.
    ///
    /// Always `false` for a sited FALLBACK ([`Self::whole_function_fallback`]
    /// is `Some`, WS5.4 (2)): the whole-function walk that would have turned
    /// every body `Assert` and instruction annotation into a condition REFUSED,
    /// and the sited VC that replaced it covers only sited obligations. Before
    /// the fallback existed such a body was an `Err`; answering `true` for it
    /// now — over a condition list that silently omits the unsited checks —
    /// would turn a refusal into a vacuous pass.
    pub fn all_proved(&self) -> bool {
        self.whole_function_fallback.is_none()
            && self
                .conditions
                .iter()
                .all(|c| matches!(c.verdict, VcVerdict::Proved))
    }

    /// Conditions the solver refuted, with their counterexamples.
    pub fn refuted(&self) -> impl Iterator<Item = &VcCondition> {
        self.conditions
            .iter()
            .filter(|c| matches!(c.verdict, VcVerdict::Refuted { .. }))
    }

    /// Conditions surfaced as structurally unsupported (fail-closed).
    pub fn unsupported(&self) -> impl Iterator<Item = &VcCondition> {
        self.conditions
            .iter()
            .filter(|c| matches!(c.verdict, VcVerdict::Unsupported { .. }))
    }
}

/// Failure to apply a whole-function VC to a module.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum VcApplyError {
    /// The module changed, or the VC came from a different module. Applying
    /// its verdicts would cross-wire proof ids and counterexamples.
    ModuleDigestMismatch {
        expected: ProofDigest,
        actual: ProofDigest,
    },
}

impl core::fmt::Display for VcApplyError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Self::ModuleDigestMismatch { expected, actual } => write!(
                f,
                "whole-function VC was generated for module {expected}, but apply target is {actual}"
            ),
        }
    }
}

impl std::error::Error for VcApplyError {}

/// Apply a checked [`FunctionVc`]'s obligation outcomes to the module's proof
/// tables (the WS3-M1 contracts-flow seed). `Pending` obligations the VC
/// refuted become `Failed` with an [`ObligationDiagnostic`] carrying the
/// refutation reason and the counterexample(s). Proved outcomes remain
/// `Pending` — but for a DIFFERENT reason than this doc used to give, and the
/// difference is the whole state of the art here:
///
/// * **Obsolete reason.** "ay does not export a replayable UNSAT-proof
///   payload." FALSE at the pinned rev. `Solver::set_produce_proofs(true)` +
///   `Solver::export_last_unsat_bundle()` yield an `ay.proofbundle/v2` that
///   `ay::re_check_bundle_strict` re-checks with NO solver run. For the
///   constant-comparison conditions the sited VC proves, the re-check accepts
///   with `trust_count == 0` — not one step taken on faith. `apply_vc_outcomes`
///   captures those payloads and records them (see [`SmtReplayEvidence`]).
/// * **Actual remaining reason.** `Discharged` is structurally unreachable in a
///   valid module: `validate_discharged_authority` requires a certificate in an
///   authority set that `validated_authority_refs` builds ONLY from `Certified`
///   obligations' kernel-rechecked CleanCic terms. No SMT evidence of any kind
///   admits a `Discharged` row today. Granting one needs the validator to (a)
///   replay the bundle itself and (b) bind the replayed refutation to THIS
///   obligation's goal — i.e. re-derive the goal from the IR rather than trust
///   the producer's label. Until (b) exists, a `Discharged` flip would rest on
///   a producer-asserted obligation<->goal link, which is precisely the
///   faith-stamping the fail-closed rules here exist to prevent.
///
/// Returns the status transitions performed, in `vc.obligations` (module) order.
///
/// Fail-closed rules — every one deliberate:
///
/// * **`Pending`-only.** A recorded verdict is never overwritten: a `Failed`
///   obligation cannot be laundered by re-running the VC,
///   and `Trusted`/`Certified`/`Discharged` rows are left for their own gates.
/// * **Exact module identity.** The target module must have the stable digest
///   captured during VC generation. This rejects stale results and prevents a
///   VC for one module from mutating same-numbered obligations in another.
/// * **`Failed` requires a real refutation.** `NotDischarged` without at least
///   one `Refuted` condition (a vacuous body, `Unknown`/`Unsupported`
///   conditions) leaves the obligation `Pending` — no evidence either way, so
///   no verdict is invented in either direction. A SAT answer whose witness ay
///   will not vouch for ([`Counterexample::Unavailable`]) is not a real
///   refutation either: the obligation stays `Pending`, with an INFO
///   diagnostic naming the reason. (Owner decision D3 of the r11 design: to
///   let such a SAT mint `Failed` instead, admit `Unavailable` witnesses into
///   `application_refutations` in `finish` — one filter.)
/// * **`Precondition` obligations never transition.** The body *assumes* its
///   `requires` clauses; they are established by callers (the B5 call-site
///   flow, outside this seed's scope). A body VC can neither discharge nor
///   refute them, so they stay `Pending` here.
/// * **No success status is minted.** A proved obligation gets an INFO-level
///   [`ObligationDiagnostic::note`] carrying the ay verdict, the bundle schema,
///   the replayed trust-step count, and the canonical goal — evidence made
///   visible without being given authority. The status stays `Pending` because
///   the validator cannot yet bind the replayed refutation to this obligation's
///   goal (see above); a `Discharged` flip on a producer-asserted binding would
///   overstate what was checked.
/// * **The in-solver `Strict` acceptance path is deliberately NOT used.**
///   `UnsatProofArtifact::accept_for_consumer(Strict)` can return `Ok` through a
///   deferred-trust rescue that runs FRESH SOLVERS to discharge an opaque
///   `:rule trust` step. That is ay re-checking itself. The gate used here is
///   the solver-free `ay::re_check_bundle_strict` plus `trust_count == 0`.
pub fn apply_vc_outcomes(
    module: &mut Module,
    vc: &FunctionVc,
) -> Result<Vec<(ProofId, ProofStatus)>, VcApplyError> {
    let actual_module_digest = module.stable_digest();
    if actual_module_digest != vc.source_module_digest {
        return Err(VcApplyError::ModuleDigestMismatch {
            expected: vc.source_module_digest,
            actual: actual_module_digest,
        });
    }

    let refuted: Vec<&VcCondition> = vc.application_refutations.iter().collect();
    let mut transitions = Vec::new();
    // The rows this pass flips to `Failed`. Any non-inherited certificate on
    // such a row is dropped afterwards: the module validator refuses a
    // discharging certificate beside a refutation
    // (`GroundCertificateStatusInconsistent`, trust-ir WS1.8 rule (a)), and a
    // Pending row may legitimately carry an evidence-awaiting-replay
    // certificate that an earlier pass attached. The refutation wins; the
    // stale evidence is not left to contradict it.
    let mut failed_rows: Vec<ProofId> = Vec::new();
    for (id, outcome) in &vc.application_obligations {
        let Some(obligation) = module.proof_obligations.iter_mut().find(|o| o.id == *id) else {
            continue;
        };
        if obligation.status != ProofStatus::Pending {
            continue;
        }
        if obligation.kind == ObligationKind::Precondition {
            continue;
        }
        match outcome {
            VcObligationOutcome::ProvedByVc => {
                // RECORD the evidence; do NOT mint a status. See this
                // function's doc comment for exactly what is still missing.
                let Some((_, evidence)) = vc.application_evidence.iter().find(|(oid, _)| oid == id)
                else {
                    module
                        .obligation_diagnostics
                        .push(ObligationDiagnostic::note(
                            *id,
                            "solver-proved in-process, but no replayable UNSAT payload was \
                             captured (or it failed the offline re-check); status stays Pending",
                        ));
                    continue;
                };
                module.obligation_diagnostics.push(
                    ObligationDiagnostic::note(
                        *id,
                        format!(
                            "ay proved this obligation's sited VC condition UNSAT and the \
                             {} proof bundle REPLAYED OFFLINE with {} trust step(s) \
                             (ay rev {}); status stays Pending because the module validator \
                             grants Discharged authority only to a certificate it can itself \
                             replay AND bind to this obligation's goal",
                            evidence.bundle_schema, evidence.trust_count, evidence.ay_rev
                        ),
                    )
                    .with_detail(format!(
                        "goal (negated condition, canonical): {}\nbundle bytes: {}",
                        evidence.goal_canonical,
                        evidence.bundle_bytes.len()
                    )),
                );
            }
            VcObligationOutcome::NotDischarged { reason } => {
                if refuted.is_empty() {
                    if let Some(unwitnessed) = unwitnessed_reasons(&vc.application_unwitnessed) {
                        module
                            .obligation_diagnostics
                            .push(ObligationDiagnostic::note(
                                *id,
                                format!(
                                    "ay answered SAT for this obligation's VC but gave no \
                                     consumer-accepted witness ({unwitnessed}); status stays \
                                     Pending: `Failed` requires a real refutation"
                                ),
                            ));
                    }
                    continue;
                }
                obligation.status = ProofStatus::Failed;
                let message = format!("whole-function VC refuted: {reason}");
                let detail = render_refutations(&refuted);
                module
                    .obligation_diagnostics
                    .push(ObligationDiagnostic::error(*id, message).with_detail(detail));
                transitions.push((*id, ProofStatus::Failed));
                failed_rows.push(*id);
            }
            VcObligationOutcome::Unsupported { .. } => {}
        }
    }
    if !failed_rows.is_empty() {
        module.proof_certificates.retain(|certificate| {
            !failed_rows.contains(&certificate.obligation)
                || matches!(
                    certificate.evidence,
                    trust_ir::proof::ProofEvidence::InheritedFromCallee { .. }
                )
        });
    }
    Ok(transitions)
}

/// The distinct reasons of unwitnessed SAT answers, joined, or `None`.
fn unwitnessed_reasons(conditions: &[VcCondition]) -> Option<String> {
    let mut reasons: Vec<String> = Vec::new();
    for condition in conditions {
        if let VcVerdict::Refuted {
            counterexample: Counterexample::Unavailable(reason),
        } = &condition.verdict
        {
            let reason = reason.to_string();
            if !reasons.contains(&reason) {
                reasons.push(reason);
            }
        }
    }
    (!reasons.is_empty()).then(|| reasons.join("; "))
}

/// Render the refuted conditions of a VC as the machine-readable `detail` of
/// an [`ObligationDiagnostic`]: one `counterexample …` line per refutation,
/// each assignment in binding (declaration) order — deterministic because
/// [`model_counterexample`] is. A refutation without a consumer-accepted
/// witness says so (`counterexample unavailable (<reason>)`).
fn render_refutations(refuted: &[&VcCondition]) -> String {
    let mut lines = Vec::with_capacity(refuted.len());
    for condition in refuted {
        let VcVerdict::Refuted { counterexample } = &condition.verdict else {
            continue;
        };
        let source = match &condition.source {
            VcSource::Assert => "assert".to_string(),
            VcSource::Annotation(annotation) => format!("{annotation}"),
            VcSource::LoweredAssert {
                obligation,
                expected,
            } => format!(
                "lowered assert for obligation #{} (cond must be {expected})",
                obligation.index()
            ),
        };
        match counterexample {
            Counterexample::Model(assignments) => {
                let assignments = assignments
                    .iter()
                    .map(|(value, mv)| format!("v{} = {mv:?}", value.index()))
                    .collect::<Vec<_>>()
                    .join(", ");
                lines.push(format!(
                    "counterexample (bb{} #{}, {source}): {assignments}",
                    condition.block.index(),
                    condition.inst_index
                ));
            }
            Counterexample::Unavailable(reason) => lines.push(format!(
                "counterexample unavailable (bb{} #{}, {source}): {reason}",
                condition.block.index(),
                condition.inst_index
            )),
        }
    }
    lines.join("\n")
}

/// Map a solver model back to `(ValueId, value)` pairs over schema-bound
/// symbols — the counterexample payload of a failure diagnostic
/// (docs/roadmap/diagnostics-representation.md). Order follows `bindings`
/// (declaration order), so the result is deterministic.
pub fn model_counterexample(
    model: &Model,
    bindings: &[(ValueId, String)],
) -> Vec<(ValueId, ModelValue)> {
    bindings
        .iter()
        .filter_map(|(value, name)| model.value_by_name(name).map(|mv| (*value, mv)))
        .collect()
}

/// Generate and check the whole-function VC for the function with id `func`.
///
/// See the module docs for scope. Fails closed with
/// [`AYError::UnsupportedOp`] / [`AYError::UnsupportedType`] on bodies the
/// encoders cannot express.
pub fn verify_function(module: &Module, func: FuncId) -> Result<FunctionVc, AYError> {
    let function = module
        .functions
        .iter()
        .find(|f| f.id == func)
        .ok_or_else(|| {
            AYError::UnsupportedOp(format!("module has no function with id f{}", func.index()))
        })?;
    generate_function_vc(module, function)
}

/// Generate and check the whole-function VC for `function`.
///
/// This is the real whole-function entry point the roadmap item
/// integration-ay-vc requires: walk the blocks, bind every `ValueId` via the
/// schema, encode supported semantics via the per-op encoders, check the
/// body's conditions, and report the function's B4-scoped obligations.
pub fn generate_function_vc(module: &Module, function: &Function) -> Result<FunctionVc, AYError> {
    let Some(module_function) = module
        .functions
        .iter()
        .find(|candidate| candidate.id == function.id)
    else {
        return Err(AYError::UnsupportedOp(format!(
            "function '{}' (f{}) is not present in the supplied module",
            function.name,
            function.id.index()
        )));
    };
    if module_function != function {
        return Err(AYError::UnsupportedOp(format!(
            "function '{}' (f{}) does not match the supplied module's function with that id",
            function.name,
            function.id.index()
        )));
    }

    if function.is_declaration() {
        return Err(AYError::UnsupportedOp(format!(
            "function '{}' is a body-less declaration; there is nothing to encode",
            function.name
        )));
    }
    if function.blocks.len() != 1 {
        // Multi-block bodies do NOT get a whole-function VC — there is no
        // path-condition machinery here and inventing one would havoc control
        // flow. What they get instead is the SITED VC: one block-local,
        // hypothesis-free condition per `ProofObligation::site`. See
        // [`generate_sited_vc`] for the soundness argument.
        return generate_sited_vc(module, function);
    }

    let mut vcb = VcBuilder::new(module, function)?;
    match vcb.walk() {
        Ok(()) => Ok(vcb.finish()),
        // WS5.4 (2): a single-block body the whole-function walk cannot encode
        // (a `Call`, an aggregate, a fat parameter, ...) falls back to the SITED
        // VC instead of erroring. The fallback is strictly weaker — fewer
        // hypotheses, one block-local condition per site — so it can lose
        // proofs but never mint one, and it never supplies a refutation (see
        // `generate_sited_vc`). Any other failure (solver, memory model) is
        // still an error.
        Err(refusal @ (AYError::UnsupportedOp(_) | AYError::UnsupportedType(_))) => {
            let mut vc = generate_sited_vc(module, function)?;
            vc.whole_function_fallback = Some(refusal);
            Ok(vc)
        }
        Err(other) => Err(other),
    }
}

/// Instructions the SITED VC will encode in a condition's backward slice.
///
/// Deliberately a whitelist of PURE, VALUE-ONLY operations: no memory, no
/// control flow, no calls, no borrow/ARC state. That restriction is what makes
/// the sited VC's "skip everything the condition does not depend on" strategy
/// sound. Skipping an effectful node (a `Store`, say) while keeping the
/// solver's memory array at its initial symbolic value would make two loads of
/// one address provably EQUAL when the real execution can make them differ —
/// a constraint reality does not have, which is exactly how a false UNSAT is
/// manufactured. With this whitelist there is no such state to desynchronize:
/// every encoded term is a pure function of the block's parameters.
fn is_pure_value_inst(inst: &Inst) -> bool {
    matches!(
        inst,
        Inst::Const { .. }
            | Inst::NullPtr
            | Inst::BinOp { .. }
            | Inst::UnOp { .. }
            | Inst::Overflow { .. }
            | Inst::ICmp { .. }
            | Inst::FCmp { .. }
            | Inst::Cast { .. }
            | Inst::Copy { .. }
            | Inst::Select { .. }
    )
}

// `is_diverging_arm` (the structural "this arm cannot fall through" test) MOVED
// to `trust_ir::proof::bvgoal`, where `lowered_assert_condition` — its only
// caller — now lives. The validator-side authority capability re-derives the
// goal from the same site this producer reads, so the two must call ONE
// implementation: a divergence between them is exactly how a proof of one
// condition gets recorded against another.

/// Does a canonically-rendered goal reduce to a constant?
///
/// Used by the vacuity gate in `capture_replay_evidence`: if the goal handed to
/// the solver is already a constant, the solver had nothing to reason about and
/// any resulting "proof" is `false |- _|_` — structurally valid, entirely
/// uninformative about the program. Kept deliberately narrow (exact match on
/// the canonical constant spellings, after trimming) so it can only ever REJECT
/// evidence, never admit it.
fn goal_is_constant(goal_canonical: &str) -> bool {
    matches!(
        goal_canonical.trim(),
        "false" | "true" | "#b0" | "#b1" | "(_ bv0 1)" | "(_ bv1 1)"
    )
}

/// Read the lowered-assert condition out of the `CondBr` at an obligation site:
/// `(cond, expected)` where `expected` is the boolean the condition must take
/// for control to AVOID the diverging arm.
///
/// MOVED to `trust_ir::proof::bvgoal::lowered_assert_condition` and re-exported
/// here verbatim (every fail-closed arm, including the `Invoke`-panic-arm
/// inversion hazard, moved with it). The producer below and the validator-side
/// `BvBlastAuthority` must agree bit-for-bit on what an obligation states; one
/// implementation is the only way to guarantee that.
use trust_ir::proof::lowered_assert_condition;

/// The SITED VC: one block-local condition per `ProofObligation::site`.
///
/// # Why this is sound
///
/// For each sited obligation the builder starts a FRESH solver at the site's
/// block, declares that block's parameters as unconstrained symbols, encodes
/// only the pure prefix ([`is_pure_value_inst`]) the assert condition depends
/// on, and asks whether the condition can be false. Nothing about how control
/// reached the block is assumed — no path condition, no predecessor `Assume`,
/// no memory contents.
///
/// That is a strictly WEAKER hypothesis set than any real execution has, so a
/// `Proved` verdict ("the negation is UNSAT for every valuation of the free
/// symbols") implies the condition holds on every real path into the block.
/// Weakening hypotheses can only lose proofs, never manufacture them — which
/// is the direction fail-closed requires. The cost is real: anything needing a
/// loop invariant, a caller precondition, or a dominating branch test will come
/// back `Refuted`, and `Refuted` here means "not provable locally", NOT "the
/// program is wrong". Hence the sited VC never mints `Failed` — see
/// [`apply_vc_outcomes`].
fn generate_sited_vc(module: &Module, function: &Function) -> Result<FunctionVc, AYError> {
    let mut conditions: Vec<VcCondition> = Vec::new();
    let mut bindings: Vec<(ValueId, String)> = Vec::new();

    for obligation in &module.proof_obligations {
        let Some(site) = &obligation.site else {
            continue;
        };
        if site.function != function.id {
            continue;
        }
        let Some(block) = function.blocks.iter().find(|b| b.id == site.block) else {
            continue; // validated elsewhere; nothing to encode here
        };
        let Some(node) = block.body.get(site.inst_index as usize) else {
            continue;
        };
        // WS5.4 (1a): only an assert-class row may be backed by the condition of
        // an assert-shaped node. No condition is generated for any other kind —
        // not even an Unsupported one, since conditions are shared by every row
        // at the site; `bind_obligations` reports the refusal for this row.
        if is_assert_site_inst(&node.inst) && !is_assert_class_kind(&obligation.kind) {
            continue;
        }
        let (cond_value, expected) = match lowered_assert_condition(function, node) {
            Ok(pair) => pair,
            Err(reason) => {
                conditions.push(VcCondition {
                    block: site.block,
                    inst_index: site.inst_index as usize,
                    source: VcSource::LoweredAssert {
                        obligation: obligation.id,
                        expected: true,
                    },
                    verdict: VcVerdict::Unsupported { reason },
                    evidence: None,
                });
                continue;
            }
        };
        let source = VcSource::LoweredAssert {
            obligation: obligation.id,
            expected,
        };
        let mut vcb = VcBuilder::new(module, function)?;
        let (verdict, evidence) =
            vcb.solve_sited_condition(block, site.inst_index as usize, cond_value, expected);
        for binding in vcb.bindings.drain(..) {
            if !bindings.contains(&binding) {
                bindings.push(binding);
            }
        }
        conditions.push(VcCondition {
            block: site.block,
            inst_index: site.inst_index as usize,
            source,
            verdict,
            evidence,
        });
    }

    let mut unsupported_function_proofs = Vec::new();
    for annotation in &function.proofs {
        if let Some(reason) = function_proof_unsupported_reason(annotation) {
            unsupported_function_proofs.push((annotation.clone(), reason));
        }
    }
    let obligations = bind_obligations(module, function, &conditions);
    let application_evidence = collect_application_evidence(module, function, &conditions);
    Ok(FunctionVc {
        source_module_digest: module.stable_digest(),
        application_obligations: obligations.clone(),
        // The sited VC never supplies refutations: a locally-unprovable
        // condition means "not provable without a loop invariant / caller
        // precondition / dominating branch test", NOT "the program is wrong".
        // Feeding those to `apply_vc_outcomes` would mint `Failed` on correct
        // code. See `generate_sited_vc`'s soundness note.
        application_refutations: Vec::new(),
        application_unwitnessed: Vec::new(),
        application_evidence,
        func: function.id,
        bindings,
        conditions,
        unsupported_function_proofs,
        obligations,
        whole_function_fallback: None,
    })
}

/// A condition collected during the walk, solved afterwards.
enum Pending {
    /// A verdict solved AT THE CONDITION'S PROGRAM POINT — the solver context
    /// then contains exactly the Assumes and instruction semantics that
    /// PRECEDE the condition in body order, so a later `Assume` can never
    /// discharge an earlier `Assert` (no assume-after-assert laundering).
    Solved(VcVerdict),
    /// Fail-closed unsupported annotation, with the reason.
    Unsupported(String),
}

struct PendingCondition {
    block: BlockId,
    inst_index: usize,
    source: VcSource,
    pending: Pending,
}

struct VcBuilder<'m> {
    module: &'m Module,
    function: &'m Function,
    solver: Solver,
    mem: MemoryModel,
    borrow: BorrowModel,
    arc: ArcModel,
    /// SSA value -> solver term, in binding order (no map iteration).
    terms: Vec<(ValueId, Term)>,
    /// SSA value -> IR type, parallel to `terms`.
    types: Vec<(ValueId, Ty)>,
    /// Declared (schema-named) symbols only — the model-visible bindings.
    bindings: Vec<(ValueId, String)>,
    pending: Vec<PendingCondition>,
    /// Set when a solver frame failed to open or close, was left unbalanced,
    /// or a solver step inside it failed ([`Self::in_frame`]). The solver is
    /// then not the one this builder believes: a leftover negated goal would
    /// make every later prefix UNSAT and every later condition falsely
    /// `Proved`, and after a caught panic (`SolverError::SolverPanic`) ay
    /// itself says the solver's state is likely corrupted. From then on no
    /// condition is solved — each is `Unknown` with this reason.
    poisoned: Option<String>,
}

impl<'m> VcBuilder<'m> {
    fn new(module: &'m Module, function: &'m Function) -> Result<Self, AYError> {
        let mut solver = create_fp_solver()?;
        // Proof production is OFF by default in ay; without this no UNSAT
        // payload exists to export, which is why the adapter previously
        // believed none was available.
        solver.set_produce_proofs(true);
        let f = function.id.index();
        // State arrays use deterministic per-function names disjoint from the
        // value-symbol namespace (`f{F}_v{V}`).
        let mem = MemoryModel::new(&mut solver, &format!("f{f}_mem"))?;
        let borrow = BorrowModel::new(&mut solver, &format!("f{f}_perm"))?;
        let arc = ArcModel::new(&mut solver, &format!("f{f}_rc"))?;
        Ok(Self {
            module,
            function,
            solver,
            mem,
            borrow,
            arc,
            terms: Vec::new(),
            types: Vec::new(),
            bindings: Vec::new(),
            pending: Vec::new(),
            poisoned: None,
        })
    }

    fn bind(&mut self, value: ValueId, term: Term, ty: Ty) {
        self.terms.push((value, term));
        self.types.push((value, ty));
    }

    /// Declare `value` under its canonical schema symbol and record the
    /// binding for model back-translation.
    fn declare(&mut self, value: ValueId, ty: &Ty) -> Result<Term, AYError> {
        let name = ay_symbol(self.function.id, value);
        let sort = ay_sort(ty)?;
        let term = self.solver.try_declare_const(&name, sort)?;
        self.bindings.push((value, name));
        self.bind(value, term, ty.clone());
        Ok(term)
    }

    fn term(&self, value: ValueId) -> Result<Term, AYError> {
        self.terms
            .iter()
            .rev()
            .find(|(id, _)| *id == value)
            .map(|(_, t)| *t)
            .ok_or_else(|| {
                AYError::UnsupportedOp(format!(
                    "use of value v{} before definition (or defined by an unencoded instruction)",
                    value.index()
                ))
            })
    }

    fn value_ty(&self, value: ValueId) -> Option<&Ty> {
        self.types
            .iter()
            .rev()
            .find(|(id, _)| *id == value)
            .map(|(_, ty)| ty)
    }

    /// BitVec(1) <- Bool: the schema stores Bool values as 1-bit bitvectors
    /// (matching `ay_sort(Bool)`), so encoder-produced Bool terms are
    /// normalized at binding time.
    fn bool_to_bv1(&mut self, b: Term) -> Result<Term, AYError> {
        let one = self.solver.try_bv_const(1, 1)?;
        let zero = self.solver.try_bv_const(0, 1)?;
        Ok(self.solver.try_ite(b, one, zero)?)
    }

    /// Bool <- BitVec(1): the inverse normalization for `Assume`/`Assert`/
    /// `Select` conditions.
    fn bv1_to_bool(&mut self, t: Term) -> Result<Term, AYError> {
        let one = self.solver.try_bv_const(1, 1)?;
        Ok(self.solver.try_eq(t, one)?)
    }

    /// Run `body` inside ONE solver frame: `try_push`, the body, then
    /// ALWAYS `try_pop` — also when the body failed. The body cannot leave
    /// the frame early (it returns its result; there is no `?` between push
    /// and pop). The session is POISONED ([`Self::poisoned`]) when the frame
    /// cannot be opened or closed, when the stack is unbalanced afterwards,
    /// when the session was already poisoned — AND when the body itself
    /// returns an error.
    ///
    /// The last clause is load-bearing (r11 review H1). ay's
    /// `try_check_sat` catches a panic inside the solver and returns
    /// `SolverError::SolverPanic`, whose contract (ay
    /// `api/types/error.rs`) is that the solver's internal state is then
    /// "likely corrupted" and must not be solved on again. The
    /// whole-function walk shares ONE solver across every condition, so
    /// answering one condition `Unknown` and solving the next on the same
    /// solver could mint a false `Proved`. [`AYError::SolverError`] flattens
    /// ay's error to a string, so no variant is matched: EVERY error a frame
    /// body returns ends the session. That is fail-closed — a benign refusal
    /// (an assertion ay rejects) costs only the later conditions' verdicts,
    /// which become `Unknown`, never a verdict.
    ///
    /// # Errors
    ///
    /// The poison reason. Every caller turns it into
    /// [`VcVerdict::Unknown`], never a verdict.
    fn in_frame<T>(
        &mut self,
        body: impl FnOnce(&mut Self) -> Result<T, AYError>,
    ) -> Result<T, String> {
        if let Some(reason) = &self.poisoned {
            return Err(reason.clone());
        }
        let level = self.solver.num_scopes();
        if let Err(error) = self.solver.try_push() {
            return Err(self.poison(format!("solver frame could not be opened: {error}")));
        }
        let value = body(self);
        if let Err(error) = self.solver.try_pop() {
            return Err(self.poison(format!("solver frame could not be closed: {error}")));
        }
        // A body that pushed without popping leaves frames — and whatever it
        // asserted in them — on the stack after the pop above succeeds. That
        // is the same hazard as a failed pop, so it is the same poison.
        let after = self.solver.num_scopes();
        if after != level {
            return Err(self.poison(format!(
                "solver frame stack unbalanced: {after} scope(s) open after the frame, expected \
                 {level}"
            )));
        }
        value.map_err(|error| {
            self.poison(format!(
                "a solver step inside the frame failed, and ay may have left the solver \
                 corrupted: {error}"
            ))
        })
    }

    /// Record a frame failure; the session proves nothing afterwards.
    fn poison(&mut self, reason: String) -> String {
        let reason = format!("solver session poisoned: {reason}");
        self.poisoned = Some(reason.clone());
        reason
    }

    /// Solve one condition NOW, under the current (prefix-only) solver
    /// context, in its own push/pop frame. Called at the program point where
    /// the condition occurs — see [`Pending::Solved`].
    ///
    /// Fail-closed at every solver step: a refused assertion or check is
    /// `Unknown` AND poisons the session, as does a frame failure (see
    /// [`Self::in_frame`]), so that no LATER condition can be solved against
    /// a stack that still holds this one's negated goal or a solver ay has
    /// declared corrupted.
    fn solve_condition_now(&mut self, cond: ProofCondition) -> VcVerdict {
        let framed = self.in_frame(|vcb| -> Result<VcVerdict, AYError> {
            vcb.solver.try_assert_term(cond.term)?;
            let result = vcb.solver.try_check_sat()?;
            Ok(if result.is_unsat() {
                VcVerdict::Proved
            } else if result.is_sat() {
                VcVerdict::Refuted {
                    counterexample: sat_witness(&vcb.solver, &vcb.bindings),
                }
            } else {
                VcVerdict::Unknown {
                    reason: "ay returned unknown".to_string(),
                }
            })
        });
        match framed {
            Ok(verdict) => verdict,
            Err(poisoned) => VcVerdict::Unknown { reason: poisoned },
        }
    }

    /// Encode the pure backward context of one block up to `upto_index`, then
    /// check whether `cond` can differ from `expected`.
    ///
    /// Nodes outside [`is_pure_value_inst`], and pure nodes whose operands are
    /// not (yet) bound, are SKIPPED rather than encoded. Skipping only removes
    /// facts, so it can never make an unprovable condition provable; if the
    /// condition itself ends up unbound the result is `Unsupported`, never a
    /// pass.
    fn solve_sited_condition(
        &mut self,
        block: &trust_ir::Block,
        upto_index: usize,
        cond: ValueId,
        expected: bool,
    ) -> (VcVerdict, Option<SmtReplayEvidence>) {
        // A parameter with no solver sort (a `FatPtr(Slice)` `(ptr, len)` pair,
        // an aggregate, ...) is left UNDECLARED rather than refusing every
        // condition in the block (WS5.4 (3)). Nothing that reads it can encode,
        // so a condition depending on it ends up unbound and is `Unsupported`
        // below — for THAT condition only. Leaving a value unbound removes
        // facts; it can never add one.
        let mut unsortable: Vec<String> = Vec::new();
        for (value, ty) in &block.params {
            if self.declare(*value, ty).is_err() {
                unsortable.push(format!("v{}: {ty}", value.index()));
            }
        }
        for (index, node) in block.body.iter().enumerate() {
            if index >= upto_index {
                break;
            }
            if !is_pure_value_inst(&node.inst) {
                continue;
            }
            // Ignore encode failures: a node whose operands are defined in
            // another block simply contributes nothing. Every whitelisted arm
            // binds only after all its operand lookups succeed, so a failed
            // encode leaves no partial binding behind.
            let _ = self.encode_node(block.id, index, node);
        }
        let Ok(term) = self.term(cond) else {
            let unsortable = if unsortable.is_empty() {
                String::new()
            } else {
                format!(
                    "; block parameters with no solver sort, left undeclared: {}",
                    unsortable.join(", ")
                )
            };
            return (
                VcVerdict::Unsupported {
                    reason: format!(
                        "the assert condition v{} is not derivable from this block's pure prefix \
                         (it depends on memory, a call, a value defined in another block, or a \
                         block parameter with no solver sort); the sited VC encodes no such \
                         context (fail-closed){unsortable}",
                        cond.index()
                    ),
                },
                None,
            );
        };
        if let Some(reason) = &self.poisoned {
            return (
                VcVerdict::Unknown {
                    reason: reason.clone(),
                },
                None,
            );
        }
        match self.sited_goal(term, expected) {
            Ok((negated, goal_canonical)) => self.solve_sited_goal(negated, goal_canonical),
            Err(error) => (
                VcVerdict::Unknown {
                    reason: error.to_string(),
                },
                None,
            ),
        }
    }

    /// The negated sited goal and its canonical rendering.
    fn sited_goal(&mut self, term: Term, expected: bool) -> Result<(Term, String), AYError> {
        let holds = self.bv1_to_bool(term)?;
        // `expected` is ALWAYS `true` now: `lowered_assert_condition` accepts
        // only the producer's `condbr assert_cond, <success>, <panic>` shape and
        // fails closed on a diverging `then` arm rather than inferring an
        // inverted polarity from block shape. The `false` branch is retained as
        // defensive structure only — if a future producer shape legitimately
        // inverts, it must record its polarity explicitly rather than have this
        // code guess it back.
        let holds = if expected {
            holds
        } else {
            self.solver.try_not(holds)?
        };
        let negated = self.solver.try_not(holds)?;
        let goal_canonical = self.solver.try_render_term_canonical(negated)?;
        Ok((negated, goal_canonical))
    }

    /// Solve one sited goal in ONE frame. Inlined rather than routed through
    /// `solve_condition_now`, because the proof payload must be exported
    /// INSIDE the solver frame: `pop()` discards the last proof along with the
    /// assertion that produced it.
    fn solve_sited_goal(
        &mut self,
        negated: Term,
        goal_canonical: String,
    ) -> (VcVerdict, Option<SmtReplayEvidence>) {
        let framed = self.in_frame(
            |vcb| -> Result<(VcVerdict, Option<SmtReplayEvidence>), AYError> {
                vcb.solver.try_assert_term(negated)?;
                let result = vcb.solver.try_check_sat()?;
                Ok(if result.is_unsat() {
                    // Capture the replayable payload ONLY on Proved, and only
                    // if it actually replays offline. A payload that does not
                    // replay is not attached at all — it would be a claim, not
                    // evidence.
                    let evidence = vcb.capture_replay_evidence(goal_canonical);
                    (VcVerdict::Proved, evidence)
                } else if result.is_sat() {
                    (
                        VcVerdict::Refuted {
                            counterexample: sat_witness(&vcb.solver, &vcb.bindings),
                        },
                        None,
                    )
                } else {
                    (
                        VcVerdict::Unknown {
                            reason: "ay returned unknown".to_string(),
                        },
                        None,
                    )
                })
            },
        );
        match framed {
            Ok(outcome) => outcome,
            Err(poisoned) => (VcVerdict::Unknown { reason: poisoned }, None),
        }
    }

    /// Export the last UNSAT proof, re-check it OFFLINE, and return it only if
    /// the re-check accepts it with zero trust steps.
    fn capture_replay_evidence(&mut self, goal_canonical: String) -> Option<SmtReplayEvidence> {
        // VACUITY GATE. A bundle whose goal canonicalises to a CONSTANT proves
        // `false |- _|_`, which is trivially valid and says NOTHING about the
        // program.
        //
        // This is not hypothetical: every certificate this path produced before
        // the gate had `goal_canonical == "false"`. ay's term CONSTRUCTOR folds
        // `not(not(icmp ult 3 10))` to the literal `false` before `check_sat`
        // ever runs, so the bundle's sole assumption is a constant and its
        // proof is `Assume(false) |- _|_`. The reasoning that actually
        // established the program property happened in the UNTRUSTED term
        // builder, not in the checkable proof — so replaying the bundle
        // re-establishes nothing. It replays perfectly and is worthless.
        //
        // Refuse to attach it. The obligation stays `Pending` with no evidence,
        // which is the honest outcome: we have no checkable artifact, and an
        // artifact that merely LOOKS like one is worse than none, because a
        // downstream gate counting `trust_count == 0` bundles would score it as
        // a real proof.
        if goal_is_constant(&goal_canonical) {
            return None;
        }
        let bundle = self.solver.export_last_unsat_bundle()?;
        let bundle_schema = bundle.schema.clone();
        let bundle_bytes = serde_json::to_vec(&bundle).ok()?;
        let trust_count = replay_bundle_offline(&bundle_bytes).ok()?;
        Some(SmtReplayEvidence {
            ay_rev: AY_REV,
            bundle_schema,
            bundle_bytes,
            goal_canonical,
            trust_count,
        })
    }

    fn walk(&mut self) -> Result<(), AYError> {
        // Copy the `&'m Function` out of `self` so iterating the body does
        // not hold a borrow of `self` across the `&mut self` encode calls.
        let function: &'m Function = self.function;
        let block = &function.blocks[0];
        for (value, ty) in &block.params {
            self.declare(*value, ty)?;
        }
        for (index, node) in block.body.iter().enumerate() {
            self.encode_node(block.id, index, node)?;
            for annotation in &node.proofs {
                match self.annotation_condition(annotation, &node.inst) {
                    Ok(Some(cond)) => {
                        let verdict = self.solve_condition_now(cond);
                        self.pending.push(PendingCondition {
                            block: block.id,
                            inst_index: index,
                            source: VcSource::Annotation(annotation.clone()),
                            pending: Pending::Solved(verdict),
                        })
                    }
                    Ok(None) => {} // claim-style hint: no obligation to check
                    Err(reason) => self.pending.push(PendingCondition {
                        block: block.id,
                        inst_index: index,
                        source: VcSource::Annotation(annotation.clone()),
                        pending: Pending::Unsupported(reason),
                    }),
                }
            }
        }
        Ok(())
    }

    fn result0(node: &InstrNode) -> Result<ValueId, AYError> {
        node.results.first().copied().ok_or_else(|| {
            AYError::UnsupportedOp("instruction node is missing its result value".to_string())
        })
    }

    fn encode_node(
        &mut self,
        block: BlockId,
        index: usize,
        node: &InstrNode,
    ) -> Result<(), AYError> {
        match &node.inst {
            Inst::Const { ty, value } => {
                let term = self.encode_constant(ty, value)?;
                self.bind(Self::result0(node)?, term, ty.clone());
            }
            Inst::NullPtr => {
                let term = self.solver.try_bv_const(0, 64)?;
                self.bind(Self::result0(node)?, term, Ty::Ptr);
            }
            Inst::BinOp { op, ty, lhs, rhs } => {
                let l = self.term(*lhs)?;
                let r = self.term(*rhs)?;
                let term = match ty {
                    Ty::Vector(elem, lanes) => {
                        encode_vector_binop(&mut self.solver, *op, elem, *lanes, l, r)?
                    }
                    _ => encode_binop(&mut self.solver, *op, l, r)?,
                };
                self.bind(Self::result0(node)?, term, ty.clone());
            }
            Inst::UnOp { op, ty, operand } => {
                let t = self.term(*operand)?;
                let term = match ty {
                    Ty::Vector(elem, lanes) => {
                        encode_vector_unop(&mut self.solver, *op, elem, *lanes, t)?
                    }
                    _ => encode_unop(&mut self.solver, *op, t)?,
                };
                self.bind(Self::result0(node)?, term, ty.clone());
            }
            Inst::Overflow { op, ty, lhs, rhs } => {
                let l = self.term(*lhs)?;
                let r = self.term(*rhs)?;
                let bin = match op {
                    OverflowOp::AddOverflow => BinOp::Add,
                    OverflowOp::SubOverflow => BinOp::Sub,
                    OverflowOp::MulOverflow => BinOp::Mul,
                };
                let value = encode_binop(&mut self.solver, bin, l, r)?;
                let safe = encode_overflow_check(&mut self.solver, *op, ty.is_signed(), l, r)?;
                let overflowed = self.solver.try_not(safe)?;
                let flag = self.bool_to_bv1(overflowed)?;
                let (v0, v1) = match node.results.as_slice() {
                    [v0, v1] => (*v0, *v1),
                    _ => {
                        return Err(AYError::UnsupportedOp(
                            "Overflow node must carry (value, overflowed) results".to_string(),
                        ));
                    }
                };
                self.bind(v0, value, ty.clone());
                self.bind(v1, flag, Ty::Bool);
            }
            Inst::ICmp { op, lhs, rhs, .. } => {
                let l = self.term(*lhs)?;
                let r = self.term(*rhs)?;
                let b = encode_icmp(&mut self.solver, *op, l, r)?;
                let term = self.bool_to_bv1(b)?;
                self.bind(Self::result0(node)?, term, Ty::Bool);
            }
            Inst::FCmp { op, lhs, rhs, .. } => {
                let l = self.term(*lhs)?;
                let r = self.term(*rhs)?;
                let b = encode_fcmp(&mut self.solver, *op, l, r)?;
                let term = self.bool_to_bv1(b)?;
                self.bind(Self::result0(node)?, term, Ty::Bool);
            }
            Inst::Cast {
                op,
                src_ty,
                dst_ty,
                operand,
            } => {
                let t = self.term(*operand)?;
                let src_width = bit_width(src_ty)?;
                let dst_width = bit_width(dst_ty)?;
                let term = encode_cast(&mut self.solver, *op, t, src_width, dst_width)?;
                self.bind(Self::result0(node)?, term, dst_ty.clone());
            }
            Inst::Copy { ty, operand } => {
                let t = self.term(*operand)?;
                self.bind(Self::result0(node)?, t, ty.clone());
            }
            Inst::Select {
                ty,
                cond,
                then_val,
                else_val,
            } => {
                let c = self.term(*cond)?;
                let c = self.bv1_to_bool(c)?;
                let t = self.term(*then_val)?;
                let e = self.term(*else_val)?;
                let term = self.solver.try_ite(c, t, e)?;
                self.bind(Self::result0(node)?, term, ty.clone());
            }
            Inst::Load { ty, ptr, .. } => {
                let addr = self.term(*ptr)?;
                let width = byte_width(ty)?;
                let term = self.mem.encode_load(&mut self.solver, addr, width)?;
                self.bind(Self::result0(node)?, term, ty.clone());
            }
            Inst::Store { ty, ptr, value, .. } => {
                let addr = self.term(*ptr)?;
                let val = self.term(*value)?;
                let width = byte_width(ty)?;
                self.mem.encode_store(&mut self.solver, addr, val, width)?;
            }
            Inst::Alloca {
                ty,
                count: None,
                align: _,
            } => {
                let size = u64::from(byte_width(ty)?);
                let addr = self.mem.encode_alloca(&mut self.solver, size)?;
                self.bind(Self::result0(node)?, addr, Ty::Ptr);
            }
            Inst::GEP {
                pointee_ty,
                base,
                indices,
                ..
            } => {
                let base_term = self.term(*base)?;
                let elem_bytes = i64::from(byte_width(pointee_ty)?);
                // TrustIr GEP is flat single-scale indexing:
                // base + (sum of indices) * size_of(pointee).
                let mut sum: Option<Term> = None;
                for index in indices {
                    let ty = self.value_ty(*index).cloned().ok_or_else(|| {
                        AYError::UnsupportedOp(format!(
                            "GEP index v{} has no recorded type",
                            index.index()
                        ))
                    })?;
                    if bit_width(&ty)? != 64 {
                        return Err(AYError::UnsupportedOp(format!(
                            "GEP index v{} has type {}; the 64-bit pointer model requires \
                             64-bit indices",
                            index.index(),
                            ty
                        )));
                    }
                    let t = self.term(*index)?;
                    sum = Some(match sum {
                        None => t,
                        Some(s) => self.solver.try_bvadd(s, t)?,
                    });
                }
                let offset = match sum {
                    None => self.solver.try_bv_const(0, 64)?,
                    Some(s) => {
                        let size = self.solver.try_bv_const(elem_bytes, 64)?;
                        self.solver.try_bvmul(s, size)?
                    }
                };
                let term = self.mem.encode_gep(&mut self.solver, base_term, offset)?;
                self.bind(Self::result0(node)?, term, Ty::Ptr);
            }
            Inst::Borrow { ptr } => {
                let t = self.term(*ptr)?;
                // The borrow result rule is stated ONCE, in
                // `trust_ir::bridge::borrow_result_ty`: the operand's type when
                // that type is FAT, `Ty::Ptr` otherwise. No second phase is
                // needed here, unlike the six whole-function sites wired by
                // the bridge: this walk is straight-line over the single block
                // and `bind` records term and type together, so the operand's
                // recorded type is already resolved when the borrow is encoded
                // and a borrow-of-borrow chain collapses in walk order. A fat
                // result type then fails closed at every width-consuming
                // reader (`ay_sort` has no fat sort), instead of flowing a fat
                // value through the 64-bit thin-pointer model under a false
                // `ptr`.
                let result_ty = trust_ir::bridge::borrow_result_ty(self.value_ty(*ptr));
                let (borrowed, _) = self.borrow.encode_borrow(&mut self.solver, t)?;
                self.bind(Self::result0(node)?, borrowed, result_ty);
            }
            Inst::BorrowMut { ptr } => {
                let t = self.term(*ptr)?;
                // Same shared rule as `Borrow` above; no local restatement.
                let result_ty = trust_ir::bridge::borrow_result_ty(self.value_ty(*ptr));
                let (borrowed, _) = self.borrow.encode_borrow_mut(&mut self.solver, t)?;
                self.bind(Self::result0(node)?, borrowed, result_ty);
            }
            Inst::EndBorrow { borrow_ptr } => {
                let t = self.term(*borrow_ptr)?;
                self.borrow.encode_end_borrow(&mut self.solver, t)?;
            }
            Inst::Retain { ptr } => {
                let t = self.term(*ptr)?;
                self.arc.encode_retain(&mut self.solver, t)?;
            }
            Inst::Release { ptr } => {
                let t = self.term(*ptr)?;
                self.arc.encode_release(&mut self.solver, t)?;
            }
            Inst::IsUnique { ptr } => {
                let t = self.term(*ptr)?;
                let b = self.arc.encode_is_unique(&mut self.solver, t)?;
                let term = self.bool_to_bv1(b)?;
                self.bind(Self::result0(node)?, term, Ty::Bool);
            }
            Inst::Assume { cond } => {
                let t = self.term(*cond)?;
                let b = self.bv1_to_bool(t)?;
                self.solver.try_assert_term(b)?;
            }
            Inst::Assert { cond, .. } => {
                let t = self.term(*cond)?;
                let b = self.bv1_to_bool(t)?;
                // Assert-and-check-UNSAT contract: check the NEGATION.
                let negated = self.solver.try_not(b)?;
                let verdict = self.solve_condition_now(ProofCondition {
                    term: negated,
                    strategy: crate::ProofStrategy::AssertAndCheckUnsat,
                });
                self.pending.push(PendingCondition {
                    block,
                    inst_index: index,
                    source: VcSource::Assert,
                    pending: Pending::Solved(verdict),
                });
            }
            Inst::Return { values } => {
                // Straight-line terminator: just require the returned values
                // to be bound (fail closed on malformed bodies).
                for value in values {
                    self.term(*value)?;
                }
            }
            other => {
                return Err(AYError::UnsupportedOp(format!(
                    "instruction {} is not supported by the whole-function VC \
                     (fail-closed: unencoded semantics are never havocked)",
                    inst_label(other)
                )));
            }
        }
        Ok(())
    }

    fn encode_constant(&mut self, ty: &Ty, value: &Constant) -> Result<Term, AYError> {
        match value {
            Constant::Bool(b) => Ok(self.solver.try_bv_const(i64::from(*b), 1)?),
            Constant::Float(value) => {
                let (bits, eb, sb) = match ty {
                    Ty::F16 => (
                        u64::from(trust_ir::interpret::f64_to_f16_bits(*value)),
                        5,
                        11,
                    ),
                    Ty::F32 => (u64::from((*value as f32).to_bits()), 8, 24),
                    Ty::F64 => (value.to_bits(), 11, 53),
                    _ => {
                        return Err(AYError::UnsupportedOp(format!(
                            "float constant at non-float type {ty}"
                        )));
                    }
                };
                Ok(self.solver.try_fp_const_from_bits(bits, eb, sb)?)
            }
            Constant::Int(i) => self.encode_integer_constant(ty, ay::BigInt::from(*i)),
            Constant::U128(i) => {
                if *ty != Ty::U128 || !value.is_canonical_int_spelling() {
                    return Err(AYError::UnsupportedOp(format!(
                        "noncanonical or mistyped U128 constant at {ty}"
                    )));
                }
                self.encode_integer_constant(ty, ay::BigInt::from(*i))
            }
            other => Err(AYError::UnsupportedOp(format!(
                "constant {other:?} is not supported by the whole-function VC"
            ))),
        }
    }

    fn encode_integer_constant(&mut self, ty: &Ty, value: ay::BigInt) -> Result<Term, AYError> {
        let width = match ay_sort(ty)? {
            Sort::BitVec(bv) => bv.width,
            _ => {
                return Err(AYError::UnsupportedOp(format!(
                    "integer constant of non-bitvector type {ty}"
                )));
            }
        };
        Ok(self.solver.try_bv_const_bigint(&value, width)?)
    }

    /// Build the solver condition for an instruction-level annotation over
    /// the node's actual operand terms.
    ///
    /// `Ok(Some(_))`: an encodable obligation. `Ok(None)`: a claim-style
    /// hint with no obligation (skipped, per the documented trust boundary).
    /// `Err(reason)`: obligation-bearing but not encodable — surfaced as a
    /// structured [`VcVerdict::Unsupported`].
    fn annotation_condition(
        &mut self,
        annotation: &ProofAnnotation,
        inst: &Inst,
    ) -> Result<Option<ProofCondition>, String> {
        match annotation {
            ProofAnnotation::NoOverflow | ProofAnnotation::NoWrap => {
                let (op, ty, lhs, rhs) = match inst {
                    Inst::BinOp {
                        op: BinOp::Add,
                        ty,
                        lhs,
                        rhs,
                    } => (OverflowOp::AddOverflow, ty, lhs, rhs),
                    Inst::BinOp {
                        op: BinOp::Sub,
                        ty,
                        lhs,
                        rhs,
                    } => (OverflowOp::SubOverflow, ty, lhs, rhs),
                    Inst::BinOp {
                        op: BinOp::Mul,
                        ty,
                        lhs,
                        rhs,
                    } => (OverflowOp::MulOverflow, ty, lhs, rhs),
                    Inst::Overflow { op, ty, lhs, rhs } => (*op, ty, lhs, rhs),
                    _ => {
                        return Err(format!(
                            "{annotation} is only encodable on integer add/sub/mul nodes"
                        ));
                    }
                };
                if matches!(ty, Ty::Vector(..)) {
                    return Err(format!(
                        "{annotation}: per-lane overflow conditions for vector ops are not encoded"
                    ));
                }
                let width = bit_width(ty).map_err(|e| e.to_string())?;
                let l = self.term(*lhs).map_err(|e| e.to_string())?;
                let r = self.term(*rhs).map_err(|e| e.to_string())?;
                let operands = ProofOperands::for_annotation(annotation, &[l, r], width)
                    .map_err(|e| e.to_string())?
                    .with_overflow_op(op)
                    // The overflow predicates are signedness-specific; thread the
                    // operand type's signedness (fail-closed in the checker).
                    .with_signedness(ty.is_signed());
                verify_proof_obligation(&mut self.solver, annotation, &operands)
                    .map(Some)
                    .map_err(|e| e.to_string())
            }
            ProofAnnotation::DivNonZero => {
                let (ty, rhs) = match inst {
                    Inst::BinOp {
                        op: BinOp::UDiv | BinOp::SDiv | BinOp::URem | BinOp::SRem,
                        ty,
                        rhs,
                        ..
                    } => (ty, rhs),
                    _ => {
                        return Err(format!(
                            "{annotation} is only encodable on integer div/rem nodes"
                        ));
                    }
                };
                if matches!(ty, Ty::Vector(..)) {
                    return Err(format!(
                        "{annotation}: per-lane divisor conditions for vector ops are not encoded"
                    ));
                }
                let width = bit_width(ty).map_err(|e| e.to_string())?;
                let divisor = self.term(*rhs).map_err(|e| e.to_string())?;
                let operands = ProofOperands::for_annotation(annotation, &[divisor], width)
                    .map_err(|e| e.to_string())?;
                verify_proof_obligation(&mut self.solver, annotation, &operands)
                    .map(Some)
                    .map_err(|e| e.to_string())
            }
            ProofAnnotation::ShiftInRange => {
                let (ty, rhs) = match inst {
                    Inst::BinOp {
                        op: BinOp::Shl | BinOp::LShr | BinOp::AShr,
                        ty,
                        rhs,
                        ..
                    } => (ty, rhs),
                    _ => return Err(format!("{annotation} is only encodable on shift nodes")),
                };
                if matches!(ty, Ty::Vector(..)) {
                    return Err(format!(
                        "{annotation}: per-lane shift conditions for vector ops are not encoded"
                    ));
                }
                let width = bit_width(ty).map_err(|e| e.to_string())?;
                let shift = self.term(*rhs).map_err(|e| e.to_string())?;
                let bit_width_term = self
                    .solver
                    .try_bv_const(i64::from(width), width)
                    .map_err(|e| e.to_string())?;
                let operands =
                    ProofOperands::for_annotation(annotation, &[shift, bit_width_term], width)
                        .map_err(|e| e.to_string())?;
                verify_proof_obligation(&mut self.solver, annotation, &operands)
                    .map(Some)
                    .map_err(|e| e.to_string())
            }
            ProofAnnotation::NotNull | ProofAnnotation::Aligned(_) => {
                let ptr = node_ptr_operand(inst).ok_or_else(|| {
                    format!("{annotation}: the node has no pointer operand to bind")
                })?;
                let t = self.term(ptr).map_err(|e| e.to_string())?;
                let operands = ProofOperands::for_annotation(annotation, &[t], 64)
                    .map_err(|e| e.to_string())?;
                verify_proof_obligation(&mut self.solver, annotation, &operands)
                    .map(Some)
                    .map_err(|e| e.to_string())
            }
            ProofAnnotation::ValidBorrow
            | ProofAnnotation::UniqueBorrow
            | ProofAnnotation::SharedBorrow
            | ProofAnnotation::ValidDealloc => {
                let ptr = node_ptr_operand(inst).ok_or_else(|| {
                    format!("{annotation}: the node has no pointer operand to bind")
                })?;
                let t = self.term(ptr).map_err(|e| e.to_string())?;
                let permission = self
                    .borrow
                    .get_permission(&mut self.solver, t)
                    .map_err(|e| e.to_string())?;
                let operands = ProofOperands::for_annotation(annotation, &[t, permission], 2)
                    .map_err(|e| e.to_string())?;
                verify_proof_obligation(&mut self.solver, annotation, &operands)
                    .map(Some)
                    .map_err(|e| e.to_string())
            }
            // Explicit no-obligation marker: wrap-around is the DEFINED
            // result, so no condition exists to check.
            ProofAnnotation::Wrapping => Ok(None),
            // Claim-style hints with no operational obligation (memory-role /
            // GPU / codegen hints, value facts, proof backrefs, descriptive
            // custom tags). Skipped per the documented trust boundary: the
            // producer is trusted for claims, and none of these carries a VC.
            ProofAnnotation::ReadonlyTable
            | ProofAnnotation::AppendOnlyBuffer
            | ProofAnnotation::ParallelMap
            | ProofAnnotation::BoundedLoop(_)
            | ProofAnnotation::DivergenceClass(_)
            | ProofAnnotation::BranchWeights(_)
            | ProofAnnotation::ValueRange { .. }
            | ProofAnnotation::KnownBits { .. }
            | ProofAnnotation::ProofRef(_)
            | ProofAnnotation::Custom(_) => Ok(None),
            // The DataRaceFree class (verify_proof_obligation's fallthrough):
            // obligation-bearing annotations with no BV/FP encoding. Surfaced
            // as structured Unsupported verdicts, never silently dropped.
            ProofAnnotation::DataRaceFree
            | ProofAnnotation::AtomicOrdering(_)
            | ProofAnnotation::AtomicSetInsert => Err(format!(
                "{annotation}: concurrency annotations need a happens-before model \
                 beyond the BV/FP encoding (fail-closed)"
            )),
            ProofAnnotation::InBounds => Err(format!(
                "{annotation}: the IR node carries no length operand; the per-op \
                 (index, length) encoder cannot be bound from a whole-function walk"
            )),
            ProofAnnotation::NoAlias => Err(format!(
                "{annotation}: a single node binds one pointer; the second pointer \
                 of the aliasing pair is not identified in the IR"
            )),
            ProofAnnotation::NoPanic | ProofAnnotation::NoUndef => Err(format!(
                "{annotation}: requires an auxiliary safe/is_defined term the IR \
                 node does not carry"
            )),
            ProofAnnotation::Pure
            | ProofAnnotation::Deterministic
            | ProofAnnotation::Commutative
            | ProofAnnotation::Associative => Err(format!(
                "{annotation}: requires a dual-evaluation harness (per-op path only)"
            )),
            ProofAnnotation::Terminates => Err(format!(
                "{annotation}: liveness is beyond the BV/FP encoding (fail-closed)"
            )),
            ProofAnnotation::Tainted | ProofAnnotation::TrustedSink => Err(format!(
                "{annotation}: information-flow (non-interference) obligations are \
                 checked by trust-ir-build validation, not the BV/FP VC"
            )),
            ProofAnnotation::BoundedOutput { .. } | ProofAnnotation::Monotonic => Err(format!(
                "{annotation}: neural-network bounds require gamma-crown, not ay"
            )),
            // Fail closed on anything this adapter does not know (feature-
            // gated variants such as `Goal` under `clean-expr`, and future
            // variants, land here until explicitly classified).
            #[allow(unreachable_patterns)]
            other => Err(format!(
                "{other}: annotation not classified by the whole-function VC (fail-closed)"
            )),
        }
    }

    fn finish(mut self) -> FunctionVc {
        // Conditions were solved at their own program points (prefix-only
        // context — see `Pending::Solved`); here they are just packaged.
        let mut conditions = Vec::with_capacity(self.pending.len());
        for pc in std::mem::take(&mut self.pending) {
            let verdict = match pc.pending {
                Pending::Unsupported(reason) => VcVerdict::Unsupported { reason },
                Pending::Solved(verdict) => verdict,
            };
            conditions.push(VcCondition {
                block: pc.block,
                inst_index: pc.inst_index,
                source: pc.source,
                verdict,
                evidence: None,
            });
        }

        // Function-level annotations: surface the obligation-bearing ones the
        // VC cannot encode (hints carry no obligation and are skipped).
        let mut unsupported_function_proofs = Vec::new();
        for annotation in &self.function.proofs {
            if let Some(reason) = function_proof_unsupported_reason(annotation) {
                unsupported_function_proofs.push((annotation.clone(), reason));
            }
        }

        // B4-scoped module obligations, in module order.
        let obligations = bind_obligations(self.module, self.function, &conditions);

        let application_obligations = obligations.clone();
        let (application_refutations, application_unwitnessed) = split_refutations(&conditions);
        let application_evidence =
            collect_application_evidence(self.module, self.function, &conditions);
        FunctionVc {
            source_module_digest: self.module.stable_digest(),
            application_obligations,
            application_refutations,
            application_unwitnessed,
            application_evidence,
            func: self.function.id,
            bindings: self.bindings,
            conditions,
            unsupported_function_proofs,
            obligations,
            whole_function_fallback: None,
        }
    }
}

/// Split a VC's refuted conditions into the ones that may mint `Failed` and
/// the ones that may not.
///
/// D3 — the crate's rule "`Failed` requires a real refutation" (see
/// [`apply_vc_outcomes`]): only a SAT answer backed by a consumer-accepted
/// model ([`Counterexample::Model`]) is a refutation; one ay will not vouch
/// for ([`Counterexample::Unavailable`]) is reported, never applied. Admitting
/// `Unavailable` into the first list is the one-line owner reversal.
fn split_refutations(conditions: &[VcCondition]) -> (Vec<VcCondition>, Vec<VcCondition>) {
    let mut witnessed = Vec::new();
    let mut unwitnessed = Vec::new();
    for condition in conditions {
        match &condition.verdict {
            VcVerdict::Refuted {
                counterexample: Counterexample::Model(_),
            } => witnessed.push(condition.clone()),
            VcVerdict::Refuted {
                counterexample: Counterexample::Unavailable(_),
            } => unwitnessed.push(condition.clone()),
            _ => {}
        }
    }
    (witnessed, unwitnessed)
}

/// Pair each obligation with the replay evidence of the condition at its site,
/// when that condition proved AND its payload replayed offline.
fn collect_application_evidence(
    module: &Module,
    function: &Function,
    conditions: &[VcCondition],
) -> Vec<(ProofId, SmtReplayEvidence)> {
    let mut out = Vec::new();
    for obligation in &module.proof_obligations {
        if obligation.function != Some(function.id) {
            continue;
        }
        if obligation.site.is_none() {
            continue;
        }
        let mut at_site = conditions_at_site(obligation, conditions).into_iter();
        if let Some(evidence) = at_site.find_map(|c| c.evidence.clone()) {
            out.push((obligation.id, evidence));
        }
    }
    out
}

/// Bind each function-scoped module obligation to the ONE VC condition that
/// can back it, and derive that obligation's outcome from that condition alone.
///
/// # The rule this replaces, and why it was unsound
///
/// The previous rule was a blanket: if every condition the body produced was
/// proved, EVERY obligation scoped to the function became `ProvedByVc`. Nothing
/// tied an obligation to a condition. A function with one proved `DivNonZero`
/// annotation and five unrelated obligations — a `Postcondition`, a
/// `MemorySafety` claim, anything — marked all five backed. The only reason
/// that never became a false `Discharged` is that the status flip was a no-op;
/// the moment it was not, one easy proof would launder every obligation in the
/// function.
///
/// The binding is `ProofObligation::site` (v34). An obligation is backed only
/// by conditions generated AT its site, and only if at least one exists and
/// ALL of them are proved. An obligation with no site is `Unsupported`, never
/// a wildcard — an unbindable obligation is precisely one no verdict may be
/// attributed to.
fn bind_obligations(
    module: &Module,
    function: &Function,
    conditions: &[VcCondition],
) -> Vec<(ProofId, VcObligationOutcome)> {
    let mut obligations = Vec::new();
    for obligation in &module.proof_obligations {
        if obligation.function != Some(function.id) {
            continue;
        }
        let sited_on_assert = obligation.site.as_ref().is_some_and(|site| {
            function
                .blocks
                .iter()
                .find(|b| b.id == site.block)
                .and_then(|b| b.body.get(site.inst_index as usize))
                .is_some_and(|node| is_assert_site_inst(&node.inst))
        });
        let outcome = if sited_on_assert && !is_assert_class_kind(&obligation.kind) {
            // WS5.4 (1a): the condition at an assert-shaped site states a
            // panic-class fact about THAT check; a Postcondition, a
            // LoopInvariant or any other kind merely sited there is not backed
            // by it, however provable the condition is.
            VcObligationOutcome::Unsupported {
                reason: assert_class_kind_refusal(&obligation.kind),
            }
        } else if let Some(refusal) = formula_refusal(module, obligation) {
            VcObligationOutcome::Unsupported { reason: refusal }
        } else if !vc_addressable_kind(&obligation.kind) {
            VcObligationOutcome::Unsupported {
                reason: format!(
                    "obligation kind {} is outside the whole-function VC's scope",
                    obligation.kind
                ),
            }
        } else if let Some(site) = &obligation.site {
            let at_site = conditions_at_site(obligation, conditions);
            if at_site.is_empty() {
                VcObligationOutcome::NotDischarged {
                    reason: format!(
                        "no VC condition was generated at this obligation's site (bb{}#{})",
                        site.block.index(),
                        site.inst_index
                    ),
                }
            } else if at_site
                .iter()
                .all(|c| matches!(c.verdict, VcVerdict::Proved))
            {
                VcObligationOutcome::ProvedByVc
            } else if let Some(unsupported) = at_site.iter().find_map(|c| match &c.verdict {
                VcVerdict::Unsupported { reason } => Some(reason.clone()),
                _ => None,
            }) {
                VcObligationOutcome::Unsupported {
                    reason: unsupported,
                }
            } else if at_site
                .iter()
                .any(|c| matches!(c.source, VcSource::LoweredAssert { .. }))
            {
                // The SITED VC's `Refuted` means "not provable from this block
                // alone", never "the program is wrong" — and it never mints
                // `Failed` (it supplies no refutations to `apply_vc_outcomes`).
                VcObligationOutcome::NotDischarged {
                    reason: format!(
                        "the VC condition at this obligation's site (bb{}#{}) is not provable \
                         locally: the sited VC is block-local and hypothesis-free, so a \
                         counterexample over the block's free inputs is not a claim that the \
                         program is wrong",
                        site.block.index(),
                        site.inst_index
                    ),
                }
            } else {
                VcObligationOutcome::NotDischarged {
                    reason: format!(
                        "the VC condition at this obligation's site (bb{}#{}) is not proved",
                        site.block.index(),
                        site.inst_index
                    ),
                }
            }
        } else if conditions.is_empty() {
            VcObligationOutcome::NotDischarged {
                reason: "the body yields no encodable VC conditions to back this obligation \
                         (vacuous discharge refused)"
                    .to_string(),
            }
        } else if conditions
            .iter()
            .any(|c| matches!(c.verdict, VcVerdict::Refuted { .. }))
        {
            // ASYMMETRIC ON PURPOSE. Without a site the two directions are not
            // equally safe:
            //
            // * Reporting a FAILURE from a function-wide refutation is
            //   conservative — it is the direction that refuses, and it is how a
            //   violated `ensures` clause (a genuinely function-scoped
            //   obligation, which by its nature HAS no instruction site)
            //   surfaces with its counterexample.
            // * Reporting a SUCCESS from a function-wide "everything proved" is
            //   not conservative at all: it is the laundering path, where one
            //   easy `DivNonZero` marks an unrelated `Postcondition` backed.
            //   That direction requires a site — see the arm above.
            let not_proved = conditions
                .iter()
                .filter(|c| !matches!(c.verdict, VcVerdict::Proved))
                .count();
            VcObligationOutcome::NotDischarged {
                reason: format!(
                    "{not_proved} of {} VC conditions are not proved",
                    conditions.len()
                ),
            }
        } else {
            VcObligationOutcome::Unsupported {
                reason: "obligation carries no site backref (ProofObligation::site), so no VC \
                         condition can be bound to it; attributing a function-wide SUCCESS to \
                         it would let one proof launder every obligation in the function \
                         (fail-closed)"
                    .to_string(),
            }
        };
        obligations.push((obligation.id, outcome));
    }
    obligations
}

/// The conditions that can back `obligation`: those generated at its site.
///
/// A sited-VC condition names the obligation it was generated FOR, and backs
/// only that one — two rows sited on one node each get their own condition, so
/// one row's verdict can never be read as another's. A whole-function condition
/// (an `Inst::Assert` walked in body order, or an instruction annotation) is
/// shared by every row at its position.
fn conditions_at_site<'c>(
    obligation: &ProofObligation,
    conditions: &'c [VcCondition],
) -> Vec<&'c VcCondition> {
    let Some(site) = &obligation.site else {
        return Vec::new();
    };
    conditions
        .iter()
        .filter(|c| c.block == site.block && c.inst_index == site.inst_index as usize)
        .filter(|c| match c.source {
            VcSource::LoweredAssert {
                obligation: owner, ..
            } => owner == obligation.id,
            _ => true,
        })
        .collect()
}

/// Why a formula-bearing obligation cannot be addressed, or `None` when it
/// carries no formula or its formula states the goal re-derived at its site.
///
/// WS5.4 (1b): the adapter has no in-process SMT-LIB bridge, so a formula is
/// admitted only in the one spelling trust-ir can compare to the IR —
/// [`trust_ir::proof::formula_binds_site_goal`] (the bit-blast goal claim, or a
/// producer `smtlib2` formula whose one SMT-LIB text IS the canonical
/// bit-vector rendering of the site goal).
/// Anything else stays `Unsupported`; the formula is never ignored and never
/// replaced.
fn formula_refusal(module: &Module, obligation: &ProofObligation) -> Option<String> {
    obligation.formula.as_ref()?;
    match derive_site_goal(module, obligation) {
        Ok(goal) if formula_binds_site_goal(obligation, &goal) => None,
        Ok(_) => Some(format!(
            "{PRODUCER_FORMULA_DISAGREES}: the obligation's formula does not state the \
             bit-vector goal re-derived at its site, and the adapter has no in-process SMT-LIB \
             bridge to check any other spelling (fail-closed)"
        )),
        Err(err) => Some(format!(
            "obligation carries a formula payload and no bit-vector site goal is derivable to \
             compare it with ({err}); the adapter has no in-process SMT-LIB bridge \
             (fail-closed)"
        )),
    }
}

/// The obligation kinds a whole-function VC over in-IR conditions
/// (Asserts + instruction annotations) can honestly back. Everything else
/// (temporal safety, liveness, translation validation, invariants, give-back
/// refinement, …) is out of scope and reported `Unsupported`.
fn vc_addressable_kind(kind: &ObligationKind) -> bool {
    matches!(
        kind,
        ObligationKind::Precondition
            | ObligationKind::Postcondition
            | ObligationKind::MemorySafety
            | ObligationKind::PanicFreedom
            | ObligationKind::ArithmeticSafety
            | ObligationKind::BoundsCheck
    )
}

/// Reason a function-level annotation is not covered by the VC, or `None`
/// for claim-style hints that carry no obligation.
fn function_proof_unsupported_reason(annotation: &ProofAnnotation) -> Option<String> {
    match annotation {
        // Hints / markers: no obligation to discharge.
        ProofAnnotation::Wrapping
        | ProofAnnotation::ReadonlyTable
        | ProofAnnotation::AppendOnlyBuffer
        | ProofAnnotation::ParallelMap
        | ProofAnnotation::BoundedLoop(_)
        | ProofAnnotation::DivergenceClass(_)
        | ProofAnnotation::BranchWeights(_)
        | ProofAnnotation::ValueRange { .. }
        | ProofAnnotation::KnownBits { .. }
        | ProofAnnotation::ProofRef(_)
        | ProofAnnotation::Custom(_) => None,
        ProofAnnotation::DataRaceFree
        | ProofAnnotation::AtomicOrdering(_)
        | ProofAnnotation::AtomicSetInsert => Some(format!(
            "{annotation}: concurrency annotations need a happens-before model \
             beyond the BV/FP encoding (fail-closed)"
        )),
        ProofAnnotation::BoundedOutput { .. } | ProofAnnotation::Monotonic => Some(format!(
            "{annotation}: neural-network bounds require gamma-crown, not ay"
        )),
        other => Some(format!(
            "{other}: function-level claim; the whole-function VC checks in-IR \
             conditions and does not verify function-level claims (producer-trusted \
             per the documented trust boundary)"
        )),
    }
}

/// The pointer operand an aliasing/borrow/nullability annotation binds to,
/// if the node has one.
fn node_ptr_operand(inst: &Inst) -> Option<ValueId> {
    match inst {
        Inst::Load { ptr, .. }
        | Inst::Store { ptr, .. }
        | Inst::Borrow { ptr }
        | Inst::BorrowMut { ptr }
        | Inst::Retain { ptr }
        | Inst::Release { ptr }
        | Inst::IsUnique { ptr }
        | Inst::Dealloc { ptr } => Some(*ptr),
        Inst::EndBorrow { borrow_ptr } => Some(*borrow_ptr),
        Inst::GEP { base, .. } => Some(*base),
        _ => None,
    }
}

/// Total bit width of a schema-sorted type (BitVec width, or eb+sb for FP),
/// by the crate's one width rule, [`crate::sort_bit_width`].
fn bit_width(ty: &Ty) -> Result<u32, AYError> {
    crate::sort_bit_width(&ay_sort(ty)?).ok_or_else(|| AYError::UnsupportedType(ty.clone()))
}

/// Byte width for the byte-addressable memory model. Fails closed on types
/// without a whole-byte width (e.g. Bool).
fn byte_width(ty: &Ty) -> Result<u32, AYError> {
    let bits = bit_width(ty)?;
    if bits % 8 != 0 {
        return Err(AYError::MemoryError(format!(
            "{ty}: {bits}-bit values have no whole-byte memory width"
        )));
    }
    Ok(bits / 8)
}

/// Compact label for an instruction in fail-closed error messages.
fn inst_label(inst: &Inst) -> String {
    let debug = format!("{inst:?}");
    debug
        .split([' ', '{', '('])
        .next()
        .unwrap_or(&debug)
        .to_string()
}

#[cfg(test)]
mod tests {
    #![allow(clippy::disallowed_methods)]

    use super::*;
    use trust_ir::Block;
    use trust_ir::proof::{ObligationKind, ProofObligation, ProofStatus};
    use trust_ir::ty::FuncTy;

    /// A one-block `f(i32) -> ()` function and its module.
    fn single_block_module() -> Module {
        let mut module = Module::new("vc_frames");
        let signature = module
            .add_func_type(FuncTy {
                abi: None,
                params: vec![Ty::I32],
                returns: vec![],
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");
        let mut function = Function::new(FuncId::new(0), "f", signature, BlockId::new(0));
        let mut block = Block::new(BlockId::new(0));
        block.params.push((ValueId::new(0), Ty::I32));
        block
            .body
            .push(InstrNode::new(Inst::Return { values: vec![] }));
        function.blocks.push(block);
        module.functions.push(function);
        module
    }

    /// `(= a b)` over two fresh 8-bit constants: `holds == false` is PROVED
    /// when `a != b` (the negation `a = b` is UNSAT), REFUTED when `a == b`.
    fn condition(vcb: &mut VcBuilder<'_>, a: i64, b: i64) -> ProofCondition {
        let a = vcb.solver.try_bv_const(a, 8).expect("constant");
        let b = vcb.solver.try_bv_const(b, 8).expect("constant");
        ProofCondition {
            term: vcb.solver.try_eq(a, b).expect("eq"),
            strategy: crate::ProofStrategy::AssertAndCheckUnsat,
        }
    }

    /// r11 C1 (evidence kind ii: no seam on origin/main). When ay's panics
    /// became `Err`s, a failed or unbalanced solver frame could leave a goal
    /// on the stack; every later condition is checked "under the current
    /// (prefix-only) solver context", so a leftover `false` would make every
    /// later condition falsely `Proved`. The session is POISONED instead and
    /// proves nothing afterwards. Mutation checks: ignoring `poisoned` in
    /// `in_frame` turns (a) `Proved`; dropping the scope-level check turns (c)
    /// into a FALSE `Proved`.
    #[test]
    fn a_poisoned_session_proves_nothing_after_the_frame_error() {
        let module = single_block_module();
        let function = &module.functions[0];

        // (a) A poisoned session does not solve an otherwise-PROVED goal.
        let mut vcb = VcBuilder::new(&module, function).expect("builder");
        let provable = condition(&mut vcb, 1, 2);
        assert_eq!(vcb.solve_condition_now(provable), VcVerdict::Proved);
        vcb.poisoned = Some("solver session poisoned: test".to_string());
        let provable = condition(&mut vcb, 1, 2);
        assert_eq!(
            vcb.solve_condition_now(provable),
            VcVerdict::Unknown {
                reason: "solver session poisoned: test".to_string()
            }
        );

        // (b) The guard's own pop underflows (the body popped its frame):
        // poisoned, and the next trivially-provable goal is `Unknown`.
        let mut vcb = VcBuilder::new(&module, function).expect("builder");
        let framed = vcb.in_frame(|vcb| vcb.solver.try_pop().map_err(AYError::from));
        assert!(matches!(&framed, Err(reason) if reason.contains("could not be closed")));
        let provable = condition(&mut vcb, 1, 2);
        assert!(matches!(
            vcb.solve_condition_now(provable),
            VcVerdict::Unknown { reason } if reason.starts_with("solver session poisoned")
        ));

        // (c) The body leaves an extra frame holding `false`: the guard's pop
        // succeeds, but the stack is unbalanced. A REFUTABLE goal would read
        // `Proved` against the leftover `false`; the poisoned session says
        // `Unknown` instead.
        let mut vcb = VcBuilder::new(&module, function).expect("builder");
        let framed = vcb.in_frame(|vcb| {
            vcb.solver.try_push().expect("push");
            let contradiction = condition(vcb, 1, 2);
            vcb.solver
                .try_assert_term(contradiction.term)
                .expect("assert");
            vcb.solver.try_push().expect("push");
            Ok(())
        });
        assert!(matches!(&framed, Err(reason) if reason.contains("unbalanced")));
        let refutable = condition(&mut vcb, 3, 3);
        assert!(matches!(
            vcb.solve_condition_now(refutable),
            VcVerdict::Unknown { reason } if reason.starts_with("solver session poisoned")
        ));
    }

    /// r11 review H1 (evidence kind ii: the seam is new). ay's
    /// `try_check_sat` turns a panic inside the solver into
    /// `SolverError::SolverPanic`, after which ay says the solver's state is
    /// likely corrupted. Before this rule the frame mapped such an error to
    /// `Unknown` and the whole-function walk went on solving later
    /// conditions on the SAME solver. Every error a frame body returns now
    /// poisons the session. Mutation check: keeping the message but dropping
    /// the `self.poison(..)` call on a body error turns the follow-up goal in
    /// (d) into `Proved` (measured at landing).
    #[test]
    fn a_failed_solver_step_inside_a_frame_poisons_the_session() {
        let module = single_block_module();
        let function = &module.functions[0];

        // (d) The `SolverPanic` shape: no input is known that makes ay's
        // `check_sat` panic, so the body returns the error a caught panic
        // flattens to. The frame closes cleanly; the session is poisoned
        // anyway, and the next trivially-provable goal is `Unknown`.
        let mut vcb = VcBuilder::new(&module, function).expect("builder");
        let framed: Result<(), String> = vcb.in_frame(|_| {
            Err(AYError::SolverError(
                "solver panicked: simulated internal invariant failure".to_string(),
            ))
        });
        assert!(
            matches!(&framed, Err(reason) if reason.contains("inside the frame failed")),
            "{framed:?}"
        );
        assert_eq!(vcb.solver.num_scopes(), 0, "the frame was still closed");
        let provable = condition(&mut vcb, 1, 2);
        assert!(matches!(
            vcb.solve_condition_now(provable),
            VcVerdict::Unknown { reason } if reason.starts_with("solver session poisoned")
        ));

        // (e) A real refusal on the condition path: ay refuses to assert a
        // non-Boolean term. That condition is `Unknown` and the session is
        // poisoned, so a following trivially-provable goal is `Unknown` too
        // — never solved on the solver that just failed.
        let mut vcb = VcBuilder::new(&module, function).expect("builder");
        let not_boolean = ProofCondition {
            term: vcb.solver.try_bv_const(1, 8).expect("constant"),
            strategy: crate::ProofStrategy::AssertAndCheckUnsat,
        };
        assert!(matches!(
            vcb.solve_condition_now(not_boolean),
            VcVerdict::Unknown { reason } if reason.starts_with("solver session poisoned")
        ));
        let provable = condition(&mut vcb, 1, 2);
        assert!(matches!(
            vcb.solve_condition_now(provable),
            VcVerdict::Unknown { reason } if reason.starts_with("solver session poisoned")
        ));
    }

    /// r11 item 4 (evidence kind ii: the seam is new). A SAT answer ay will
    /// not vouch for is `Unavailable`, never an EMPTY model: with no
    /// `check_sat` at all, and after an UNSAT, there is no SAT result.
    #[test]
    fn a_sat_without_a_consumer_model_is_unavailable_never_empty() {
        let module = single_block_module();
        let function = &module.functions[0];
        let mut vcb = VcBuilder::new(&module, function).expect("builder");
        assert_eq!(
            sat_witness(&vcb.solver, &vcb.bindings),
            Counterexample::Unavailable(WitnessUnavailable::NoSatResult)
        );
        let provable = condition(&mut vcb, 1, 2);
        vcb.solver.try_assert_term(provable.term).expect("assert");
        assert!(vcb.solver.try_check_sat().expect("check").is_unsat());
        assert_eq!(
            sat_witness(&vcb.solver, &vcb.bindings),
            Counterexample::Unavailable(WitnessUnavailable::NoSatResult)
        );
    }

    /// r11 item 4 / D3 (evidence kind ii). A VC whose only refutation carries
    /// an `Unavailable` witness mints no `Failed`: the row stays `Pending`
    /// and a diagnostic names ay's reason. A model-backed refutation still
    /// fails the row. Mutation check: admitting `Unavailable` in
    /// `split_refutations` mints `Failed` here.
    #[test]
    fn an_unavailable_witness_never_mints_failed() {
        let refuted = |counterexample| VcCondition {
            block: BlockId::new(0),
            inst_index: 0,
            source: VcSource::Assert,
            verdict: VcVerdict::Refuted { counterexample },
            evidence: None,
        };
        for (witness, expect_failed) in [
            (
                Counterexample::Unavailable(WitnessUnavailable::NotValidated),
                false,
            ),
            (Counterexample::Model(Vec::new()), true),
        ] {
            let mut module = single_block_module();
            let id = ProofId::new(0);
            module.proof_obligations.push(
                ProofObligation::new(
                    id,
                    ObligationKind::Postcondition,
                    ProofStatus::Pending,
                    "ensures",
                )
                .with_function(FuncId::new(0)),
            );
            let conditions = vec![refuted(witness)];
            let (application_refutations, application_unwitnessed) = split_refutations(&conditions);
            let outcome = VcObligationOutcome::NotDischarged {
                reason: "1 of 1 VC conditions are not proved".to_string(),
            };
            let vc = FunctionVc {
                source_module_digest: module.stable_digest(),
                application_obligations: vec![(id, outcome.clone())],
                application_refutations,
                application_unwitnessed,
                application_evidence: Vec::new(),
                func: FuncId::new(0),
                bindings: Vec::new(),
                conditions,
                unsupported_function_proofs: Vec::new(),
                obligations: vec![(id, outcome)],
                whole_function_fallback: None,
            };
            let transitions = apply_vc_outcomes(&mut module, &vc).expect("same module");
            if expect_failed {
                assert_eq!(transitions, vec![(id, ProofStatus::Failed)]);
            } else {
                assert!(transitions.is_empty(), "no Failed on an unvouched SAT");
                assert_eq!(module.proof_obligations[0].status, ProofStatus::Pending);
                assert!(
                    module
                        .obligation_diagnostics
                        .iter()
                        .any(|diagnostic| diagnostic
                            .message
                            .contains("ay did not validate its SAT model for a consumer")),
                    "the diagnostic names the reason: {:?}",
                    module.obligation_diagnostics
                );
            }
        }
    }
}
