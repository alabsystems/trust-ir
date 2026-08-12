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
//! * **Straight-line bodies only (v1).** A function must consist of a single
//!   entry block ending in `Return`. Control flow (`Br`/`CondBr`/`Switch`),
//!   calls, atomics, aggregates, and every other unencoded instruction fail
//!   closed with [`AYError::UnsupportedOp`] — there is no silent havoc: an
//!   unencodable instruction aborts VC generation rather than weakening it.
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
//!   [`VcObligationOutcome`]. An obligation is `ProvedByVc` only when the body
//!   produced at least one condition and every condition proved;
//!   formula-carrying obligations fail closed (`Unsupported`) because the
//!   adapter has no in-process SMT-LIB bridge.
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
    ObligationDiagnostic, ObligationKind, ProofAnnotation, ProofDigest, ProofStatus,
};
use trust_ir::ty::Ty;
use trust_ir::value::{BlockId, FuncId, ProofId, ValueId};
use trust_ir::{Constant, Function, InstrNode, Module};

use crate::{
    AYError, ArcModel, BorrowModel, MemoryModel, ProofCondition, ProofOperands, ay_sort, ay_symbol,
    create_fp_solver, encode_binop, encode_cast, encode_fcmp, encode_icmp, encode_overflow_check,
    encode_unop, encode_vector_binop, verify_proof_obligation,
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
    /// A LOWERED assert: the `CondBr` at a [`trust_ir::ObligationSite`] exactly
    /// one of whose successors diverges (a `core::panicking` arm ending
    /// `Unreachable`). The VC is that control never takes the diverging arm.
    ///
    /// This is how a rustc `Assert` arrives in TrustIr — the frontend lowers it
    /// to explicit control flow, so there is no `Inst::Assert` to find.
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
    /// `counterexample` maps the schema-bound inputs back to source values.
    Refuted {
        /// `(value, assignment)` pairs over the function's bound symbols,
        /// in binding (declaration) order.
        counterexample: Vec<(ValueId, ModelValue)>,
    },
    /// The solver could not decide (timeout / resource limit).
    Unknown,
    /// Fail-closed: the annotation has no BV/FP encoding (the
    /// `DataRaceFree`-class fallthrough of [`verify_proof_obligation`]).
    /// Surfaced structurally so it can never be mistaken for a PASS.
    Unsupported {
        /// Why the condition could not be encoded.
        reason: String,
    },
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
pub const AY_REV: &str = "882800fa351d5045e6f8ca67c756b4081ffbf2cf";

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
    application_refutations: Vec<VcCondition>,
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
    pub fn all_proved(&self) -> bool {
        self.conditions
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
///   no verdict is invented in either direction.
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
                    continue;
                }
                obligation.status = ProofStatus::Failed;
                let message = format!("whole-function VC refuted: {reason}");
                let detail = render_refutations(&refuted);
                module
                    .obligation_diagnostics
                    .push(ObligationDiagnostic::error(*id, message).with_detail(detail));
                transitions.push((*id, ProofStatus::Failed));
            }
            VcObligationOutcome::Unsupported { .. } => {}
        }
    }
    Ok(transitions)
}

/// Render the refuted conditions of a VC as the machine-readable `detail` of
/// an [`ObligationDiagnostic`]: one `counterexample …` line per refutation,
/// each assignment in binding (declaration) order — deterministic because
/// [`model_counterexample`] is.
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
        let assignments = counterexample
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
    vcb.walk()?;
    Ok(vcb.finish())
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
        application_evidence,
        func: function.id,
        bindings,
        conditions,
        unsupported_function_proofs,
        obligations,
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
        let mem = MemoryModel::new(&mut solver, &format!("f{f}_mem"));
        let borrow = BorrowModel::new(&mut solver, &format!("f{f}_perm"));
        let arc = ArcModel::new(&mut solver, &format!("f{f}_rc"));
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
        let term = self.solver.declare_const(&name, sort);
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
    fn bool_to_bv1(&mut self, b: Term) -> Term {
        let one = self.solver.bv_const(1, 1);
        let zero = self.solver.bv_const(0, 1);
        self.solver.ite(b, one, zero)
    }

    /// Bool <- BitVec(1): the inverse normalization for `Assume`/`Assert`/
    /// `Select` conditions.
    fn bv1_to_bool(&mut self, t: Term) -> Term {
        let one = self.solver.bv_const(1, 1);
        self.solver.eq(t, one)
    }

    /// Solve one condition NOW, under the current (prefix-only) solver
    /// context, in its own push/pop frame. Called at the program point where
    /// the condition occurs — see [`Pending::Solved`].
    fn solve_condition_now(&mut self, cond: ProofCondition) -> VcVerdict {
        self.solver.push();
        self.solver.assert_term(cond.term);
        let result = self.solver.check_sat();
        let verdict = if result.is_unsat() {
            VcVerdict::Proved
        } else if result.is_sat() {
            let counterexample = self
                .solver
                .model()
                .map(|m| model_counterexample(m.model(), &self.bindings))
                .unwrap_or_default();
            VcVerdict::Refuted { counterexample }
        } else {
            VcVerdict::Unknown
        };
        self.solver.pop();
        verdict
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
        for (value, ty) in &block.params {
            if self.declare(*value, ty).is_err() {
                return (
                    VcVerdict::Unsupported {
                        reason: format!(
                            "block parameter v{} has type {ty}, which has no solver sort \
                             (fail-closed)",
                            value.index()
                        ),
                    },
                    None,
                );
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
            return (
                VcVerdict::Unsupported {
                    reason: format!(
                        "the assert condition v{} is not derivable from this block's pure prefix \
                         (it depends on memory, a call, or a value defined in another block); \
                         the sited VC encodes no such context (fail-closed)",
                        cond.index()
                    ),
                },
                None,
            );
        };
        let holds = self.bv1_to_bool(term);
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
            self.solver.not(holds)
        };
        let negated = self.solver.not(holds);
        let goal_canonical = self.solver.render_term_canonical(negated);
        // Inlined rather than routed through `solve_condition_now`, because the
        // proof payload must be exported INSIDE the solver frame: `pop()`
        // discards the last proof along with the assertion that produced it.
        self.solver.push();
        self.solver.assert_term(negated);
        let result = self.solver.check_sat();
        let (verdict, evidence) = if result.is_unsat() {
            // Capture the replayable payload ONLY on Proved, and only if it
            // actually replays offline. A payload that does not replay is not
            // attached at all — it would be a claim, not evidence.
            let evidence = self.capture_replay_evidence(goal_canonical);
            (VcVerdict::Proved, evidence)
        } else if result.is_sat() {
            let counterexample = self
                .solver
                .model()
                .map(|m| model_counterexample(m.model(), &self.bindings))
                .unwrap_or_default();
            (VcVerdict::Refuted { counterexample }, None)
        } else {
            (VcVerdict::Unknown, None)
        };
        self.solver.pop();
        (verdict, evidence)
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
                let term = self.solver.bv_const(0, 64);
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
                let term = encode_unop(&mut self.solver, *op, t)?;
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
                let safe = encode_overflow_check(&mut self.solver, *op, ty.is_signed(), l, r);
                let overflowed = self.solver.not(safe);
                let flag = self.bool_to_bv1(overflowed);
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
                let b = encode_icmp(&mut self.solver, *op, l, r);
                let term = self.bool_to_bv1(b);
                self.bind(Self::result0(node)?, term, Ty::Bool);
            }
            Inst::FCmp { op, lhs, rhs, .. } => {
                let l = self.term(*lhs)?;
                let r = self.term(*rhs)?;
                let b = encode_fcmp(&mut self.solver, *op, l, r);
                let term = self.bool_to_bv1(b);
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
                let c = self.bv1_to_bool(c);
                let t = self.term(*then_val)?;
                let e = self.term(*else_val)?;
                let term = self.solver.ite(c, t, e);
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
                let addr = self.mem.encode_alloca(&mut self.solver, size);
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
                        Some(s) => self.solver.bvadd(s, t),
                    });
                }
                let offset = match sum {
                    None => self.solver.bv_const(0, 64),
                    Some(s) => {
                        let size = self.solver.bv_const(elem_bytes, 64);
                        self.solver.bvmul(s, size)
                    }
                };
                let term = self.mem.encode_gep(&mut self.solver, base_term, offset);
                self.bind(Self::result0(node)?, term, Ty::Ptr);
            }
            Inst::Borrow { ptr } => {
                let t = self.term(*ptr)?;
                let (borrowed, _) = self.borrow.encode_borrow(&mut self.solver, t);
                self.bind(Self::result0(node)?, borrowed, Ty::Ptr);
            }
            Inst::BorrowMut { ptr } => {
                let t = self.term(*ptr)?;
                let (borrowed, _) = self.borrow.encode_borrow_mut(&mut self.solver, t);
                self.bind(Self::result0(node)?, borrowed, Ty::Ptr);
            }
            Inst::EndBorrow { borrow_ptr } => {
                let t = self.term(*borrow_ptr)?;
                self.borrow.encode_end_borrow(&mut self.solver, t);
            }
            Inst::Retain { ptr } => {
                let t = self.term(*ptr)?;
                self.arc.encode_retain(&mut self.solver, t);
            }
            Inst::Release { ptr } => {
                let t = self.term(*ptr)?;
                self.arc.encode_release(&mut self.solver, t)?;
            }
            Inst::IsUnique { ptr } => {
                let t = self.term(*ptr)?;
                let b = self.arc.encode_is_unique(&mut self.solver, t);
                let term = self.bool_to_bv1(b);
                self.bind(Self::result0(node)?, term, Ty::Bool);
            }
            Inst::Assume { cond } => {
                let t = self.term(*cond)?;
                let b = self.bv1_to_bool(t);
                self.solver.assert_term(b);
            }
            Inst::Assert { cond } => {
                let t = self.term(*cond)?;
                let b = self.bv1_to_bool(t);
                // Assert-and-check-UNSAT contract: check the NEGATION.
                let negated = self.solver.not(b);
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
            Constant::Bool(b) => Ok(self.solver.bv_const(i64::from(*b), 1)),
            Constant::Int(i) => {
                let width = match ay_sort(ty)? {
                    Sort::BitVec(bv) => bv.width,
                    _ => {
                        return Err(AYError::UnsupportedOp(format!(
                            "integer constant of non-bitvector type {ty}"
                        )));
                    }
                };
                let v = i64::try_from(*i).map_err(|_| {
                    AYError::UnsupportedOp(format!(
                        "constant {i} exceeds the i64 range of the ay bv_const API"
                    ))
                })?;
                Ok(self.solver.bv_const(v, width))
            }
            other => Err(AYError::UnsupportedOp(format!(
                "constant {other:?} is not supported by the whole-function VC"
            ))),
        }
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
                let bit_width_term = self.solver.bv_const(i64::from(width), width);
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
                let permission = self.borrow.get_permission(&mut self.solver, t);
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
        let application_refutations = conditions
            .iter()
            .filter(|condition| matches!(condition.verdict, VcVerdict::Refuted { .. }))
            .cloned()
            .collect();
        let application_evidence =
            collect_application_evidence(self.module, self.function, &conditions);
        FunctionVc {
            source_module_digest: self.module.stable_digest(),
            application_obligations,
            application_refutations,
            application_evidence,
            func: self.function.id,
            bindings: self.bindings,
            conditions,
            unsupported_function_proofs,
            obligations,
        }
    }
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
        let Some(site) = &obligation.site else {
            continue;
        };
        let mut at_site = conditions
            .iter()
            .filter(|c| c.block == site.block && c.inst_index == site.inst_index as usize);
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
        let outcome = if obligation.formula.is_some() {
            VcObligationOutcome::Unsupported {
                reason: "obligation carries a formula payload; the adapter has no in-process \
                         SMT-LIB bridge (fail-closed)"
                    .to_string(),
            }
        } else if !vc_addressable_kind(&obligation.kind) {
            VcObligationOutcome::Unsupported {
                reason: format!(
                    "obligation kind {} is outside the whole-function VC's scope",
                    obligation.kind
                ),
            }
        } else if let Some(site) = &obligation.site {
            let at_site: Vec<&VcCondition> = conditions
                .iter()
                .filter(|c| c.block == site.block && c.inst_index == site.inst_index as usize)
                .collect();
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

/// Total bit width of a schema-sorted type (BitVec width, or eb+sb for FP).
fn bit_width(ty: &Ty) -> Result<u32, AYError> {
    match ay_sort(ty)? {
        Sort::BitVec(bv) => Ok(bv.width),
        Sort::FloatingPoint(eb, sb) => Ok(eb + sb),
        _ => Err(AYError::UnsupportedType(ty.clone())),
    }
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
