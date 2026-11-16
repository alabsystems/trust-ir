// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! The BIT-BLAST proof route: a sited panic-class obligation to a replayable,
//! goal-bound refutation, and the validator capability that grants it authority.
//!
//! # What this route is, and why it is not the solver-bundle route
//!
//! The adapter's other proof path ([`crate::vc`]) drives ay's `Solver` and
//! captures an `ay.proofbundle/v2`. At the pinned revision, supported symbolic
//! BV bundles replay offline with zero trust steps, while a vacuity gate still
//! rejects goals that folded to a literal before solving. That path does not yet
//! independently bind the replayed formula to a goal re-derived from the live
//! IR, so it records evidence but cannot mint discharge authority.
//!
//! This route uses `ay_proof::export_bv_blast_proof_expr_bounded` instead. Its
//! format is *structurally incapable* of a trust step — `bv_blast_export` states
//! there is no `trust` variant to emit — and the refutation is DERIVED by the
//! ay-sat CDCL engine (`prove_unsat_resolution_dag`), not asserted by the
//! exporter. Both production and replay run under the finite policy below.
//!
//! # The soundness problem this module actually solves
//!
//! `BvBlastProof::validate()` is a real re-check: it requires an inhabitable
//! gate graph, re-derives every gate's Tseitin clause set from an exhaustive
//! truth-table walk, requires exactly one well-formed disequality over all
//! `BitEq` outputs, and replays every resolution step. Tampering is caught —
//! dropping the last step, corrupting a gate kind, flipping a clause literal,
//! or injecting junk disequality clauses were each measured to fail.
//!
//! But `validate()` says nothing about *which* fact was proved:
//!
//! * The goal is not in the object. `asserted_smt` is a hardcoded placeholder
//!   and the `obligation` record is fabricated regardless of the real goal (the
//!   producer's own comment says it is "NOT load-bearing and NOT consulted by
//!   `validate()`").
//! * Leaf NAMES are erased — `VarRole::InputLeaf` carries an index only — so
//!   proofs of goals over entirely different program variables are
//!   byte-identical.
//! * The object does not authenticate its own construction from a live source
//!   formula. A valid proof for a different graph remains a valid proof object,
//!   and its descriptive metadata can be relabelled without changing that
//!   graph.
//!
//! So `validate() == Ok` means only: *this object is an internally-consistent
//! resolution refutation of its internally authenticated Boolean graph*. It is
//! not evidence that the graph came from this module's obligation.
//!
//! [`BvBlastAuthority`] closes this by RE-DERIVATION, never by reading the
//! payload's own claims:
//!
//! 1. the goal is re-derived from the module IR by
//!    [`trust_ir::proof::derive_site_goal`] — validator-owned, zero-dep code;
//! 2. the obligation's own `formula` must pin that goal's digest;
//! 3. the CNF is re-derived by re-running the blaster on the re-derived goal;
//! 4. the stored payload's CNF must equal the re-derived one exactly;
//! 5. only then is the payload's refutation replayed by
//!    `validate_with_limits()`.
//!
//! Step 3 is precisely what `recheck_lowering_resolution` documents itself as
//! unable to do, and it is why that anchor is refused `Certified`. Here it is
//! possible because the goal comes from the IR and the CNF comes from the goal.
//!
//! # What remains trusted
//!
//! MACHINE-CHECKED: the goal is re-derived from the module by validator-owned
//! code; the CNF is re-derived from that goal; the payload's CNF is exactly the
//! re-derived one; every resolution step is replayed against gate CNF re-derived
//! from the gate's own truth table; the chain ends in the empty clause; a
//! satisfiable goal yields no proof at all.
//!
//! STILL TRUSTED: (a) that ay's private `ExprBlaster` wires the correct gate
//! TOPOLOGY for each node — `validate()` catches a wrong CNF *for* a gate, not a
//! wrong gate; and (b) for a lowered `CondBr` site, the producer's
//! `condbr assert_cond, <success>, <panic>` convention, which every other
//! branch shape fails closed on. An `Inst::Assert` site (WS5.4) needs no such
//! convention: `assert c` states `c` itself. The falsifiers for (a)
//! are the sharp-boundary matrix and the anti-vacuity tests in
//! `tests/bvblast_authority.rs`; they are tests, not a proof, and are named as a
//! residual rather than glossed. Closing (a) needs trust-ir's own canonical
//! Tseitin blaster replayed through the existing `satres` checker — a separate
//! rung, not promised here.

use std::time::Duration;

use ay_proof::{
    BvBlastProof, BvBlastValidateError, BvBlastValidateLimits, BvExpr, BvExprExportError,
    BvExprProofBudget,
};
use trust_ir::Module;
use trust_ir::proof::{
    ASSERT_CLASS_OBLIGATION_KINDS, BVBLAST_GOAL_SCHEMA, BvGoal, BvTerm, GoalDeriveError,
    ObligationKind, PRODUCER_FORMULA_DISAGREES, ProofCertificate, ProofEvidence, ProofObligation,
    ProofStatus, bvblast_goal_formula_parts, bvgoal_digest_hex, derive_site_goal,
    formula_binds_site_goal, formula_matches_goal, is_assert_class_kind, is_bvgoal_digest_hex,
};

use crate::vc::AY_REV;

/// Identity of this prover, stamped into every certificate.
///
/// Includes the ay revision, so a pin bump invalidates every stored
/// certificate rather than silently re-interpreting it: `ProofCertificateRef`
/// is `(obligation, prover, evidence_digest)`, and the authority capability
/// requires an exact match on this string.
pub const BVBLAST_PROVER: &str = "trust-ir-ay/bvblast@8bbc43108643d475a81a89b2b4f262e817ee1724";

/// Schema tag of the certificate payload carried inside
/// [`ProofEvidence::SmtProof`].
pub const BVBLAST_CERT_SCHEMA: &str = "trust-ir.bvblast.cert.v1";

// The TrustIR goal language already rejects more than 256 source nodes and a
// blast-cost score above 16,384. These independent producer/replay limits close
// the remaining search, materialization, and hostile-certificate surfaces.
// They deliberately mirror AY's conservative public bounded-export envelope
// rather than being inferred from the proof currently being checked: a stored
// proof is untrusted input and must not get to choose its own limits.
const BVBLAST_PROOF_TIMEOUT: Duration = Duration::from_secs(30);
const BVBLAST_REPLAY_TIMEOUT: Duration = Duration::from_secs(30);
const BVBLAST_MAX_RESOLUTION_STEPS: usize = 250_000;

const BVBLAST_MAX_REPLAY_VARS: usize = 150_000;
const BVBLAST_MAX_REPLAY_BIT_LEMMAS: usize = 100_000;
const BVBLAST_MAX_REPLAY_CLAUSES: usize = 700_000;
const BVBLAST_MAX_REPLAY_CLAUSE_LITERALS: usize = 64;
const BVBLAST_MAX_REPLAY_ORIGINAL_LITERALS: usize = 3_000_000;
const BVBLAST_MAX_REPLAY_DERIVED_LITERALS: usize = 2_000_000;
const BVBLAST_MAX_REPLAY_WORK: u64 = 50_000_000;

// Maximum serialized certificate payload accepted before JSON decoding. This
// is checked before deserialization because structural replay limits cannot
// protect allocations made while decoding an already oversized byte string.
const BVBLAST_MAX_CERTIFICATE_BYTES: usize = 16 * 1024 * 1024;

fn proof_budget() -> Result<BvExprProofBudget, ProveError> {
    BvExprProofBudget::conservative(BVBLAST_PROOF_TIMEOUT, BVBLAST_MAX_RESOLUTION_STEPS)
        .map_err(|error| ProveError::Incomplete(format!("invalid internal proof budget: {error}")))
}

fn replay_limits() -> BvBlastValidateLimits {
    // AY's native Instant is exactly std::time::Instant. AY supplies a custom
    // wasm clock through ay-core, which this adapter does not depend on
    // directly; wasm therefore retains the same finite size/work limits but no
    // duplicate replay deadline. Proof production itself remains deadline-
    // bounded on every AY-supported target.
    #[cfg(not(target_arch = "wasm32"))]
    let deadline = std::time::Instant::now().checked_add(BVBLAST_REPLAY_TIMEOUT);
    #[cfg(target_arch = "wasm32")]
    let deadline = None;

    BvBlastValidateLimits {
        deadline,
        max_vars: BVBLAST_MAX_REPLAY_VARS,
        max_bit_lemmas: BVBLAST_MAX_REPLAY_BIT_LEMMAS,
        max_clauses: BVBLAST_MAX_REPLAY_CLAUSES,
        max_clause_literals: BVBLAST_MAX_REPLAY_CLAUSE_LITERALS,
        max_original_literals: BVBLAST_MAX_REPLAY_ORIGINAL_LITERALS,
        max_resolution_steps: BVBLAST_MAX_RESOLUTION_STEPS,
        max_derived_literals: BVBLAST_MAX_REPLAY_DERIVED_LITERALS,
        max_work: BVBLAST_MAX_REPLAY_WORK,
    }
}

fn ensure_certificate_size(actual: usize) -> Result<(), BvBlastPayloadError> {
    if actual <= BVBLAST_MAX_CERTIFICATE_BYTES {
        Ok(())
    } else {
        Err(BvBlastPayloadError::Oversized {
            limit: BVBLAST_MAX_CERTIFICATE_BYTES,
            actual,
        })
    }
}

/// How many leading characters of a goal digest a refusal message shows.
const DIGEST_PREFIX_CHARS: usize = 16;

/// The leading [`DIGEST_PREFIX_CHARS`] characters of a goal digest, for a
/// refusal message.
///
/// Total by construction: `str::get` never panics, so a digest that is shorter
/// than the prefix or whose cut would split a UTF-8 character (possible only
/// for an untrusted spelling — every canonical digest is 64 ASCII hex digits,
/// [`is_bvgoal_digest_hex`]) renders as a fixed marker instead of aborting the
/// validator. No bytes of such a spelling are echoed.
fn digest_prefix(digest: &str) -> &str {
    digest
        .get(..DIGEST_PREFIX_CHARS)
        .unwrap_or("<non-canonical digest>")
}

fn replay_stored_proof(proof: &BvBlastProof) -> Result<(), String> {
    proof
        .validate_with_limits(&replay_limits())
        .map_err(|error| format!("stored refutation does not replay: {error:?}"))
}

fn classify_replay(error: BvBlastValidateError) -> ProveError {
    match error {
        BvBlastValidateError::ResourceLimit {
            resource,
            limit,
            actual,
        } => ProveError::Incomplete(format!(
            "proof replay resource `{resource}` exceeded limit {limit} (actual {actual})"
        )),
        BvBlastValidateError::DeadlineExceeded => {
            ProveError::Incomplete("proof replay deadline expired".to_string())
        }
        other => ProveError::ValidationFailed(format!("{other:?}")),
    }
}

/// Obligation kinds this route may back: exactly
/// [`trust_ir::proof::ASSERT_CLASS_OBLIGATION_KINDS`], the one constant the
/// SMT sited VC and [`trust_ir::proof::derive_site_goal`] read too (WS5.4
/// (1a)), so no route can back a kind another refuses.
///
/// Deliberately narrow, and the narrowness is the point. A bit-vector proof that
/// the sited `CondBr` condition always holds establishes a panic-freedom fact:
/// the check the frontend emitted cannot fail, so the panic arm is unreachable.
/// That reading is sound for `BoundsCheck` (index-in-bounds) and
/// `ArithmeticSafety` (overflow / shift range / divisor nonzero).
///
/// `MemorySafety` is EXCLUDED even though its conditions encode perfectly well
/// (`ptrtoint p & 7 == 0` is three nodes of `And`/`Eq`). Alignment and
/// non-nullness are PROVENANCE facts — that the pointer came from an 8-aligned
/// allocation, or from a `&x` that cannot be null. With the pointer bound as an
/// unconstrained symbol, `p & 7 == 0` is falsified by `p = 1`, so the honest
/// yield is zero anyway; and `MemorySafety` routes to borrow-check semantics
/// that a bit-vector condition does not generally imply. Admitting the kind to
/// raise a headline number is exactly the failure this gate exists to prevent.
///
/// `PanicFreedom` is excluded for a different reason: it is a whole-function
/// claim, and one site's condition does not establish it.
pub const BVBLAST_ALLOWED_KINDS: [ObligationKind; 2] = ASSERT_CLASS_OBLIGATION_KINDS;

fn kind_is_allowed(kind: &ObligationKind) -> bool {
    is_assert_class_kind(kind)
}

// ─────────────────────────────── the lowering ───────────────────────────────

/// Total, structure-preserving map from the validator-owned [`BvTerm`] to ay's
/// `BvExpr`.
///
/// Deliberately 1:1 with NO normalization, constant folding, or rewriting. A
/// rewriter here would be trusted code sitting between the goal the digest
/// commits to and the formula the solver actually refutes — precisely the gap
/// this module exists to close. `BvTerm` has no `Mul` variant, so the one known
/// proof-explosion node remains unreachable by construction in addition to the
/// producer's hard resource limits.
pub fn to_bv_expr(term: &BvTerm) -> BvExpr {
    match term {
        BvTerm::Leaf { name, width } => BvExpr::Leaf {
            name: name.clone(),
            width: *width,
        },
        BvTerm::Const { value, width } => BvExpr::Const {
            value: *value,
            width: *width,
        },
        BvTerm::Add(a, b) => BvExpr::Add(Box::new(to_bv_expr(a)), Box::new(to_bv_expr(b))),
        BvTerm::Sub(a, b) => BvExpr::Sub(Box::new(to_bv_expr(a)), Box::new(to_bv_expr(b))),
        BvTerm::And(a, b) => BvExpr::And(Box::new(to_bv_expr(a)), Box::new(to_bv_expr(b))),
        BvTerm::Or(a, b) => BvExpr::Or(Box::new(to_bv_expr(a)), Box::new(to_bv_expr(b))),
        BvTerm::Xor(a, b) => BvExpr::Xor(Box::new(to_bv_expr(a)), Box::new(to_bv_expr(b))),
        BvTerm::Shl(a, b) => BvExpr::Shl(Box::new(to_bv_expr(a)), Box::new(to_bv_expr(b))),
        BvTerm::Lshr(a, b) => BvExpr::Lshr(Box::new(to_bv_expr(a)), Box::new(to_bv_expr(b))),
        BvTerm::Ashr(a, b) => BvExpr::Ashr(Box::new(to_bv_expr(a)), Box::new(to_bv_expr(b))),
        BvTerm::Not(inner) => BvExpr::Not(Box::new(to_bv_expr(inner))),
        BvTerm::ZeroExt(inner, added) => BvExpr::ZeroExt(Box::new(to_bv_expr(inner)), *added),
        BvTerm::SignExt(inner, added) => BvExpr::SignExt(Box::new(to_bv_expr(inner)), *added),
        BvTerm::Extract { inner, high, low } => BvExpr::Extract {
            inner: Box::new(to_bv_expr(inner)),
            high: *high,
            low: *low,
        },
        BvTerm::Eq(a, b) => BvExpr::Eq(Box::new(to_bv_expr(a)), Box::new(to_bv_expr(b))),
        BvTerm::CarryOut { lhs, rhs, is_sub } => BvExpr::CarryOut {
            lhs: Box::new(to_bv_expr(lhs)),
            rhs: Box::new(to_bv_expr(rhs)),
            is_sub: *is_sub,
        },
    }
}

/// Why a goal produced no proof.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ProveError {
    /// The goal is not structurally well-formed (checked before the blaster
    /// sees it, so a malformed goal never reaches ay).
    Shape(String),
    /// The goal has no free variable. Refused before proving: a refutation of a
    /// literal's negation is structurally genuine and says nothing about any
    /// execution.
    GroundGoal,
    /// **The obligation is FALSE.** `not(lhs == rhs)` has a model, so no
    /// refutation exists. This is the anti-vacuity guarantee, and it comes from
    /// the solver, not from a structural shortcut.
    NoRefutation,
    /// The goal is outside the exporter's supported shape (width mismatch,
    /// malformed expression, unsupported compared width).
    OutOfScope(String),
    /// **Incompleteness, NOT falsity.** The solver returned unknown, or the
    /// refutation could not be lifted to pure resolution. Must never be read as
    /// "the obligation does not hold".
    Incomplete(String),
    /// The exporter produced a proof that does not pass its own re-check. A
    /// proof that does not validate is not evidence and is never attached.
    ValidationFailed(String),
}

impl core::fmt::Display for ProveError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Self::Shape(detail) => write!(f, "goal is not well-formed: {detail}"),
            Self::GroundGoal => write!(
                f,
                "goal mentions no free variable; a refutation of its negation says nothing about \
                 any execution (anti-vacuity)"
            ),
            Self::NoRefutation => write!(
                f,
                "no refutation: the goal is SATISFIABLE, i.e. the claimed condition does not \
                 hold for every valuation of its free inputs. For a sited goal — block-local \
                 and hypothesis-free — that means it is not provable locally, NOT that the \
                 program is wrong: no Failed is ever minted from it"
            ),
            Self::OutOfScope(detail) => {
                write!(f, "goal is outside the bit-blast fragment: {detail}")
            }
            Self::Incomplete(detail) => write!(
                f,
                "the prover did not decide this goal ({detail}); this is INCOMPLETENESS, not a \
                 claim that the obligation is false"
            ),
            Self::ValidationFailed(detail) => write!(
                f,
                "the exported proof failed its own re-check ({detail}); it is not evidence"
            ),
        }
    }
}

impl std::error::Error for ProveError {}

fn classify(err: BvExprExportError) -> ProveError {
    match err {
        // The ONLY variant that means "the obligation is false".
        BvExprExportError::NoRefutation => ProveError::NoRefutation,
        BvExprExportError::WidthMismatch { lhs, rhs } => {
            ProveError::OutOfScope(format!("width mismatch: lhs {lhs} bits, rhs {rhs} bits"))
        }
        BvExprExportError::Malformed(detail) => ProveError::OutOfScope(detail),
        BvExprExportError::UnsupportedWidth { got, max } => {
            ProveError::OutOfScope(format!("compared width {got} exceeds the supported {max}"))
        }
        // Incompleteness. Deliberately a DIFFERENT variant from `NoRefutation`:
        // conflating them would let "the solver gave up" be reported as "the
        // program is wrong".
        BvExprExportError::SolverUnknown => {
            ProveError::Incomplete("solver returned unknown".into())
        }
        // ay 82111544f (0.27.0): the caller's cancellation hook refused further
        // work before a verdict. Nothing about the goal was decided, so this is
        // incompleteness — never falsity, never malformed evidence.
        BvExprExportError::Cancelled => ProveError::Incomplete("proof production cancelled".into()),
        BvExprExportError::RefutationNotSurfaceable(detail) => ProveError::Incomplete(detail),
        BvExprExportError::ResourceLimit {
            resource,
            limit,
            actual,
        } => ProveError::Incomplete(format!(
            "proof resource `{resource}` exceeded limit {limit} (actual {actual})"
        )),
    }
}

/// Prove a goal and IMMEDIATELY re-check the result.
///
/// The two steps are inseparable on purpose: a `BvBlastProof` that does not pass
/// finite `validate_with_limits()` replay is not evidence, so there is no API
/// here that returns an unvalidated proof.
///
/// # Errors
///
/// [`ProveError`]. Note carefully that [`ProveError::NoRefutation`] (the
/// obligation is false) and [`ProveError::Incomplete`] (the prover gave up) are
/// distinct variants and must stay distinct.
///
/// Each call gets a fresh 30-second producer deadline and may surface at most
/// 250,000 resolution steps. Expression, CNF, SAT/LRAT materialization, and
/// replay also remain under AY's conservative finite preset. Exhausting any
/// bound returns [`ProveError::Incomplete`], never [`ProveError::NoRefutation`].
pub fn prove(goal: &BvGoal) -> Result<BvBlastProof, ProveError> {
    let budget = proof_budget()?;
    prove_with_budget(goal, &budget)
}

fn prove_with_budget(
    goal: &BvGoal,
    budget: &BvExprProofBudget,
) -> Result<BvBlastProof, ProveError> {
    goal.validate_shape()
        .map_err(|e| ProveError::Shape(e.to_string()))?;
    if goal.is_ground() {
        return Err(ProveError::GroundGoal);
    }
    let lhs = to_bv_expr(&goal.lhs);
    let rhs = to_bv_expr(&goal.rhs);
    let proof =
        ay_proof::export_bv_blast_proof_expr_bounded(&lhs, &rhs, budget).map_err(classify)?;
    proof
        .validate_with_limits(&replay_limits())
        .map_err(classify_replay)?;
    Ok(proof)
}

// ────────────────────────────── the certificate ──────────────────────────────

/// The certificate payload stored in [`ProofEvidence::SmtProof`].
///
/// Carried as opaque bytes in an existing evidence variant rather than as a new
/// `ProofEvidence` arm: a new variant would be a binary-format break plus
/// conformance-fixture regeneration across four formats, and it would buy
/// nothing — authority never comes from the variant tag, it comes from replay.
///
/// `goal_digest` is stored so the artifact is self-describing to an auditor. It
/// is NOT the binding: the capability re-derives the goal from the IR and
/// compares, so a payload that lies about its own digest is rejected rather than
/// believed. [`Self::from_bytes`] refuses a `goal_digest` that is not spelled as
/// a goal digest at all ([`BvBlastPayloadError::MalformedGoalDigest`]), so an
/// untrusted spelling never reaches the comparison.
#[derive(Debug, Clone, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct BvBlastCertPayload {
    /// Always [`BVBLAST_CERT_SCHEMA`].
    pub schema: String,
    /// The ay revision whose blaster produced `proof`.
    pub ay_rev: String,
    /// Hex digest of the goal this proof is claimed to be about.
    pub goal_digest: String,
    /// The refutation itself.
    pub proof: BvBlastProof,
}

impl BvBlastCertPayload {
    /// Build a payload for a proved goal.
    pub fn new(goal: &BvGoal, proof: BvBlastProof) -> Self {
        Self {
            schema: BVBLAST_CERT_SCHEMA.to_string(),
            ay_rev: AY_REV.to_string(),
            goal_digest: bvgoal_digest_hex(goal),
            proof,
        }
    }

    /// Serialize to the bytes carried by [`ProofEvidence::SmtProof`].
    pub fn to_bytes(&self) -> Result<Vec<u8>, String> {
        let bytes = serde_json::to_vec(self).map_err(|e| e.to_string())?;
        ensure_certificate_size(bytes.len()).map_err(|e| e.to_string())?;
        Ok(bytes)
    }

    /// Strictly decode, rejecting an oversized payload before JSON allocation,
    /// a wrong schema, a foreign ay revision, or a `goal_digest` that is not
    /// spelled as a goal digest.
    ///
    /// # Errors
    ///
    /// [`BvBlastPayloadError`], naming which check refused.
    pub fn from_bytes(bytes: &[u8]) -> Result<Self, BvBlastPayloadError> {
        ensure_certificate_size(bytes.len())?;
        let payload: Self = serde_json::from_slice(bytes)
            .map_err(|e| BvBlastPayloadError::Undecodable(e.to_string()))?;
        if payload.schema != BVBLAST_CERT_SCHEMA {
            return Err(BvBlastPayloadError::WrongSchema(payload.schema));
        }
        if payload.ay_rev != AY_REV {
            return Err(BvBlastPayloadError::ForeignAyRev(payload.ay_rev));
        }
        if !is_bvgoal_digest_hex(&payload.goal_digest) {
            return Err(BvBlastPayloadError::MalformedGoalDigest {
                bytes: payload.goal_digest.len(),
            });
        }
        Ok(payload)
    }
}

/// Why [`BvBlastCertPayload::from_bytes`] refused a certificate payload.
///
/// Every variant is a refusal of UNTRUSTED bytes before any of their content is
/// used; none is a verdict about the goal.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum BvBlastPayloadError {
    /// The serialized payload exceeds the byte ceiling (checked before JSON
    /// decoding, so an oversized string never allocates).
    Oversized { limit: usize, actual: usize },
    /// The bytes are not a JSON payload of this shape.
    Undecodable(String),
    /// `schema` is not [`BVBLAST_CERT_SCHEMA`].
    WrongSchema(String),
    /// The payload was produced at a different ay revision.
    ForeignAyRev(String),
    /// `goal_digest` is not 64 lowercase hex digits
    /// ([`is_bvgoal_digest_hex`]). Its content is deliberately not carried: an
    /// untrusted spelling is never echoed, only its byte length.
    MalformedGoalDigest { bytes: usize },
}

impl core::fmt::Display for BvBlastPayloadError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Self::Oversized { limit, actual } => write!(
                f,
                "certificate payload exceeds byte limit {limit} (actual {actual})"
            ),
            Self::Undecodable(detail) => write!(f, "payload does not decode: {detail}"),
            Self::WrongSchema(schema) => write!(
                f,
                "payload schema is {schema:?}, expected {BVBLAST_CERT_SCHEMA:?}"
            ),
            Self::ForeignAyRev(rev) => write!(
                f,
                "payload was produced at ay rev {rev}, but this build is pinned to {AY_REV}; the \
                 blaster's gate topology and var numbering are implementation details, so a \
                 cross-rev payload cannot be bound to a re-derived CNF"
            ),
            Self::MalformedGoalDigest { bytes } => write!(
                f,
                "payload goal_digest is not a goal digest ({bytes} bytes; a goal digest is \
                 exactly 64 lowercase hex digits)"
            ),
        }
    }
}

impl std::error::Error for BvBlastPayloadError {}

/// Everything needed to attach evidence for one obligation.
#[derive(Debug, Clone)]
pub struct BvBlastCertificate {
    /// The re-derived goal (for the obligation's `formula`).
    pub goal: BvGoal,
    /// The certificate to push onto `Module::proof_certificates`.
    pub certificate: ProofCertificate,
}

/// Derive the goal for a sited obligation, prove it, validate the proof, and
/// build the certificate — the producer half of the route.
///
/// Returns `Ok(None)` when the obligation is out of scope for this route (wrong
/// kind, or already carrying a recorded verdict); `Err` when it is in scope but
/// no evidence could be produced.
///
/// # Errors
///
/// [`BvBlastAttachError`] naming exactly which stage refused.
pub fn certify_obligation(
    module: &Module,
    obligation: &ProofObligation,
) -> Result<Option<BvBlastCertificate>, BvBlastAttachError> {
    if !kind_is_allowed(&obligation.kind) {
        return Ok(None);
    }
    if obligation.status != ProofStatus::Pending {
        return Ok(None);
    }
    let goal = derive_site_goal(module, obligation).map_err(BvBlastAttachError::Derive)?;
    let proof = prove(&goal).map_err(BvBlastAttachError::Prove)?;
    let payload = BvBlastCertPayload::new(&goal, proof);
    let bytes = payload.to_bytes().map_err(BvBlastAttachError::Encode)?;
    Ok(Some(BvBlastCertificate {
        goal,
        certificate: ProofCertificate {
            obligation: obligation.id,
            prover: BVBLAST_PROVER.to_string(),
            evidence: ProofEvidence::SmtProof(bytes),
            // v41: this adapter records no coverage bound of its own; the
            // projection is the bundle writer's job, and `None` reads as
            // UNKNOWN coverage rather than `Unbounded`.
            assurance: None,
        },
    }))
}

/// Why an in-scope obligation produced no certificate.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum BvBlastAttachError {
    /// The goal could not be re-derived from the IR.
    Derive(GoalDeriveError),
    /// The goal was derived but not proved.
    Prove(ProveError),
    /// The certificate payload could not be serialized.
    Encode(String),
}

impl core::fmt::Display for BvBlastAttachError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Self::Derive(e) => write!(f, "{e}"),
            Self::Prove(e) => write!(f, "{e}"),
            Self::Encode(e) => write!(f, "certificate payload does not serialize: {e}"),
        }
    }
}

impl std::error::Error for BvBlastAttachError {}

/// Attach bit-blast evidence to every eligible obligation in `module`, flipping
/// each proved row `Pending` -> `Discharged`.
///
/// A formula-less row gets the bit-blast goal claim stamped as its formula. A
/// row that already carries a formula keeps it unchanged, and is discharged
/// only when that formula states the goal re-derived at its site
/// ([`trust_ir::proof::formula_binds_site_goal`]); otherwise it stays `Pending`
/// with the outcome detail "producer formula disagrees with the site goal"
/// (WS5.4 (1b)).
///
/// The status flip is only meaningful together with [`BvBlastAuthority`]: a
/// `Discharged` row with no capability supplied to the validator is INVALID
/// (`DischargedWithoutCertificate`), so this function cannot smuggle a status
/// past a consumer that does not run the replay.
///
/// Returns one report line per in-scope obligation.
pub fn attach_bvblast_evidence(module: &mut Module) -> Vec<BvBlastAttachOutcome> {
    let mut outcomes = Vec::new();
    let candidates: Vec<ProofObligation> = module
        .proof_obligations
        .iter()
        .filter(|o| kind_is_allowed(&o.kind) && o.status == ProofStatus::Pending)
        .cloned()
        .collect();

    for obligation in candidates {
        // WS5.4 (1b): a row that ALREADY carries a formula is discharged only
        // when that formula states the goal re-derived at its site. The check
        // runs before any solver work, and the formula is never replaced: a
        // producer formula that disagrees with the site IS the disagreement a
        // verifier must see, so it stays on the row, byte for byte, and the row
        // stays Pending.
        if obligation.formula.is_some() {
            match derive_site_goal(module, &obligation) {
                Ok(goal) if formula_binds_site_goal(&obligation, &goal) => {}
                Ok(_) => {
                    outcomes.push(BvBlastAttachOutcome {
                        obligation: obligation.id.index(),
                        discharged: false,
                        detail: format!(
                            "{PRODUCER_FORMULA_DISAGREES}: the row's formula does not state the \
                             bit-vector goal re-derived at its site; it is left unchanged and \
                             the row stays Pending"
                        ),
                    });
                    continue;
                }
                Err(err) => {
                    outcomes.push(BvBlastAttachOutcome {
                        obligation: obligation.id.index(),
                        discharged: false,
                        detail: err.to_string(),
                    });
                    continue;
                }
            }
        }
        match certify_obligation(module, &obligation) {
            Ok(None) => {}
            Ok(Some(minted)) => {
                let formula = match &obligation.formula {
                    // Admitted above: the producer's own statement stays.
                    Some(existing) => Some(existing.clone()),
                    None => trust_ir::proof::bvblast_goal_formula(
                        obligation
                            .site
                            .as_ref()
                            .expect("derive_site_goal succeeded, so the site is present"),
                        &obligation.kind,
                        &minted.goal,
                    ),
                };
                let Some(formula) = formula else {
                    // Unreachable for an allowed kind, but a silent `None` here
                    // would leave a Discharged row with no binding claim.
                    outcomes.push(BvBlastAttachOutcome {
                        obligation: obligation.id.index(),
                        discharged: false,
                        detail: "kind has no goal-formula spelling".to_string(),
                    });
                    continue;
                };
                let bytes = match &minted.certificate.evidence {
                    ProofEvidence::SmtProof(bytes) => bytes.len(),
                    _ => 0,
                };
                if let Some(row) = module
                    .proof_obligations
                    .iter_mut()
                    .find(|o| o.id == obligation.id)
                {
                    row.formula = Some(formula);
                    row.status = ProofStatus::Discharged;
                }
                module.proof_certificates.push(minted.certificate);
                outcomes.push(BvBlastAttachOutcome {
                    obligation: obligation.id.index(),
                    discharged: true,
                    detail: format!(
                        "goal {} proved and validated; {bytes} bytes of evidence",
                        digest_prefix(&bvgoal_digest_hex(&minted.goal))
                    ),
                });
            }
            Err(err) => outcomes.push(BvBlastAttachOutcome {
                obligation: obligation.id.index(),
                discharged: false,
                detail: err.to_string(),
            }),
        }
    }
    outcomes
}

/// One line of [`attach_bvblast_evidence`]'s report.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BvBlastAttachOutcome {
    pub obligation: u32,
    pub discharged: bool,
    pub detail: String,
}

// ─────────────────────────── the authority capability ───────────────────────────

/// The validator capability that turns a stored bit-blast certificate into
/// proof authority.
///
/// # Soundness contract
///
/// Every gate below is ordered, the first failure returns `false`, and there is
/// no path that returns `true` without all of them. The claim is reconstructed
/// from the OBLIGATION and the MODULE — never from the certificate bytes, which
/// are treated as an untrusted artifact throughout.
///
/// 1. the certificate names this obligation;
/// 2. the obligation's status is `Discharged`;
/// 3. its kind is in [`BVBLAST_ALLOWED_KINDS`];
/// 4. the prover string matches [`BVBLAST_PROVER`] exactly (so a pin bump
///    invalidates rather than reinterprets);
/// 5. the evidence is `SmtProof` decoding strictly as a
///    [`BvBlastCertPayload`] at this build's ay revision;
/// 6. the goal RE-DERIVES from the module IR at the obligation's own site;
/// 7. **the binding** — the obligation's `formula` parses in the bv-blast goal
///    schema, its site and kind equal the obligation's own, and its goal digest
///    equals the digest of the re-derived goal; OR (WS5.4 (1b)) the formula is a
///    producer formula whose ONE SMT-LIB text (an `smtlib2` payload; an
///    opaque schema states none) makes
///    [`trust_ir::proof::formula_matches_goal`] hold against the re-derived goal
///    (canonical bit-vector rendering equality, bindings included) — anything
///    else is refused as "producer formula disagrees with the site goal";
/// 8. the payload's self-reported digest also matches (redundant, checked so a
///    stored artifact is self-describing);
/// 9. **the re-derivation** — re-running the blaster on the re-derived goal
///    produces a refutation. This is where a FALSE obligation is caught: the
///    exporter returns `NoRefutation` and authority is denied. Anti-vacuity
///    comes from the solver, never from a structural shortcut;
/// 10. the payload's CNF (`vars`, `bit_lemmas`, `clauses`) is EXACTLY the
///     re-derived CNF — the payload refutes the formula the validator derived,
///     not one it chose;
/// 11. the payload's own finite `validate_with_limits()` replays every
///     resolution step.
///
/// Gate 10 is the source-binding step. AY's replay now rejects malformed gate
/// graphs and disequality clauses, but it deliberately does not authenticate a
/// serialized graph against the caller's live source formula. Without exact
/// equality to the graph re-derived here, a valid proof of a different formula
/// could be relabelled and granted authority for this obligation.
///
/// # Cost
///
/// Gate 9 RE-SOLVES under the same 30-second/250,000-step producer policy.
/// At most one result is cached per authority instance. A distinct goal evicts
/// the previous entry, so attacker-controlled goal diversity cannot accumulate
/// retained CNFs. The capability is opt-in — plain `validate_module` supplies
/// the rejecting default and never runs a solver.
#[derive(Debug, Default)]
pub struct BvBlastAuthority {
    cache: std::sync::Mutex<Option<(String, Option<CachedCnf>)>>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct CachedCnf {
    vars: ay_proof::VarTable,
    bit_lemmas: Vec<ay_proof::BitLemma>,
    clauses: Vec<ay_proof::Clause>,
}

impl BvBlastAuthority {
    pub fn new() -> Self {
        Self::default()
    }

    /// Re-derive the CNF for `goal`, retaining only the most recent digest.
    fn rederive_cnf(&self, goal: &BvGoal, digest_hex: &str) -> Option<CachedCnf> {
        if let Ok(cache) = self.cache.lock()
            && let Some((cached_digest, hit)) = cache.as_ref()
            && cached_digest == digest_hex
        {
            return hit.clone();
        }
        let fresh = prove(goal).ok().map(|proof| CachedCnf {
            vars: proof.vars,
            bit_lemmas: proof.bit_lemmas,
            clauses: proof.clauses,
        });
        if let Ok(mut cache) = self.cache.lock() {
            *cache = Some((digest_hex.to_string(), fresh.clone()));
        }
        fresh
    }

    #[cfg(test)]
    fn cached_digest(&self) -> Option<String> {
        self.cache
            .lock()
            .ok()
            .and_then(|cache| cache.as_ref().map(|(digest, _)| digest.clone()))
    }

    /// The full gate chain, exposed so tests can assert WHICH gate rejected.
    pub fn explain(
        &self,
        module: &Module,
        obligation: &ProofObligation,
        certificate: &ProofCertificate,
    ) -> Result<(), String> {
        // (1) the certificate names this obligation.
        if certificate.obligation != obligation.id {
            return Err("certificate names a different obligation".to_string());
        }
        // (2) only a Discharged row is being authorized here.
        if obligation.status != ProofStatus::Discharged {
            return Err(format!(
                "obligation status is {:?}, not Discharged",
                obligation.status
            ));
        }
        // (3) the kind allowlist.
        if !kind_is_allowed(&obligation.kind) {
            return Err(format!(
                "obligation kind {:?} is outside the bv-blast allowlist {:?}",
                obligation.kind, BVBLAST_ALLOWED_KINDS
            ));
        }
        // (4) exact prover identity, including the ay rev.
        if certificate.prover != BVBLAST_PROVER {
            return Err(format!(
                "certificate prover is {:?}, expected {BVBLAST_PROVER:?}",
                certificate.prover
            ));
        }
        // (5) strict payload decode at this build's ay rev.
        let ProofEvidence::SmtProof(bytes) = &certificate.evidence else {
            return Err("certificate evidence is not SmtProof".to_string());
        };
        let payload = BvBlastCertPayload::from_bytes(bytes).map_err(|e| e.to_string())?;

        // (6) the goal RE-DERIVES from the IR. Nothing from the payload is used.
        let goal = derive_site_goal(module, obligation).map_err(|e| e.to_string())?;
        let digest_hex = bvgoal_digest_hex(&goal);

        // (7) THE BINDING. The obligation's own claim must name this goal.
        let site = obligation
            .site
            .as_ref()
            .ok_or("obligation has no site (unreachable: derive_site_goal succeeded)")?;
        let formula = obligation
            .formula
            .as_ref()
            .ok_or("obligation carries no formula, so it states no goal to bind against")?;
        // (7') WS5.4 (1b): a PRODUCER formula (any schema other than the
        //      bit-blast claim) binds only when its one SMT-LIB text is the
        //      canonical bit-vector rendering of the re-derived goal, bindings
        //      included. The claim schema keeps the site/kind/digest gates below.
        if formula.schema != BVBLAST_GOAL_SCHEMA {
            if !formula_matches_goal(formula, &goal) {
                return Err(format!(
                    "{PRODUCER_FORMULA_DISAGREES}: the obligation's formula does not state the \
                     goal re-derived from its site"
                ));
            }
            return self.replay_and_bind(&goal, &digest_hex, &payload);
        }
        let ((f, b, i), kind_tag, claimed_digest) = bvblast_goal_formula_parts(formula)
            .ok_or("obligation formula is not a well-formed bv-blast goal claim")?;
        if (f, b, i) != (site.function.index(), site.block.index(), site.inst_index) {
            return Err(
                "obligation formula names a different site than the obligation".to_string(),
            );
        }
        let expected_kind = match obligation.kind {
            ObligationKind::BoundsCheck => "BoundsCheck",
            ObligationKind::ArithmeticSafety => "ArithmeticSafety",
            _ => return Err("kind has no goal-formula spelling".to_string()),
        };
        if kind_tag != expected_kind {
            return Err("obligation formula names a different kind".to_string());
        }
        if claimed_digest != digest_hex {
            return Err(format!(
                "BINDING FAILURE: the obligation claims goal {}…, but the goal re-derived from \
                 its site is {}…; this certificate is about a different fact",
                digest_prefix(claimed_digest),
                digest_prefix(&digest_hex)
            ));
        }
        self.replay_and_bind(&goal, &digest_hex, &payload)
    }

    /// Gates (8)-(11): the payload's self-report, the stored replay, the
    /// re-derivation, and exact CNF equality. Shared by both formula spellings.
    fn replay_and_bind(
        &self,
        goal: &BvGoal,
        digest_hex: &str,
        payload: &BvBlastCertPayload,
    ) -> Result<(), String> {
        // (8) the payload's self-report agrees too.
        if payload.goal_digest != digest_hex {
            return Err(format!(
                "payload claims goal {}…, but the re-derived goal is {}…",
                digest_prefix(&payload.goal_digest),
                digest_prefix(digest_hex)
            ));
        }

        // (9a) REPLAY THE STORED REFUTATION FIRST. This gate is self-contained
        //      — it needs nothing from the re-derivation — and it is cheap,
        //      whereas (9b) re-solves from scratch under the same finite
        //      producer policy. Running the
        //      expensive step first meant an attacker needed no valid proof at
        //      all: an honestly-computable formula digest plus any decodable
        //      payload was enough to burn unbounded validator time (measured:
        //      68 goal nodes at width 128 did not finish in 400 s). Now a
        //      caller must at minimum supply an internally-consistent
        //      refutation before we will spend a solve on their goal.
        //
        //      This is ordering for cost only. It is NOT the binding — a
        //      self-consistent refutation of some unrelated CNF passes here and
        //      is caught by (10).
        replay_stored_proof(&payload.proof)?;

        // (9b) RE-DERIVE the CNF by re-running the blaster on the re-derived
        //      goal. A FALSE obligation dies here with `NoRefutation`.
        let fresh = self
            .rederive_cnf(goal, digest_hex)
            .ok_or("re-deriving a refutation for this goal failed (unprovable, out of scope, or undecided)")?;

        // (10) the payload must refute EXACTLY the re-derived CNF.
        if fresh.vars != payload.proof.vars {
            return Err("payload's variable table is not the re-derived one".to_string());
        }
        if fresh.bit_lemmas != payload.proof.bit_lemmas {
            return Err("payload's gate lemmas are not the re-derived ones".to_string());
        }
        if fresh.clauses != payload.proof.clauses {
            return Err(
                "payload's clause set is not the re-derived one; it refutes some other formula"
                    .to_string(),
            );
        }

        // (11) the stored refutation already replayed at (9a), and (10) has now
        //      pinned that what it refutes is EXACTLY the re-derived CNF.
        //      Together those are the original gate 11's guarantee, with the
        //      cheap half moved ahead of the expensive solve.
        Ok(())
    }
}

impl trust_ir::proof::ModuleProofAuthority for BvBlastAuthority {
    fn replays_authority(
        &self,
        module: &Module,
        obligation: &ProofObligation,
        certificate: &ProofCertificate,
    ) -> bool {
        self.explain(module, obligation, certificate).is_ok()
    }
}

#[cfg(test)]
mod classify_tests {
    use std::time::Duration;

    use ay_proof::BvExprProofBudget;
    use trust_ir::proof::{BvGoal, BvTerm};

    use super::{
        BVBLAST_MAX_CERTIFICATE_BYTES, BVBLAST_MAX_REPLAY_VARS, BvBlastAuthority,
        BvBlastCertPayload, BvBlastPayloadError, BvBlastValidateError, BvExprExportError,
        ProveError, bvgoal_digest_hex, classify, classify_replay, digest_prefix,
        ensure_certificate_size, prove, prove_with_budget, replay_stored_proof,
    };

    fn shift_identity_goal() -> BvGoal {
        let value = BvTerm::leaf("value", 4);
        let amount = BvTerm::leaf("amount", 4);
        let shift = BvTerm::Shl(Box::new(value), Box::new(amount));
        BvGoal {
            lhs: BvTerm::Or(
                Box::new(BvTerm::Const { value: 0, width: 4 }),
                Box::new(shift.clone()),
            ),
            rhs: shift,
        }
    }

    #[test]
    fn proof_resource_exhaustion_is_incomplete_not_falsity() {
        let classified = classify(BvExprExportError::ResourceLimit {
            resource: "resolution-steps",
            limit: 10,
            actual: 11,
        });
        assert!(matches!(
            classified,
            ProveError::Incomplete(detail)
                if detail == "proof resource `resolution-steps` exceeded limit 10 (actual 11)"
        ));
    }

    #[test]
    fn cancelled_proof_production_is_incomplete_not_falsity() {
        // ay 0.27.0 added `BvExprExportError::Cancelled` ("the caller refused
        // further work; this is not a satisfiability verdict"). It must land on
        // the incompleteness side of the NoRefutation/Incomplete line.
        assert_eq!(
            classify(BvExprExportError::Cancelled),
            ProveError::Incomplete("proof production cancelled".to_string())
        );
    }

    #[test]
    fn real_bounded_export_exhaustion_is_incomplete_not_falsity() {
        // This is the exact public bounded-export path with an intentionally
        // tiny cap, not a fabricated error value. `0 | (x << k) == x << k` is
        // valid but needs more than one surfaced resolution step.
        let goal = shift_identity_goal();
        let budget = BvExprProofBudget::conservative(Duration::from_secs(2), 1)
            .expect("one step is a valid, deliberately insufficient budget");
        let error = prove_with_budget(&goal, &budget).unwrap_err();
        assert!(
            matches!(error, ProveError::Incomplete(detail)
                if detail.contains("proof resource") && detail.contains("limit 1")),
            "resource exhaustion must remain typed as incompleteness"
        );
    }

    #[test]
    fn replay_resource_exhaustion_is_incomplete_not_malformed_evidence() {
        let error = classify_replay(BvBlastValidateError::ResourceLimit {
            resource: "replay work",
            limit: 10,
            actual: 11,
        });
        assert!(matches!(
            error,
            ProveError::Incomplete(detail)
                if detail == "proof replay resource `replay work` exceeded limit 10 (actual 11)"
        ));
    }

    #[test]
    fn replay_deadline_is_incomplete_not_malformed_evidence() {
        assert_eq!(
            classify_replay(BvBlastValidateError::DeadlineExceeded),
            ProveError::Incomplete("proof replay deadline expired".to_string())
        );
    }

    #[test]
    fn malformed_replay_remains_validation_failure() {
        let error = classify_replay(BvBlastValidateError::UnsupportedFormatVersion {
            got: 0,
            expected: 1,
        });
        assert!(matches!(error, ProveError::ValidationFailed(_)));
    }

    #[test]
    fn authority_cache_retains_only_the_most_recent_distinct_goal() {
        let first = shift_identity_goal();
        let mut second = shift_identity_goal();
        second.lhs = BvTerm::Xor(
            Box::new(BvTerm::leaf("second-value", 4)),
            Box::new(BvTerm::Const { value: 0, width: 4 }),
        );
        second.rhs = BvTerm::leaf("second-value", 4);

        let first_digest = bvgoal_digest_hex(&first);
        let second_digest = bvgoal_digest_hex(&second);
        assert_ne!(
            first_digest, second_digest,
            "the cache keys must be distinct"
        );

        let authority = BvBlastAuthority::new();
        assert!(
            authority.rederive_cnf(&first, &first_digest).is_some(),
            "the first valid goal must really be proved"
        );
        assert_eq!(
            authority.cached_digest().as_deref(),
            Some(first_digest.as_str())
        );

        assert!(
            authority.rederive_cnf(&second, &second_digest).is_some(),
            "the second valid goal must really be proved"
        );
        assert_eq!(
            authority.cached_digest().as_deref(),
            Some(second_digest.as_str()),
            "a distinct goal must evict rather than accumulate beside the first"
        );

        assert!(
            authority.rederive_cnf(&first, &first_digest).is_some(),
            "the evicted goal must remain reproducible"
        );
        assert_eq!(
            authority.cached_digest().as_deref(),
            Some(first_digest.as_str())
        );
    }

    #[test]
    fn serialized_payload_size_is_checked_without_allocating_the_boundary() {
        assert_eq!(
            ensure_certificate_size(BVBLAST_MAX_CERTIFICATE_BYTES),
            Ok(())
        );
        let error = ensure_certificate_size(BVBLAST_MAX_CERTIFICATE_BYTES + 1)
            .expect_err("one byte over the policy must fail before JSON decoding");
        assert_eq!(
            error,
            BvBlastPayloadError::Oversized {
                limit: BVBLAST_MAX_CERTIFICATE_BYTES,
                actual: BVBLAST_MAX_CERTIFICATE_BYTES + 1,
            }
        );
        let message = error.to_string();
        assert!(
            message.contains("certificate payload exceeds byte limit")
                && message.contains(&(BVBLAST_MAX_CERTIFICATE_BYTES + 1).to_string()),
            "unexpected size rejection: {message}"
        );
    }

    /// A goal digest spelled with multi-byte characters, 64 BYTES long, whose
    /// byte 16 falls inside a character (21 three-byte euro signs, then `0`).
    fn non_ascii_digest() -> String {
        let digest = format!("{}0", "\u{20ac}".repeat(21));
        assert_eq!(digest.len(), 64);
        assert!(
            !digest.is_char_boundary(16),
            "the cut must split a character"
        );
        digest
    }

    #[test]
    fn digest_prefix_is_total_on_any_spelling() {
        let canonical = bvgoal_digest_hex(&shift_identity_goal());
        assert_eq!(digest_prefix(&canonical), &canonical[..16]);
        assert_eq!(digest_prefix("abc"), "<non-canonical digest>");
        assert_eq!(digest_prefix(&non_ascii_digest()), "<non-canonical digest>");
    }

    #[test]
    fn a_non_hex_goal_digest_is_refused_at_decode_by_name() {
        // The certificate bytes are untrusted: `goal_digest` arrives through
        // serde from whatever a producer wrote. A spelling other than the one
        // `bvgoal_digest_hex` emits is refused before anything reads it.
        let goal = shift_identity_goal();
        let proof = prove(&goal).expect("small control goal proves");
        for (spelling, label) in [
            (non_ascii_digest(), "non-ASCII"),
            (bvgoal_digest_hex(&goal).to_uppercase(), "uppercase hex"),
            ("00".to_string(), "short"),
        ] {
            let mut payload = BvBlastCertPayload::new(&goal, proof.clone());
            payload.goal_digest = spelling.clone();
            let bytes = payload
                .to_bytes()
                .expect("the encoder does not police content");
            assert_eq!(
                BvBlastCertPayload::from_bytes(&bytes),
                Err(BvBlastPayloadError::MalformedGoalDigest {
                    bytes: spelling.len()
                }),
                "{label} goal_digest must be refused at decode"
            );
        }
        // Control: the writer's own spelling decodes.
        let payload = BvBlastCertPayload::new(&goal, proof);
        let bytes = payload.to_bytes().expect("encodes");
        assert_eq!(BvBlastCertPayload::from_bytes(&bytes), Ok(payload));
    }

    #[test]
    fn a_non_canonical_payload_digest_is_an_error_not_a_panic() {
        // Behind the decode check, the comparison gate itself must still be
        // total: a payload built in memory (its fields are public) reaches
        // gate (8) without `from_bytes`. Slicing its digest at byte 16 split
        // a character and aborted the validator; now it is a refusal.
        let goal = shift_identity_goal();
        let digest_hex = bvgoal_digest_hex(&goal);
        let mut payload =
            BvBlastCertPayload::new(&goal, prove(&goal).expect("small control goal proves"));
        payload.goal_digest = non_ascii_digest();
        let error = BvBlastAuthority::new()
            .replay_and_bind(&goal, &digest_hex, &payload)
            .expect_err("a payload naming another digest is refused");
        assert!(
            error.contains("payload claims goal <non-canonical digest>")
                && error.contains(&digest_hex[..16]),
            "unexpected refusal: {error}"
        );
    }

    #[test]
    fn stored_proof_one_over_the_replay_cap_is_rejected_before_traversal() {
        let goal = shift_identity_goal();
        let mut payload = BvBlastCertPayload::new(
            &goal,
            prove(&goal).expect("small stored-proof control must prove"),
        );
        payload.proof.vars.roles.resize(
            BVBLAST_MAX_REPLAY_VARS + 1,
            ay_proof::VarRole::Aux { bit: 0 },
        );

        // Round-trip the hostile object so this exercises the stored format,
        // while remaining well below the independent 16 MiB byte ceiling.
        let bytes = payload.to_bytes().expect("cap+1 vars fit the byte cap");
        assert!(bytes.len() < BVBLAST_MAX_CERTIFICATE_BYTES);
        let decoded = BvBlastCertPayload::from_bytes(&bytes).expect("stored payload decodes");
        let error = replay_stored_proof(&decoded.proof)
            .expect_err("one variable over the policy must fail before graph traversal");
        assert!(
            error.contains("ResourceLimit")
                && error.contains("variables")
                && error.contains(&BVBLAST_MAX_REPLAY_VARS.to_string()),
            "unexpected oversized-proof rejection: {error}"
        );
    }
}
