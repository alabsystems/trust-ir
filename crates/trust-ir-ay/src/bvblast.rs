// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! The BIT-BLAST proof route: a sited panic-class obligation to a replayable,
//! goal-bound refutation, and the validator capability that grants it authority.
//!
//! # What this route is, and why it is not the solver-bundle route
//!
//! The adapter's other proof path ([`crate::vc`]) drives ay's `Solver` and
//! captures an `ay.proofbundle/v2`. That path is a dead end for real work,
//! measured rather than assumed: a genuinely symbolic goal exports a bundle
//! whose offline replay REJECTS it (`UnsupportedTheoryLemmaKind { kind: Generic
//! }`), while a goal ay's term constructor folds to a literal replays fine and
//! proves `false |- ⊥`. Every certificate that path could mint was of the second
//! shape, and a vacuity gate now refuses them.
//!
//! This route uses `ay_proof::export_bv_blast_proof_expr` instead. Its format is
//! *structurally incapable* of a trust step — `bv_blast_export` states there is
//! no `trust` variant to emit — and the refutation is DERIVED by the ay-sat CDCL
//! engine (`prove_unsat_resolution_dag`), not asserted by the exporter.
//!
//! # The soundness problem this module actually solves
//!
//! `BvBlastProof::validate()` is a real re-check: it re-derives every gate's
//! Tseitin clause set from an exhaustive truth-table walk and replays every
//! resolution step. Tampering is caught — dropping the last step, corrupting a
//! gate kind, and flipping a clause literal were each measured to fail.
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
//! * `ClauseProvenance::Disequality` is unchecked (the match arm is empty), so
//!   arbitrary starting axioms are accepted. A 441-byte object with two
//!   contradictory junk units and one resolution step validates.
//!
//! So `validate() == Ok` means only: *this object is an internally-consistent
//! resolution refutation of the CNF it itself carries*. Granting proof authority
//! on that alone would make one 441-byte artifact a universal certificate for
//! every obligation in the module.
//!
//! [`BvBlastAuthority`] closes this by RE-DERIVATION, never by reading the
//! payload's own claims:
//!
//! 1. the goal is re-derived from the module IR by
//!    [`trust_ir::proof::derive_site_goal`] — validator-owned, zero-dep code;
//! 2. the obligation's own `formula` must pin that goal's digest;
//! 3. the CNF is re-derived by re-running the blaster on the re-derived goal;
//! 4. the stored payload's CNF must equal the re-derived one exactly;
//! 5. only then is the payload's refutation replayed by `validate()`.
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
//! wrong gate; and (b) the producer's `condbr assert_cond, <success>, <panic>`
//! convention, which every other shape fails closed on. The falsifiers for (a)
//! are the sharp-boundary matrix and the anti-vacuity tests in
//! `tests/bvblast_authority.rs`; they are tests, not a proof, and are named as a
//! residual rather than glossed. Closing (a) needs trust-ir's own canonical
//! Tseitin blaster replayed through the existing `satres` checker — a separate
//! rung, not promised here.

use ay_proof::{BvBlastProof, BvExpr, BvExprExportError};
use trust_ir::Module;
use trust_ir::proof::{
    BvGoal, BvTerm, GoalDeriveError, ObligationKind, ProofCertificate, ProofEvidence,
    ProofObligation, ProofStatus, bvblast_goal_formula_parts, bvgoal_digest_hex, derive_site_goal,
};

use crate::vc::AY_REV;

/// Identity of this prover, stamped into every certificate.
///
/// Includes the ay revision, so a pin bump invalidates every stored
/// certificate rather than silently re-interpreting it: `ProofCertificateRef`
/// is `(obligation, prover, evidence_digest)`, and the authority capability
/// requires an exact match on this string.
pub const BVBLAST_PROVER: &str = "trust-ir-ay/bvblast@286c85566bcc409a63391f839d8f9fae3b281781";

/// Schema tag of the certificate payload carried inside
/// [`ProofEvidence::SmtProof`].
pub const BVBLAST_CERT_SCHEMA: &str = "trust-ir.bvblast.cert.v1";

/// Obligation kinds this route may back.
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
pub const BVBLAST_ALLOWED_KINDS: [ObligationKind; 2] = [
    ObligationKind::BoundsCheck,
    ObligationKind::ArithmeticSafety,
];

fn kind_is_allowed(kind: &ObligationKind) -> bool {
    BVBLAST_ALLOWED_KINDS.iter().any(|allowed| allowed == kind)
}

// ─────────────────────────────── the lowering ───────────────────────────────

/// Total, structure-preserving map from the validator-owned [`BvTerm`] to ay's
/// `BvExpr`.
///
/// Deliberately 1:1 with NO normalization, constant folding, or rewriting. A
/// rewriter here would be trusted code sitting between the goal the digest
/// commits to and the formula the solver actually refutes — precisely the gap
/// this module exists to close. `BvTerm` has no `Mul` variant, so the
/// unbounded-blast node is unreachable by construction rather than by a check.
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
                "no refutation: the obligation is SATISFIABLE, i.e. the claimed condition does \
                 not hold for every valuation"
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
        BvExprExportError::RefutationNotSurfaceable(detail) => ProveError::Incomplete(detail),
    }
}

/// Prove a goal and IMMEDIATELY re-check the result.
///
/// The two steps are inseparable on purpose: a `BvBlastProof` that does not pass
/// `validate()` is not evidence, so there is no API here that returns an
/// unvalidated proof.
///
/// # Errors
///
/// [`ProveError`]. Note carefully that [`ProveError::NoRefutation`] (the
/// obligation is false) and [`ProveError::Incomplete`] (the prover gave up) are
/// distinct variants and must stay distinct.
pub fn prove(goal: &BvGoal) -> Result<BvBlastProof, ProveError> {
    goal.validate_shape()
        .map_err(|e| ProveError::Shape(e.to_string()))?;
    if goal.is_ground() {
        return Err(ProveError::GroundGoal);
    }
    let lhs = to_bv_expr(&goal.lhs);
    let rhs = to_bv_expr(&goal.rhs);
    let proof = ay_proof::export_bv_blast_proof_expr(&lhs, &rhs).map_err(classify)?;
    proof
        .validate()
        .map_err(|e| ProveError::ValidationFailed(format!("{e:?}")))?;
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
/// believed.
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
        serde_json::to_vec(self).map_err(|e| e.to_string())
    }

    /// Strictly decode, rejecting a wrong schema or a foreign ay revision.
    pub fn from_bytes(bytes: &[u8]) -> Result<Self, String> {
        let payload: Self =
            serde_json::from_slice(bytes).map_err(|e| format!("payload does not decode: {e}"))?;
        if payload.schema != BVBLAST_CERT_SCHEMA {
            return Err(format!(
                "payload schema is {:?}, expected {BVBLAST_CERT_SCHEMA:?}",
                payload.schema
            ));
        }
        if payload.ay_rev != AY_REV {
            return Err(format!(
                "payload was produced at ay rev {}, but this build is pinned to {AY_REV}; the \
                 blaster's gate topology and var numbering are implementation details, so a \
                 cross-rev payload cannot be bound to a re-derived CNF",
                payload.ay_rev
            ));
        }
        Ok(payload)
    }
}

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
        match certify_obligation(module, &obligation) {
            Ok(None) => {}
            Ok(Some(minted)) => {
                let formula = trust_ir::proof::bvblast_goal_formula(
                    obligation
                        .site
                        .as_ref()
                        .expect("derive_site_goal succeeded, so the site is present"),
                    &obligation.kind,
                    &minted.goal,
                );
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
                        &bvgoal_digest_hex(&minted.goal)[..16]
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
///    equals the digest of the re-derived goal;
/// 8. the payload's self-reported digest also matches (redundant, checked so a
///    stored artifact is self-describing);
/// 9. **the re-derivation** — re-running the blaster on the re-derived goal
///    produces a refutation. This is where a FALSE obligation is caught: the
///    exporter returns `NoRefutation` and authority is denied. Anti-vacuity
///    comes from the solver, never from a structural shortcut;
/// 10. the payload's CNF (`vars`, `bit_lemmas`, `clauses`) is EXACTLY the
///     re-derived CNF — the payload refutes the formula the validator derived,
///     not one it chose;
/// 11. the payload's own `validate()` replays every resolution step.
///
/// Gate 10 is the whole design. Without it, `ClauseProvenance::Disequality`
/// being unchecked by `validate()` means arbitrary starting axioms are accepted,
/// and a 441-byte hand-built object validates.
///
/// # Cost
///
/// Gate 9 RE-SOLVES. Results are cached per goal digest within one instance, and
/// the capability is opt-in — plain `validate_module` supplies the rejecting
/// default and never runs a solver.
#[derive(Debug, Default)]
pub struct BvBlastAuthority {
    cache: std::sync::Mutex<std::collections::HashMap<String, Option<CachedCnf>>>,
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

    /// Re-derive the CNF for `goal`, memoized on its digest.
    fn rederive_cnf(&self, goal: &BvGoal, digest_hex: &str) -> Option<CachedCnf> {
        if let Ok(cache) = self.cache.lock()
            && let Some(hit) = cache.get(digest_hex)
        {
            return hit.clone();
        }
        let fresh = prove(goal).ok().map(|proof| CachedCnf {
            vars: proof.vars,
            bit_lemmas: proof.bit_lemmas,
            clauses: proof.clauses,
        });
        if let Ok(mut cache) = self.cache.lock() {
            cache.insert(digest_hex.to_string(), fresh.clone());
        }
        fresh
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
        let payload = BvBlastCertPayload::from_bytes(bytes)?;

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
                &claimed_digest[..16.min(claimed_digest.len())],
                &digest_hex[..16]
            ));
        }
        // (8) the payload's self-report agrees too.
        if payload.goal_digest != digest_hex {
            return Err(format!(
                "payload claims goal {}…, but the re-derived goal is {}…",
                &payload.goal_digest[..16.min(payload.goal_digest.len())],
                &digest_hex[..16]
            ));
        }

        // (9a) REPLAY THE STORED REFUTATION FIRST. This gate is self-contained
        //      — it needs nothing from the re-derivation — and it is cheap,
        //      whereas (9b) re-solves from scratch with no timeout. Running the
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
        payload
            .proof
            .validate()
            .map_err(|e| format!("stored refutation does not replay: {e:?}"))?;

        // (9b) RE-DERIVE the CNF by re-running the blaster on the re-derived
        //      goal. A FALSE obligation dies here with `NoRefutation`.
        let fresh = self
            .rederive_cnf(&goal, &digest_hex)
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
