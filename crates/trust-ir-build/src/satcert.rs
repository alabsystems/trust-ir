// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! UNTRUSTED producer-side plumbing for t-silicon lowering-resolution
//! certificates: DIMACS/TraceCheck parsing, the drat-trim resolution-trace →
//! binary-resolution-`Step` converter, and the certificate assembler.
//!
//! # Position in the chain (and why NOTHING here is trusted)
//!
//! ```text
//! trust-cg: lowering VC ──sat_blast──> CNF ──MicroSAT──> DRAT
//!             ──drat-trim -r──> TraceCheck trace
//! HERE:     (cnf, trace) ──trace_to_steps──> binary resolution Steps
//!             ──build_lowering_resolution_cert──> CleanCic certificate
//! TCB:      trust_ir_build::validate — decodes the payload, rebuilds the
//!             kernel term ITSELF, and clean-kernel's VERIFIED
//!             `Clean.Res.checkRefutes3` (+ proved `checkRefutes3_sound`)
//!             decides by reflection.
//! ```
//!
//! A bug anywhere in this module produces a certificate the kernel REJECTS
//! (`Bool.false`), never one it wrongly accepts — the converter sits outside
//! the trusted base by construction, exactly like the `trust-ir-giveback`
//! elaborator. The [`verify_steps`] replay below is a producer-side
//! *convenience* self-check (fail fast with a good error instead of a kernel
//! rejection later); it is NOT the authority.
//! Even a kernel-accepted payload is only CNF UNSAT assurance: because the
//! validator does not independently derive the exact semantic miter, the
//! assembled obligation remains `Pending` and cannot discharge lowering.
//!
//! # The conversion itself
//!
//! drat-trim's `-r` TraceCheck output lists, per RUP lemma, its clause and the
//! antecedents whose unit propagation refutes it. `Clean.Res.checkRefutes3`
//! consumes BINARY resolution steps over GLOBAL clause ids (originals
//! `0..n-1`, then each derived resolvent at `n, n+1, ...`). [`trace_to_steps`]
//! expands each k-antecedent RUP inference into `k-1` binary resolutions by
//! trivial-resolution replay — reverse propagation order first, greedy
//! fallback — giving intermediate resolvents fresh global ids. Single-
//! antecedent lemmas (duplicates/subsumptions) are aliased, not re-derived.

use std::collections::BTreeSet;

use trust_ir::proof::satprov::MiterProvenance;
use trust_ir::proof::satres::{
    SATRES_CERT_UNSAT_THEOREM, SatLit, SatResolutionCertPayload, SatResolutionStep, satres_formula,
};
use trust_ir::proof::{
    CleanCicKernelRecheck, KERNEL_ANCHOR_TRUSTCG_LOWERING_RESOLUTION, ObligationKind,
    ProofCertificate, ProofEvidence, ProofObligation, ProofStatus, clean_cic_lineage_digest,
};
use trust_ir::value::{FuncId, ProofId};

/// Signed DIMACS literal (1-based variable, sign = polarity). Internal to the
/// converter; the payload boundary uses 0-based [`SatLit`] pairs.
type DimacsLit = i64;
type Clause = BTreeSet<DimacsLit>;

/// Fail-closed converter errors. Every anomaly rejects the whole conversion —
/// the producer fixes its inputs rather than shipping a certificate the
/// kernel would refuse.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SatCertError {
    /// Malformed DIMACS text.
    BadDimacs(String),
    /// Malformed TraceCheck text.
    BadTrace(String),
    /// A trace "original clause" entry disagrees with the CNF.
    TraceCnfMismatch { trace_id: u64 },
    /// A lemma references an antecedent at or after itself.
    NonTopologicalAntecedent { trace_id: u64 },
    /// The RUP chain for a lemma could not be linearized into binary
    /// resolutions (neither replay order works).
    ChainStuck { trace_id: u64 },
    /// The converted chain fails the producer-side replay ([`verify_steps`]).
    ReplayRejected { step_index: usize },
    /// The chain never derives the empty clause.
    NoEmptyClause,
}

impl core::fmt::Display for SatCertError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            SatCertError::BadDimacs(msg) => write!(f, "bad DIMACS input: {msg}"),
            SatCertError::BadTrace(msg) => write!(f, "bad TraceCheck input: {msg}"),
            SatCertError::TraceCnfMismatch { trace_id } => write!(
                f,
                "trace original clause {trace_id} does not match the CNF clause at its index"
            ),
            SatCertError::NonTopologicalAntecedent { trace_id } => {
                write!(
                    f,
                    "trace lemma {trace_id} cites a non-topological antecedent"
                )
            }
            SatCertError::ChainStuck { trace_id } => write!(
                f,
                "could not linearize the RUP chain of trace lemma {trace_id} into binary \
                 resolutions"
            ),
            SatCertError::ReplayRejected { step_index } => {
                write!(f, "producer-side replay rejected step {step_index}")
            }
            SatCertError::NoEmptyClause => {
                write!(f, "converted chain does not derive the empty clause")
            }
        }
    }
}

/// Parse DIMACS CNF text into 0-based [`SatLit`] clauses (in file order —
/// global ids `0..n-1`). Comment (`c`) and header (`p`) lines are skipped;
/// every clause line must be zero-terminated.
pub fn parse_dimacs(text: &str) -> Result<Vec<Vec<SatLit>>, SatCertError> {
    let mut clauses = Vec::new();
    for line in text.lines() {
        let line = line.trim();
        if line.is_empty()
            || line.starts_with('c')
            || line.starts_with('p')
            || line.starts_with('%')
        {
            continue;
        }
        let lits: Vec<i64> = line
            .split_whitespace()
            .map(|t| {
                t.parse::<i64>()
                    .map_err(|_| SatCertError::BadDimacs(format!("non-integer token '{t}'")))
            })
            .collect::<Result<_, _>>()?;
        match lits.split_last() {
            Some((0, body)) => {
                let mut clause = Vec::with_capacity(body.len());
                for &l in body {
                    if l == 0 {
                        return Err(SatCertError::BadDimacs(
                            "interior zero in clause line".to_string(),
                        ));
                    }
                    clause.push(dimacs_to_satlit(l)?);
                }
                clauses.push(clause);
            }
            _ => {
                return Err(SatCertError::BadDimacs(
                    "clause line not zero-terminated".to_string(),
                ));
            }
        }
    }
    Ok(clauses)
}

fn dimacs_to_satlit(l: i64) -> Result<SatLit, SatCertError> {
    let var = l.unsigned_abs();
    if var == 0 || var > u64::from(u32::MAX >> 1) {
        return Err(SatCertError::BadDimacs(format!(
            "variable {var} out of range"
        )));
    }
    Ok(((var - 1) as u32, l < 0))
}

fn satlit_to_dimacs((var, neg): SatLit) -> DimacsLit {
    let v = i64::from(var) + 1;
    if neg { -v } else { v }
}

/// One parsed TraceCheck entry: `<id> <lits> 0 <antecedent ids> 0`.
struct TraceEntry {
    id: u64,
    lits: Clause,
    antecedents: Vec<u64>,
}

fn parse_tracecheck(text: &str) -> Result<Vec<TraceEntry>, SatCertError> {
    let mut entries = Vec::new();
    for line in text.lines() {
        let nums: Vec<i64> = line
            .split_whitespace()
            .map(|t| {
                t.parse::<i64>()
                    .map_err(|_| SatCertError::BadTrace(format!("non-integer token '{t}'")))
            })
            .collect::<Result<_, _>>()?;
        if nums.is_empty() {
            continue;
        }
        let id = u64::try_from(nums[0])
            .map_err(|_| SatCertError::BadTrace(format!("negative trace id {}", nums[0])))?;
        let first_zero = nums[1..]
            .iter()
            .position(|&n| n == 0)
            .map(|p| p + 1)
            .ok_or_else(|| {
                SatCertError::BadTrace(format!("trace line {id}: no literal terminator"))
            })?;
        if nums.last() != Some(&0) || nums.len() < first_zero + 1 {
            return Err(SatCertError::BadTrace(format!(
                "trace line {id}: missing antecedent terminator"
            )));
        }
        let lits: Clause = nums[1..first_zero].iter().copied().collect();
        let antecedents: Vec<u64> = nums[first_zero + 1..nums.len() - 1]
            .iter()
            .map(|&a| {
                u64::try_from(a)
                    .map_err(|_| SatCertError::BadTrace(format!("negative antecedent {a}")))
            })
            .collect::<Result<_, _>>()?;
        entries.push(TraceEntry {
            id,
            lits,
            antecedents,
        });
    }
    Ok(entries)
}

/// clean-kernel oriented resolve: drop `+pivot` from `a` and `-pivot` from `b`
/// (the #22 single-oriented-polarity-drop soundness fix — see
/// clean-kernel `resolution_check.rs`).
fn resolve(a: &Clause, b: &Clause, pivot: i64) -> Clause {
    debug_assert!(pivot > 0);
    a.iter()
        .copied()
        .filter(|&l| l != pivot)
        .chain(b.iter().copied().filter(|&l| l != -pivot))
        .collect()
}

fn is_tautology(c: &Clause) -> bool {
    c.iter().any(|&l| c.contains(&-l))
}

/// A pending binary step whose "previous resolvent in this chain" premise is
/// symbolic until global ids are assigned.
enum ChainRef {
    Concrete(u64),
    Prev,
}

/// Linear trivial-resolution replay of one RUP lemma: fold `order[1..]` into
/// `order[0]`, each time resolving on the unique clashing literal. `None` if
/// stuck, a step resolves to a tautology, or the final resolvent is not a
/// subset of `target`.
fn try_chain(
    target: &Clause,
    order: &[(u64, Clause)],
) -> Option<Vec<(Clause, ChainRef, ChainRef, u32)>> {
    let (first, rest) = order.split_first()?;
    let (cur_gid, mut cur) = (first.0, first.1.clone());
    let mut remaining: Vec<&(u64, Clause)> = rest.iter().collect();
    let mut steps = Vec::new();
    while !remaining.is_empty() {
        let mut pick: Option<(usize, i64)> = None;
        for (i, (_, clause)) in remaining.iter().enumerate() {
            let clashes: Vec<i64> = cur
                .iter()
                .copied()
                .filter(|l| clause.contains(&-l))
                .collect();
            if clashes.len() == 1 {
                pick = Some((i, clashes[0]));
                break;
            }
        }
        let (i, lit) = pick?;
        let (gid, clause) = remaining.remove(i);
        let pivot_var_1based = lit.unsigned_abs();
        let pivot = pivot_var_1based as i64;
        let prev_ref = || {
            if steps.is_empty() {
                ChainRef::Concrete(cur_gid)
            } else {
                ChainRef::Prev
            }
        };
        let res = if lit > 0 {
            // cur holds +pivot: orientation (a=cur, b=clause).
            let r = resolve(&cur, clause, pivot);
            steps.push((
                r.clone(),
                prev_ref(),
                ChainRef::Concrete(*gid),
                (pivot_var_1based - 1) as u32,
            ));
            r
        } else {
            // cur holds -pivot: orientation (a=clause, b=cur).
            let r = resolve(clause, &cur, pivot);
            steps.push((
                r.clone(),
                ChainRef::Concrete(*gid),
                prev_ref(),
                (pivot_var_1based - 1) as u32,
            ));
            r
        };
        if is_tautology(&res) {
            return None;
        }
        cur = res;
    }
    if cur.is_subset(target) {
        Some(steps)
    } else {
        None
    }
}

/// Convert a drat-trim TraceCheck resolution trace over `clauses` into the
/// binary-resolution [`SatResolutionStep`] list `Clean.Res.checkRefutes3`
/// consumes (global-id scheme; see module docs). The returned chain has
/// already passed the producer-side [`verify_steps`] replay, including the
/// final-empty-resolvent requirement.
pub fn trace_to_steps(
    clauses: &[Vec<SatLit>],
    trace_text: &str,
) -> Result<Vec<SatResolutionStep>, SatCertError> {
    let entries = parse_tracecheck(trace_text)?;
    let n = clauses.len() as u64;

    let originals: Vec<Clause> = clauses
        .iter()
        .map(|c| c.iter().map(|&l| satlit_to_dimacs(l)).collect())
        .collect();

    // Global clause database and trace-id -> global-id map.
    let mut db: Vec<Clause> = originals.clone();
    let mut gid_of_tid: std::collections::HashMap<u64, u64> = std::collections::HashMap::new();

    // Pass 1: original clauses. drat-trim prints original clause i as trace
    // id i+1 (appended at the END of the -r file), with no antecedents.
    let mut lemmas: Vec<&TraceEntry> = Vec::new();
    for entry in &entries {
        if entry.antecedents.is_empty() {
            let idx = entry
                .id
                .checked_sub(1)
                .filter(|&i| i < n)
                .ok_or(SatCertError::TraceCnfMismatch { trace_id: entry.id })?;
            if db[idx as usize] != entry.lits {
                return Err(SatCertError::TraceCnfMismatch { trace_id: entry.id });
            }
            gid_of_tid.insert(entry.id, idx);
        } else {
            lemmas.push(entry);
        }
    }

    // Pass 2: lemmas in trace-id order (ids increase with derivation order).
    lemmas.sort_by_key(|e| e.id);
    let mut steps: Vec<SatResolutionStep> = Vec::new();
    for lemma in lemmas {
        let mut antecedent_clauses: Vec<(u64, Clause)> =
            Vec::with_capacity(lemma.antecedents.len());
        for &ant in &lemma.antecedents {
            if ant >= lemma.id {
                return Err(SatCertError::NonTopologicalAntecedent { trace_id: lemma.id });
            }
            let gid = *gid_of_tid
                .get(&ant)
                .ok_or(SatCertError::NonTopologicalAntecedent { trace_id: lemma.id })?;
            antecedent_clauses.push((gid, db[gid as usize].clone()));
        }
        if antecedent_clauses.len() == 1 {
            // Duplicate/subsumed lemma: alias its trace id to the antecedent.
            gid_of_tid.insert(lemma.id, antecedent_clauses[0].0);
            continue;
        }

        // Reverse propagation order first (the standard trivial-resolution
        // replay for RUP), then the forward order as a greedy fallback.
        let reversed: Vec<(u64, Clause)> = antecedent_clauses.iter().rev().cloned().collect();
        let chain = try_chain(&lemma.lits, &reversed)
            .or_else(|| try_chain(&lemma.lits, &antecedent_clauses))
            .ok_or(SatCertError::ChainStuck { trace_id: lemma.id })?;

        let mut prev_gid: Option<u64> = None;
        for (resolvent, p1, p2, pivot_var) in chain {
            let gid = db.len() as u64;
            let concrete = |r: ChainRef, prev: Option<u64>| -> u64 {
                match r {
                    ChainRef::Concrete(g) => g,
                    ChainRef::Prev => prev.expect("Prev only after the first step"),
                }
            };
            let prem1 = concrete(p1, prev_gid);
            let prem2 = concrete(p2, prev_gid);
            steps.push(SatResolutionStep {
                resolvent: resolvent
                    .iter()
                    .map(|&l| dimacs_to_satlit(l))
                    .collect::<Result<_, _>>()
                    .map_err(|_| {
                        SatCertError::BadTrace(format!("lemma {}: bad literal", lemma.id))
                    })?,
                prem1: prem1 as u32,
                prem2: prem2 as u32,
                pivot_var,
            });
            db.push(resolvent);
            prev_gid = Some(gid);
        }
        if let Some(g) = prev_gid {
            gid_of_tid.insert(lemma.id, g);
        }
    }

    verify_steps(clauses, &steps)?;
    Ok(steps)
}

/// Producer-side replay of a binary-resolution chain — the Rust twin of the
/// kernel's `checkStep3`/`checkRefutes3` (single oriented polarity drop, both
/// orientations admitted, tautology-free, final resolvent empty). This is a
/// CONVENIENCE self-check so producers fail fast with a good error; the
/// authoritative judgment is the clean-kernel reflection re-check in
/// `trust_ir_build::validate` — nothing downstream trusts this function.
pub fn verify_steps(
    clauses: &[Vec<SatLit>],
    steps: &[SatResolutionStep],
) -> Result<(), SatCertError> {
    let mut db: Vec<Clause> = clauses
        .iter()
        .map(|c| c.iter().map(|&l| satlit_to_dimacs(l)).collect())
        .collect();
    for (index, step) in steps.iter().enumerate() {
        let get = |id: u32| -> Option<&Clause> { db.get(id as usize) };
        let (Some(a), Some(b)) = (get(step.prem1), get(step.prem2)) else {
            return Err(SatCertError::ReplayRejected { step_index: index });
        };
        let pivot = i64::from(step.pivot_var) + 1;
        let resolvent: Clause = step
            .resolvent
            .iter()
            .map(|&l| satlit_to_dimacs(l))
            .collect();
        let oriented_ab =
            a.contains(&pivot) && b.contains(&-pivot) && resolvent == resolve(a, b, pivot);
        let oriented_ba = !oriented_ab
            && a.contains(&-pivot)
            && b.contains(&pivot)
            && resolvent == resolve(b, a, pivot);
        if !(oriented_ab || oriented_ba) || is_tautology(&resolvent) {
            return Err(SatCertError::ReplayRejected { step_index: index });
        }
        db.push(resolvent);
    }
    match steps.last() {
        Some(last) if last.resolvent.is_empty() => Ok(()),
        _ => Err(SatCertError::NoEmptyClause),
    }
}

/// An assembled lowering-resolution assurance artifact: a `Pending`
/// obligation plus the `CleanCic` payload and kernel-recheck directive.
///
/// The payload can establish that the producer-selected clause list is UNSAT.
/// It cannot establish that the clause list is the exact semantic miter for the
/// named lowering rule, because the validator does not independently derive
/// that miter from Trust-IR semantics. Consequently this builder must never
/// mint a `Certified` obligation.
#[derive(Debug, Clone)]
pub struct LoweringResolutionCert {
    pub obligation: ProofObligation,
    pub certificate: ProofCertificate,
}

/// Assemble a [`ObligationKind::TranslationValidation`] `Pending` obligation
/// plus a CNF-refutation assurance payload for a lowering rule.
///
/// The obligation's formula pins the exact clause list by digest
/// ([`satres_formula`]); the certificate's `term` carries the payload bytes,
/// its `context` carries the producer's ENCODING-FIDELITY statement (the
/// named trust boundary — see `trust_ir::proof::satres`), and its recheck
/// directive cites exactly the per-certificate ground theorem the validator
/// itself registers ([`SATRES_CERT_UNSAT_THEOREM`]) under the
/// [`KERNEL_ANCHOR_TRUSTCG_LOWERING_RESOLUTION`] anchor with an EMPTY
/// allowed-axioms set (the reflection proof is fully constructive).
///
/// When `provenance` is `Some`, the structured gate-level clause provenance is
/// VALIDATED against the payload's clause list (fail-closed: a mismatched or
/// wrong-rule provenance returns `None`, so no cert ships whose carried
/// provenance lies about its clauses) and then CARRIED in the certificate
/// context (digest + full `satprov1` text), lifting the encoding-fidelity
/// boundary from "asserted" to "gate-level checked, gate-DAG⇔SmtExpr asserted"
/// (see `trust_ir::proof::satprov`). When `None`, only the plain asserted
/// boundary statement is carried (back-compat; used by pure-negative tests).
/// Neither form binds the gate DAG to the exact validator-derived source and
/// target semantics, so neither form carries obligation-discharge authority.
///
/// Returns `None` if the rule name cannot be bound into a formula, or if a
/// provided provenance fails validation (fail-closed) — callers must not fall
/// back to an unpinned or unchecked obligation.
#[must_use]
pub fn build_lowering_resolution_cert(
    obligation_id: ProofId,
    function: Option<FuncId>,
    rule_name: &str,
    payload: &SatResolutionCertPayload,
    provenance: Option<&MiterProvenance>,
) -> Option<LoweringResolutionCert> {
    let term = payload.try_to_bytes().ok()?;
    let formula = satres_formula(rule_name, &payload.clauses)?;
    // Fail-closed provenance gate: if provenance is supplied it must validate
    // against THIS clause list and name THIS rule, or the cert is not built.
    let context = match provenance {
        Some(prov) => {
            prov.validate_for_rule(rule_name, &payload.clauses).ok()?;
            let digest = prov.digest()?;
            let text = prov.to_text()?;
            format!(
                "ENCODING-FIDELITY BOUNDARY (gate-level CHECKED; gate-DAG<=>SmtExpr asserted): the \
                 untrusted producer's clause list was re-derived from the named-gate provenance \
                 below and confirmed to be EXACTLY the Tseitin miter of lowering rule \
                 '{rule_name}' (every clause a checked gate CNF, the two sides compared \
                 bit-for-bit). The ck0 kernel certifies UNSAT of the clause list only; that the \
                 recorded gate DAG faithfully bit-blasts the rule's SmtExpr sides remains \
                 ASSERTED, not proven.\nsatprov-digest: {digest}\n\n{text}"
            )
        }
        None => format!(
            "ENCODING-FIDELITY BOUNDARY (asserted, not kernel-proven): the untrusted producer \
             asserts the embedded clause list encodes the semantic-equivalence miter of lowering \
             rule '{rule_name}'. The ck0 kernel certifies UNSAT of the clause list only."
        ),
    };
    let obligation = ProofObligation {
        id: obligation_id,
        kind: ObligationKind::TranslationValidation,
        // CNF replay is useful assurance, but it is not translation-validation
        // authority until the validator independently re-derives the exact
        // miter from the lowering rule and the Trust-IR machine semantics.
        status: ProofStatus::Pending,
        description: format!(
            "lowering rule '{rule_name}': SAT refutation of the equivalence miter, \
             kernel-re-checked via Clean.Res.checkRefutes3"
        ),
        formula: Some(formula),
        function,
        source: None,
        site: None,
        spec: None,
    };
    let lineage = clean_cic_lineage_digest(&obligation);
    let certificate = ProofCertificate {
        obligation: obligation_id,
        prover: "trust-cg-sat/microsat+drat-trim".to_string(),
        evidence: ProofEvidence::CleanCic {
            term,
            context: context.into_bytes(),
            lineage,
            kernel_recheck: Some(CleanCicKernelRecheck {
                module: "Clean.Res".to_string(),
                theorems: vec![SATRES_CERT_UNSAT_THEOREM.to_string()],
                anchor: KERNEL_ANCHOR_TRUSTCG_LOWERING_RESOLUTION.to_string(),
                // The reflection proof is fully constructive: empty structural
                // axiom closure, so NOTHING need be allowed.
                allowed_axioms: vec![],
                binding: None,
            }),
        },

        assurance: None,
    };
    Some(LoweringResolutionCert {
        obligation,
        certificate,
    })
}
