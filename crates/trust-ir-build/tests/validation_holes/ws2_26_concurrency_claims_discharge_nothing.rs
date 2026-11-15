// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! WS2.26 (F-044, row `trust-ir-self-declared/concurrency-single-threaded`;
//! ruled 2026-10-02, DG-08: keep the ratified sequentially consistent,
//! single-threaded projection).
//!
//! THE RATIFICATION. `TRUST.md` item 8 and `docs/ub-numerics-policy.md` §5
//! state that the executable models are single-threaded and SC, and that the
//! concurrency annotations `DataRaceFree` / `AtomicOrdering` have NO discharge
//! path: carrying one is trusting the producer. Until this module that was
//! documented, not enforced — nothing failed if a validator change let a
//! concurrency claim stand in for proof authority.
//!
//! THE RULE HELD HERE. `validate_module` (and the authority-tier and linked
//! entry points beside it) never counts a `DataRaceFree` or `AtomicOrdering`
//! annotation toward a `Discharged` obligation: a `Discharged` row is admitted
//! only by a certificate in the validator's authority set, the claims never
//! change a verdict or the replayed-authority set, and annotation synthesis
//! (`Module::add_function`) mints `Pending` rows only.
//!
//! * positive control — the claims beside REAL authority (a kernel-certified
//!   Clean callee row and its admitted same-module restatement) validate
//!   everywhere, with the same replayed-authority set as without them;
//! * negative twins — a `Discharged` `TemporalSafety` (the kind `DataRaceFree`
//!   maps to) and `Ownership` (the kind that backs it) row sited on the very
//!   claim-carrying atomic store, with no certificate, is
//!   `DischargedWithoutCertificate`; so is the restatement once its
//!   inheritance certificate is removed; and a `ProofRef` round trip through a
//!   `DataRaceFree` claim launders nothing (`ProofRefUnresolved`);
//! * mutation controls — stripping every concurrency claim leaves each error
//!   list byte-identical, and the single mutation `Discharged` → `Pending`
//!   removes exactly the named refusals.

use std::collections::BTreeSet;

use trust_ir::clean_expr_lowering::contract::contract_clean_cic_certificate_in;
use trust_ir::inst::{Inst, Ordering};
use trust_ir::proof::{
    ClauseBinding, ClausePlace, ClauseSort, ObligationKind, ObligationSite, ProofAnnotation,
    ProofCertificate, ProofEvidence, ProofFormula, ProofObligation, ProofStatus,
    RejectingModuleProofAuthority,
};
use trust_ir::ty::{FuncTy, Ty};
use trust_ir::value::{BlockId, FuncId, ProofId};
use trust_ir::{Block, Endianness, Function, Module, Producer, TargetInfo};
use trust_ir_build::{
    ModuleBuilder, ModuleSet, ValidationError, validate_linked_module, validate_module,
    validate_module_report, validate_module_with_authority,
};

const PROVER: &str = "trust_vc-clean-kernel";
/// Index of the Clean callee `g` and the Rust caller `f` in `functions`.
const G: usize = 0;
const F: usize = 1;
/// The kernel-certified callee row, its restatement, and the two
/// concurrency-kind rows that carry no certificate.
const CALLEE_ROW: u32 = 0;
const RESTATEMENT_ROW: u32 = 1;
const TEMPORAL_ROW: u32 = 2;
const OWNERSHIP_ROW: u32 = 3;

// ===========================================================================
// fixture
// ===========================================================================

fn target() -> TargetInfo {
    TargetInfo {
        triple: "aarch64-apple-darwin".into(),
        pointer_size: 8,
        endianness: Endianness::Little,
        abi: None,
        struct_passing: Default::default(),
    }
}

/// `(>= result 0)` bound to the first result slot at sort `Int`.
fn ensures() -> ProofFormula {
    let mut formula = ProofFormula::smtlib2("(>= result 0)", "Bool");
    formula.bindings = vec![(
        "result".to_string(),
        ClauseBinding {
            sort: ClauseSort::Int,
            place: ClausePlace::ResultSlot { index: 0 },
        },
    )];
    formula
}

/// Every concurrency claim of the format, one of each `AtomicOrdering`.
fn concurrency_claims() -> Vec<ProofAnnotation> {
    vec![
        ProofAnnotation::DataRaceFree,
        ProofAnnotation::AtomicOrdering(Ordering::Relaxed),
        ProofAnnotation::AtomicOrdering(Ordering::Acquire),
        ProofAnnotation::AtomicOrdering(Ordering::Release),
        ProofAnnotation::AtomicOrdering(Ordering::AcqRel),
        ProofAnnotation::AtomicOrdering(Ordering::SeqCst),
    ]
}

fn is_concurrency_claim(annotation: &ProofAnnotation) -> bool {
    matches!(
        annotation,
        ProofAnnotation::DataRaceFree | ProofAnnotation::AtomicOrdering(_)
    )
}

/// Index of `f`'s atomic store in its entry block.
fn atomic_store_index(m: &Module) -> u32 {
    m.functions[F].blocks[0]
        .body
        .iter()
        .position(|node| matches!(node.inst, Inst::AtomicStore { .. }))
        .expect("f carries an atomic store") as u32
}

fn atomic_store_site(m: &Module) -> ObligationSite {
    ObligationSite::new(m.functions[F].id, BlockId::new(0), atomic_store_index(m))
}

/// A concurrency-kind row scoped to `f` and sited on its atomic store, with
/// NO certificate.
fn concurrency_row(
    m: &Module,
    id: u32,
    kind: ObligationKind,
    status: ProofStatus,
) -> ProofObligation {
    ProofObligation::new(
        ProofId::new(id),
        kind,
        status,
        "the atomic store is data-race free under its declared ordering",
    )
    .with_function(m.functions[F].id)
    .with_site(atomic_store_site(m))
}

/// The positive fixture:
///
/// ```text
/// fn#0 g() -> u64 { 42 }                       Clean
/// fn#1 f() -> u64 {                            Rust
///        slot = alloca u64
///        atomic_store seq_cst slot, 7          [DataRaceFree, AtomicOrdering(SeqCst)]
///        fence seq_cst                         [AtomicOrdering(SeqCst)]
///        x = atomic_load acquire slot          [AtomicOrdering(Acquire)]
///        r = call g()
///        ret r }                               fn-level: every concurrency claim
///
/// #0 Certified  Postcondition (>= result 0) scoped to g   kernel CleanCic
/// #1 Discharged Postcondition (>= result 0) scoped to g   InheritedFromCallee { g, #0 }
/// #2 `concurrency_status` TemporalSafety  sited on the atomic store   (no certificate)
/// #3 `concurrency_status` Ownership       sited on the atomic store   (no certificate)
/// ```
fn fixture(concurrency_status: ProofStatus) -> Module {
    let mut mb = ModuleBuilder::new_with_target_info("ws2_26_concurrency_claims", target());
    let ft = mb.add_func_type(vec![], vec![Ty::U64]);
    let mut fb = mb.function("g", ft);
    fb.set_producer(Producer::Clean);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    let v = fb.uconst(Ty::U64, 42);
    fb.ret(vec![v]);
    let g = fb.build();
    let mut fb = mb.function("f", ft);
    fb.set_producer(Producer::TRust);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    let slot = fb.alloca(Ty::U64);
    let seven = fb.uconst(Ty::U64, 7);
    fb.atomic_store(Ty::U64, slot, seven, Ordering::SeqCst);
    fb.fence(Ordering::SeqCst);
    let _observed = fb.atomic_load(Ty::U64, slot, Ordering::Acquire);
    let r = fb.call(g, vec![]);
    fb.ret(vec![r]);
    fb.build();
    let mut m = mb.build().expect("ModuleBuilder::build: test fixture");

    // The claims, attached after `build` so no annotation synthesis runs (the
    // synthesis path is held by its own test below).
    m.functions[G].proofs.push(ProofAnnotation::DataRaceFree);
    m.functions[F].proofs.extend(concurrency_claims());
    for node in &mut m.functions[F].blocks[0].body {
        match node.inst {
            Inst::AtomicStore { ordering, .. } => {
                node.proofs.push(ProofAnnotation::DataRaceFree);
                node.proofs.push(ProofAnnotation::AtomicOrdering(ordering));
            }
            Inst::AtomicLoad { ordering, .. } | Inst::Fence { ordering } => {
                node.proofs.push(ProofAnnotation::AtomicOrdering(ordering));
            }
            _ => {}
        }
    }

    m.proof_obligations.push(
        ProofObligation::new(
            ProofId::new(CALLEE_ROW),
            ObligationKind::Postcondition,
            ProofStatus::Certified,
            "ensures clause 0 of 'g'",
        )
        .with_function(g)
        .with_formula(ensures()),
    );
    let kernel = contract_clean_cic_certificate_in(&m, &m.proof_obligations[0], PROVER)
        .expect("a bound nonneg clause over a u64 result is mintable");
    m.proof_certificates.push(kernel);
    m.proof_obligations.push(
        ProofObligation::new(
            ProofId::new(RESTATEMENT_ROW),
            ObligationKind::Postcondition,
            ProofStatus::Discharged,
            "f relies on ensures clause 0 of 'g'",
        )
        .with_function(g)
        .with_formula(ensures()),
    );
    m.proof_certificates.push(ProofCertificate {
        obligation: ProofId::new(RESTATEMENT_ROW),
        prover: "compose".to_string(),
        evidence: ProofEvidence::InheritedFromCallee {
            callee: g,
            obligation: ProofId::new(CALLEE_ROW),
            external: None,
        },
        assurance: None,
    });
    let temporal = concurrency_row(
        &m,
        TEMPORAL_ROW,
        ObligationKind::TemporalSafety,
        concurrency_status,
    );
    let ownership = concurrency_row(
        &m,
        OWNERSHIP_ROW,
        ObligationKind::Ownership,
        concurrency_status,
    );
    m.proof_obligations.push(temporal);
    m.proof_obligations.push(ownership);
    m
}

/// The mutation: the same module with every `DataRaceFree` /
/// `AtomicOrdering` claim removed (function level and every node), nothing
/// else touched.
fn without_concurrency_claims(m: &Module) -> Module {
    let mut stripped = m.clone();
    let mut removed = 0usize;
    for function in &mut stripped.functions {
        let before = function.proofs.len();
        function.proofs.retain(|a| !is_concurrency_claim(a));
        removed += before - function.proofs.len();
        for block in &mut function.blocks {
            for node in &mut block.body {
                let before = node.proofs.len();
                node.proofs.retain(|a| !is_concurrency_claim(a));
                removed += before - node.proofs.len();
            }
        }
    }
    assert!(removed > 0, "the mutation must remove at least one claim");
    stripped
}

fn linked_alone(m: &Module) -> Vec<ValidationError> {
    let none = ModuleSet::new(std::iter::empty::<&Module>());
    validate_linked_module(m, &none, &RejectingModuleProofAuthority).into_errors()
}

/// The verdict of every entry point that decides `Discharged` authority.
fn verdicts(m: &Module) -> [Vec<ValidationError>; 3] {
    [
        validate_module(m),
        validate_module_with_authority(m, &RejectingModuleProofAuthority),
        linked_alone(m),
    ]
}

fn discharged_without_certificate(obligation: u32) -> ValidationError {
    ValidationError::DischargedWithoutCertificate { obligation }
}

// ===========================================================================
// positive control
// ===========================================================================

/// The claims beside REAL authority validate under every entry point, and
/// the replayed kernel-authority set is exactly the callee's CleanCic
/// certificate — with or without the claims.
#[test]
fn ws2_26_concurrency_claims_beside_real_authority_validate() {
    let m = fixture(ProofStatus::Pending);
    for errors in verdicts(&m) {
        assert_eq!(errors, vec![]);
    }
    let kernel = BTreeSet::from([m.proof_certificates[0].lineage_ref()]);
    assert_eq!(
        validate_module_report(&m).replayed_certificate_refs(),
        Some(&kernel)
    );
    let stripped = without_concurrency_claims(&m);
    assert_eq!(
        validate_module_report(&stripped).replayed_certificate_refs(),
        Some(&kernel),
        "the concurrency claims add nothing to the replayed authority set"
    );
}

// ===========================================================================
// negative twins
// ===========================================================================

/// `Discharged` rows of the kind `DataRaceFree` maps to (`TemporalSafety`)
/// and of the kind that backs it (`Ownership`), sited on the atomic store
/// that CARRIES `DataRaceFree` + `AtomicOrdering(SeqCst)` and scoped to a
/// function carrying every concurrency claim, are refused by name: no claim
/// stands in for a certificate.
#[test]
fn ws2_26_discharged_row_backed_only_by_concurrency_claims_is_refused() {
    let m = fixture(ProofStatus::Discharged);
    let store = &m.functions[F].blocks[0].body[atomic_store_index(&m) as usize];
    assert!(store.proofs.contains(&ProofAnnotation::DataRaceFree));
    assert!(
        store
            .proofs
            .contains(&ProofAnnotation::AtomicOrdering(Ordering::SeqCst))
    );
    for errors in verdicts(&m) {
        assert_eq!(
            errors,
            vec![
                discharged_without_certificate(TEMPORAL_ROW),
                discharged_without_certificate(OWNERSHIP_ROW),
            ]
        );
    }
    assert_eq!(validate_module_report(&m).replayed_certificate_refs(), None);
}

/// The restatement row, which IS admitted with its inheritance certificate,
/// is refused once that certificate is removed — the concurrency claims on
/// the caller do not rescue it.
#[test]
fn ws2_26_restatement_stripped_of_its_certificate_is_not_rescued_by_claims() {
    let mut m = fixture(ProofStatus::Pending);
    m.proof_certificates
        .retain(|c| c.obligation != ProofId::new(RESTATEMENT_ROW));
    for errors in verdicts(&m) {
        assert_eq!(
            errors,
            vec![discharged_without_certificate(RESTATEMENT_ROW)]
        );
    }
}

/// The circular shape: the atomic store carries `DataRaceFree` AND a
/// `ProofRef` to the uncertified `Ownership` row (the kind that may back
/// `DataRaceFree`). The claim does not ground the row, and the row cannot
/// back the claim: `DischargedWithoutCertificate` plus an unreplayed
/// `ProofRefUnresolved`.
#[test]
fn ws2_26_proof_ref_round_trip_through_a_concurrency_claim_launders_nothing() {
    let mut m = fixture(ProofStatus::Discharged);
    let index = atomic_store_index(&m) as usize;
    m.functions[F].blocks[0].body[index]
        .proofs
        .push(ProofAnnotation::ProofRef(ProofId::new(OWNERSHIP_ROW)));
    let f = m.functions[F].id.index();
    let errors = validate_module(&m);
    assert!(
        errors.contains(&discharged_without_certificate(OWNERSHIP_ROW)),
        "{errors:?}"
    );
    assert!(
        errors.contains(&discharged_without_certificate(TEMPORAL_ROW)),
        "{errors:?}"
    );
    assert!(
        errors.iter().any(|e| matches!(
            e,
            ValidationError::ProofRefUnresolved { function, obligation, missing: false }
                if *function == f && *obligation == OWNERSHIP_ROW
        )),
        "{errors:?}"
    );
}

// ===========================================================================
// mutation controls
// ===========================================================================

/// Stripping every concurrency claim leaves every entry point's error list
/// byte-identical on the positive fixture, both negative twins and the
/// stripped-certificate twin: the claims are never counted, either way.
#[test]
fn ws2_26_mutation_control_concurrency_claims_never_change_a_verdict() {
    let mut no_restatement_cert = fixture(ProofStatus::Discharged);
    no_restatement_cert
        .proof_certificates
        .retain(|c| c.obligation != ProofId::new(RESTATEMENT_ROW));
    for m in [
        fixture(ProofStatus::Pending),
        fixture(ProofStatus::Discharged),
        no_restatement_cert,
    ] {
        let stripped = without_concurrency_claims(&m);
        assert_eq!(verdicts(&m), verdicts(&stripped));
    }
}

/// The single mutation `Discharged` → `Pending` on the two concurrency rows
/// removes exactly their two refusals, so the refusal is the missing
/// certificate and nothing else about the rows.
#[test]
fn ws2_26_mutation_control_pending_twin_removes_exactly_the_named_refusals() {
    let discharged = fixture(ProofStatus::Discharged);
    let mut pending = discharged.clone();
    for row in &mut pending.proof_obligations {
        if row.id == ProofId::new(TEMPORAL_ROW) || row.id == ProofId::new(OWNERSHIP_ROW) {
            row.status = ProofStatus::Pending;
        }
    }
    assert_eq!(pending, fixture(ProofStatus::Pending));
    let [refused, ..] = verdicts(&discharged);
    let [admitted, ..] = verdicts(&pending);
    assert_eq!(admitted, vec![]);
    assert_eq!(
        refused,
        vec![
            discharged_without_certificate(TEMPORAL_ROW),
            discharged_without_certificate(OWNERSHIP_ROW),
        ]
    );
}

// ===========================================================================
// annotation synthesis
// ===========================================================================

/// `Module::add_function` maps function-level claims to obligation drafts:
/// `DataRaceFree` mints exactly one `Pending` `TemporalSafety` row with no
/// certificate, and `AtomicOrdering` (no obligation kind) mints none — so the
/// synthesis path never produces a `Discharged` row either.
#[test]
fn ws2_26_annotation_synthesis_mints_pending_rows_only() {
    let mut m = Module::new("ws2_26_synthesis");
    let ft = m
        .add_func_type(FuncTy {
            abi: None,
            params: vec![],
            returns: vec![],
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut f = Function::new(FuncId::new(0), "f", ft, BlockId::new(0));
    let mut entry = Block::new(BlockId::new(0));
    entry
        .body
        .push(trust_ir::node::InstrNode::new(Inst::Return {
            values: vec![],
        }));
    f.blocks.push(entry);
    f.proofs = concurrency_claims();
    m.try_add_function(f)
        .expect("Module::try_add_function: test fixture");

    assert_eq!(m.proof_obligations.len(), 1, "{:?}", m.proof_obligations);
    let row = &m.proof_obligations[0];
    assert_eq!(row.kind, ObligationKind::TemporalSafety);
    assert_eq!(row.status, ProofStatus::Pending);
    assert_eq!(row.function, Some(FuncId::new(0)));
    assert!(m.proof_certificates.is_empty());
    assert!(
        validate_module(&m)
            .iter()
            .all(|e| !matches!(e, ValidationError::DischargedWithoutCertificate { .. })),
    );

    // AtomicOrdering alone mints nothing.
    let mut only_ordering = Module::new("ws2_26_synthesis_ordering");
    let ft = only_ordering
        .add_func_type(FuncTy {
            abi: None,
            params: vec![],
            returns: vec![],
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut f = Function::new(FuncId::new(0), "f", ft, BlockId::new(0));
    let mut entry = Block::new(BlockId::new(0));
    entry
        .body
        .push(trust_ir::node::InstrNode::new(Inst::Return {
            values: vec![],
        }));
    f.blocks.push(entry);
    f.proofs = concurrency_claims()
        .into_iter()
        .filter(|a| matches!(a, ProofAnnotation::AtomicOrdering(_)))
        .collect();
    only_ordering
        .try_add_function(f)
        .expect("Module::try_add_function: test fixture");
    assert!(only_ordering.proof_obligations.is_empty());
}

// ===========================================================================
// review (adversarial twins the first cut did not write)
// ===========================================================================

/// Every entry point's verdict, with and without the concurrency claims, is
/// identical, and each contains `wanted`.
fn assert_refused_with_or_without_claims(m: &Module, wanted: &[ValidationError]) {
    let stripped = without_concurrency_claims(m);
    for (errors, stripped_errors) in verdicts(m).into_iter().zip(verdicts(&stripped)) {
        for error in wanted {
            assert!(errors.contains(error), "missing {error:?} in {errors:?}");
        }
        assert_eq!(
            errors, stripped_errors,
            "a concurrency claim moved a verdict"
        );
    }
}

/// A forged, non-kernel certificate on a concurrency row — every evidence
/// shape a producer could spell `DataRaceFree` into (SMT bytes, a Lean
/// string, a Kani harness, a manual audit, a translation-validation hash) —
/// is outside the validator's authority set: the `Discharged` row stays
/// `DischargedWithoutCertificate`, and the claims change nothing.
#[test]
fn ws2_26_review_forged_noncertified_evidence_on_concurrency_rows_is_refused() {
    let shapes = [
        ProofEvidence::SmtProof(b"(data-race-free)".to_vec()),
        ProofEvidence::LeanProof("theorem drf : DataRaceFree := trivial".into()),
        ProofEvidence::KaniHarness("drf_harness".into()),
        ProofEvidence::Trusted("rustc's Send/Sync discipline established DataRaceFree".into()),
        ProofEvidence::TranslationValidation {
            rule_name: "data_race_free".into(),
            smt_hash: [7; 32],
        },
    ];
    for evidence in shapes {
        let mut m = fixture(ProofStatus::Discharged);
        for row in [TEMPORAL_ROW, OWNERSHIP_ROW] {
            m.proof_certificates.push(ProofCertificate {
                obligation: ProofId::new(row),
                prover: "producer".to_string(),
                evidence: evidence.clone(),
                assurance: None,
            });
        }
        assert_refused_with_or_without_claims(
            &m,
            &[
                discharged_without_certificate(TEMPORAL_ROW),
                discharged_without_certificate(OWNERSHIP_ROW),
            ],
        );
    }
}

/// The kernel tier is no softer: `Certified` concurrency rows sited on the
/// claim-carrying atomic store, with no `CleanCic` certificate, are
/// `CertifiedWithoutCleanCic`, claims or no claims.
#[test]
fn ws2_26_review_certified_concurrency_rows_need_a_clean_cic_certificate() {
    let m = fixture(ProofStatus::Certified);
    assert_refused_with_or_without_claims(
        &m,
        &[
            ValidationError::CertifiedWithoutCleanCic {
                obligation: TEMPORAL_ROW,
            },
            ValidationError::CertifiedWithoutCleanCic {
                obligation: OWNERSHIP_ROW,
            },
        ],
    );
}

/// The site is not what refuses the first-cut twins: the same rows scoped to
/// the claim-carrying function but UNSITED, and with no function scope at
/// all, are refused by the same name.
#[test]
fn ws2_26_review_unsited_and_unscoped_concurrency_rows_are_refused() {
    let mut unsited = fixture(ProofStatus::Discharged);
    for row in &mut unsited.proof_obligations {
        if row.id == ProofId::new(TEMPORAL_ROW) || row.id == ProofId::new(OWNERSHIP_ROW) {
            row.site = None;
        }
    }
    let mut unscoped = unsited.clone();
    for row in &mut unscoped.proof_obligations {
        if row.id == ProofId::new(TEMPORAL_ROW) || row.id == ProofId::new(OWNERSHIP_ROW) {
            row.function = None;
        }
    }
    for m in [unsited, unscoped] {
        let wanted = [
            discharged_without_certificate(TEMPORAL_ROW),
            discharged_without_certificate(OWNERSHIP_ROW),
        ];
        for errors in verdicts(&m) {
            assert_eq!(errors, wanted.to_vec());
        }
        assert_refused_with_or_without_claims(&m, &wanted);
    }
}

/// Inheritance does not launder a claim either: a `Discharged`
/// `TemporalSafety` restatement whose `InheritedFromCallee` certificate cites
/// a callee row that only the callee's `DataRaceFree` claim "backs" (a
/// `Pending` row, then an uncertified `Discharged` one) is refused.
#[test]
fn ws2_26_review_inheritance_from_a_claim_only_callee_row_is_refused() {
    const CALLEE_TEMPORAL: u32 = 4;
    const CALLER_RESTATEMENT: u32 = 5;
    for callee_status in [ProofStatus::Pending, ProofStatus::Discharged] {
        let mut m = fixture(ProofStatus::Pending);
        let g = m.functions[G].id;
        assert!(
            m.functions[G]
                .proofs
                .contains(&ProofAnnotation::DataRaceFree)
        );
        m.proof_obligations.push(
            ProofObligation::new(
                ProofId::new(CALLEE_TEMPORAL),
                ObligationKind::TemporalSafety,
                callee_status,
                "g is data-race free",
            )
            .with_function(g),
        );
        m.proof_obligations.push(
            ProofObligation::new(
                ProofId::new(CALLER_RESTATEMENT),
                ObligationKind::TemporalSafety,
                ProofStatus::Discharged,
                "f relies on g being data-race free",
            )
            .with_function(g),
        );
        m.proof_certificates.push(ProofCertificate {
            obligation: ProofId::new(CALLER_RESTATEMENT),
            prover: "compose".to_string(),
            evidence: ProofEvidence::InheritedFromCallee {
                callee: g,
                obligation: ProofId::new(CALLEE_TEMPORAL),
                external: None,
            },
            assurance: None,
        });
        let mut wanted = vec![discharged_without_certificate(CALLER_RESTATEMENT)];
        if callee_status == ProofStatus::Discharged {
            wanted.push(discharged_without_certificate(CALLEE_TEMPORAL));
        }
        assert_refused_with_or_without_claims(&m, &wanted);
    }
}

/// The read-modify-write atomics carry the claims too: `Discharged` rows
/// sited on a claim-carrying `AtomicRMW` and `CmpXchg` are refused by name,
/// and the `Pending` twin of the same module validates (so the atomics and
/// their claims are themselves admissible).
#[test]
fn ws2_26_review_rmw_and_cmpxchg_claims_ground_nothing() {
    use trust_ir::inst::AtomicRMWOp;
    let build = |status: ProofStatus| {
        let mut mb = ModuleBuilder::new_with_target_info("ws2_26_rmw_cmpxchg", target());
        let ft = mb.add_func_type(vec![], vec![Ty::U64]);
        let mut fb = mb.function("h", ft);
        fb.set_producer(Producer::TRust);
        let entry = fb.create_block();
        fb.switch_to_block(entry);
        let slot = fb.alloca(Ty::U64);
        let one = fb.uconst(Ty::U64, 1);
        let old = fb.atomic_rmw(AtomicRMWOp::Add, Ty::U64, slot, one, Ordering::AcqRel);
        let two = fb.uconst(Ty::U64, 2);
        let _ = fb.cmpxchg(Ty::U64, slot, old, two, Ordering::SeqCst, Ordering::Acquire);
        fb.ret(vec![old]);
        let h = fb.build();
        let mut m = mb.build().expect("ModuleBuilder::build: test fixture");
        let mut sites = Vec::new();
        for (index, node) in m.functions[0].blocks[0].body.iter_mut().enumerate() {
            let ordering = match node.inst {
                Inst::AtomicRMW { ordering, .. } => ordering,
                Inst::CmpXchg { success, .. } => success,
                _ => continue,
            };
            node.proofs.push(ProofAnnotation::DataRaceFree);
            node.proofs.push(ProofAnnotation::AtomicOrdering(ordering));
            sites.push(index as u32);
        }
        assert_eq!(sites.len(), 2);
        m.functions[0].proofs.extend(concurrency_claims());
        let mut next = 0u32;
        for site in sites {
            for kind in [ObligationKind::TemporalSafety, ObligationKind::Ownership] {
                m.proof_obligations.push(
                    ProofObligation::new(ProofId::new(next), kind, status, "atomic is race free")
                        .with_function(h)
                        .with_site(ObligationSite::new(h, BlockId::new(0), site)),
                );
                next += 1;
            }
        }
        m
    };
    for errors in verdicts(&build(ProofStatus::Pending)) {
        assert_eq!(errors, vec![]);
    }
    let refused = build(ProofStatus::Discharged);
    let wanted: Vec<_> = (0..4).map(discharged_without_certificate).collect();
    for errors in verdicts(&refused) {
        assert_eq!(errors, wanted);
    }
    assert_refused_with_or_without_claims(&refused, &wanted);
}

/// The builder door synthesizes like `Module::add_function`: a function-level
/// `DataRaceFree` (and every `AtomicOrdering`) added through
/// `FunctionBuilder::add_function_proof`, plus node-level claims through
/// `annotate_last`, yields no `Discharged` row and no certificate.
#[test]
fn ws2_26_review_builder_synthesis_mints_no_discharged_row() {
    let mut mb = ModuleBuilder::new_with_target_info("ws2_26_builder_synthesis", target());
    let ft = mb.add_func_type(vec![], vec![]);
    let mut fb = mb.function("f", ft);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    let slot = fb.alloca(Ty::U64);
    let seven = fb.uconst(Ty::U64, 7);
    fb.atomic_store(Ty::U64, slot, seven, Ordering::Release);
    fb.annotate_last(ProofAnnotation::DataRaceFree)
        .expect("a node was emitted");
    fb.annotate_last(ProofAnnotation::AtomicOrdering(Ordering::Release))
        .expect("a node was emitted");
    for claim in concurrency_claims() {
        fb.add_function_proof(claim);
    }
    fb.ret(vec![]);
    fb.build();
    let m = mb.build().expect("ModuleBuilder::build: test fixture");
    assert!(m.proof_certificates.is_empty());
    assert!(
        m.proof_obligations
            .iter()
            .all(|row| row.status == ProofStatus::Pending),
        "{:?}",
        m.proof_obligations
    );
    assert!(
        validate_module(&m)
            .iter()
            .all(|e| !matches!(e, ValidationError::DischargedWithoutCertificate { .. })),
    );
}

/// Across a link edge the claims buy nothing either. An importer whose sole
/// dependency is the claim-carrying module with uncertified `Discharged`
/// concurrency rows is refused `ImportedModuleInvalid`, naming the
/// dependency's first `DischargedWithoutCertificate`; the same edge to the
/// `Pending` dependency links clean (so the edge itself is authentic), and
/// stripping every claim from the bad dependency leaves the verdict identical.
#[test]
fn ws2_26_review_dependency_with_claim_only_discharged_rows_does_not_link() {
    use trust_ir::{IdentityScheme, ModuleImport};
    let link = |dependency: &Module| {
        let mut importer = Module::new("ws2_26_importer");
        importer.target_info = Some(target());
        importer.imports.push(ModuleImport {
            name: dependency.name.clone(),
            digest: dependency.stable_digest(),
            producer: Some(Producer::TRust),
            scheme: IdentityScheme::CURRENT,
        });
        let resolver = |_import: &ModuleImport| Some(dependency);
        validate_linked_module(&importer, &resolver, &RejectingModuleProofAuthority).into_errors()
    };
    assert_eq!(link(&fixture(ProofStatus::Pending)), vec![]);
    let refused = fixture(ProofStatus::Discharged);
    let errors = link(&refused);
    assert_eq!(
        errors,
        vec![ValidationError::ImportedModuleInvalid {
            import: 0,
            errors: 2,
            first: discharged_without_certificate(TEMPORAL_ROW).to_string(),
        }]
    );
    assert_eq!(link(&without_concurrency_claims(&refused)), errors);
}
