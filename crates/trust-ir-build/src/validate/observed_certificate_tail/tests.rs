// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Authored UNRUN: real original certificate-tail decisions, no authority.
#![allow(
    clippy::drop_non_drop,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
use std::{cell::Cell, rc::Rc};
use trust_ir::interpret::InterpretOptions;
use trust_ir::proof::{ObligationKind, ProofCertificate, ProofDigest, ProofDigestAlgorithm};
mod custody;
mod parity;
mod stops;
#[derive(Default)]
struct Observer {
    events: Vec<ExecutionProgress>,
    calls: Rc<Cell<usize>>,
    stop: Option<usize>,
    cleanup_after: Option<usize>,
    work: usize,
    bytes: usize,
    work_cap: Option<usize>,
    byte_cap: Option<usize>,
}
impl ExecutionObserver for Observer {
    type Refusal = &'static str;
    fn admit(&mut self, e: ExecutionProgress) -> Result<(), Self::Refusal> {
        self.events.push(e);
        self.calls.set(self.events.len());
        if self.stop == Some(self.events.len()) {
            return Err("original certificate stop");
        }
        if e.phase == ExecutionPhase::ScratchRetirement
            && self.cleanup_after.is_some_and(|n| self.events.len() > n)
        {
            return Err("cleanup");
        }
        self.work = self.work.checked_add(e.work).ok_or("overflow")?;
        self.bytes = self.bytes.checked_add(e.copy_bytes).ok_or("overflow")?;
        if self.work_cap.is_some_and(|n| self.work > n) {
            return Err("work");
        }
        if self.byte_cap.is_some_and(|n| self.bytes > n) {
            return Err("copy");
        }
        Ok(())
    }
}
fn site() -> ExecutionSite {
    ExecutionSite::Entry(FuncId::new(487))
}
fn row(id: u32, status: ProofStatus, kind: ObligationKind) -> ProofObligation {
    ProofObligation {
        id: ProofId::new(id),
        kind,
        status,
        description: "unread".into(),
        formula: None,
        function: None,
        source: None,
        site: None,
        spec: None,
    }
}
fn cert(id: u32, evidence: ProofEvidence) -> ProofCertificate {
    ProofCertificate {
        obligation: ProofId::new(id),
        prover: "unread".into(),
        evidence,
        assurance: None,
    }
}
fn evidence() -> Vec<ProofEvidence> {
    vec![
        ProofEvidence::SmtProof(vec![0, 255]),
        ProofEvidence::LeanProof("raw λ\0".into()),
        ProofEvidence::KaniHarness("raw 尾\0".into()),
        ProofEvidence::GammaCrownBound {
            epsilon: f64::NAN,
            verified_layers: u32::MAX,
        },
        ProofEvidence::TranslationValidation {
            rule_name: "raw λ\0".into(),
            smt_hash: [255; 32],
        },
        ProofEvidence::Trusted("attributed".into()),
        ProofEvidence::InheritedFromCallee {
            callee: FuncId::new(9),
            obligation: ProofId::new(77),
            external: None,
        },
        ProofEvidence::CleanCic {
            term: vec![255],
            context: vec![],
            lineage: ProofDigest {
                algorithm: ProofDigestAlgorithm::Sha256,
                bytes: [0; 32],
            },
            kernel_recheck: None,
        },
    ]
}
fn kinds() -> Vec<ObligationKind> {
    vec![
        ObligationKind::Precondition,
        ObligationKind::Postcondition,
        ObligationKind::LoopInvariant,
        ObligationKind::TypeInvariant,
        ObligationKind::RefinementType,
        ObligationKind::TranslationValidation,
        ObligationKind::MemorySafety,
        ObligationKind::PanicFreedom,
        ObligationKind::TemporalSafety,
        ObligationKind::Liveness,
        ObligationKind::ArithmeticSafety,
        ObligationKind::BoundsCheck,
        ObligationKind::GiveBackRefinement,
        ObligationKind::Termination,
        ObligationKind::Ownership,
        ObligationKind::Custom {
            namespace: "trust.vc".into(),
            name: "raw λ\0".into(),
        },
    ]
}
fn ordinary(m: &Module) -> Vec<ValidationError> {
    super::super::validate_proof_obligation_integrity(m)
        .into_iter()
        .filter(|e| {
            matches!(
                e,
                ValidationError::DanglingProofCertificate { .. }
                    | ValidationError::GroundCertificateStatusInconsistent { .. }
                    | ValidationError::EvidenceKindMismatch { .. }
                    | ValidationError::TrustedWithoutJustification { .. }
            )
        })
        .collect()
}
fn run(m: &Module) -> (Vec<ValidationError>, Observer, usize) {
    let mut o = Observer::default();
    let calls = o.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let out = validate_module_certificate_integrity_tail_observed(m, &mut s, site()).unwrap();
    assert_eq!(out, ordinary(m));
    let saved = out.clone();
    let bound = calls.get();
    retire_validation_errors_observed(out, &mut s, site()).unwrap();
    assert!(s.first_refusal().is_none());
    assert_eq!(s.remaining_fuel(), InterpretOptions::default().fuel);
    drop(s);
    assert!(o.events.iter().all(|e| e.site == site()));
    assert_eq!(o.events[bound - 1].phase, ExecutionPhase::Publication);
    (saved, o, bound)
}
fn fixture() -> Module {
    let mut m = Module::new("");
    m.proof_obligations = vec![
        row(7, ProofStatus::Failed, ObligationKind::BoundsCheck),
        row(9, ProofStatus::Trusted, ObligationKind::Postcondition),
    ];
    m.proof_certificates = vec![
        cert(99, ProofEvidence::Trusted("dangling".into())),
        cert(
            7,
            ProofEvidence::TranslationValidation {
                rule_name: "ignored".into(),
                smt_hash: [0; 32],
            },
        ),
        cert(9, ProofEvidence::Trusted(" \u{a0}\u{3000}\t\n".into())),
    ];
    m
}
fn empty(state: &State) -> bool {
    state.errors.capacity() == 0
}
fn drain<O: ExecutionObserver>(state: &mut State, w: &mut Work<'_, '_, O>) {
    let _ = retire_validation_errors_observed(take(&mut state.errors), w.session, w.site);
}
