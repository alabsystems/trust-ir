// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Authored UNRUN: actual four-child composition, whole batch/row custody.
#![allow(
    clippy::drop_non_drop,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
use std::{cell::Cell, rc::Rc};
use trust_ir::interpret::InterpretOptions;
use trust_ir::proof::{
    FormulaSite, ObligationKind, ProofCertificate, ProofDigest, ProofDigestAlgorithm, ProofFormula,
    ProofObligation, ProofObligationSourceIdentity, ProofStatus, PublicObligationIdentity,
};
use trust_ir::value::ProofId;
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
            return Err("original integrity stop");
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
    ExecutionSite::Entry(FuncId::new(499))
}
fn row(id: u32, kind: ObligationKind, status: ProofStatus) -> ProofObligation {
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
fn public(legacy: bool) -> PublicObligationIdentity {
    PublicObligationIdentity {
        obligation_id: "raw?#".into(),
        semantic_digest: ProofDigest {
            algorithm: if legacy {
                ProofDigestAlgorithm::TrustIrStableV1
            } else {
                ProofDigestAlgorithm::Sha256
            },
            bytes: if legacy { [0; 32] } else { [1; 32] },
        },
    }
}
fn fixture() -> Module {
    let mut m = Module::new("");
    let mut a = row(
        7,
        ObligationKind::Custom {
            namespace: "unadmitted λ\0".into(),
            name: "raw 尾\0full".into(),
        },
        ProofStatus::Failed,
    );
    a.source = Some(
        ProofObligationSourceIdentity::new(" source ", "assertion\0bad").with_public(public(true)),
    );
    let mut b = row(7, ObligationKind::Liveness, ProofStatus::Pending);
    let mut f = ProofFormula::smtlib2("true", "Bool");
    f.payload = "false".into();
    b.formula = Some(f);
    b.source =
        Some(ProofObligationSourceIdentity::new("source", "assertion").with_public(public(false)));
    m.proof_obligations = vec![
        a,
        b,
        row(9, ObligationKind::Postcondition, ProofStatus::Trusted),
    ];
    m.proof_certificates = vec![
        ProofCertificate {
            obligation: ProofId::new(99),
            prover: "ignored".into(),
            evidence: trust_ir::proof::ProofEvidence::Trusted("dangling".into()),
            assurance: None,
        },
        ProofCertificate {
            obligation: ProofId::new(9),
            prover: "ignored".into(),
            evidence: trust_ir::proof::ProofEvidence::Trusted("\u{3000}".into()),
            assurance: None,
        },
    ];
    m
}
fn run(m: &Module) -> (Vec<ValidationError>, Observer, usize) {
    let mut o = Observer::default();
    let calls = o.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let out = validate_module_proof_obligation_integrity_observed(m, &mut s, site()).unwrap();
    assert_eq!(out, super::super::validate_proof_obligation_integrity(m));
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
fn error(label: &str) -> ValidationError {
    ValidationError::FormulaTextsDisagree {
        site: FormulaSite::SpecTemporal {
            machine: format!("machine λ\0{label}"),
            property: format!("property 尾\0{label}"),
        },
    }
}
fn empty(state: &State) -> bool {
    state.errors.capacity() == 0 && state.batch.capacity() == 0 && state.row.is_none()
}
fn drain<O: ExecutionObserver>(state: &mut State, w: &mut Work<'_, '_, O>) {
    state.retire_scratch(w);
    let _ = retire_validation_errors_observed(take(&mut state.errors), w.session, w.site);
}
