// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Authored UNRUN; fixtures isolate the exact original source/public-ID group.
#![allow(
    clippy::drop_non_drop,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
use std::{cell::Cell, rc::Rc};
use trust_ir::interpret::{InstructionSite, InterpretOptions};
use trust_ir::proof::{
    ObligationKind, ProofDigest, ProofObligationSourceRange, ProofStatus, PublicObligationIdentity,
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
    work: usize,
    bytes: usize,
    work_cap: Option<usize>,
    byte_cap: Option<usize>,
    cleanup_after: Option<usize>,
}
impl ExecutionObserver for Observer {
    type Refusal = &'static str;
    fn admit(&mut self, e: ExecutionProgress) -> Result<(), Self::Refusal> {
        self.events.push(e);
        self.calls.set(self.events.len());
        if self.stop == Some(self.events.len()) {
            return Err("original obligation-source stop");
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
        };
        if self.byte_cap.is_some_and(|n| self.bytes > n) {
            return Err("copy");
        };
        Ok(())
    }
}
fn site() -> ExecutionSite {
    ExecutionSite::Instruction(InstructionSite {
        function: FuncId::new(443),
        block: BlockId::new(45),
        instruction_index: 31,
    })
}
fn public(id: &str) -> PublicObligationIdentity {
    PublicObligationIdentity {
        obligation_id: id.into(),
        semantic_digest: ProofDigest {
            algorithm: ProofDigestAlgorithm::Sha256,
            bytes: [1; 32],
        },
    }
}
fn row(id: u32, source: Option<ProofObligationSourceIdentity>) -> ProofObligation {
    ProofObligation {
        id: ProofId::new(id),
        kind: ObligationKind::Liveness,
        status: ProofStatus::Pending,
        description: "unused".into(),
        formula: None,
        function: None,
        source,
        site: None,
        spec: None,
    }
}
fn source(id: &str) -> ProofObligationSourceIdentity {
    ProofObligationSourceIdentity::new("source λ internal", "assertion 尾 internal")
        .with_public(public(id))
}
fn fixture() -> Module {
    let mut m = Module::new("");
    m.files.push("unused filename".into());
    m.proof_obligations = vec![
        row(5, Some(source("public-id"))),
        row(7, Some(source("public-id"))),
    ];
    m
}
fn run(m: &Module) -> (Vec<ValidationError>, Observer, usize) {
    // Exact full ordinary oracle: these fixtures carry unique obligation IDs,
    // no custom kind, formula, certificate or non-Pending status claims.
    assert!(m.proof_certificates.is_empty());
    assert!(m.proof_obligations.iter().all(|p| p.formula.is_none()
        && p.status == ProofStatus::Pending
        && matches!(p.kind, ObligationKind::Liveness)));
    let mut ids = std::collections::BTreeSet::new();
    assert!(m.proof_obligations.iter().all(|p| ids.insert(p.id.index())));
    let mut o = Observer::default();
    let calls = o.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let out = validate_module_obligation_source_observed(m, &mut s, site()).unwrap();
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
fn prior() -> ValidationError {
    ValidationError::NonCanonicalDrop {
        function: "priorλ\0FULL".into(),
        block: 19,
        reason: "prior尾\0FULL".into(),
    }
}
fn seeded() -> State {
    State {
        errors: vec![prior()],
        ..State::default()
    }
}
fn drain<O: ExecutionObserver>(state: &mut State, w: &mut Work<'_, '_, O>) {
    w.flat(take(&mut state.public_id));
    let _ = retire_validation_errors_observed(take(&mut state.errors), w.session, w.site);
}
fn empty(state: &State) -> bool {
    state.public_id.capacity() == 0 && state.errors.capacity() == 0
}
fn bad_source() -> ProofObligationSourceIdentity {
    let mut s = ProofObligationSourceIdentity::new(" source ", "assertion\0bad").with_range(
        ProofObligationSourceRange {
            file: u32::MAX,
            start_line: 1,
            start_col: 4,
            end_line: 0,
            end_col: 1,
        },
    );
    s.public = Some(PublicObligationIdentity {
        obligation_id: "?bad".into(),
        semantic_digest: ProofDigest {
            algorithm: ProofDigestAlgorithm::TrustIrStableV1,
            bytes: [0; 32],
        },
    });
    s
}
