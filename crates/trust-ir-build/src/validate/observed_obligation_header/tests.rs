// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Authored UNRUN; fixtures isolate the actual first two ordinary integrity groups.
#![allow(
    clippy::drop_non_drop,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
use std::{cell::Cell, rc::Rc};
use trust_ir::interpret::{InstructionSite, InterpretOptions};
use trust_ir::proof::{ProofObligation, ProofStatus};
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
            return Err("original obligation-header stop");
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
        function: FuncId::new(439),
        block: BlockId::new(37),
        instruction_index: 26,
    })
}
fn row(id: u32, kind: ObligationKind) -> ProofObligation {
    ProofObligation {
        id: ProofId::new(id),
        kind,
        status: ProofStatus::Pending,
        description: "unread".into(),
        formula: None,
        function: None,
        source: None,
        site: None,
        spec: None,
    }
}
fn custom(id: u32, ns: &str, name: &str) -> ProofObligation {
    row(
        id,
        ObligationKind::Custom {
            namespace: ns.into(),
            name: name.into(),
        },
    )
}
fn fixture() -> Module {
    let mut m = Module::new("");
    m.proof_obligations = vec![
        custom(7, "unadmitted", "full name λ\0TAIL"),
        custom(7, "trust.vc", "unused"),
    ];
    m
}
fn run(m: &Module) -> (Vec<ValidationError>, Observer, usize) {
    // These fixtures have no source/formula/certificate/status claims, so the
    // entire original integrity function independently yields only this prefix.
    assert!(m.proof_certificates.is_empty());
    assert!(
        m.proof_obligations
            .iter()
            .all(|p| p.source.is_none() && p.formula.is_none() && p.status == ProofStatus::Pending)
    );
    let mut o = Observer::default();
    let calls = o.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let out = validate_module_proof_obligation_header_observed(m, &mut s, site()).unwrap();
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
        function: "prior λ\0FULL".into(),
        block: 11,
        reason: "prior 尾\0FULL".into(),
    }
}
fn seeded() -> State {
    State {
        errors: vec![prior()],
        ..State::default()
    }
}
fn drain<O: ExecutionObserver>(state: &mut State, work: &mut Work<'_, '_, O>) {
    work.flat(take(&mut state.namespace));
    work.flat(take(&mut state.name));
    let _ = retire_validation_errors_observed(take(&mut state.errors), work.session, work.site);
}
fn empty(state: &State) -> bool {
    state.namespace.capacity() == 0 && state.name.capacity() == 0 && state.errors.capacity() == 0
}
