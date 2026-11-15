// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Authored UNRUN; original obligation spec-surface pass is the semantic oracle.
#![allow(
    clippy::drop_non_drop,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
use std::{cell::Cell, rc::Rc};
use trust_ir::SpecVar;
use trust_ir::interpret::{InstructionSite, InterpretOptions};
use trust_ir::proof::{ClauseSort, ProofFormula, ProofStatus, SpecObligationRef};
use trust_ir::value::{ProofId, ValueId};
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
    fn admit(&mut self, event: ExecutionProgress) -> Result<(), Self::Refusal> {
        self.events.push(event);
        self.calls.set(self.events.len());
        if self.stop == Some(self.events.len()) {
            return Err("original spec-surface stop");
        }
        if event.phase == ExecutionPhase::ScratchRetirement
            && self.cleanup_after.is_some_and(|n| self.events.len() > n)
        {
            return Err("cleanup");
        }
        self.work = self.work.checked_add(event.work).ok_or("overflow")?;
        self.bytes = self.bytes.checked_add(event.copy_bytes).ok_or("overflow")?;
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
    ExecutionSite::Instruction(InstructionSite {
        function: FuncId::new(417),
        block: BlockId::new(28),
        instruction_index: 53,
    })
}
fn formula(bindings: Vec<(&str, ClausePlace, ClauseSort)>) -> ProofFormula {
    let mut p = ProofFormula::new("unread schema", "unread payload");
    p.bindings = bindings
        .into_iter()
        .map(|(n, place, sort)| (n.into(), ClauseBinding { place, sort }))
        .collect();
    p
}
fn obligation(id: u32, kind: ObligationKind) -> ProofObligation {
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
fn fixture() -> Module {
    let mut m = Module::new("obligation spec surface");
    let mut machine = SpecModule::new("M");
    machine.vars = vec![
        SpecVar::new("x", "Int").with_sort(ClauseSort::Int),
        SpecVar::new("y", "Bool"),
    ];
    machine.temporal.push(SpecTemporal::new(
        "T",
        TemporalForm::Always(ProofFormula::new("opaque", "opaque")),
    ));
    m.spec_modules.push(machine);
    let mut p = obligation(3, ObligationKind::Liveness);
    p.spec = Some(SpecObligationRef::new("M", "T"));
    p.formula = Some(formula(vec![(
        "y",
        ClausePlace::SpecVarNext { index: 0 },
        ClauseSort::Bool,
    )]));
    m.proof_obligations.push(p);
    m
}
fn ordinary(m: &Module) -> Vec<ValidationError> {
    super::super::validate_obligation_spec_surface(m)
}
fn run(m: &Module) -> (Vec<ValidationError>, Observer, usize) {
    let mut o = Observer::default();
    let calls = o.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let out = validate_module_obligation_spec_surface_observed(m, &mut s, site()).unwrap();
    assert_eq!(out, ordinary(m));
    let saved = out.clone();
    let bound = calls.get();
    retire_validation_errors_observed(out, &mut s, site()).unwrap();
    assert!(s.first_refusal().is_none());
    assert_eq!(s.remaining_fuel(), InterpretOptions::default().fuel);
    drop(s);
    assert!(o.events.iter().all(|event| event.site == site()));
    assert_eq!(o.events[bound - 1].phase, ExecutionPhase::Publication);
    (saved, o, bound)
}
fn prior() -> ValidationError {
    ValidationError::NonCanonicalDrop {
        function: "priorλ\0FULL".into(),
        block: 17,
        reason: "prior尾\0FULL".into(),
    }
}
fn seeded() -> State {
    State {
        errors: vec![prior()],
        ..State::default()
    }
}
fn drain<O: ExecutionObserver>(state: &mut State, work: &mut Work<'_, '_, O>) {
    state.retire_scratch(work);
    let _ = retire_validation_errors_observed(take(&mut state.errors), work.session, work.site);
}
fn empty(state: &State) -> bool {
    state.machine.capacity() == 0
        && state.temporal.capacity() == 0
        && state.detail.capacity() == 0
        && state.sort.is_none()
        && state.debug.capacity() == 0
        && state.errors.capacity() == 0
}
fn forms() -> Vec<TemporalForm> {
    let f = || ProofFormula::new("opaque", "opaque");
    vec![
        TemporalForm::Always(f()),
        TemporalForm::Eventually(f()),
        TemporalForm::LeadsTo(f(), f()),
        TemporalForm::WeakFair {
            action: "undeclared unused".into(),
            relation: None,
        },
        TemporalForm::StrongFair {
            action: "undeclared unused".into(),
            relation: None,
        },
    ]
}
fn nested() -> ClauseSort {
    ClauseSort::Datatype {
        name: "Dλ\n\"'\\".repeat(40),
        constructors: vec![(
            "C尾".into(),
            vec![(
                "field\0".into(),
                ClauseSort::Array(
                    Box::new(ClauseSort::BitVec(u32::MAX)),
                    Box::new(ClauseSort::Float {
                        eb: 0,
                        sb: u32::MAX,
                    }),
                ),
            )],
        )],
    }
}
