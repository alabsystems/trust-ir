// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Authored UNRUN; full ordinary obligation-binding pass is the oracle.
#![allow(
    clippy::drop_non_drop,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
use std::{cell::Cell, rc::Rc};
use trust_ir::interpret::{InstructionSite, InterpretOptions};
use trust_ir::proof::{ObligationSite, ProofFormula, ProofStatus};
use trust_ir::value::{FuncTyId, ProofId};
use trust_ir::{Block, InstrNode};
mod custody;
mod parity;
mod stops;
mod types;
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
            return Err("original obligation-binding stop");
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
    ExecutionSite::Instruction(InstructionSite {
        function: FuncId::new(433),
        block: BlockId::new(21),
        instruction_index: 38,
    })
}
fn v(id: u32) -> ValueId {
    ValueId::new(id)
}
fn formula(entries: Vec<(&str, ClausePlace, ClauseSort)>) -> ProofFormula {
    let mut p = ProofFormula::new("opaque", "unparsed");
    p.bindings = entries
        .into_iter()
        .map(|(n, place, sort)| (n.into(), ClauseBinding { place, sort }))
        .collect();
    p
}
fn obligation() -> ProofObligation {
    ProofObligation {
        id: ProofId::new(3),
        kind: ObligationKind::Precondition,
        status: ProofStatus::Pending,
        description: "unread".into(),
        formula: None,
        function: Some(FuncId::new(7)),
        source: None,
        site: None,
        spec: None,
    }
}
fn fixture() -> Module {
    let mut m = Module::new("obligation bindings");
    m.func_types.push(FuncTy::unrecorded(
        vec![
            Ty::U8,
            Ty::RefMut(Box::new(Ty::U16)),
            Ty::Ref(Box::new(Ty::Bool)),
            Ty::PtrMut(Box::new(Ty::I32)),
        ],
        vec![Ty::Bool],
        false,
    ));
    let mut f = Function::new(
        FuncId::new(7),
        "unread name",
        FuncTyId::new(0),
        BlockId::new(0),
    );
    let mut b = Block::new(BlockId::new(0));
    b.params.push((v(4), Ty::U32));
    b.body.push(
        InstrNode::new(Inst::Copy {
            ty: Ty::Bool,
            operand: v(4),
        })
        .with_results([v(5)]),
    );
    f.blocks.push(b);
    m.functions.push(f);
    let mut p = obligation();
    p.formula = Some(formula(vec![(
        "x",
        ClausePlace::Param { index: 2 },
        ClauseSort::Int,
    )]));
    m.proof_obligations.push(p);
    m
}
fn set(m: &mut Module, place: ClausePlace, sort: ClauseSort) {
    m.proof_obligations[0].formula = Some(formula(vec![("x", place, sort)]));
}
fn ordinary(m: &Module) -> Vec<ValidationError> {
    super::super::validate_obligation_bindings(m, &ModuleFunctionCatalog::new(m))
}
fn run(m: &Module) -> (Vec<ValidationError>, Observer, usize) {
    let mut o = Observer::default();
    let calls = o.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let out = validate_module_obligation_bindings_observed(m, &mut s, site()).unwrap();
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
fn prior() -> ValidationError {
    ValidationError::NonCanonicalDrop {
        function: "priorλ\0TAIL".into(),
        block: 27,
        reason: "priorreason尾\0TAIL".into(),
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
    state.detail.capacity() == 0
        && state.render.is_none()
        && state.values.is_none()
        && state.errors.capacity() == 0
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
            namespace: "rawλ\0/namespace".into(),
            name: "raw尾\n/name".into(),
        },
    ]
}
