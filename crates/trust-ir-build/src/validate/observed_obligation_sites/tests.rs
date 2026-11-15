// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Authored UNRUN; exact ordinary scope/site pass is the oracle.
#![allow(
    clippy::drop_non_drop,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
use std::{cell::Cell, rc::Rc};
use trust_ir::inst::{AssertKind, AssertOverflowOp, BinOp};
use trust_ir::interpret::{InstructionSite, InterpretOptions};
use trust_ir::proof::{ObligationKind, ObligationSite, ProofFormula, ProofStatus};
use trust_ir::value::{FuncTyId, ProofId, ValueId};
use trust_ir::{Block, InstrNode};
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
            return Err("original obligation-site stop");
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
    ExecutionSite::Entry(FuncId::new(397))
}
fn obligation(
    id: u32,
    scope: Option<u32>,
    at: Option<(u32, u32, u32)>,
    kind: ObligationKind,
) -> ProofObligation {
    ProofObligation {
        id: ProofId::new(id),
        kind,
        status: ProofStatus::Pending,
        description: "unread description".into(),
        formula: None,
        function: scope.map(FuncId::new),
        source: None,
        site: at.map(|(f, b, i)| ObligationSite::new(FuncId::new(f), BlockId::new(b), i)),
        spec: None,
    }
}
fn function(id: u32, block: u32, inst: Inst) -> Function {
    let mut f = Function::new(
        FuncId::new(id),
        "unread name",
        FuncTyId::new(0),
        BlockId::new(block),
    );
    let mut b = Block::new(BlockId::new(block));
    b.body.push(InstrNode::new(inst));
    f.blocks.push(b);
    f
}
fn fixture() -> Module {
    let mut m = Module::new("obligation sites");
    m.functions
        .push(function(7, 3, Inst::Return { values: vec![] }));
    m.proof_obligations.push(obligation(
        1,
        None,
        Some((7, 3, 0)),
        ObligationKind::ArithmeticSafety,
    ));
    m
}
fn ordinary(m: &Module) -> Vec<ValidationError> {
    super::super::validate_obligation_sites(m, &ModuleFunctionCatalog::new(m))
}
fn run(m: &Module) -> (Vec<ValidationError>, Observer, usize) {
    let mut o = Observer::default();
    let calls = o.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let out = validate_module_obligation_sites_observed(m, &mut s, site()).unwrap();
    assert_eq!(out, ordinary(m));
    let copy = out.clone();
    let bound = calls.get();
    retire_validation_errors_observed(out, &mut s, site()).unwrap();
    assert!(s.first_refusal().is_none());
    assert_eq!(s.remaining_fuel(), InterpretOptions::default().fuel);
    drop(s);
    assert!(o.events.iter().all(|e| e.site == site()));
    assert_eq!(o.events[bound - 1].phase, ExecutionPhase::Publication);
    (copy, o, bound)
}
fn owned_prefix() -> ValidationError {
    ValidationError::NonCanonicalDrop {
        function: "prior owned λ\0TAIL".into(),
        block: 29,
        reason: "prior full reason 尾\0TAIL".into(),
    }
}
fn seeded() -> State {
    State {
        errors: vec![owned_prefix()],
    }
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
            namespace: "custom".into(),
            name: "opaque".into(),
        },
    ]
}
