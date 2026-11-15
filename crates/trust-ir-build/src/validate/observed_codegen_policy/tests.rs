// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Authored UNRUN; each entire actual original leaf is the oracle.
#![allow(
    clippy::drop_non_drop,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
use std::{cell::Cell, rc::Rc};
use trust_ir::inst::{AssertKind, PanicLocation, PanicSite};
use trust_ir::interpret::InterpretOptions;
use trust_ir::{Block, FuncTyId, InstrNode};
mod custody;
mod error_precedence;
mod parity;
mod stops;
#[derive(Default)]
struct Observer {
    events: Vec<ExecutionProgress>,
    calls: Rc<Cell<usize>>,
    stop: Option<usize>,
    arm: Option<Rc<Cell<bool>>>,
    cleanup: Option<Rc<Cell<bool>>>,
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
            return Err("original codegen policy stop");
        }
        if self.arm.as_ref().is_some_and(|a| a.get()) {
            return Err("interrupt");
        }
        if self.cleanup.as_ref().is_some_and(|a| a.get())
            && e.phase == ExecutionPhase::ScratchRetirement
        {
            return Err("cleanup");
        }
        self.work = self.work.checked_add(e.work).ok_or("overflow")?;
        self.bytes = self.bytes.checked_add(e.copy_bytes).ok_or("overflow")?;
        if self.work_cap.is_some_and(|c| self.work > c) {
            return Err("work");
        }
        if self.byte_cap.is_some_and(|c| self.bytes > c) {
            return Err("copy");
        }
        Ok(())
    }
}
fn site() -> ExecutionSite {
    ExecutionSite::Entry(FuncId::new(7901))
}
fn fixture() -> Module {
    let mut m = Module::new("policy");
    m.global_asm = vec!["".into(), "raw λ assembly".repeat(5)];
    for id in [9, 1, 9] {
        let mut f = Function::new(
            FuncId::new(id),
            format!("whole λ {id}"),
            FuncTyId::new(0),
            BlockId::new(0),
        );
        f.body_gate = Some(trust_ir::BodyGate::gated("clean-kernel-tv"));
        for b in [7, 0] {
            let mut block = Block::new(BlockId::new(b));
            block
                .body
                .push(InstrNode::new(Inst::Return { values: vec![] }));
            block.body.push(InstrNode::new(Inst::Assert {
                cond: ValueId::new(0),
                kind: AssertKind::Unspecified,
                site: None,
            }));
            block.body.push(InstrNode::new(Inst::Assert {
                cond: ValueId::new(0),
                kind: AssertKind::DivByZero,
                site: Some(PanicSite {
                    entry: FuncId::new(99),
                    location: PanicLocation::Value(ValueId::new(4)),
                }),
            }));
            f.blocks.push(block);
        }
        m.functions.push(f);
    }
    m
}
fn expected(m: &Module, rule: Rule) -> Vec<ValidationError> {
    match rule {
        Rule::GateEvidence => unevidenced_gate_errors(m),
        Rule::GlobalAsm => codegen_global_asm_errors(m),
        Rule::PanicKinds => unspecified_assert_kind_errors(m),
        Rule::PanicSites => missing_panic_site_errors(m),
    }
}
fn rules() -> [Rule; 4] {
    [
        Rule::GateEvidence,
        Rule::GlobalAsm,
        Rule::PanicKinds,
        Rule::PanicSites,
    ]
}
fn run(m: &Module, rule: Rule) -> (Vec<ValidationError>, Observer, usize) {
    let mut o = Observer::default();
    let calls = o.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let actual = codegen_policy_errors_observed(m, rule, &mut s, site()).unwrap();
    let end = calls.get();
    assert_eq!(actual, expected(m, rule));
    let copy = actual.clone();
    retire_validation_errors_observed(actual, &mut s, site()).unwrap();
    assert!(s.first_refusal().is_none());
    assert_eq!(s.remaining_fuel(), InterpretOptions::default().fuel);
    drop(s);
    assert!(o.events.iter().all(|e| e.site == site()));
    (copy, o, end)
}
fn drain<O: ExecutionObserver>(state: &mut State, w: &mut Work<'_, '_, O>) {
    state.retire_scratch(w);
    w.record(1, size_of::<Vec<ValidationError>>());
    let _ = retire_validation_errors_observed(take(&mut state.errors), w.session, w.site);
}
fn empty(state: &State) {
    assert!(state.pending.is_none());
    assert_eq!(state.text.capacity() + state.errors.capacity(), 0);
}
