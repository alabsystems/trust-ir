// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Sixteen authored UNRUN controls; the ordinary physical loop is the oracle.
#![allow(
    clippy::drop_non_drop,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
use std::{cell::Cell, rc::Rc};
use trust_ir::inst::{AllocOrigin, Inst};
use trust_ir::interpret::{InstructionSite, InterpretOptions};
use trust_ir::proof::{ProofDigest, ProofFormula};
use trust_ir::value::{BlockId, FuncId, FuncTyId, ImportId, ProofId};
use trust_ir::{Block, CallingConv, ExternRef, FuncTy, FunctionSummary, InstrNode, ModuleImport};
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
            return Err("original module-contract stop");
        }
        if self.cleanup_after.is_some_and(|at| self.events.len() > at)
            && e.phase == ExecutionPhase::ScratchRetirement
        {
            return Err("cleanup");
        }
        self.work = self.work.checked_add(e.work).ok_or("work overflow")?;
        self.bytes = self
            .bytes
            .checked_add(e.copy_bytes)
            .ok_or("copy overflow")?;
        if self.work_cap.is_some_and(|cap| self.work > cap) {
            return Err("work");
        }
        if self.byte_cap.is_some_and(|cap| self.bytes > cap) {
            return Err("copy");
        }
        Ok(())
    }
}
fn site() -> ExecutionSite {
    ExecutionSite::Entry(FuncId::new(352))
}
fn function(id: u32, name: &str, body: bool) -> Function {
    let mut f = Function::new(FuncId::new(id), name, FuncTyId::new(0), BlockId::new(id));
    f.calling_conv = CallingConv::Rust;
    let mut summary = FunctionSummary::new();
    summary.requires.push(ProofFormula::new(" ", "opaque"));
    summary.effects = Some(trust_ir::EffectSummary::pure());
    f.summary = Some(summary);
    if body {
        let mut block = Block::new(BlockId::new(id));
        block.body.push(InstrNode::new(Inst::HeapAlloc {
            ty: Ty::U8,
            count: None,
            align: None,
            origin: AllocOrigin::RustHeap,
        }));
        f.blocks.push(block);
    }
    f
}
fn fixture() -> Module {
    let mut m = Module::new("physical contract loop");
    m.func_types.push(FuncTy::unrecorded(vec![], vec![], true));
    m.functions.push(function(7, "firstλ\0", true));
    m
}
fn oracle(m: &Module, policy: ImportPolicy<'_>) -> Vec<ValidationError> {
    // Exact original contiguous loop; no complete-module diagnostics added.
    let mut errors = Vec::new();
    for f in &m.functions {
        if let Some(summary) = &f.summary {
            errors.extend(super::super::validate_function_summary(
                m, f, summary, policy,
            ));
            errors.extend(super::super::effects::validate_effect_summary(m, f, policy));
        }
        errors.extend(super::super::validate_rust_abi_is_not_variadic(m, f));
    }
    errors
}
fn run(m: &Module, policy: ImportPolicy<'_>) -> (Vec<ValidationError>, Observer, usize) {
    let expected = oracle(m, policy);
    let mut o = Observer::default();
    let calls = o.calls.clone();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut o);
    let output =
        validate_module_function_contracts_observed(m, policy, &mut session, site()).unwrap();
    assert_eq!(output, expected);
    let copy = output.clone(); // Assertion fixture, not observed implementation.
    let bound = calls.get(); // Actual outer return, before caller disposal.
    retire_validation_errors_observed(output, &mut session, site()).unwrap();
    assert!(session.first_refusal().is_none());
    assert_eq!(session.remaining_fuel(), InterpretOptions::default().fuel);
    drop(session);
    assert!(o.events.iter().all(|e| e.site == site()));
    assert_eq!(o.events[bound - 1].phase, ExecutionPhase::Publication);
    (copy, o, bound)
}
fn summary_error(label: &str) -> ValidationError {
    ValidationError::InvalidFunctionSummary {
        function: 7,
        detail: label.into(),
    }
}
fn prefix() -> ValidationError {
    summary_error("already owned prefix λ\0TAIL")
}
fn child_module() -> Module {
    let mut m = fixture();
    let s = m.functions[0].summary.as_mut().unwrap();
    s.requires = (0..3).map(|_| ProofFormula::new(" ", "opaque")).collect();
    s.effects = None;
    m
}
fn child_expected(m: &Module) -> Vec<ValidationError> {
    let f = &m.functions[0];
    super::super::validate_function_summary(
        m,
        f,
        f.summary.as_ref().unwrap(),
        ImportPolicy::Structural,
    )
}
fn seeded() -> State {
    State {
        errors: vec![prefix()],
        ..State::default()
    }
}
fn capture_child(m: &Module, state: &mut State, work: &mut Work<'_, '_, Observer>) -> R {
    // Same prepare/call/immediate IntoIter assignment as the production loop.
    state.prepare(work)?;
    let f = &m.functions[0];
    state.batch = Some(
        validate_function_summary_observed(
            m,
            f,
            f.summary.as_ref().unwrap(),
            ImportPolicy::Structural,
            work.session,
            work.site,
        )?
        .into_iter(),
    );
    Ok(())
}
fn empty(state: &State) -> bool {
    state.errors.capacity() == 0 && state.pending.is_none() && state.batch.is_none()
}
