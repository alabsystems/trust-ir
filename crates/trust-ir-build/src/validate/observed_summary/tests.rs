// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Authored UNRUN: the complete original function is the independent oracle.
use super::*;
use std::{cell::Cell, rc::Rc};
use trust_ir::interpret::{InstructionSite, InterpretOptions};
use trust_ir::proof::{
    ClauseBinding, ClausePlace, ClauseSort, ObligationKind, ProofFormula, ProofObligation,
    ProofStatus,
};
use trust_ir::value::{FuncTyId, ImportId, ProofId};
use trust_ir::{Block, ExternRef, FuncTy, ModuleImport};
mod custody;
mod parity;
mod stops;
#[derive(Default)]
struct Observer {
    events: Vec<ExecutionProgress>,
    stop: Option<usize>,
    work: usize,
    bytes: usize,
    work_cap: Option<usize>,
    byte_cap: Option<usize>,
    cleanup: Option<Rc<Cell<bool>>>,
}
impl ExecutionObserver for Observer {
    type Refusal = &'static str;
    fn admit(&mut self, e: ExecutionProgress) -> Result<(), Self::Refusal> {
        self.events.push(e);
        if self.stop == Some(self.events.len()) {
            return Err("original whole-summary stop");
        }
        if self.cleanup.as_ref().is_some_and(|arm| arm.get())
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
    ExecutionSite::Entry(FuncId::new(200))
}
fn fixture() -> (Module, Function, FunctionSummary) {
    let mut m = Module::new("whole summary");
    m.func_types
        .push(FuncTy::unrecorded(vec![Ty::Bool], vec![Ty::U8], false));
    let mut f = Function::new(FuncId::new(23), "f", FuncTyId::new(0), BlockId::new(0));
    f.blocks.push(Block::new(BlockId::new(0)));
    m.functions.push(f.clone());
    (m, f, FunctionSummary::new())
}
fn mixed() -> (Module, Function, FunctionSummary) {
    let (m, f, mut s) = fixture();
    s.proved = true;
    let c = ProofFormula::new(" ", "opaque");
    s.requires = vec![c.clone(), c];
    s.backed_by = Some(ExternRef::new(ImportId::new(u32::MAX), "raw"));
    (m, f, s)
}
fn run(
    m: &Module,
    f: &Function,
    s: &FunctionSummary,
    policy: ImportPolicy<'_>,
) -> (Vec<ValidationError>, Observer) {
    let mut o = Observer::default();
    let mut owner = ObservedSession::new(InterpretOptions::default(), &mut o);
    let actual = validate_function_summary_observed(m, f, s, policy, &mut owner, site()).unwrap();
    assert_eq!(
        actual,
        super::super::validate_function_summary(m, f, s, policy)
    );
    assert!(owner.first_refusal().is_none());
    assert_eq!(owner.remaining_fuel(), InterpretOptions::default().fuel);
    assert!(o.events.iter().all(|e| e.site == site()));
    assert_eq!(o.events.last().unwrap().phase, ExecutionPhase::Publication);
    (actual, o)
}
/// For a private linked-module fixture: compare complete ordinary results;
/// no test fixture or stored outcome produces proof/import admission evidence.
pub(crate) fn assert_ordinary(
    m: &Module,
    f: &Function,
    s: &FunctionSummary,
    policy: ImportPolicy<'_>,
) -> Vec<ValidationError> {
    run(m, f, s, policy).0
}
fn raw_trace(m: &Module, f: &Function, s: &FunctionSummary, policy: ImportPolicy<'_>) -> Observer {
    let mut o = Observer::default();
    let mut owner = ObservedSession::new(InterpretOptions::default(), &mut o);
    let mut w = Work {
        session: &mut owner,
        site: site(),
    };
    let mut state = State::default();
    state.run(m, f, s, policy, &mut w).unwrap();
    assert_eq!(
        state.errors,
        super::super::validate_function_summary(m, f, s, policy)
    );
    let out = state.finish(Ok(()), &mut w).unwrap();
    assert_eq!(
        out,
        super::super::validate_function_summary(m, f, s, policy)
    );
    assert!(empty(&state));
    o
}
fn empty(state: &State) -> bool {
    state.errors.capacity() == 0
        && state.batch.is_none()
        && state.pending.is_none()
        && state.imported.is_none()
}
fn error(label: &str) -> ValidationError {
    ValidationError::InvalidFunctionSummary {
        function: 23,
        detail: label.into(),
    }
}
fn row(
    id: u32,
    kind: ObligationKind,
    status: ProofStatus,
    formula: Option<ProofFormula>,
) -> ProofObligation {
    ProofObligation {
        id: ProofId::new(id),
        kind,
        status,
        description: "opaque".into(),
        formula,
        function: Some(FuncId::new(23)),
        source: None,
        site: None,
        spec: None,
    }
}
