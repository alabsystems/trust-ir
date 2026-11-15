// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Authored UNRUN. Original contiguous final block is the parity oracle.
#![allow(
    clippy::drop_non_drop,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
use std::{cell::Cell, rc::Rc};
use trust_ir::Block;
use trust_ir::interpret::InterpretOptions;
use trust_ir::proof::{ClauseBinding, ClausePlace, ClauseSort, ObligationKind, ProofObligation};
use trust_ir::value::{FuncTyId, ProofId};
mod custody;
mod oracle;
mod parity;
mod stops;
#[derive(Default)]
struct Observer {
    events: Vec<ExecutionProgress>,
    at: Option<usize>,
    work: usize,
    bytes: usize,
    cap: Option<usize>,
    byte_cap: Option<usize>,
    next: Option<Rc<Cell<bool>>>,
    cleanup: bool,
}
impl ExecutionObserver for Observer {
    type Refusal = &'static str;
    fn admit(&mut self, event: ExecutionProgress) -> Result<(), Self::Refusal> {
        self.events.push(event);
        if self.at == Some(self.events.len())
            || self.next.as_ref().is_some_and(|v| v.replace(false))
        {
            return Err("original interior");
        }
        if self.cleanup && event.phase == ExecutionPhase::ScratchRetirement {
            return Err("cleanup");
        }
        self.work = self.work.checked_add(event.work).ok_or("overflow")?;
        self.bytes = self.bytes.checked_add(event.copy_bytes).ok_or("overflow")?;
        if self.cap.is_some_and(|n| self.work > n) {
            return Err("work");
        }
        if self.byte_cap.is_some_and(|n| self.bytes > n) {
            return Err("bytes");
        }
        Ok(())
    }
}
fn site() -> ExecutionSite {
    ExecutionSite::Entry(FuncId::new(157))
}
fn fixture() -> (Module, Function, FunctionSummary) {
    let m = Module::new("summary local");
    let mut f = Function::new(
        FuncId::new(23),
        "not parsed λ",
        FuncTyId::new(99),
        BlockId::new(4),
    );
    f.blocks.push(Block::new(BlockId::new(4)));
    let mut summary = FunctionSummary::new();
    summary.proved = true;
    (m, f, summary)
}
fn formula(text: &str) -> ProofFormula {
    ProofFormula::new("opaque-schema", text)
}
fn row(
    id: u32,
    kind: ObligationKind,
    status: ProofStatus,
    formula: Option<ProofFormula>,
    function: Option<FuncId>,
) -> ProofObligation {
    ProofObligation {
        id: ProofId::new(id),
        kind,
        status,
        description: "ignored".into(),
        formula,
        function,
        source: None,
        site: None,
        spec: None,
    }
}
fn execute(
    m: &Module,
    f: &Function,
    summary: &FunctionSummary,
    citation: SummaryCitation,
) -> (Vec<ValidationError>, Observer) {
    let mut observer = Observer::default();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    let out = validate_function_summary_local_backing_observed(
        m,
        f,
        summary,
        citation,
        &mut session,
        site(),
    )
    .unwrap();
    assert_eq!(out, oracle::ordinary(m, f, summary, citation));
    assert!(session.first_refusal().is_none());
    assert_eq!(session.remaining_fuel(), InterpretOptions::default().fuel);
    drop(session);
    assert!(observer.events.iter().all(|e| e.site == site()));
    assert_eq!(
        observer.events.last().unwrap().phase,
        ExecutionPhase::Publication
    );
    (out, observer)
}
fn details(errors: &[ValidationError]) -> Vec<&str> {
    errors
        .iter()
        .map(|error| match error {
            ValidationError::InvalidFunctionSummary { function, detail } => {
                assert_eq!(*function, 23);
                detail.as_str()
            }
            _ => panic!("outside exact local-summary constituent"),
        })
        .collect()
}
fn mixed() -> (Module, Function, FunctionSummary) {
    let (mut m, f, mut summary) = fixture();
    summary.requires = vec![formula("r"), formula("r")];
    summary.ensures = vec![formula("e")];
    m.proof_obligations.push(row(
        91,
        ObligationKind::Termination,
        ProofStatus::Failed,
        None,
        Some(f.id),
    ));
    (m, f, summary)
}
