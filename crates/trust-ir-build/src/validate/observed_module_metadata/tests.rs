// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Authored UNRUN controls; original reference bodies retained in original.rs.
use super::*;
use std::{cell::Cell, rc::Rc};
use trust_ir::interpret::InterpretOptions;
use trust_ir::proof::{
    DiagnosticSeverity, ObligationDiagnostic, ObligationKind, ProofObligation, ProofStatus,
};
use trust_ir::value::{FuncId, FuncTyId, InlinedAt, ProofId, ScopeData, SourceSpan, ValueId};
use trust_ir::{Block, InstrNode};
mod original;
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
            return Err("original metadata stop");
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
            .ok_or("byte overflow")?;
        if self.work_cap.is_some_and(|n| self.work > n) {
            return Err("work");
        }
        if self.byte_cap.is_some_and(|n| self.bytes > n) {
            return Err("bytes");
        }
        Ok(())
    }
}
fn site() -> ExecutionSite {
    ExecutionSite::Entry(FuncId::new(128))
}
fn span(file: u32) -> SourceSpan {
    SourceSpan {
        file,
        line: 9,
        col: 7,
    }
}
fn diagnostic(id: u32, file: Option<u32>) -> ObligationDiagnostic {
    ObligationDiagnostic {
        obligation: ProofId::new(id),
        severity: DiagnosticSeverity::Error,
        message: "no authority".into(),
        location: file.map(span),
        detail: None,
    }
}
fn obligation(id: u32) -> ProofObligation {
    ProofObligation::new(
        ProofId::new(id),
        ObligationKind::Precondition,
        ProofStatus::Pending,
        "not evidence",
    )
}
fn condbr() -> Inst {
    Inst::CondBr {
        cond: ValueId::new(0),
        then_target: BlockId::new(0),
        then_args: vec![],
        else_target: BlockId::new(0),
        else_args: vec![],
    }
}
fn switch() -> Inst {
    Inst::Switch {
        value: ValueId::new(0),
        default: BlockId::new(0),
        default_args: vec![],
        cases: vec![trust_ir::inst::SwitchCase {
            value: Constant::Int(3),
            target: BlockId::new(0),
            args: vec![],
        }],
        exhaustive_enum_unreachable: false,
    }
}
fn fixture() -> Module {
    let mut m = Module::new("metadata");
    m.files = vec!["one.rs".into(), "two.rs".into()];
    let mut f = Function::new(FuncId::new(7), "body", FuncTyId::new(0), BlockId::new(0));
    f.scopes = Some(vec![
        ScopeData {
            parent: None,
            span: Some(span(3)),
            inlined_at: Some(InlinedAt {
                span: span(4),
                callee: "callee".into(),
            }),
        },
        ScopeData::new(Some(0), Some(span(1))),
    ]);
    f.proofs = vec![
        trust_ir::ProofAnnotation::BranchWeights(vec![]),
        trust_ir::ProofAnnotation::BranchWeights(vec![1, 2]),
    ];
    let mut b = Block::new(BlockId::new(9));
    for (inst, weights, file) in [
        (condbr(), vec![1], 5),
        (switch(), vec![1, 2, 3], 1),
        (Inst::Unreachable, vec![], 6),
    ] {
        let mut n = InstrNode::new(inst);
        n.span = Some(span(file));
        n.proofs
            .push(trust_ir::ProofAnnotation::BranchWeights(weights));
        b.body.push(n);
    }
    f.blocks.push(b);
    m.functions.push(f);
    m.proof_obligations = vec![obligation(4), obligation(1), obligation(4)];
    m.obligation_diagnostics = vec![
        diagnostic(4, Some(7)),
        diagnostic(8, None),
        diagnostic(1, Some(0)),
        diagnostic(8, None),
    ];
    m
}
fn run(m: &Module, kind: Component) -> (Vec<ValidationError>, Observer) {
    let mut o = Observer::default();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let out = component(m, kind, &mut s, site()).unwrap();
    assert_eq!(out, original::run(m, kind));
    assert!(s.first_refusal().is_none());
    assert_eq!(s.remaining_fuel(), InterpretOptions::default().fuel);
    assert!(o.events.iter().all(|e| e.site == site()));
    assert_eq!(o.events.last().unwrap().phase, ExecutionPhase::Publication);
    (out, o)
}
fn drain(state: &mut State, work: &mut Work<'_, '_, impl ExecutionObserver>) {
    state.retire_ids(work);
    let _ = retire_validation_errors_observed(take(&mut state.errors), work.session, work.site);
}
fn empty(state: &State) -> bool {
    state.ids.capacity() == 0 && state.errors.capacity() == 0
}
