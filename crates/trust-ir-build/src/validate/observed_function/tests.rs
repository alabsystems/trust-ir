// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
use trust_ir::interpret::InterpretOptions;
use trust_ir::{Block, FunctionSummary, InlinedAt, InstrNode, ScopeData, SourceSpan, Visibility};
mod parity;
mod stops;
#[derive(Default)]
struct Observer {
    events: Vec<ExecutionProgress>,
    stop_at: Option<usize>,
    work: usize,
    bytes: usize,
    work_cap: Option<usize>,
    byte_cap: Option<usize>,
}
impl ExecutionObserver for Observer {
    type Refusal = &'static str;
    fn admit(&mut self, event: ExecutionProgress) -> Result<(), Self::Refusal> {
        self.events.push(event);
        if self.stop_at == Some(self.events.len()) {
            return Err("interior");
        }
        self.work = self.work.checked_add(event.work).ok_or("overflow")?;
        self.bytes = self.bytes.checked_add(event.copy_bytes).ok_or("overflow")?;
        if self.work_cap.is_some_and(|cap| self.work > cap) {
            return Err("work");
        }
        if self.byte_cap.is_some_and(|cap| self.bytes > cap) {
            return Err("bytes");
        }
        Ok(())
    }
}
#[derive(Clone, Copy)]
enum Case {
    Structure,
    BodyGate,
    Symbols,
}
fn site() -> ExecutionSite {
    ExecutionSite::Entry(FuncId::new(81))
}
fn fixture() -> Function {
    let mut f = Function::new(
        FuncId::new(81),
        "observed",
        trust_ir::FuncTyId::new(0),
        BlockId::new(7),
    );
    let mut block = Block::new(BlockId::new(0)).with_param(ValueId::new(3), Ty::Bool);
    block.body = vec![
        InstrNode::new(Inst::Return { values: vec![] }).with_scope(9),
        InstrNode::new(Inst::NullPtr).with_result(ValueId::new(5)),
    ];
    f.blocks = vec![block.clone(), block];
    f.value_names = Some(vec![
        (ValueId::new(3), "p".into()),
        (ValueId::new(5), "result".into()),
        (ValueId::new(99), "unknown".into()),
        (ValueId::new(99), "duplicate".into()),
    ]);
    let link = InlinedAt {
        span: SourceSpan {
            file: 0,
            line: 1,
            col: 1,
        },
        callee: String::new(),
    };
    f.scopes = Some(vec![
        ScopeData {
            parent: Some(0),
            span: None,
            inlined_at: Some(link.clone()),
        },
        ScopeData {
            parent: Some(1),
            span: None,
            inlined_at: Some(link),
        },
    ]);
    f.body_gate = Some(trust_ir::BodyGate::Gated {
        authority: " \u{2003}".into(),
        evidence: None,
    });
    f.display_path = Some("path\ncomponent".into());
    f.section = Some("section\0name".into());
    f.linkage = Linkage::Internal;
    f.visibility = Visibility::Hidden;
    f
}
fn run(
    f: &Function,
    case: Case,
    session: &mut ObservedSession<'_, Observer>,
) -> R<Vec<ValidationError>> {
    match case {
        Case::Structure => validate_function_structure_observed(f, session, site()),
        Case::BodyGate => validate_function_body_gate_observed(f, session, site()),
        Case::Symbols => validate_function_symbol_attributes_observed(f, session, site()),
    }
}
fn observed(f: &Function, case: Case) -> (Vec<ValidationError>, Observer) {
    let mut observer = Observer::default();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    let output = run(f, case, &mut session).unwrap();
    assert!(session.first_refusal().is_none());
    assert_eq!(session.remaining_fuel(), InterpretOptions::default().fuel);
    (output, observer)
}
fn ordinary(f: &Function, case: Case) -> Vec<ValidationError> {
    match case {
        Case::Structure => validate_structure(f),
        Case::BodyGate => validate_body_gate(f),
        Case::Symbols => validate_function_symbol_attributes(f),
    }
}
fn assert_parity(f: &Function, case: Case) {
    let (actual, observer) = observed(f, case);
    assert_eq!(actual, ordinary(f, case));
    assert_eq!(
        observer.events.last().unwrap().phase,
        ExecutionPhase::Publication
    );
    assert!(observer.events.iter().all(|e| e.site == site()));
}
