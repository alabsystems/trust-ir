// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Authored UNRUN; entire actual validate_const_shapes is the oracle.
#![allow(
    clippy::drop_non_drop,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
use std::{cell::Cell, rc::Rc};
use trust_ir::interpret::InterpretOptions;
use trust_ir::value::{FuncTyId, PredId, TyId};
use trust_ir::{Block, Global, InstrNode, Linkage, Visibility};
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
    cleanup: Option<Rc<Cell<bool>>>,
}
impl ExecutionObserver for Observer {
    type Refusal = &'static str;
    fn admit(&mut self, e: ExecutionProgress) -> Result<(), Self::Refusal> {
        self.events.push(e);
        self.calls.set(self.events.len());
        if self.stop == Some(self.events.len()) {
            return Err("original const-shapes stop");
        }
        if self.cleanup.as_ref().is_some_and(|a| a.get())
            && e.phase == ExecutionPhase::ScratchRetirement
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
    ExecutionSite::Entry(FuncId::new(3811))
}
fn v(n: u32) -> ValueId {
    ValueId::new(n)
}
fn global(name: &str, ty: Ty, initializer: Option<Constant>) -> Global {
    Global {
        name: name.into(),
        ty,
        mutable: false,
        initializer,
        linkage: Linkage::Internal,
        tls: None,
        align: None,
        section: None,
        visibility: Visibility::Default,
        retained: false,
    }
}
fn literal(ty: Ty, value: Constant) -> InstrNode {
    InstrNode::new(Inst::Const { ty, value })
}
fn switch(value: ValueId, cases: Vec<Constant>) -> InstrNode {
    InstrNode::new(Inst::Switch {
        value,
        default: BlockId::new(8),
        default_args: vec![],
        cases: cases
            .into_iter()
            .map(|value| trust_ir::inst::SwitchCase {
                value,
                target: BlockId::new(8),
                args: vec![],
            })
            .collect(),
        exhaustive_enum_unreachable: false,
    })
}
fn fixture() -> Module {
    let mut m = Module::new("");
    m.types = vec![Ty::U8, Ty::Bool, Ty::Refine(TyId::new(0), PredId::new(0))];
    m.func_types = vec![
        FuncTy::unrecorded(vec![], vec![], false),
        FuncTy::unrecorded(vec![], vec![Ty::U8], false),
    ];
    m.globals.push(global("G", Ty::U8, Some(Constant::U128(1))));
    let mut f = Function::new(FuncId::new(3811), "body", FuncTyId::new(0), BlockId::new(7));
    let mut block = Block::new(f.entry);
    block.params = vec![(v(1), Ty::U8)];
    block.body = vec![
        literal(Ty::Bool, Constant::Int(9)),
        switch(v(1), vec![Constant::Int(300), Constant::U128(1)]),
        literal(Ty::Char, Constant::Int(0xd800)),
    ];
    f.blocks.push(block);
    m.functions = vec![
        f,
        Function::new(
            FuncId::new(900),
            "sparse",
            FuncTyId::new(1),
            BlockId::new(0),
        ),
    ];
    m
}
fn original(m: &Module, nominal: bool) -> Vec<ValidationError> {
    let layouts = m.layout_table();
    let functions = ModuleFunctionCatalog::new(m);
    let summary = nominal.then(|| m.nominal_type_reachability());
    super::super::validate_const_shapes(&layouts, &functions, summary.as_ref())
}
fn setup<'m, O: ExecutionObserver>(
    m: &'m Module,
    nominal: bool,
    s: &mut ObservedSession<'_, O>,
) -> Option<ObservedNominalTypeReachability<'m>> {
    nominal.then(|| m.nominal_type_reachability_observed(s, site()).unwrap())
}
fn run(m: &Module, nominal: bool) -> (Vec<ValidationError>, Observer, usize, usize) {
    let expected = original(m, nominal);
    let layouts = m.layout_table();
    let functions = ModuleFunctionCatalog::new(m);
    let mut o = Observer::default();
    let calls = o.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let summary = setup(m, nominal, &mut s);
    let begin = calls.get();
    let out =
        validate_const_shapes_observed(&layouts, &functions, summary.as_ref(), &mut s, site())
            .unwrap();
    let end = calls.get();
    assert_eq!(out, expected);
    retire_validation_errors_observed(out, &mut s, site()).unwrap();
    if let Some(summary) = summary {
        summary.retire_observed(&mut s, site()).unwrap();
    }
    assert!(s.first_refusal().is_none());
    assert_eq!(s.remaining_fuel(), InterpretOptions::default().fuel);
    drop(s);
    assert!(o.events.iter().all(|e| e.site == site()));
    (expected, o, begin, end)
}
fn empty(s: &State<'_>) {
    assert!(s.canonical_current.is_none() && s.values.is_none() && s.row.is_none());
    assert_eq!(
        s.location.capacity()
            + s.here.capacity()
            + s.expected.capacity()
            + s.actual.capacity()
            + s.detail.capacity()
            + s.canonical_pending.capacity()
            + s.pending.capacity()
            + s.errors.capacity(),
        0
    );
}
fn drain<O: ExecutionObserver>(state: &mut State<'_>, work: &mut Work<'_, '_, O>) {
    state.retire_scratch(work);
    let _ = retire_validation_errors_observed(take(&mut state.errors), work.session, work.site);
}
