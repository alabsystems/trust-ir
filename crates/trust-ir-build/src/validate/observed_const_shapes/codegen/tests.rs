// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Authored UNRUN; actual public ordinary narrow front is the full oracle.
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
            return Err("original narrow switch stop");
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
    ExecutionSite::Entry(FuncId::new(80001))
}
fn v(n: u32) -> ValueId {
    ValueId::new(n)
}
fn switch(value: ValueId, values: Vec<Constant>) -> InstrNode {
    InstrNode::new(Inst::Switch {
        value,
        default: BlockId::new(8),
        default_args: vec![],
        cases: values
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
    m.types = vec![Ty::U8];
    m.func_types = vec![
        FuncTy::unrecorded(vec![], vec![], false),
        FuncTy::unrecorded(vec![], vec![Ty::U8], false),
    ];
    m.globals = vec![Global {
        name: "ignored-global".into(),
        ty: Ty::Bool,
        mutable: false,
        initializer: Some(Constant::Int(7)),
        linkage: Linkage::Internal,
        tls: None,
        align: None,
        section: None,
        visibility: Visibility::Default,
        retained: false,
    }];
    let mut f = Function::new(FuncId::new(99), "caller", FuncTyId::new(0), BlockId::new(7));
    let mut b = Block::new(f.entry);
    b.params = vec![(v(0), Ty::U8), (v(1), Ty::Char)];
    b.body = vec![
        InstrNode::new(Inst::Const {
            ty: Ty::Bool,
            value: Constant::Int(3),
        }),
        switch(v(0), vec![Constant::Int(300), Constant::U128(1)]),
        switch(v(1), vec![Constant::Int(0xd800)]),
    ];
    f.blocks.push(b);
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
fn run(m: &Module) -> (Vec<ValidationError>, Observer, usize) {
    let expected = crate::codegen_switch_case_literal_errors(m);
    let mut o = Observer::default();
    let calls = o.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let out = crate::codegen_switch_case_literal_errors_observed(m, &mut s, site()).unwrap();
    let end = calls.get();
    assert_eq!(out, expected);
    retire_validation_errors_observed(out, &mut s, site()).unwrap();
    assert!(s.first_refusal().is_none());
    drop(s);
    assert!(
        o.events
            .iter()
            .all(|e| e.site == site() || e.phase == ExecutionPhase::ModuleLookup)
    );
    (expected, o, end)
}
fn empty(s: &Front<'_>) {
    assert!(
        s.layouts.is_none()
            && s.catalog.is_none()
            && s.literals.values.is_none()
            && s.literals.canonical_current.is_none()
            && s.literals.row.is_none()
    );
    assert_eq!(
        s.literals.location.capacity()
            + s.literals.here.capacity()
            + s.literals.expected.capacity()
            + s.literals.actual.capacity()
            + s.literals.detail.capacity()
            + s.literals.canonical_pending.capacity()
            + s.literals.pending.capacity()
            + s.literals.errors.capacity(),
        0
    );
}
fn drain<O: ExecutionObserver>(s: &mut Front<'_>, w: &mut Work<'_, '_, O>) {
    s.literals.retire_scratch(w);
    let _ = s.retire_context(w);
    let _ = retire_validation_errors_observed(take(&mut s.literals.errors), w.session, w.site);
}
