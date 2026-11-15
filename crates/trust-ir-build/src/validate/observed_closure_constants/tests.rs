// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Authored UNRUN; actual complete validate_closure_constants is the oracle.
#![allow(
    clippy::drop_non_drop,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
use std::{cell::Cell, rc::Rc};
use trust_ir::interpret::InterpretOptions;
use trust_ir::ty::ClosureTy;
use trust_ir::value::{ClosureTyId, FuncTyId, TyId};
use trust_ir::{Block, InstrNode};
mod custody;
mod parity;
mod stops;
#[derive(Default)]
struct Observer {
    events: Vec<ExecutionProgress>,
    calls: Rc<Cell<usize>>,
    work: Rc<Cell<usize>>,
    bytes: Rc<Cell<usize>>,
    stop: Option<usize>,
    work_cap: Option<usize>,
    byte_cap: Option<usize>,
}
impl ExecutionObserver for Observer {
    type Refusal = &'static str;
    fn admit(&mut self, e: ExecutionProgress) -> Result<(), Self::Refusal> {
        self.events.push(e);
        self.calls.set(self.events.len());
        if self.stop == Some(self.events.len()) {
            return Err("original closure-constant stop");
        }
        self.work
            .set(self.work.get().checked_add(e.work).ok_or("overflow")?);
        self.bytes.set(
            self.bytes
                .get()
                .checked_add(e.copy_bytes)
                .ok_or("overflow")?,
        );
        if self.work_cap.is_some_and(|n| self.work.get() > n) {
            return Err("work");
        }
        if self.byte_cap.is_some_and(|n| self.bytes.get() > n) {
            return Err("copy");
        }
        Ok(())
    }
}

fn site() -> ExecutionSite {
    ExecutionSite::Entry(FuncId::new(1491))
}
fn c(id: u32) -> Ty {
    Ty::Closure(ClosureTyId::new(id))
}
fn closure(captures: Vec<Constant>) -> Constant {
    Constant::Closure {
        func: FuncId::new(9),
        captures,
    }
}
fn global(name: &str, ty: Ty, initializer: Option<Constant>) -> trust_ir::Global {
    trust_ir::Global {
        name: name.into(),
        ty,
        mutable: false,
        initializer,
        linkage: trust_ir::Linkage::External,
        tls: None,
        align: None,
        section: None,
        visibility: trust_ir::Visibility::Default,
        retained: false,
    }
}
fn fixture() -> Module {
    let mut m = Module::new("");
    m.types = vec![Ty::Bool];
    m.closure_types = vec![
        ClosureTy {
            func: FuncTyId::new(0),
            captures: vec![Ty::Bool, Ty::Vector(Box::new(Ty::U8), 2), c(1)],
        },
        ClosureTy {
            func: FuncTyId::new(0),
            captures: vec![Ty::U64],
        },
    ];
    m.globals = vec![global(
        "G",
        c(0),
        Some(closure(vec![
            Constant::Bool(true),
            Constant::Vector(vec![Constant::Int(0), Constant::Int(255)]),
            closure(vec![Constant::Int(7)]),
        ])),
    )];
    m.func_types = vec![FuncTy::unrecorded(vec![], vec![], false)];
    let mut f = Function::new(FuncId::new(1491), "body", FuncTyId::new(0), BlockId::new(7));
    let mut block = Block::new(f.entry);
    block.body = vec![
        InstrNode::new(Inst::Const {
            ty: c(1),
            value: closure(vec![Constant::Int(8)]),
        })
        .with_result(ValueId::new(10)),
        InstrNode::new(Inst::Return { values: vec![] }),
    ];
    f.blocks.push(block);
    m.functions.push(f);
    m
}
fn captures(m: &mut Module) -> &mut Vec<Constant> {
    let Constant::Closure { captures, .. } = m.globals[0].initializer.as_mut().unwrap() else {
        panic!()
    };
    captures
}
fn run(m: &Module) -> (Vec<ValidationError>, Observer, usize) {
    let expected = validate_closure_constants(m);
    let mut o = Observer::default();
    let calls = o.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let out = validate_closure_constants_observed(m, &mut s, site()).unwrap();
    let end = calls.get();
    assert_eq!(out, expected);
    retire_validation_errors_observed(out, &mut s, site()).unwrap();
    assert!(s.first_refusal().is_none());
    assert_eq!(s.remaining_fuel(), InterpretOptions::default().fuel);
    drop(s);
    assert!(o.events.iter().all(|e| e.site == site()));
    (expected, o, end)
}
fn empty(s: &State<'_>) {
    assert!(s.current.is_none());
    assert_eq!(
        s.location.capacity()
            + s.detail.capacity()
            + s.expected.capacity()
            + s.actual.capacity()
            + s.pending.capacity()
            + s.errors.capacity(),
        0
    );
}
fn drain<O: ExecutionObserver>(s: &mut State<'_>, w: &mut Work<'_, '_, O>) {
    s.retire(w);
    let _ = retire_validation_errors_observed(take(&mut s.errors), w.session, w.site);
}
fn symbol() -> Constant {
    Constant::SymbolAddr {
        symbol: "é🦀Symbol中".repeat(300),
        addend: i64::MIN,
    }
}
fn rich_bad() -> Module {
    let mut m = fixture();
    m.globals[0].name = "é🦀Global中".repeat(300);
    captures(&mut m)[0] = symbol();
    captures(&mut m).push(Constant::Uninit);
    m
}
