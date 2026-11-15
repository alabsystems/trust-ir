// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Authored UNRUN; complete actual ordinary purity rule and result_tys oracles.
#![allow(
    clippy::drop_non_drop,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
use std::{cell::Cell, rc::Rc};
use trust_ir::interpret::InterpretOptions;
use trust_ir::ty::ClosureTy;
use trust_ir::value::{FuncTyId, PredId, TyId};
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
            return Err("original closure-purity stop");
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
    ExecutionSite::Entry(FuncId::new(1441))
}
fn v(n: u32) -> ValueId {
    ValueId::new(n)
}
fn c(n: u32) -> Ty {
    Ty::Closure(ClosureTyId::new(n))
}
fn node(inst: Inst, values: &[u32]) -> InstrNode {
    let mut node = InstrNode::new(inst);
    node.proofs.push(ProofAnnotation::Pure);
    node.results = values.iter().copied().map(v).collect();
    node
}
fn fixture() -> Module {
    let mut m = Module::new("");
    m.types = vec![Ty::Bool];
    m.closure_types = vec![
        ClosureTy {
            func: FuncTyId::new(0),
            captures: vec![
                Ty::Bool,
                Ty::Ref(Box::new(Ty::Bool)),
                Ty::PtrConst(Box::new(Ty::Bool)),
            ],
        },
        ClosureTy {
            func: FuncTyId::new(0),
            captures: vec![Ty::Bool, Ty::RefMut(Box::new(Ty::Bool))],
        },
        ClosureTy {
            func: FuncTyId::new(0),
            captures: vec![Ty::PtrMut(Box::new(Ty::Bool))],
        },
        ClosureTy {
            func: FuncTyId::new(0),
            captures: vec![Ty::Rc(Box::new(Ty::Bool))],
        },
        ClosureTy {
            func: FuncTyId::new(0),
            captures: vec![Ty::Tuple(vec![Ty::RefMut(Box::new(Ty::Bool))])],
        },
    ];
    m.func_types = vec![
        FuncTy::unrecorded(vec![c(1)], vec![], false),
        FuncTy::unrecorded(vec![], vec![Ty::Bool, c(2), c(1)], false),
        FuncTy::unrecorded(vec![], vec![c(3), c(0)], false),
    ];
    let mut f = Function::new(FuncId::new(1441), "pure", FuncTyId::new(0), BlockId::new(1));
    f.proofs.push(ProofAnnotation::Pure);
    let mut block = Block::new(f.entry);
    block.body = vec![
        node(Inst::Undef { ty: c(1) }, &[10]),
        InstrNode::new(Inst::Return { values: vec![] }),
    ];
    f.blocks.push(block);
    m.functions = vec![
        f,
        Function::new(FuncId::new(9), "target", FuncTyId::new(1), BlockId::new(0)),
    ];
    m
}
fn run(m: &Module) -> (Vec<ValidationError>, Observer, usize) {
    let expected = validate_closure_purity(m);
    let mut o = Observer::default();
    let calls = o.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let out = validate_closure_purity_observed(m, &mut s, site()).unwrap();
    let end = calls.get();
    assert_eq!(out, expected);
    retire_validation_errors_observed(out, &mut s, site()).unwrap();
    assert!(s.first_refusal().is_none());
    assert_eq!(s.remaining_fuel(), InterpretOptions::default().fuel);
    drop(s);
    assert!(o.events.iter().all(|e| e.site == site()));
    (expected, o, end)
}
fn closure_results(m: &Module, node: &InstrNode) -> Vec<(usize, ClosureTyId)> {
    let expected: Vec<_> = node
        .result_tys(m)
        .into_iter()
        .enumerate()
        .filter_map(|(i, t)| {
            if let Ty::Closure(id) = t {
                Some((i, id))
            } else {
                None
            }
        })
        .collect();
    let mut o = Observer::default();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let out = module_closure_results_observed(m, node, &mut s, site()).unwrap();
    assert_eq!(out, expected);
    Work {
        session: &mut s,
        site: site(),
    }
    .rows(out);
    assert!(s.first_refusal().is_none());
    expected
}
fn empty(s: &State) {
    assert_eq!(
        s.name.capacity() + s.capture.capacity() + s.results.capacity() + s.errors.capacity(),
        0
    );
}
fn drain<O: ExecutionObserver>(s: &mut State, w: &mut Work<'_, '_, O>) {
    s.retire(w);
    let _ = retire_validation_errors_observed(take(&mut s.errors), w.session, w.site);
}
fn rich() -> Module {
    let mut m = fixture();
    m.functions[0].name = "é🦀function".repeat(300);
    m.closure_types[1].captures[1] = Ty::RefMut(Box::new(Ty::Tuple(vec![
        Ty::handle("中Name".repeat(300), "éRuntime".repeat(300)),
        Ty::Bool,
    ])));
    m
}
