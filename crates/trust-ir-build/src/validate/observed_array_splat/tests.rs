// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Authored UNRUN; actual original ArraySplat helper, never full module validity.
#![allow(
    clippy::drop_non_drop,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
use std::{cell::Cell, rc::Rc};
use trust_ir::interpret::InterpretOptions;
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
            return Err("original array-splat stop");
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
    ExecutionSite::Entry(FuncId::new(1291))
}
fn v(n: u32) -> ValueId {
    ValueId::new(n)
}
fn array(len: u64) -> Inst {
    Inst::ArraySplat {
        ty: Ty::Array(TyId::new(0), len),
        value: v(0),
    }
}
fn fixture(actual: Ty) -> Module {
    let mut m = Module::new("");
    m.types = vec![Ty::Bool, Ty::U64, Ty::Refine(TyId::new(0), PredId::new(0))];
    m.func_types = vec![FuncTy::unrecorded(vec![actual.clone()], vec![], false)];
    let mut f = Function::new(
        FuncId::new(1291),
        "array_splat",
        FuncTyId::new(0),
        BlockId::new(1),
    );
    let mut b = Block::new(f.entry);
    b.params = vec![(v(0), actual)];
    b.body.push(InstrNode::new(Inst::Return { values: vec![] }));
    f.blocks.push(b);
    m.functions.push(f);
    m
}
fn original(m: &Module, inst: &Inst, block: BlockId) -> Vec<ValidationError> {
    let mut errors = Vec::new();
    if let Inst::ArraySplat { ty, value } = inst {
        validate_array_splat(
            &mut errors,
            m,
            block.index(),
            ty,
            *value,
            &build_module_value_types(&m.functions[0], m),
        );
    }
    errors
}
fn setup<O: ExecutionObserver>(m: &Module, s: &mut ObservedSession<'_, O>) -> ObservedValueTypes {
    build_module_value_types_observed(&m.functions[0], m, s, site()).unwrap()
}
fn run(m: &Module, inst: &Inst) -> (Vec<ValidationError>, Observer, usize, usize) {
    run_block(m, inst, BlockId::new(1))
}
fn run_block(
    m: &Module,
    inst: &Inst,
    block: BlockId,
) -> (Vec<ValidationError>, Observer, usize, usize) {
    let expected = original(m, inst, block);
    let mut o = Observer::default();
    let calls = o.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let values = setup(m, &mut s);
    let begin = calls.get();
    let out = validate_array_splat_observed(m, inst, &values, block, &mut s, site()).unwrap();
    let end = calls.get();
    assert_eq!(out, expected);
    retire_validation_errors_observed(out, &mut s, site()).unwrap();
    values.retire_observed(&mut s, site()).unwrap();
    assert!(s.first_refusal().is_none());
    assert_eq!(s.remaining_fuel(), InterpretOptions::default().fuel);
    drop(s);
    assert!(o.events.iter().all(|e| e.site == site()));
    (expected, o, begin, end)
}
fn empty(s: &State) {
    assert_eq!(
        s.ty.capacity()
            + s.reason.capacity()
            + s.op.capacity()
            + s.role.capacity()
            + s.expected.capacity()
            + s.actual.capacity()
            + s.location.capacity()
            + s.spelling.capacity()
            + s.errors.capacity(),
        0
    )
}
fn drain<O: ExecutionObserver>(s: &mut State, work: &mut Work<'_, '_, O>) {
    s.retire(work);
    let _ = retire_validation_errors_observed(take(&mut s.errors), work.session, work.site);
}
