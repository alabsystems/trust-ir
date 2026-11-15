// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Authored UNRUN. Actual ordinary whole-module SeqMap diagnostic projection;
//! no unrelated validation error is treated as full-module success.
#![allow(
    clippy::drop_non_drop,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
use std::{cell::Cell, rc::Rc};
use trust_ir::interpret::InterpretOptions;
use trust_ir::value::{FuncTyId, TyId};
use trust_ir::{Block, InstrNode};
mod custody;
mod parity;
mod stops;
#[derive(Default)]
pub(super) struct Observer {
    pub(super) events: Vec<ExecutionProgress>,
    pub(super) calls: Rc<Cell<usize>>,
    pub(super) work: Rc<Cell<usize>>,
    pub(super) bytes: Rc<Cell<usize>>,
    pub(super) stop: Option<usize>,
    pub(super) cleanup_after: Option<usize>,
    pub(super) work_cap: Option<usize>,
    pub(super) byte_cap: Option<usize>,
}
impl ExecutionObserver for Observer {
    type Refusal = &'static str;
    fn admit(&mut self, e: ExecutionProgress) -> Result<(), Self::Refusal> {
        self.events.push(e);
        self.calls.set(self.events.len());
        if self.stop == Some(self.events.len()) {
            return Err("original SeqMap stop");
        }
        if e.phase == ExecutionPhase::ScratchRetirement
            && self.cleanup_after.is_some_and(|n| self.events.len() > n)
        {
            return Err("cleanup");
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
    ExecutionSite::Entry(FuncId::new(1111))
}
fn fixture() -> Module {
    let mut m = Module::new("");
    m.types = vec![Ty::U64];
    m.func_types = vec![
        FuncTy::unrecorded(vec![Ty::Sequence(TyId::new(0))], vec![], false),
        FuncTy::unrecorded(vec![Ty::RefMut(Box::new(Ty::U64))], vec![], false),
    ];
    let mut f = Function::new(
        FuncId::new(1111),
        "caller",
        FuncTyId::new(0),
        BlockId::new(1),
    );
    let mut b = Block::new(f.entry);
    b.params = vec![(ValueId::new(0), Ty::Sequence(TyId::new(0)))];
    b.body.push(InstrNode::new(Inst::Return { values: vec![] }));
    f.blocks.push(b);
    m.functions = vec![
        f,
        Function::new(FuncId::new(9), "forward", FuncTyId::new(1), BlockId::new(0)),
    ];
    m
}
fn inst() -> Inst {
    Inst::SeqMap {
        ty: Ty::Sequence(TyId::new(0)),
        seq: ValueId::new(0),
        fwd: FuncId::new(9),
    }
}
fn setup<'m, O: ExecutionObserver>(
    m: &'m Module,
    s: &mut ObservedSession<'_, O>,
) -> ModuleFunctionCatalog<'m> {
    ModuleFunctionCatalog::new_observed(m, s, site()).unwrap()
}
fn run(m: &Module, node: &Inst) -> (Vec<ValidationError>, Observer, usize, usize) {
    let mut original = m.clone();
    original.functions[0].blocks[0]
        .body
        .insert(0, InstrNode::new(node.clone()).with_result(ValueId::new(1)));
    let expected: Vec<_> = super::super::validate_module(&original)
        .into_iter()
        .filter(|e| {
            matches!(
                e,
                ValidationError::SeqMapFwdNotFound { .. }
                    | ValidationError::SeqMapTypeNotSequence { .. }
                    | ValidationError::SeqMapFwdSignatureMismatch { .. }
            )
        })
        .collect();
    let mut o = Observer::default();
    let calls = o.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let catalog = setup(m, &mut s);
    let begin = calls.get();
    let out = validate_seq_map_observed(&catalog, node, BlockId::new(1), &mut s, site()).unwrap();
    let end = calls.get();
    assert_eq!(out, expected);
    retire_validation_errors_observed(out, &mut s, site()).unwrap();
    catalog.retire_observed(&mut s, site()).unwrap();
    assert!(s.first_refusal().is_none());
    drop(s);
    assert!(o.events[begin..].iter().all(|e| e.site == site()));
    (expected, o, begin, end)
}
fn empty(s: &State) -> bool {
    s.name.capacity() == 0
        && s.expected.capacity() == 0
        && s.actual.capacity() == 0
        && s.render.capacity() == 0
        && s.pending.is_none()
        && s.errors.capacity() == 0
}
fn drain<O: ExecutionObserver>(state: &mut State, work: &mut Work<'_, '_, O>) {
    state.retire_scratch(work);
    let _ = retire_validation_errors_observed(take(&mut state.errors), work.session, work.site);
}
