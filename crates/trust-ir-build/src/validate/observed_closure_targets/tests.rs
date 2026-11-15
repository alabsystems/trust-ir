// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Native parity and refusal controls for the actual local closure-target walk.
//! Map parity is never valid SSA/type/target/module/source/proof authority.
#![allow(
    clippy::drop_non_drop,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
use std::{cell::Cell, rc::Rc};
use trust_ir::interpret::InterpretOptions;
use trust_ir::value::{ClosureTyId, FuncTyId};
use trust_ir::{Block, InstrNode};
mod block_parameters;
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
            return Err("original closure target stop");
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
    ExecutionSite::Entry(FuncId::new(1113))
}
fn v(id: u32) -> ValueId {
    ValueId::new(id)
}
fn constant(result: u32, target: u32) -> InstrNode {
    InstrNode::new(Inst::Const {
        ty: Ty::Closure(ClosureTyId::new(0)),
        value: Constant::Closure {
            func: FuncId::new(target),
            captures: vec![],
        },
    })
    .with_result(v(result))
}
fn copy(result: u32, source: u32) -> InstrNode {
    InstrNode::new(Inst::Copy {
        ty: Ty::Closure(ClosureTyId::new(0)),
        operand: v(source),
    })
    .with_result(v(result))
}
fn fixture() -> Function {
    let mut f = Function::new(FuncId::new(1113), "F", FuncTyId::new(0), BlockId::new(1));
    let mut b = Block::new(f.entry);
    b.body = vec![copy(12, 11), copy(11, 10), constant(10, 99)];
    f.blocks.push(b);
    f
}
fn run(f: &Function) -> (Observer, usize) {
    let old = super::super::local_closure_constant_targets(f);
    let mut o = Observer::default();
    let calls = o.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let a = ObservedLocalClosureTargets::new_observed(f, &mut s, site()).unwrap();
    let end = calls.get();
    assert!(core::ptr::eq(a._function, f));
    assert_eq!(a.targets, old);
    for key in old.keys().copied().chain([0, u32::MAX]) {
        assert_eq!(
            a.get_observed(v(key), &mut s, site()).unwrap(),
            old.get(&key).copied()
        );
    }
    a.retire_observed(&mut s, site()).unwrap();
    assert!(s.first_refusal().is_none());
    drop(s);
    assert!(o.events.iter().all(|e| e.site == site()));
    (o, end)
}

#[test]
fn closure_capture_update_preserves_the_observed_target() {
    let mut function = fixture();
    function.blocks[0].body.insert(
        0,
        InstrNode::new(Inst::InsertField {
            ty: Ty::Closure(ClosureTyId::new(0)),
            aggregate: v(12),
            field: 0,
            value: v(91),
        })
        .with_result(v(13)),
    );
    assert_eq!(
        super::super::local_closure_constant_targets(&function).get(&13),
        Some(&FuncId::new(99))
    );
    run(&function);
}

#[test]
fn closure_capture_update_observer_stops_at_every_callback() {
    let mut function = fixture();
    function.blocks[0].body.insert(
        0,
        InstrNode::new(Inst::InsertField {
            ty: Ty::Closure(ClosureTyId::new(0)),
            aggregate: v(12),
            field: 0,
            value: v(91),
        })
        .with_result(v(13)),
    );
    let (_, end) = run(&function);
    for stop in 1..=end {
        let mut observer = Observer {
            stop: Some(stop),
            ..Observer::default()
        };
        let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
        assert!(
            ObservedLocalClosureTargets::new_observed(&function, &mut session, site()).is_err(),
            "construction must refuse at callback {stop}"
        );
        assert!(session.first_refusal().is_some());
    }
}

fn selected_function(right: Option<u32>) -> Function {
    let mut function = fixture();
    let mut entry = Block::new(BlockId::new(2));
    entry.body.push(constant(20, 99));
    if let Some(target) = right {
        entry.body.push(constant(21, target));
    }
    function.blocks.push(entry);
    // The selection precedes its inputs in physical order. A copy chain then
    // requires another fixed-point iteration before its identity is known.
    function.blocks[0].body.insert(
        0,
        InstrNode::new(Inst::Select {
            ty: Ty::Closure(ClosureTyId::new(0)),
            cond: v(30),
            then_val: v(20),
            else_val: v(21),
        })
        .with_result(v(22)),
    );
    function.blocks[0].body.insert(0, copy(23, 22));
    function
}

#[test]
fn closure_select_observed_parity_preserves_only_agreeing_targets() {
    for right in [Some(99), Some(100), None] {
        let function = selected_function(right);
        let targets = super::super::local_closure_constant_targets(&function);
        assert_eq!(
            targets.get(&22).copied(),
            right.filter(|target| *target == 99).map(FuncId::new)
        );
        assert_eq!(targets.get(&23), targets.get(&22));
        run(&function);
    }
}

#[test]
fn closure_select_observer_stops_at_every_callback() {
    let function = selected_function(Some(99));
    let (_, end) = run(&function);
    for stop in 1..=end {
        let mut observer = Observer {
            stop: Some(stop),
            ..Observer::default()
        };
        let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
        assert!(
            ObservedLocalClosureTargets::new_observed(&function, &mut session, site()).is_err(),
            "construction must refuse at callback {stop}"
        );
        assert!(session.first_refusal().is_some());
    }
}
