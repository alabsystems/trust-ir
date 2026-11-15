// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Source-authored UNRUN controls; the actual original rule is the oracle.
#![allow(
    clippy::drop_non_drop,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
use std::{cell::Cell, rc::Rc};
use trust_ir::inst::SwitchCase;
use trust_ir::interpret::{InstructionSite, InterpretOptions};
use trust_ir::value::{FuncTyId, StructId};
use trust_ir::{Global, InstrNode};
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
    cleanup: bool,
}
impl ExecutionObserver for Observer {
    type Refusal = &'static str;
    fn admit(&mut self, e: ExecutionProgress) -> Result<(), Self::Refusal> {
        self.events.push(e);
        self.calls.set(self.events.len());
        if self.stop == Some(self.events.len()) {
            return Err("uninit original stop");
        }
        if self.cleanup
            && self.stop.is_some_and(|n| self.events.len() > n)
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
    ExecutionSite::Instruction(InstructionSite {
        function: FuncId::new(811),
        block: BlockId::new(73),
        instruction_index: 29,
    })
}
fn fixture(ty: Ty, value: Constant) -> Module {
    let mut m = Module::new("uninit");
    let mut f = Function::new(
        FuncId::new(7),
        "rawλ'\n\\name",
        FuncTyId::new(0),
        BlockId::new(3),
    );
    let mut b = Block::new(BlockId::new(3));
    b.body.push(InstrNode::new(Inst::Const { ty, value }));
    f.blocks.push(b);
    m.functions.push(f);
    m
}
fn global(name: &str, value: Option<Constant>) -> Global {
    Global {
        name: name.into(),
        ty: Ty::U8,
        mutable: false,
        initializer: value,
        linkage: Linkage::External,
        tls: None,
        align: None,
        section: None,
        visibility: Default::default(),
        retained: false,
    }
}
fn switch(values: Vec<Constant>) -> Inst {
    Inst::Switch {
        value: ValueId::new(0),
        cases: values
            .into_iter()
            .map(|value| SwitchCase {
                value,
                target: BlockId::new(0),
                args: vec![],
            })
            .collect(),
        default: BlockId::new(0),
        default_args: vec![],
        exhaustive_enum_unreachable: false,
    }
}
fn ordinary(m: &Module) -> Vec<ValidationError> {
    super::super::validate_uninit_lanes(m)
}
fn run(m: &Module) -> (Vec<ValidationError>, Observer, usize) {
    let mut o = Observer::default();
    let calls = o.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let out = validate_module_uninit_lanes_observed(m, &mut s, site()).unwrap();
    assert_eq!(out, ordinary(m));
    let saved = out.clone();
    let bound = calls.get();
    retire_validation_errors_observed(out, &mut s, site()).unwrap();
    assert!(s.first_refusal().is_none());
    assert_eq!(s.remaining_fuel(), InterpretOptions::default().fuel);
    drop(s);
    assert!(o.events.iter().all(|e| e.site == site()));
    assert_eq!(o.events[bound - 1].phase, ExecutionPhase::Publication);
    (saved, o, bound)
}
fn carriers(value: Constant) -> Vec<Constant> {
    vec![
        Constant::Aggregate(vec![value.clone()]),
        Constant::Array(vec![value.clone()]),
        Constant::Vector(vec![value.clone()]),
        Constant::Sequence(vec![value.clone()]),
        Constant::Set(vec![value.clone()]),
        Constant::Splat {
            elem: Box::new(value.clone()),
            len: u64::MAX,
        },
        Constant::Record(vec![("raw ignored name".into(), value.clone())]),
        Constant::Closure {
            func: FuncId::new(u32::MAX),
            captures: vec![value],
        },
    ]
}
fn prior() -> ValidationError {
    ValidationError::NonCanonicalDrop {
        function: "priorλ\0TAIL".into(),
        block: 11,
        reason: "prior尾\0TAIL".into(),
    }
}
fn seeded<'a>() -> State<'a> {
    State {
        errors: vec![prior()],
        ..State::default()
    }
}
fn drain<O: ExecutionObserver>(state: &mut State<'_>, work: &mut Work<'_, '_, O>) {
    state.retire_scratch(work);
    let _ = retire_validation_errors_observed(take(&mut state.errors), work.session, work.site);
}
fn empty(state: &State<'_>) -> bool {
    state.frames.capacity() == 0
        && state.pending.is_none()
        && state.location.capacity() == 0
        && state.expected.capacity() == 0
        && state.actual.capacity() == 0
        && state.render.is_none()
        && state.errors.capacity() == 0
}
