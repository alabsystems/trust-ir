// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Authored UNRUN source controls.
use super::*;
use std::{cell::Cell, rc::Rc};
use trust_ir::inst::SwitchCase;
use trust_ir::interpret::InterpretOptions;
use trust_ir::{Block, FuncTyId, InstrNode};
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
    fn admit(&mut self, event: ExecutionProgress) -> Result<(), Self::Refusal> {
        self.events.push(event);
        if self.stop == Some(self.events.len()) {
            return Err("original exhaustive stop");
        }
        if event.phase == ExecutionPhase::ScratchRetirement
            && self.cleanup.as_ref().is_some_and(|arm| arm.get())
        {
            return Err("original exhaustive cleanup");
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
fn site() -> ExecutionSite {
    ExecutionSite::Entry(FuncId::new(131))
}
fn v(id: u32) -> ValueId {
    ValueId::new(id)
}
fn case(value: Constant) -> SwitchCase {
    SwitchCase {
        value,
        target: BlockId::new(1),
        args: vec![],
    }
}
fn function(ty: Option<Ty>, cases: Vec<Constant>) -> Function {
    let mut f = Function::new(
        FuncId::new(131),
        "exhaustive-shape",
        FuncTyId::new(0),
        BlockId::new(0),
    );
    let mut entry = Block::new(BlockId::new(0));
    if let Some(ty) = ty {
        entry.params.push((v(0), ty));
    }
    entry.body.push(InstrNode::new(Inst::Switch {
        value: v(0),
        default: BlockId::new(1),
        default_args: vec![],
        cases: cases.into_iter().map(case).collect(),
        exhaustive_enum_unreachable: true,
    }));
    let mut dead = Block::new(BlockId::new(1));
    dead.body.push(InstrNode::new(Inst::Unreachable));
    f.blocks = vec![entry, dead];
    f
}
fn fixture() -> Function {
    let mut f = function(
        Some(Ty::Usize),
        vec![Constant::Int(0), Constant::Int(1i128 << 32)],
    );
    if let Inst::Switch { default_args, .. } = &mut f.blocks[0].body[0].inst {
        default_args.push(v(0));
    }
    f.blocks[1].params.push((v(9), Ty::U32));
    f.blocks[1].body.insert(0, InstrNode::new(Inst::NullPtr));
    f
}
fn run(f: &Function, bits: u32) -> (Vec<ValidationError>, Observer) {
    let mut observer = Observer::default();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    let out =
        validate_function_exhaustive_switch_shape_observed(f, bits, &mut session, site()).unwrap();
    assert!(session.first_refusal().is_none());
    assert_eq!(session.remaining_fuel(), InterpretOptions::default().fuel);
    (out, observer)
}
fn parity(f: &Function, bits: u32) -> Vec<ValidationError> {
    let (out, observer) = run(f, bits);
    assert_eq!(
        out,
        super::super::exhaustive_switch::validate_exhaustive_switch_shape(f, bits)
    );
    assert!(observer.events.iter().all(|event| event.site == site()));
    assert_eq!(
        observer.events.last().unwrap().phase,
        ExecutionPhase::Publication
    );
    out
}
fn reasons(errors: &[ValidationError]) -> Vec<&str> {
    errors
        .iter()
        .map(|e| match e {
            ValidationError::ExhaustiveSwitchDefaultReachable { reason, .. } => reason.as_str(),
            _ => panic!("wrong diagnostic"),
        })
        .collect()
}
fn empty(s: &State<'_>) -> bool {
    s.values.is_none()
        && s.seen.capacity() == 0
        && s.first.capacity() == 0
        && s.second.capacity() == 0
        && s.ty.capacity() == 0
        && s.reason.capacity() == 0
        && s.errors.capacity() == 0
}
