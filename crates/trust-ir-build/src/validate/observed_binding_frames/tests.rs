// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Ordinary/observed parity, CFG and resource-custody regression controls.
use super::*;
use std::{cell::Cell, rc::Rc};
use trust_ir::inst::{BindingFrameDef, BindingSlot};
use trust_ir::interpret::InterpretOptions;
use trust_ir::value::{BindingFrameId, FuncTyId, PredId, TyId};
use trust_ir::{Block, InstrNode};
mod cfg;
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
    cleanup_stop: Option<Rc<Cell<bool>>>,
}
impl ExecutionObserver for Observer {
    type Refusal = &'static str;
    fn admit(&mut self, event: ExecutionProgress) -> Result<(), Self::Refusal> {
        self.events.push(event);
        if self.stop == Some(self.events.len()) {
            return Err("original frame stop");
        }
        if event.phase == ExecutionPhase::ScratchRetirement
            && self.cleanup_stop.as_ref().is_some_and(|armed| armed.get())
        {
            return Err("original frame cleanup stop");
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
    ExecutionSite::Entry(FuncId::new(81))
}
fn v(id: u32) -> ValueId {
    ValueId::new(id)
}
fn b(id: u32) -> BlockId {
    BlockId::new(id)
}
fn function(nodes: Vec<InstrNode>) -> Function {
    let mut f = Function::new(FuncId::new(81), "frames", FuncTyId::new(0), b(0));
    let mut block = Block::new(b(0));
    block.params = vec![(v(10), Ty::U32), (v(11), Ty::I32)];
    block.body = nodes;
    f.blocks.push(block);
    f
}
fn open(frame: u32, types: Vec<Ty>, value: u32) -> InstrNode {
    InstrNode::new(Inst::OpenFrame {
        def: BindingFrameDef::new(
            BindingFrameId::new(frame),
            "frame",
            types
                .into_iter()
                .enumerate()
                .map(|(i, ty)| BindingSlot::new(i.to_string(), ty))
                .collect(),
        ),
    })
    .with_result(v(value))
}
fn bind(frame: u32, slot: u32, value: u32, result: u32) -> InstrNode {
    InstrNode::new(Inst::BindSlot {
        frame: v(frame),
        slot,
        value: v(value),
    })
    .with_result(v(result))
}
fn load(frame: u32, slot: u32, ty: Ty) -> InstrNode {
    InstrNode::new(Inst::LoadSlot {
        frame: v(frame),
        slot,
        ty,
    })
}
fn close(frame: u32) -> InstrNode {
    InstrNode::new(Inst::CloseFrame { frame: v(frame) })
}
fn fixture() -> Function {
    function(vec![
        open(0, vec![Ty::U32], 1),
        bind(1, 0, 11, 2),
        close(1),
        load(1, 0, Ty::I32),
        bind(99, 0, 10, 4),
        close(99),
        close(1),
    ])
}
fn run(f: &Function) -> (Vec<ValidationError>, Observer) {
    let mut observer = Observer::default();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    let result = validate_function_binding_frames_observed(f, &mut session, site()).unwrap();
    assert!(session.first_refusal().is_none());
    assert_eq!(session.remaining_fuel(), InterpretOptions::default().fuel);
    (result, observer)
}
fn parity(f: &Function) -> Vec<ValidationError> {
    let (actual, observer) = run(f);
    assert_eq!(actual, validate_binding_frames(f));
    assert!(observer.events.iter().all(|e| e.site == site()));
    assert_eq!(
        observer.events.last().unwrap().phase,
        ExecutionPhase::Publication
    );
    actual
}
