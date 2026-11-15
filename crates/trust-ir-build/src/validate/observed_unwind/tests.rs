// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Authored controls, UNRUN.
use super::*;
use trust_ir::inst::{AssertKind, PanicLocation, PanicSite, SwitchCase};
use trust_ir::interpret::InterpretOptions;
use trust_ir::{Block, FuncTyId, InstrNode};
mod parity;
mod stops;
#[derive(Default)]
struct Observer {
    events: Vec<ExecutionProgress>,
    stop_at: Option<usize>,
    work: usize,
    bytes: usize,
    work_cap: Option<usize>,
    byte_cap: Option<usize>,
}
impl ExecutionObserver for Observer {
    type Refusal = &'static str;
    fn admit(&mut self, event: ExecutionProgress) -> Result<(), Self::Refusal> {
        self.events.push(event);
        if self.stop_at == Some(self.events.len()) {
            return Err("original stop");
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
    ExecutionSite::Entry(FuncId::new(93))
}
fn node(instruction: Inst) -> InstrNode {
    InstrNode::new(instruction)
}
fn pad(results: &[u32]) -> InstrNode {
    let mut node = node(Inst::LandingPad {
        is_cleanup: true,
        catch_type_indices: vec![],
    });
    node.results = results.iter().copied().map(ValueId::new).collect();
    node
}
fn block(id: u32, body: Vec<InstrNode>) -> Block {
    let mut block = Block::new(BlockId::new(id));
    block.body = body;
    block
}
fn ret() -> InstrNode {
    node(Inst::Return { values: vec![] })
}
fn branch(target: u32) -> InstrNode {
    node(Inst::Br {
        target: BlockId::new(target),
        args: vec![],
    })
}
fn resume(value: u32) -> InstrNode {
    node(Inst::Resume {
        exn: ValueId::new(value),
    })
}
fn function(blocks: Vec<Block>) -> Function {
    let mut function = Function::new(FuncId::new(93), "unwind", FuncTyId::new(0), BlockId::new(0));
    function.blocks = blocks;
    function
}
fn invokes(normal: u32, unwind: u32) -> Vec<Inst> {
    let normal_dest = BlockId::new(normal);
    let unwind_dest = BlockId::new(unwind);
    vec![
        Inst::Invoke {
            callee: FuncId::new(1),
            args: vec![],
            normal_dest,
            normal_args: vec![],
            unwind_dest,
        },
        Inst::AssertInvoke {
            cond: ValueId::new(0),
            kind: AssertKind::DivByZero,
            site: PanicSite {
                entry: FuncId::new(1),
                location: PanicLocation::Value(ValueId::new(0)),
            },
            normal_dest,
            normal_args: vec![],
            unwind_dest,
        },
        Inst::DropInvoke {
            ty: Ty::Bool,
            ptr: ValueId::new(0),
            normal_dest,
            normal_args: vec![],
            unwind_dest,
        },
        Inst::InvokeIndirect {
            callee: ValueId::new(0),
            sig: FuncTyId::new(0),
            args: vec![],
            calling_conv: CallingConv::C,
            normal_dest,
            normal_args: vec![],
            unwind_dest,
        },
    ]
}
fn fixture() -> Function {
    function(vec![
        block(0, vec![node(invokes(1, 2).remove(0))]),
        block(1, vec![branch(2)]),
        block(2, vec![pad(&[3, 4]), resume(4)]),
        block(3, vec![node(Inst::NullPtr), pad(&[5, 6]), ret()]),
    ])
}
fn observed(function: &Function) -> (Vec<ValidationError>, Observer) {
    let mut observer = Observer::default();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    let errors =
        validate_function_unwind_structure_observed(function, &mut session, site()).unwrap();
    assert!(session.first_refusal().is_none());
    assert_eq!(session.remaining_fuel(), InterpretOptions::default().fuel);
    (errors, observer)
}
fn parity(function: &Function) -> Vec<ValidationError> {
    let (actual, observer) = observed(function);
    assert_eq!(actual, validate_unwind_structure(function));
    assert!(observer.events.iter().all(|event| event.site == site()));
    assert_eq!(
        observer.events.last().unwrap().phase,
        ExecutionPhase::Publication
    );
    actual
}
