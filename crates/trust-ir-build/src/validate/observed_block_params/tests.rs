// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//! Authored source controls, all UNRUN.
use super::*;
use std::cell::Cell;
use std::rc::Rc;
use trust_ir::interpret::InterpretOptions;
use trust_ir::value::{BlockId, FuncId, FuncTyId, PredId, TyId};
use trust_ir::{Block, CallingConv, FatPtrKind, HandleTy, InstrNode};
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
    cleanup_stop: Option<Rc<Cell<bool>>>,
}
impl ExecutionObserver for Observer {
    type Refusal = &'static str;
    fn admit(&mut self, event: ExecutionProgress) -> Result<(), Self::Refusal> {
        self.events.push(event);
        if self.stop_at == Some(self.events.len()) {
            return Err("original block-param stop");
        }
        if event.phase == ExecutionPhase::ScratchRetirement
            && self.cleanup_stop.as_ref().is_some_and(|stop| stop.get())
        {
            return Err("original cleanup stop");
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
    ExecutionSite::Entry(FuncId::new(96))
}
fn v(id: u32) -> ValueId {
    ValueId::new(id)
}
fn b(id: u32) -> BlockId {
    BlockId::new(id)
}
fn function(term: Inst, target_types: Vec<Ty>) -> Function {
    let mut f = Function::new(FuncId::new(96), "block params", FuncTyId::new(0), b(0));
    let mut entry = Block::new(b(0));
    entry.params = vec![(v(0), Ty::U32), (v(1), Ty::I32), (v(2), Ty::Ptr)];
    entry.body.push(InstrNode::new(term));
    f.blocks.push(entry);
    let mut target = Block::new(b(1));
    target.params = target_types
        .into_iter()
        .enumerate()
        .map(|(index, ty)| (v(100 + index as u32), ty))
        .collect();
    target
        .body
        .push(InstrNode::new(Inst::Return { values: vec![] }));
    f.blocks.push(target);
    f
}
fn fixture() -> Function {
    function(
        Inst::Br {
            target: b(1),
            args: vec![v(0), v(1)],
        },
        vec![Ty::I32, Ty::U32, Ty::Bool],
    )
}
fn observed(f: &Function, module: Option<&Module>) -> (Vec<ValidationError>, Observer) {
    let mut observer = Observer::default();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    let errors = validate_function_block_params_observed(f, module, &mut session, site()).unwrap();
    assert!(session.first_refusal().is_none());
    assert_eq!(session.remaining_fuel(), InterpretOptions::default().fuel);
    (errors, observer)
}
fn parity(f: &Function, module: Option<&Module>) -> Vec<ValidationError> {
    let expected = super::super::validate_block_param_arity(f, module);
    let (actual, observer) = observed(f, module);
    assert_eq!(actual, expected);
    assert!(observer.events.iter().all(|event| event.site == site()));
    assert_eq!(
        observer.events.last().unwrap().phase,
        ExecutionPhase::Publication
    );
    actual
}
fn call_fixture(known_callee: bool) -> (Function, Module) {
    let mut module = Module::new("block params calls");
    let sig = module
        .add_func_type(trust_ir::FuncTy {
            params: vec![],
            returns: vec![Ty::I32],
            abi: None,
            is_vararg: false,
        })
        .unwrap();
    if known_callee {
        module
            .functions
            .push(Function::new(FuncId::new(7), "callee", sig, b(7)));
    }
    let mut f = function(
        Inst::Br {
            target: b(1),
            args: vec![v(7)],
        },
        vec![Ty::U32],
    );
    f.blocks[0].body.insert(
        0,
        InstrNode::new(Inst::Call {
            callee: FuncId::new(7),
            args: vec![],
        })
        .with_result(v(7)),
    );
    (f, module)
}
