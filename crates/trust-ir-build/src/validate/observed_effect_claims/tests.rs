// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Authored UNRUN controls, not compiler or execution evidence.
use super::*;
use std::{cell::Cell, rc::Rc};
use trust_ir::dialect::DialectInst;
use trust_ir::inst::{
    AllocOrigin, AssertKind, AtomicRMWOp, BinOp, BindingFrameDef, BindingSlot, FCmpOp, ICmpOp,
    OverflowOp, PanicLocation, PanicSite, SwitchCase, UnOp,
};
use trust_ir::interpret::InterpretOptions;
use trust_ir::value::{BindingFrameId, BlockId, FuncTyId, GlobalId, TyId};
use trust_ir::{Block, Constant, DropGlueEntry, InstrNode, Ty};
mod calls;
mod parity;
mod roots;
mod stops;
mod witnesses;

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
            return Err("original effect stop");
        }
        if event.phase == ExecutionPhase::ScratchRetirement
            && self.cleanup.as_ref().is_some_and(|arm| arm.get())
        {
            return Err("original effect cleanup");
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
fn node(inst: Inst, results: &[u32]) -> InstrNode {
    InstrNode::new(inst).with_results(results.iter().copied().map(v))
}
fn function(nodes: Vec<InstrNode>) -> Function {
    let mut function = Function::new(
        FuncId::new(131),
        "effects",
        FuncTyId::new(0),
        BlockId::new(0),
    );
    function.attrs.readnone = true;
    let mut block = Block::new(BlockId::new(0));
    block.params = vec![(v(1), Ty::Ptr)];
    block.body = nodes;
    function.blocks.push(block);
    function
}
fn store(ptr: u32) -> Inst {
    Inst::Store {
        ty: Ty::U32,
        ptr: v(ptr),
        value: v(1),
        volatile: false,
        align: None,
    }
}
fn load(ptr: u32) -> Inst {
    Inst::Load {
        ty: Ty::U32,
        ptr: v(ptr),
        volatile: false,
        align: None,
    }
}
fn alloca() -> Inst {
    Inst::Alloca {
        ty: Ty::U32,
        count: None,
        align: None,
    }
}
fn copy(value: u32) -> Inst {
    Inst::Copy {
        ty: Ty::Ptr,
        operand: v(value),
    }
}
fn callee(id: u32, name: &str, readnone: bool, readonly: bool) -> Function {
    let mut f = Function::new(FuncId::new(id), name, FuncTyId::new(0), BlockId::new(0));
    f.attrs.readnone = readnone;
    f.attrs.readonly = readonly;
    f
}
fn frame(count: usize) -> Inst {
    Inst::OpenFrame {
        def: BindingFrameDef::new(
            BindingFrameId::new(71),
            "frame",
            (0..count)
                .map(|i| BindingSlot::new(i.to_string(), Ty::Tuple(vec![Ty::U32])))
                .collect(),
        ),
    }
}
fn dialect(count: usize) -> Inst {
    let mut op = DialectInst::new("observed", "effects");
    op.result_tys = (0..count).map(|_| Ty::Tuple(vec![Ty::U8])).collect();
    Inst::DialectOp(Box::new(op))
}
fn fixture() -> Function {
    function(vec![
        node(alloca(), &[10]),
        node(copy(10), &[11]),
        node(store(11), &[]),
        node(load(1), &[]),
        node(
            Inst::Call {
                callee: FuncId::new(9),
                args: vec![],
            },
            &[],
        ),
        node(
            Inst::Fence {
                ordering: Ordering::Relaxed,
            },
            &[],
        ),
    ])
}
fn run(f: &Function, module: Option<&Module>) -> (Vec<ValidationError>, Observer) {
    let mut observer = Observer::default();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    let result = validate_function_effect_claims_observed(f, module, &mut session, site()).unwrap();
    assert!(session.first_refusal().is_none());
    assert_eq!(session.remaining_fuel(), InterpretOptions::default().fuel);
    (result, observer)
}
fn parity(f: &Function, module: Option<&Module>) -> Vec<ValidationError> {
    let (actual, observer) = run(f, module);
    assert_eq!(
        actual,
        super::super::claims::validate_func_attr_claims(f, module)
    );
    assert!(observer.events.iter().all(|event| event.site == site()));
    assert_eq!(
        observer.events.last().unwrap().phase,
        ExecutionPhase::Publication
    );
    actual
}
fn text(error: &ValidationError) -> &str {
    let ValidationError::FuncAttrClaimViolated { inst, .. } = error else {
        panic!("wrong diagnostic")
    };
    inst
}
fn empty(state: &State<'_, '_>) -> bool {
    state.definitions.capacity() == 0
        && state.stack.capacity() == 0
        && state.seen.capacity() == 0
        && state.roots.capacity() == 0
        && state.drop_index.is_none()
        && state.function_name.capacity() == 0
        && state.inst_text.capacity() == 0
        && state.errors.capacity() == 0
}
