// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Authored UNRUN; actual original local Drop arm, not full validity.
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
            return Err("original drop-place stop");
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
    ExecutionSite::Entry(FuncId::new(1221))
}
fn v(n: u32) -> ValueId {
    ValueId::new(n)
}
fn refine(n: u32) -> Ty {
    Ty::Refine(TyId::new(n), PredId::new(0))
}
fn fixture(ty: Ty) -> Module {
    let mut m = Module::new("");
    m.types = vec![Ty::Ptr, refine(0), Ty::Bool];
    m.func_types = vec![FuncTy::unrecorded(vec![ty.clone()], vec![], false)];
    let mut f = Function::new(
        FuncId::new(1221),
        "drop_place",
        FuncTyId::new(0),
        BlockId::new(1),
    );
    let mut b = Block::new(f.entry);
    b.params = vec![(v(0), ty)];
    b.body.push(InstrNode::new(Inst::Return { values: vec![] }));
    f.blocks.push(b);
    m.functions.push(f);
    m
}
fn drop_inst(invoke: bool, value: u32) -> Inst {
    if invoke {
        Inst::DropInvoke {
            ty: Ty::Bool,
            ptr: v(value),
            normal_dest: BlockId::new(2),
            normal_args: vec![],
            unwind_dest: BlockId::new(3),
        }
    } else {
        Inst::Drop {
            ty: Ty::Bool,
            ptr: v(value),
        }
    }
}
fn original(module: &Module, inst: &Inst) -> Vec<ValidationError> {
    let mut errors = Vec::new();
    let val_ty = build_module_value_types(&module.functions[0], module);
    let node = InstrNode::new(inst.clone());
    let block_id = 1;
    match &node.inst {
        Inst::Drop { ptr, .. } | Inst::DropInvoke { ptr, .. } => {
            if let Some(actual) = val_ty.get(&ptr.index())
                && module.representation_ty(actual) != Some(&Ty::Ptr)
            {
                errors.push(ValidationError::OperandTypeMismatch {
                    block: block_id,
                    op: instruction_kind(&node.inst).to_string(),
                    role: "ptr".to_string(),
                    expected: "ptr".to_string(),
                    actual: format!("{actual}"),
                });
            }
        }
        _ => {}
    }
    errors
}
fn setup<O: ExecutionObserver>(m: &Module, s: &mut ObservedSession<'_, O>) -> ObservedValueTypes {
    build_module_value_types_observed(&m.functions[0], m, s, site()).unwrap()
}
fn run(m: &Module, inst: &Inst) -> (Vec<ValidationError>, Observer, usize, usize) {
    let expected = original(m, inst);
    let mut o = Observer::default();
    let calls = o.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let values = setup(m, &mut s);
    let begin = calls.get();
    let out =
        validate_drop_place_observed(m, inst, &values, BlockId::new(1), &mut s, site()).unwrap();
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
        s.op.capacity()
            + s.role.capacity()
            + s.expected.capacity()
            + s.actual.capacity()
            + s.errors.capacity(),
        0
    )
}
