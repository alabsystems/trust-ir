// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Authored source controls; all Rust controls UNRUN.
use super::*;
use std::{cell::Cell, rc::Rc};
use trust_ir::interpret::InterpretOptions;
use trust_ir::value::{FuncTyId, PredId, TyId};
use trust_ir::{Block, FatPtrKind, InstrNode};
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
            return Err("original pointer/select stop");
        }
        if event.phase == ExecutionPhase::ScratchRetirement
            && self.cleanup.as_ref().is_some_and(|arm| arm.get())
        {
            return Err("original pointer/select cleanup");
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
    ExecutionSite::Entry(FuncId::new(111))
}
fn v(id: u32) -> ValueId {
    ValueId::new(id)
}
fn function(inst: Inst) -> Function {
    let mut f = Function::new(
        FuncId::new(111),
        "pointer-select",
        FuncTyId::new(0),
        BlockId::new(0),
    );
    let mut b = Block::new(BlockId::new(0));
    b.params = vec![
        (v(0), Ty::Ptr),
        (v(1), Ty::I32),
        (v(2), Ty::Bool),
        (v(3), Ty::U64),
        (v(4), Ty::FatPtr(FatPtrKind::Str)),
        (v(5), Ty::Refine(TyId::new(0), PredId::new(0))),
        (v(6), Ty::Vector(Box::new(Ty::Bool), 4)),
        (v(7), Ty::Vector(Box::new(Ty::I32), 4)),
    ];
    b.body.push(InstrNode::new(inst));
    f.blocks.push(b);
    f
}
fn fixture() -> Function {
    function(Inst::PtrFromParts {
        ptr_ty: Ty::FatPtr(FatPtrKind::Str),
        metadata_ty: Ty::U16,
        data: v(1),
        metadata: v(2),
    })
}
fn values(f: &Function) -> ObservedValueTypes {
    let mut observer = Observer::default();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    build_function_value_types_observed(f, &mut session, site()).unwrap()
}
fn original(f: &Function, bits: u32) -> Vec<ValidationError> {
    let map = super::super::build_function_value_types(f);
    let mut errors = Vec::new();
    match &f.blocks[0].body[0].inst {
        Inst::PtrData { ptr_ty, ptr } => {
            super::super::check_ptr_data_operands(&mut errors, 0, ptr_ty, *ptr, &map)
        }
        Inst::PtrMetadata {
            ptr_ty,
            metadata_ty,
            ptr,
        } => super::super::check_ptr_metadata_operands(
            &mut errors,
            0,
            ptr_ty,
            metadata_ty,
            *ptr,
            &map,
            bits,
        ),
        Inst::PtrFromParts {
            ptr_ty,
            metadata_ty,
            data,
            metadata,
        } => {
            let constants = BTreeMap::new();
            let ctx = ValueValidationContext {
                block_id: 0,
                val_ty: &map,
                const_int_values: &constants,
            };
            super::super::check_ptr_from_parts_operands(
                &mut errors,
                ptr_ty,
                metadata_ty,
                *data,
                *metadata,
                &ctx,
                bits,
            );
        }
        Inst::Select {
            ty,
            cond,
            then_val,
            else_val,
        } => super::super::check_select_operands(
            &mut errors,
            0,
            ty,
            *cond,
            *then_val,
            *else_val,
            &map,
        ),
        _ => panic!("fixture is outside constituent"),
    }
    errors
}
fn run(f: &Function, bits: u32) -> (Vec<ValidationError>, Observer) {
    let values = values(f);
    let mut observer = Observer::default();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    let out = validate_pointer_select_operands_observed(
        0,
        &f.blocks[0].body[0].inst,
        &values,
        bits,
        &mut session,
        site(),
    )
    .unwrap();
    assert!(session.first_refusal().is_none());
    assert_eq!(session.remaining_fuel(), InterpretOptions::default().fuel);
    (out, observer)
}
fn parity(f: &Function, bits: u32) -> Vec<ValidationError> {
    let (out, observer) = run(f, bits);
    assert_eq!(out, original(f, bits));
    assert!(observer.events.iter().all(|e| e.site == site()));
    assert_eq!(
        observer.events.last().unwrap().phase,
        ExecutionPhase::Publication
    );
    out
}
fn empty(s: &State) -> bool {
    s.op.capacity() == 0
        && s.role.capacity() == 0
        && s.pointer.capacity() == 0
        && s.expected.capacity() == 0
        && s.actual.capacity() == 0
        && s.reason.capacity() == 0
        && s.pending_ty.is_none()
        && s.errors.capacity() == 0
}
