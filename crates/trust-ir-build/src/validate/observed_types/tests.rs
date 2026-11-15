// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Authored UNRUN controls; this is not execution evidence.
use super::*;
use std::{cell::Cell, rc::Rc};
use trust_ir::interpret::InterpretOptions;
use trust_ir::value::{FuncTyId, TyId};
use trust_ir::{Block, FatPtrKind, FuncTy, InstrNode, Producer};
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
            return Err("original full type stop");
        }
        if event.phase == ExecutionPhase::ScratchRetirement
            && self.cleanup.as_ref().is_some_and(|arm| arm.get())
        {
            return Err("original full type cleanup");
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
    ExecutionSite::Entry(FuncId::new(121))
}
fn v(id: u32) -> ValueId {
    ValueId::new(id)
}
fn node(inst: Inst, results: &[u32]) -> InstrNode {
    InstrNode::new(inst).with_results(results.iter().copied().map(v))
}
fn function(nodes: Vec<InstrNode>) -> Function {
    let mut f = Function::new(
        FuncId::new(121),
        "full-types",
        FuncTyId::new(0),
        BlockId::new(0),
    );
    let mut b = Block::new(BlockId::new(0));
    b.body = nodes;
    b.params = vec![
        (v(0), Ty::I32),
        (v(1), Ty::Bool),
        (v(2), Ty::Ptr),
        (v(3), Ty::U64),
        (v(4), Ty::Vector(Box::new(Ty::U32), 4)),
    ];
    f.blocks.push(b);
    f
}
fn fixture() -> Function {
    function(vec![
        node(
            Inst::PtrFromParts {
                ptr_ty: Ty::FatPtr(FatPtrKind::Str),
                metadata_ty: Ty::U16,
                data: v(0),
                metadata: v(1),
            },
            &[],
        ),
        node(
            Inst::Cast {
                op: CastOp::ZExt,
                src_ty: Ty::U64,
                dst_ty: Ty::U8,
                operand: v(0),
            },
            &[],
        ),
        node(
            Inst::Select {
                ty: Ty::U32,
                cond: v(3),
                then_val: v(0),
                else_val: v(1),
            },
            &[],
        ),
    ])
}
fn context(module: Option<&Module>) -> ValidationContext<'_> {
    ValidationContext {
        module,
        cast_mode: if module.is_some() {
            CastValidationMode::DeferLayoutSensitive
        } else {
            CastValidationMode::FunctionOnly
        },
        pointer_bits: module.map_or(DEFAULT_POINTER_BITS, Module::pointer_bits),
    }
}
fn run(f: &Function, module: Option<&Module>) -> (Vec<ValidationError>, Observer) {
    let mut observer = Observer::default();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    let out = validate_function_types_observed(f, module, &mut session, site()).unwrap();
    assert!(session.first_refusal().is_none());
    assert_eq!(session.remaining_fuel(), InterpretOptions::default().fuel);
    (out, observer)
}
fn parity(f: &Function, module: Option<&Module>) -> Vec<ValidationError> {
    let (out, observer) = run(f, module);
    assert_eq!(out, super::super::validate_types(f, context(module)));
    assert!(observer.events.iter().all(|e| e.site == site()));
    assert_eq!(
        observer.events.last().unwrap().phase,
        ExecutionPhase::Publication
    );
    out
}
fn empty(s: &State) -> bool {
    s.values.is_none()
        && s.constants.capacity() == 0
        && s.pending.capacity() == 0
        && s.errors.capacity() == 0
}
fn seed_values(s: &mut State, f: &Function, work: &mut Work<'_, '_, impl ExecutionObserver>) {
    s.values = Some(build_function_value_types_observed(f, work.session, work.site).unwrap());
}
fn error(id: u32) -> ValidationError {
    ValidationError::UnOpNotOnScalarBool { block: id }
}
