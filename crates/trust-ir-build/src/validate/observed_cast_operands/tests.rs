// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Authored controls only, all UNRUN.
use super::*;
use std::{cell::Cell, collections::BTreeMap, rc::Rc};
use trust_ir::interpret::InterpretOptions;
use trust_ir::value::{FuncTyId, TyId};
use trust_ir::{Block, DialectTy, FatPtrKind, HandleTy};
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
            return Err("original cast stop");
        }
        if event.phase == ExecutionPhase::ScratchRetirement
            && self.cleanup_stop.as_ref().is_some_and(|arm| arm.get())
        {
            return Err("original cast cleanup");
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
    ExecutionSite::Entry(FuncId::new(213))
}
fn v(n: u32) -> ValueId {
    ValueId::new(n)
}
fn rows(actual: Ty) -> Vec<(ValueId, Ty)> {
    vec![(v(0), actual)]
}
fn values(rows: &[(ValueId, Ty)]) -> ObservedValueTypes {
    // Caller-owned fixture construction, outside the subject session.
    let mut f = Function::new(FuncId::new(213), "casts", FuncTyId::new(0), BlockId::new(0));
    let mut block = Block::new(BlockId::new(0));
    block.params = rows.to_vec();
    f.blocks.push(block);
    let mut observer = Observer::default();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    build_function_value_types_observed(&f, &mut session, site()).unwrap()
}
const OPS: [CastOp; 17] = [
    CastOp::Trunc,
    CastOp::ZExt,
    CastOp::SExt,
    CastOp::FPTrunc,
    CastOp::FPExt,
    CastOp::FPToUI,
    CastOp::FPToSI,
    CastOp::UIToFP,
    CastOp::SIToFP,
    CastOp::PtrToInt,
    CastOp::IntToPtr,
    CastOp::PtrToPtr,
    CastOp::Bitcast,
    CastOp::Transmute,
    CastOp::ReifyFnPointer,
    CastOp::FPToSISat,
    CastOp::FPToUISat,
];
const MODES: [CastValidationMode; 2] = [
    CastValidationMode::FunctionOnly,
    CastValidationMode::DeferLayoutSensitive,
];
fn run(
    op: CastOp,
    src: &Ty,
    dst: &Ty,
    rows: &[(ValueId, Ty)],
    operand: ValueId,
    mode: CastValidationMode,
) -> (Vec<ValidationError>, Observer) {
    let values = values(rows);
    let mut observer = Observer::default();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    let errors = validate_cast_operands_observed(
        7,
        op,
        src,
        dst,
        operand,
        &values,
        mode,
        &mut session,
        site(),
    )
    .unwrap();
    assert!(session.first_refusal().is_none());
    assert_eq!(session.remaining_fuel(), InterpretOptions::default().fuel);
    (errors, observer)
}
fn parity(
    op: CastOp,
    src: &Ty,
    dst: &Ty,
    rows: &[(ValueId, Ty)],
    operand: ValueId,
    mode: CastValidationMode,
) -> Vec<ValidationError> {
    let (actual, observer) = run(op, src, dst, rows, operand, mode);
    let map: BTreeMap<u32, Ty> = rows.iter().map(|(v, ty)| (v.index(), ty.clone())).collect();
    let mut expected = Vec::new();
    super::super::check_cast_compatibility(&mut expected, 7, op, src.clone(), dst.clone(), mode);
    super::super::check_cast_operand_and_width(&mut expected, 7, op, src, dst, operand, &map);
    assert_eq!(actual, expected);
    assert!(observer.events.iter().all(|event| event.site == site()));
    assert_eq!(
        observer.events.last().unwrap().phase,
        ExecutionPhase::Publication
    );
    actual
}
fn handle() -> Ty {
    Ty::Handle(Box::new(HandleTy::new("λ'\n", "runtime\0")))
}
fn vector(mut ty: Ty, depth: usize, lanes: u32) -> Ty {
    for _ in 0..depth {
        ty = Ty::Vector(Box::new(ty), lanes);
    }
    ty
}
fn check_fixture<O: ExecutionObserver>(
    state: &mut State,
    values: &ObservedValueTypes,
    work: &mut Work<'_, '_, O>,
) -> R {
    state.compatibility(
        7,
        CastOp::Trunc,
        &Ty::Bool,
        &Ty::U128,
        CastValidationMode::FunctionOnly,
        work,
    )?;
    state.operand_and_width(7, CastOp::Trunc, &Ty::Bool, &Ty::U128, v(0), values, work)
}
fn empty(state: &State) -> bool {
    state.op.capacity()
        + state.src.capacity()
        + state.dst.capacity()
        + state.actual.capacity()
        + state.reason.capacity()
        + state.errors.capacity()
        == 0
}
fn retire<O: ExecutionObserver>(state: &mut State, work: &mut Work<'_, '_, O>) {
    state.retire_scratch(work);
    let _ = super::super::retire_validation_errors_observed(
        take(&mut state.errors),
        work.session,
        work.site,
    );
}
