// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Authored source controls, all UNRUN.
use super::*;
use std::{cell::Cell, rc::Rc};
use trust_ir::inst::{FCmpOp, ICmpOp};
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
    cleanup_stop: Option<Rc<Cell<bool>>>,
}
impl ExecutionObserver for Observer {
    type Refusal = &'static str;
    fn admit(&mut self, event: ExecutionProgress) -> Result<(), Self::Refusal> {
        self.events.push(event);
        if self.stop == Some(self.events.len()) {
            return Err("original numeric stop");
        }
        if event.phase == ExecutionPhase::ScratchRetirement
            && self.cleanup_stop.as_ref().is_some_and(|arm| arm.get())
        {
            return Err("original numeric cleanup");
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
    ExecutionSite::Entry(FuncId::new(101))
}
fn v(id: u32) -> ValueId {
    ValueId::new(id)
}
fn f(inst: Inst) -> Function {
    let mut function = Function::new(
        FuncId::new(101),
        "numeric",
        FuncTyId::new(0),
        BlockId::new(0),
    );
    let mut block = Block::new(BlockId::new(0));
    block.params = vec![
        (v(0), Ty::U32),
        (v(1), Ty::I32),
        (v(2), Ty::Bool),
        (v(3), Ty::F32),
        (v(4), Ty::Char),
        (v(5), Ty::Ptr),
        (v(6), Ty::Refine(TyId::new(0), PredId::new(0))),
        (v(7), Ty::Refine(TyId::new(0), PredId::new(1))),
        (v(8), Ty::Refine(TyId::new(1), PredId::new(0))),
        (v(9), Ty::FatPtr(FatPtrKind::Str)),
    ];
    block.body.push(InstrNode::new(inst));
    function.blocks.push(block);
    function
}
fn fixture() -> Function {
    f(Inst::BinOp {
        op: BinOp::Add,
        ty: Ty::F32,
        lhs: v(1),
        rhs: v(2),
    })
}
fn module() -> Module {
    let mut module = Module::new("representations");
    module.types = vec![Ty::U32, Ty::F32, Ty::Refine(TyId::new(0), PredId::new(0))];
    module
}
fn values(function: &Function, module: Option<&Module>) -> ObservedValueTypes {
    // Fixed fixture input preparation is not a renewed owner for the API.
    let mut observer = Observer::default();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    match module {
        Some(module) => {
            build_module_value_types_observed(function, module, &mut session, site()).unwrap()
        }
        None => build_function_value_types_observed(function, &mut session, site()).unwrap(),
    }
}
fn run(function: &Function, module: Option<&Module>) -> (Vec<ValidationError>, Observer) {
    let values = values(function, module);
    let mut observer = Observer::default();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    let errors = validate_instruction_numeric_type_operands_observed(
        0,
        &function.blocks[0].body[0].inst,
        &values,
        module,
        &mut session,
        site(),
    )
    .unwrap();
    assert!(session.first_refusal().is_none());
    assert_eq!(session.remaining_fuel(), InterpretOptions::default().fuel);
    (errors, observer)
}
fn included(e: &ValidationError) -> bool {
    matches!(
        e,
        ValidationError::BinOpTypeMismatch { .. }
            | ValidationError::OperandTypeMismatch { .. }
            | ValidationError::BinOpRequiresInteger { .. }
            | ValidationError::BinOpRequiresFloat { .. }
            | ValidationError::BinOpRequiresBool { .. }
            | ValidationError::OperandNotInteger { .. }
            | ValidationError::UnOpNotOnScalarBool { .. }
            | ValidationError::ICmpRequiresIntegerOrPtr { .. }
            | ValidationError::FCmpRequiresFloat { .. }
    )
}
fn parity(function: &Function, module: Option<&Module>) -> Vec<ValidationError> {
    let (actual, observer) = run(function, module);
    let expected = super::super::validate_types(
        function,
        ValidationContext {
            cast_mode: CastValidationMode::FunctionOnly,
            pointer_bits: module.map_or(DEFAULT_POINTER_BITS, Module::pointer_bits),
            module,
        },
    )
    .into_iter()
    .filter(included)
    .collect::<Vec<_>>();
    assert_eq!(actual, expected);
    assert!(observer.events.iter().all(|event| event.site == site()));
    assert_eq!(
        observer.events.last().unwrap().phase,
        ExecutionPhase::Publication
    );
    actual
}
const BINARY: [BinOp; 26] = [
    BinOp::Add,
    BinOp::Sub,
    BinOp::Mul,
    BinOp::UDiv,
    BinOp::SDiv,
    BinOp::URem,
    BinOp::SRem,
    BinOp::FAdd,
    BinOp::FSub,
    BinOp::FMul,
    BinOp::FDiv,
    BinOp::FRem,
    BinOp::FMin,
    BinOp::FMax,
    BinOp::And,
    BinOp::Or,
    BinOp::Xor,
    BinOp::Shl,
    BinOp::LShr,
    BinOp::AShr,
    BinOp::BAnd,
    BinOp::BOr,
    BinOp::BXor,
    BinOp::RotL,
    BinOp::RotR,
    BinOp::FCopySign,
];
const UNARY: [UnOp; 13] = [
    UnOp::Neg,
    UnOp::FNeg,
    UnOp::FAbs,
    UnOp::FSqrt,
    UnOp::FFloor,
    UnOp::FCeil,
    UnOp::FTrunc,
    UnOp::Not,
    UnOp::CtPop,
    UnOp::CtLz,
    UnOp::CtTz,
    UnOp::BSwap,
    UnOp::BitReverse,
];
fn categories() -> Vec<Ty> {
    vec![
        Ty::U32,
        Ty::I128,
        Ty::Usize,
        Ty::Bool,
        Ty::Char,
        Ty::F32,
        Ty::Ptr,
        Ty::Tuple(vec![]),
        Ty::Vector(Box::new(Ty::U32), 0),
        Ty::Vector(Box::new(Ty::U32), 4),
        Ty::Vector(Box::new(Ty::Bool), 4),
        Ty::Vector(Box::new(Ty::F32), 4),
        Ty::Vector(Box::new(Ty::I128), 4),
        Ty::Vector(Box::new(Ty::Vector(Box::new(Ty::U32), 4)), 4),
    ]
}
