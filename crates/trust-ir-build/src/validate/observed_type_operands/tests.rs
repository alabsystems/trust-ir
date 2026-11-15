// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Authored source controls, all UNRUN.
use super::*;
use std::{cell::Cell, rc::Rc};
use trust_ir::inst::{AssertKind, AtomicRMWOp, PanicLocation, PanicSite};
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
            return Err("original operand stop");
        }
        if event.phase == ExecutionPhase::ScratchRetirement
            && self.cleanup_stop.as_ref().is_some_and(|arm| arm.get())
        {
            return Err("original operand cleanup");
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
    ExecutionSite::Entry(FuncId::new(91))
}
fn v(id: u32) -> ValueId {
    ValueId::new(id)
}
fn f(inst: Inst) -> Function {
    let mut function = Function::new(
        FuncId::new(91),
        "operands",
        FuncTyId::new(0),
        BlockId::new(0),
    );
    let mut block = Block::new(BlockId::new(0));
    block.params = vec![
        (v(0), Ty::Ptr),
        (v(1), Ty::U32),
        (v(2), Ty::I32),
        (v(3), Ty::U8),
        (v(4), Ty::U64),
        (v(5), Ty::Usize),
        (v(6), Ty::Bool),
        (v(7), Ty::Refine(TyId::new(0), PredId::new(0))),
        (v(8), Ty::FatPtr(FatPtrKind::Str)),
    ];
    block.body.push(InstrNode::new(inst));
    function.blocks.push(block);
    function
}
fn fixture() -> Function {
    f(Inst::CmpXchg {
        ty: Ty::U32,
        ptr: v(1),
        expected: v(2),
        desired: v(6),
        success: Ordering::Relaxed,
        failure: Ordering::Release,
        weak: true,
    })
}
fn values(f: &Function, module: Option<&Module>) -> ObservedValueTypes {
    // Fixture materialization is independent of the original session supplied
    // to the constituent under test. Its immutable input is then borrowed.
    let mut observer = Observer::default();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    match module {
        Some(module) => build_module_value_types_observed(f, module, &mut session, site()).unwrap(),
        None => build_function_value_types_observed(f, &mut session, site()).unwrap(),
    }
}
fn run(f: &Function, module: Option<&Module>) -> (Vec<ValidationError>, Observer) {
    let values = values(f, module);
    let mut observer = Observer::default();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    let errors = validate_instruction_basic_type_operands_observed(
        0,
        &f.blocks[0].body[0].inst,
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
fn included(error: &ValidationError) -> bool {
    matches!(
        error,
        ValidationError::OperandTypeMismatch { .. }
            | ValidationError::OperandNotPointer { .. }
            | ValidationError::GepIndexNotInteger { .. }
            | ValidationError::CondBrRequiresBool { .. }
            | ValidationError::PredicateRequiresBool { .. }
            | ValidationError::IllegalAtomicOrdering { .. }
    )
}
fn parity(f: &Function, module: Option<&Module>) -> Vec<ValidationError> {
    let (actual, observer) = run(f, module);
    let expected = super::super::validate_types(
        f,
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
    assert!(observer.events.iter().all(|e| e.site == site()));
    assert_eq!(
        observer.events.last().unwrap().phase,
        ExecutionPhase::Publication
    );
    actual
}
fn target(module: &mut Module) {
    module.target_info = Some(trust_ir::TargetInfo {
        triple: "aarch64-unknown-linux-gnu".into(),
        pointer_size: 8,
        endianness: trust_ir::Endianness::Little,
        abi: None,
        struct_passing: trust_ir::StructPassingPolicy::default(),
    });
}
