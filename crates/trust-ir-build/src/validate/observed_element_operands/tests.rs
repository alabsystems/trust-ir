// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Authored controls only. No Rust control has run.
use super::*;
use std::{cell::Cell, rc::Rc};
use trust_ir::interpret::InterpretOptions;
use trust_ir::value::{FuncTyId, PredId, StructId, TyId};
use trust_ir::{Block, InstrNode};
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
            return Err("original element stop");
        }
        if event.phase == ExecutionPhase::ScratchRetirement
            && self.cleanup_stop.as_ref().is_some_and(|arm| arm.get())
        {
            return Err("original element cleanup");
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
    ExecutionSite::Entry(FuncId::new(113))
}
fn v(id: u32) -> ValueId {
    ValueId::new(id)
}
#[derive(Clone, Copy)]
enum Kind {
    Extract,
    Insert,
}
fn fixture(
    kind: Kind,
    aggregate: Option<Ty>,
    index: Option<Ty>,
    value: Option<Ty>,
    declared: Ty,
) -> Function {
    let mut function = Function::new(
        FuncId::new(113),
        "elements",
        FuncTyId::new(0),
        BlockId::new(0),
    );
    let mut block = Block::new(BlockId::new(0));
    for (id, ty) in [(0, aggregate), (1, index), (2, value)] {
        if let Some(ty) = ty {
            block.params.push((v(id), ty));
        }
    }
    block.body.push(InstrNode::new(match kind {
        Kind::Extract => Inst::ExtractElement {
            ty: declared,
            array: v(0),
            index: v(1),
        },
        Kind::Insert => Inst::InsertElement {
            ty: declared,
            array: v(0),
            index: v(1),
            value: v(2),
        },
    }));
    function.blocks.push(block);
    function
}
fn subject(function: &Function) -> &Inst {
    &function.blocks[0].body.last().unwrap().inst
}
fn values(function: &Function, module: Option<&Module>) -> ObservedValueTypes {
    // Fixture setup is not a new production owner or renewed allowance.
    let mut observer = Observer::default();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    match module {
        Some(module) => {
            build_module_value_types_observed(function, module, &mut session, site()).unwrap()
        }
        None => build_function_value_types_observed(function, &mut session, site()).unwrap(),
    }
}
fn run(
    function: &Function,
    constants: &[(u32, i128)],
    module: Option<&Module>,
) -> (Vec<ValidationError>, Observer) {
    let values = values(function, module);
    let mut observer = Observer::default();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    let errors = validate_element_operands_observed(
        0,
        subject(function),
        &values,
        constants,
        module,
        &mut session,
        site(),
    )
    .unwrap();
    assert!(session.first_refusal().is_none());
    assert_eq!(session.remaining_fuel(), InterpretOptions::default().fuel);
    (errors, observer)
}
fn ordinary(
    function: &Function,
    constants: &[(u32, i128)],
    module: Option<&Module>,
) -> Vec<ValidationError> {
    let values = module.map_or_else(
        || build_function_value_types(function),
        |module| build_module_value_types(function, module),
    );
    let constants = constants.iter().copied().collect::<BTreeMap<_, _>>();
    let mut errors = Vec::new();
    match subject(function) {
        Inst::ExtractElement { ty, array, index } => check_extract_element_operands(
            &mut errors,
            0,
            ty,
            *array,
            *index,
            &values,
            &constants,
            module,
        ),
        Inst::InsertElement {
            ty,
            array,
            index,
            value,
        } => check_insert_element_operands(
            &mut errors,
            ty,
            *array,
            *index,
            *value,
            &ValueValidationContext {
                block_id: 0,
                val_ty: &values,
                const_int_values: &constants,
            },
            module,
        ),
        _ => panic!("wrong test family"),
    }
    errors
}
fn parity(
    function: &Function,
    constants: &[(u32, i128)],
    module: Option<&Module>,
) -> Vec<ValidationError> {
    let (errors, observer) = run(function, constants, module);
    assert_eq!(errors, ordinary(function, constants, module));
    assert!(observer.events.iter().all(|event| event.site == site()));
    assert_eq!(
        observer.events.last().unwrap().phase,
        ExecutionPhase::Publication
    );
    errors
}
fn reasons(errors: &[ValidationError]) -> Vec<&str> {
    errors
        .iter()
        .map(|error| match error {
            ValidationError::InvalidVectorElementOp {
                block: 0, reason, ..
            } => reason.as_str(),
            _ => panic!("unexpected test diagnostic"),
        })
        .collect()
}
fn failing() -> Function {
    fixture(
        Kind::Insert,
        Some(Ty::Vector(Box::new(Ty::U32), 2)),
        Some(Ty::Bool),
        Some(Ty::I32),
        Ty::Vector(Box::new(Ty::F32), 2),
    )
}
fn module() -> Module {
    let mut module = Module::new("elements");
    module.types = vec![Ty::U32, Ty::I32, Ty::Refine(TyId::new(0), PredId::new(0))];
    module
}
