// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Source-authored Rust controls; all UNRUN.
use super::*;
use trust_ir::inst::{BindingFrameDef, BindingSlot, CastOp};
use trust_ir::interpret::InterpretOptions;
use trust_ir::ty::SetRepr;
use trust_ir::value::{BindingFrameId, ClosureTyId, EnumId, PredId, RecordId, StructId, TyId};
use trust_ir::{Block, FuncTyId, InstrNode};
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
}
impl ExecutionObserver for Observer {
    type Refusal = &'static str;
    fn admit(&mut self, event: ExecutionProgress) -> Result<(), Self::Refusal> {
        self.events.push(event);
        if self.stop == Some(self.events.len()) {
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
    ExecutionSite::Entry(FuncId::new(111))
}
fn refined() -> Ty {
    Ty::Refine(TyId::new(u32::MAX), PredId::new(u32::MAX))
}
fn block(id: u32, params: Vec<Ty>, instructions: Vec<Inst>) -> Block {
    let mut block = Block::new(BlockId::new(id));
    block.params = params
        .into_iter()
        .enumerate()
        .map(|(i, ty)| (ValueId::new(i as u32), ty))
        .collect();
    block.body = instructions.into_iter().map(InstrNode::new).collect();
    block
}
fn function(name: &str, blocks: Vec<Block>) -> Function {
    let mut f = Function::new(FuncId::new(111), name, FuncTyId::new(0), BlockId::new(0));
    f.blocks = blocks;
    f
}
fn cast(source: Ty, target: Ty) -> Inst {
    Inst::Cast {
        op: CastOp::Bitcast,
        src_ty: source,
        dst_ty: target,
        operand: ValueId::new(0),
    }
}
fn fixture() -> Function {
    function(
        "refinement",
        vec![
            block(
                9,
                vec![Ty::Bool, Ty::Tuple(vec![Ty::Bool, refined()])],
                vec![
                    cast(refined(), refined()),
                    Inst::NullPtr,
                    Inst::Undef { ty: refined() },
                ],
            ),
            block(9, vec![refined()], vec![]),
        ],
    )
}
fn diagnostic(location: String) -> ValidationError {
    ValidationError::RefinementTypeInvalid {
        location,
        detail: DETAIL.to_owned(),
    }
}
fn observed(f: &Function) -> (Vec<ValidationError>, Observer) {
    let mut observer = Observer::default();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    let actual =
        validate_function_standalone_refinements_observed(f, &mut session, site()).unwrap();
    assert!(session.first_refusal().is_none());
    assert_eq!(session.remaining_fuel(), InterpretOptions::default().fuel);
    (actual, observer)
}
fn parity(f: &Function) -> Vec<ValidationError> {
    let (actual, observer) = observed(f);
    assert_eq!(actual, validate_standalone_refinement_surface(f));
    assert!(observer.events.iter().all(|event| event.site == site()));
    assert_eq!(
        observer.events.last().unwrap().phase,
        ExecutionPhase::Publication
    );
    actual
}
fn frame(types: Vec<Ty>) -> Inst {
    Inst::OpenFrame {
        def: BindingFrameDef::new(
            BindingFrameId::new(1),
            "frame",
            types
                .into_iter()
                .enumerate()
                .map(|(i, ty)| BindingSlot::new(format!("slot{i}"), ty))
                .collect(),
        ),
    }
}
