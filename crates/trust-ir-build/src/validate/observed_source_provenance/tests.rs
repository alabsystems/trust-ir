// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Authored UNRUN controls for the parent's observed provenance constituent.
use super::*;
use std::{cell::Cell, rc::Rc};
use trust_ir::analysis::StaticFunctionPointerAnalysis;
use trust_ir::inst::{AssertKind, PanicLocation, PanicSite, SwitchCase};
use trust_ir::interpret::InterpretOptions;
use trust_ir::value::{FuncId, FuncTyId, ValueId};
use trust_ir::{Block, Constant, FuncTy, InstrNode, ProofDigest, SourceBindingProvenance, Ty};
mod bindings;
mod loops;
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
            return Err("original provenance stop");
        }
        if event.phase == ExecutionPhase::ScratchRetirement
            && self.cleanup.as_ref().is_some_and(|arm| arm.get())
        {
            return Err("original provenance cleanup");
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
    ExecutionSite::Entry(FuncId::new(161))
}
fn v(id: u32) -> ValueId {
    ValueId::new(id)
}
fn node(inst: Inst) -> InstrNode {
    InstrNode::new(inst)
}
fn branch(id: u32, args: &[u32]) -> InstrNode {
    node(Inst::Br {
        target: BlockId::new(id),
        args: args.iter().copied().map(v).collect(),
    })
}
fn binding(name: &str, hir: u32, place: SourcePlace) -> SourceBindingProvenance {
    SourceBindingProvenance {
        name: name.into(),
        hir_local_id: hir,
        place,
    }
}
fn rows() -> Vec<SourceLoopProvenance> {
    vec![SourceLoopProvenance {
        source_loop_id: 0,
        hir_local_id: 10,
        header: BlockId::new(1),
        bindings: vec![
            binding("arg", 100, SourcePlace::FunctionParameter { index: 0 }),
            binding("iter", 101, SourcePlace::LoopParameter { index: 0 }),
        ],
    }]
}
fn function() -> Function {
    let mut f = Function::new(
        FuncId::new(161),
        "source_target",
        FuncTyId::new(0),
        BlockId::new(0),
    );
    let mut entry = Block::new(BlockId::new(0));
    entry.params = vec![(v(0), Ty::U32), (v(1), Ty::Bool)];
    entry.body.push(branch(1, &[0, 0]));
    let mut header = Block::new(BlockId::new(1));
    header.params = vec![(v(2), Ty::U32), (v(3), Ty::U32)];
    header.body.push(node(Inst::CondBr {
        cond: v(1),
        then_target: BlockId::new(2),
        then_args: vec![v(2)],
        else_target: BlockId::new(3),
        else_args: vec![],
    }));
    let mut latch = Block::new(BlockId::new(2));
    latch.params.push((v(4), Ty::U32));
    latch.body.push(branch(1, &[4, 4]));
    let mut exit = Block::new(BlockId::new(3));
    exit.body.push(node(Inst::Return { values: vec![] }));
    f.blocks = vec![entry, header, latch, exit];
    f
}
fn seal(module: &mut Module, rows: Vec<SourceLoopProvenance>) {
    let id = module.functions[0].id;
    let semantic = module.source_provenance_semantic_digest(id).unwrap();
    module.functions[0].source_provenance = Some(SourceProvenance::new(
        ProofDigest::sha256([3; 32]),
        semantic,
        rows,
    ));
}
fn module() -> Module {
    let mut module = Module::new("source_module_λ");
    module
        .add_func_type(FuncTy {
            params: vec![Ty::U32, Ty::Bool],
            returns: vec![],
            abi: None,
            is_vararg: false,
        })
        .unwrap();
    module.functions.push(function());
    seal(&mut module, rows());
    module
}
fn extra_loop(module: &mut Module, header: u32) {
    let mut block = Block::new(BlockId::new(header));
    block.params.push((v(50 + header), Ty::U32));
    block.body.push(branch(header, &[50 + header]));
    module.functions[0].blocks.push(block);
}
fn run(function: &Function, module: Option<&Module>) -> (Vec<ValidationError>, Observer) {
    let mut observer = Observer::default();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    let output =
        validate_function_source_provenance_observed(function, module, &mut session, site())
            .unwrap();
    assert!(session.first_refusal().is_none());
    assert_eq!(session.remaining_fuel(), InterpretOptions::default().fuel);
    (output, observer)
}
fn parity(function: &Function, module: Option<&Module>) -> Vec<ValidationError> {
    let analysis = StaticFunctionPointerAnalysis::new(function);
    let expected = super::super::validate_source_provenance(function, module, &analysis);
    let (actual, observer) = run(function, module);
    assert_eq!(actual, expected);
    assert!(observer.events.iter().all(|event| event.site == site()));
    assert_eq!(
        observer.events.last().unwrap().phase,
        ExecutionPhase::Publication
    );
    actual
}
fn details(errors: &[ValidationError]) -> Vec<&str> {
    errors
        .iter()
        .map(|error| match error {
            ValidationError::InvalidSourceProvenance { detail, .. } => detail.as_str(),
            _ => panic!("unexpected provenance diagnostic"),
        })
        .collect()
}
fn empty(state: &State<'_>) -> bool {
    state.detail.capacity() == 0
        && state.pending.capacity() == 0
        && state.errors.capacity() == 0
        && state.dominators.is_none()
        && state.edges.capacity() == 0
        && state.loop_hir.capacity() == 0
        && state.headers.capacity() == 0
        && state.local_hir.capacity() == 0
        && state.local_places.capacity() == 0
        && state.global_names.capacity() == 0
        && state.global_places.capacity() == 0
}
fn retire(state: &mut State<'_>, work: &mut Work<'_, '_, impl ExecutionObserver>) {
    state.retire_scratch(work);
    let _ = retire_validation_errors_observed(take(&mut state.errors), work.session, work.site);
}
