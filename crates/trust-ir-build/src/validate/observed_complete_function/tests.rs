// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Authored UNRUN Rust controls, not execution evidence.
use super::*;
use trust_ir::interpret::InterpretOptions;
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
    cleanup: bool,
}
impl ExecutionObserver for Observer {
    type Refusal = &'static str;
    fn admit(&mut self, event: ExecutionProgress) -> Result<(), Self::Refusal> {
        self.events.push(event);
        if self.stop == Some(self.events.len()) {
            return Err("original complete function stop");
        }
        if self.cleanup && event.phase == ExecutionPhase::ScratchRetirement {
            return Err("cleanup");
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
    ExecutionSite::Entry(FuncId::new(122))
}
fn v(id: u32) -> ValueId {
    ValueId::new(id)
}
fn function(nodes: Vec<InstrNode>) -> Function {
    let mut f = Function::new(
        FuncId::new(122),
        "complete-function",
        FuncTyId::new(0),
        BlockId::new(0),
    );
    let mut b = Block::new(BlockId::new(0));
    b.params = vec![(v(0), Ty::Ptr), (v(1), Ty::Bool), (v(2), Ty::U32)];
    b.body = nodes;
    f.blocks.push(b);
    f
}
fn simple() -> Function {
    function(vec![InstrNode::new(Inst::Return { values: vec![] })])
}
fn fixture() -> Function {
    let mut load = InstrNode::new(Inst::Load {
        ty: Ty::I32,
        ptr: v(1),
        volatile: false,
        align: Some(3),
    })
    .with_result(v(4));
    load.proofs = vec![ProofAnnotation::Wrapping, ProofAnnotation::NoOverflow];
    let mut f = function(vec![
        load,
        InstrNode::new(Inst::Store {
            ty: Ty::U32,
            ptr: v(0),
            value: v(1),
            volatile: false,
            align: Some(0),
        }),
        InstrNode::new(Inst::Return { values: vec![] }),
    ]);
    f.attrs.readnone = true;
    f.section = Some("bad\0section".into());
    f
}
fn observed(f: &Function, module: Option<&Module>) -> (FunctionValidationReport, Observer) {
    let mut observer = Observer::default();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    let report = validate_function_with_context_observed(f, module, &mut session, site()).unwrap();
    assert!(session.first_refusal().is_none());
    assert_eq!(session.remaining_fuel(), InterpretOptions::default().fuel);
    (report, observer)
}
fn parity(f: &Function, module: Option<&Module>) -> FunctionValidationReport {
    let analysis = StaticFunctionPointerAnalysis::new(f);
    let expected = validate_function_with_context_report(
        f,
        ValidationContext {
            module,
            cast_mode: if module.is_some() {
                CastValidationMode::DeferLayoutSensitive
            } else {
                CastValidationMode::FunctionOnly
            },
            pointer_bits: module.map_or(DEFAULT_POINTER_BITS, Module::pointer_bits),
        },
        &analysis,
    );
    let (actual, observer) = observed(f, module);
    assert_eq!(actual.errors, expected.errors);
    assert_eq!(actual.has_indirect_call, expected.has_indirect_call);
    assert!(observer.events.iter().all(|e| e.site == site()));
    assert_eq!(
        observer.events.last().unwrap().phase,
        ExecutionPhase::Publication
    );
    actual
}
fn error(id: u32) -> ValidationError {
    ValidationError::UnOpNotOnScalarBool { block: id }
}
fn owned_error() -> ValidationError {
    ValidationError::OperandNotPointer {
        block: 0,
        op: "retained op".repeat(32),
        ty: "retained type".repeat(64),
    }
}
fn drain(state: &mut State, work: &mut Work<'_, '_, impl ExecutionObserver>) {
    state.retire_pending(work);
    let _ = retire_validation_errors_observed(take(&mut state.errors), work.session, work.site);
}
fn empty(state: &State) -> bool {
    state.errors.capacity() == 0 && state.pending.capacity() == 0
}

fn source_module() -> Module {
    use trust_ir::proof::ProofDigest;
    use trust_ir::{SourceBindingProvenance, SourceLoopProvenance, SourcePlace, SourceProvenance};

    let mut module = Module::new("source-provenance");
    let ft = module
        .add_func_type(FuncTy {
            params: vec![Ty::U64],
            returns: vec![],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut function = Function::new(FuncId::new(0), "looping", ft, BlockId::new(0));
    let mut entry = Block::new(BlockId::new(0));
    entry.params.push((ValueId::new(0), Ty::U64));
    entry.body.push(InstrNode::new(Inst::Br {
        target: BlockId::new(1),
        args: vec![ValueId::new(0)],
    }));
    let mut header = Block::new(BlockId::new(1));
    header.params.push((ValueId::new(1), Ty::U64));
    header.body.push(InstrNode::new(Inst::Br {
        target: BlockId::new(2),
        args: vec![],
    }));
    let mut latch = Block::new(BlockId::new(2));
    latch.body.push(InstrNode::new(Inst::Br {
        target: BlockId::new(1),
        args: vec![ValueId::new(1)],
    }));
    function.blocks.extend([entry, header, latch]);
    module
        .try_add_function(function)
        .expect("Module::try_add_function: test fixture");

    let semantic = module
        .source_provenance_semantic_digest(FuncId::new(0))
        .expect("unique fixture function");
    module.functions[0].source_provenance = Some(SourceProvenance::new(
        ProofDigest::sha256_domain("test.compiler-source.v1", b"looping"),
        semantic,
        vec![SourceLoopProvenance {
            source_loop_id: 0,
            hir_local_id: 40,
            header: BlockId::new(1),
            bindings: vec![
                SourceBindingProvenance {
                    name: "limit".into(),
                    hir_local_id: 41,
                    place: SourcePlace::FunctionParameter { index: 0 },
                },
                SourceBindingProvenance {
                    name: "x".into(),
                    hir_local_id: 42,
                    place: SourcePlace::LoopParameter { index: 0 },
                },
            ],
        }],
    ));
    module
}
