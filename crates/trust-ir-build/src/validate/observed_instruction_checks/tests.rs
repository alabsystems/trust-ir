// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Authored controls, UNRUN.
use super::*;
use trust_ir::interpret::InterpretOptions;
use trust_ir::{Block, FuncTyId, InstrNode};
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
    ExecutionSite::Entry(FuncId::new(94))
}
fn function(body: Vec<InstrNode>) -> Function {
    let mut function = Function::new(
        FuncId::new(94),
        "annotations",
        FuncTyId::new(0),
        BlockId::new(0),
    );
    let mut block = Block::new(BlockId::new(0));
    block.body = body;
    function.blocks = vec![block];
    function
}
fn variants(align: Option<u64>) -> Vec<Inst> {
    vec![
        Inst::Load {
            ty: Ty::I32,
            ptr: ValueId::new(0),
            volatile: false,
            align,
        },
        Inst::Store {
            ty: Ty::I32,
            ptr: ValueId::new(0),
            value: ValueId::new(1),
            volatile: false,
            align,
        },
        Inst::Alloca {
            ty: Ty::I32,
            count: None,
            align,
        },
        Inst::HeapAlloc {
            ty: Ty::I32,
            count: None,
            align,
            origin: AllocOrigin::RustHeap,
        },
    ]
}
fn fixture() -> Function {
    let mut nodes: Vec<_> = variants(Some(3)).into_iter().map(InstrNode::new).collect();
    nodes[0].proofs = vec![ProofAnnotation::Wrapping, ProofAnnotation::NoWrap];
    nodes[1].proofs = vec![ProofAnnotation::NoOverflow, ProofAnnotation::Wrapping];
    nodes.push(InstrNode::new(Inst::CallIndirect {
        callee: ValueId::new(0),
        sig: FuncTyId::new(0),
        args: vec![],
        calling_conv: CallingConv::C,
    }));
    nodes.push(InstrNode::new(Inst::Return { values: vec![] }));
    function(nodes)
}
fn observed(function: &Function) -> (ObservedFunctionInstructionChecks, Observer) {
    let mut observer = Observer::default();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    let result =
        validate_function_instruction_checks_observed(function, &mut session, site()).unwrap();
    assert!(session.first_refusal().is_none());
    assert_eq!(session.remaining_fuel(), InterpretOptions::default().fuel);
    (result, observer)
}
fn parity(function: &Function) -> ObservedFunctionInstructionChecks {
    let analysis = StaticFunctionPointerAnalysis::new(function);
    let ordinary = validate_function_with_context_report(
        function,
        ValidationContext {
            cast_mode: CastValidationMode::FunctionOnly,
            pointer_bits: DEFAULT_POINTER_BITS,
            module: None,
        },
        &analysis,
    );
    let expected: Vec<_> = ordinary
        .errors
        .into_iter()
        .filter(|error| {
            matches!(
                error,
                ValidationError::AccessAlignInvalid { .. }
                    | ValidationError::WrappingConflictsWithNoOverflow { .. }
            )
        })
        .collect();
    let (actual, observer) = observed(function);
    assert_eq!(actual.errors, expected);
    assert_eq!(actual.has_indirect_call, ordinary.has_indirect_call);
    assert!(observer.events.iter().all(|event| event.site == site()));
    assert_eq!(
        observer.events.last().unwrap().phase,
        ExecutionPhase::Publication
    );
    actual
}
#[test]
fn all_alignment_forms_and_boundary_values_match_the_actual_original_prefix() {
    for align in [
        None,
        Some(0),
        Some(1),
        Some(2),
        Some(3),
        Some(1 << 63),
        Some(u64::MAX),
    ] {
        let f = function(variants(align).into_iter().map(InstrNode::new).collect());
        let result = parity(&f);
        assert_eq!(
            result.errors.len(),
            if align.is_some_and(|n| n == 0 || !n.is_power_of_two()) {
                4
            } else {
                0
            }
        );
    }
}
#[test]
fn arithmetic_annotations_keep_all_alignment_errors_before_conflicts_and_all_indirect_forms() {
    let result = parity(&fixture());
    assert_eq!(result.errors.len(), 6);
    assert!(
        result.errors[..4]
            .iter()
            .all(|error| matches!(error, ValidationError::AccessAlignInvalid { .. }))
    );
    assert!(result.errors[4..].iter().all(|error| matches!(
        error,
        ValidationError::WrappingConflictsWithNoOverflow { block: 0 }
    )));
    for instruction in [
        Inst::CallIndirect {
            callee: ValueId::new(0),
            sig: FuncTyId::new(0),
            args: vec![],
            calling_conv: CallingConv::C,
        },
        Inst::CallIndirectCannotUnwind {
            callee: ValueId::new(0),
            sig: FuncTyId::new(0),
            args: vec![],
            calling_conv: CallingConv::C,
        },
        Inst::InvokeIndirect {
            callee: ValueId::new(0),
            sig: FuncTyId::new(0),
            args: vec![],
            normal_dest: BlockId::new(1),
            normal_args: vec![],
            unwind_dest: BlockId::new(2),
            calling_conv: CallingConv::C,
        },
    ] {
        assert!(parity(&function(vec![InstrNode::new(instruction)])).has_indirect_call);
    }
}
#[test]
fn arithmetic_pair_matrix_and_empty_function_preserve_original_classification() {
    for proofs in [
        vec![],
        vec![ProofAnnotation::Wrapping],
        vec![ProofAnnotation::NoWrap],
        vec![ProofAnnotation::NoOverflow],
        vec![ProofAnnotation::NoWrap, ProofAnnotation::NoOverflow],
        vec![ProofAnnotation::Wrapping, ProofAnnotation::Wrapping],
    ] {
        let mut node = InstrNode::new(Inst::NullPtr);
        node.proofs = proofs;
        let result = parity(&function(vec![node]));
        assert!(result.errors.is_empty());
        assert!(!result.has_indirect_call);
    }
    let mut empty = function(vec![]);
    empty.blocks.clear();
    assert!(parity(&empty).errors.is_empty());
}
#[test]
fn every_actual_instruction_check_stop_refuses_and_only_drains_fixed_errors() {
    let f = fixture();
    let (_, baseline) = observed(&f);
    for stop in 1..=baseline.events.len() {
        let mut observer = Observer {
            stop: Some(stop),
            ..Observer::default()
        };
        let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
        assert!(matches!(
            validate_function_instruction_checks_observed(&f, &mut session, site()),
            Err(ObservedValueError::AdmissionRefused)
        ));
        assert_eq!(session.first_refusal().unwrap().cause, "original stop");
        assert!(
            observer
                .events
                .iter()
                .skip(stop)
                .all(|event| event.phase == ExecutionPhase::ScratchRetirement)
        );
    }
}
#[test]
fn cumulative_work_and_requested_bytes_are_never_reset_between_prefix_calls() {
    let f = fixture();
    let (_, baseline) = observed(&f);
    for bytes in [false, true] {
        let mut observer = Observer {
            work_cap: (!bytes).then_some(baseline.work),
            byte_cap: bytes.then_some(baseline.bytes),
            ..Observer::default()
        };
        let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
        assert_eq!(
            validate_function_instruction_checks_observed(&f, &mut session, site())
                .unwrap()
                .errors
                .len(),
            6
        );
        assert!(matches!(
            validate_function_instruction_checks_observed(&f, &mut session, site()),
            Err(ObservedValueError::AdmissionRefused)
        ));
        assert_eq!(
            session.first_refusal().unwrap().cause,
            if bytes { "bytes" } else { "work" }
        );
        assert_eq!(session.remaining_fuel(), InterpretOptions::default().fuel);
    }
}
#[test]
fn error_storage_is_admitted_before_allocating_or_constructing_the_fixed_error() {
    let mut observer = Observer {
        byte_cap: Some(0),
        ..Observer::default()
    };
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    let mut work = Work {
        session: &mut session,
        site: site(),
    };
    let mut output = ObservedFunctionInstructionChecks::default();
    let constructed = core::cell::Cell::new(false);
    assert_eq!(
        output.fixed(
            || {
                constructed.set(true);
                ValidationError::AccessAlignInvalid {
                    inst: "load",
                    align: 0,
                }
            },
            &mut work
        ),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert!(!constructed.get());
    assert_eq!((output.errors.len(), output.errors.capacity()), (0, 0));
}
#[test]
fn wide_proof_list_is_interrupted_inside_real_short_circuit_annotation_scan() {
    let mut node = InstrNode::new(Inst::NullPtr);
    node.proofs = vec![ProofAnnotation::Tainted; 50_000];
    let f = function(vec![node]);
    let mut observer = Observer {
        work_cap: Some(100),
        ..Observer::default()
    };
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    assert!(matches!(
        validate_function_instruction_checks_observed(&f, &mut session, site()),
        Err(ObservedValueError::AdmissionRefused)
    ));
    assert_eq!(session.first_refusal().unwrap().cause, "work");
    assert!(observer.events.len() < 200);
}
#[test]
fn final_publication_stop_observes_actual_completed_error_retirement() {
    let f = fixture();
    let (_, baseline) = observed(&f);
    let mut observer = Observer {
        stop: Some(baseline.events.len()),
        ..Observer::default()
    };
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    assert!(matches!(
        validate_function_instruction_checks_observed(&f, &mut session, site()),
        Err(ObservedValueError::AdmissionRefused)
    ));
    assert_eq!(
        session.first_refusal().unwrap().progress.phase,
        ExecutionPhase::Publication
    );
    assert!(observer.events.len() > baseline.events.len() + 6);
    assert!(
        observer
            .events
            .iter()
            .skip(baseline.events.len())
            .all(|event| event.phase == ExecutionPhase::ScratchRetirement)
    );
}
