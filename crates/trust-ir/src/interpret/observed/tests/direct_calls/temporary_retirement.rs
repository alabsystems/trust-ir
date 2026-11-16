// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Actual public execution controls for callee-created temporary ownership.
//! These explicit modules are test DATA; no compiler/native ABI claim follows.
use super::*;

fn callee_site(index: usize) -> ExecutionSite {
    ExecutionSite::Instruction(InstructionSite {
        function: FuncId::new(1),
        block: b(),
        instruction_index: index,
    })
}

fn dense() -> Module {
    let mut module = program();
    let ty = Ty::Array(TyId::new(0), 64);
    add(
        &mut module,
        0,
        vec![],
        vec![ty.clone()],
        vec![call(1, vec![], 0), returned(0)],
        false,
    );
    add(
        &mut module,
        1,
        vec![],
        vec![ty.clone()],
        vec![
            node(
                Inst::Const {
                    ty,
                    value: Constant::Array((0..64).map(Constant::Int).collect()),
                },
                0,
            ),
            returned(0),
        ],
        false,
    );
    module
}

#[derive(Default)]
struct Cut {
    at: usize,
    seen: usize,
    stopped: bool,
    cleanup: Vec<ExecutionProgress>,
}
impl ExecutionObserver for Cut {
    type Refusal = &'static str;
    fn admit(&mut self, event: ExecutionProgress) -> Result<(), Self::Refusal> {
        self.seen += 1;
        // The refusing event itself has not performed its admitted operation.
        if self.stopped && event.phase == ExecutionPhase::ScratchRetirement {
            self.cleanup.push(event);
        }
        if self.seen == self.at {
            self.stopped = true;
        }
        if self.stopped {
            Err("actual callee temporary cut")
        } else {
            Ok(())
        }
    }
}

fn cut(module: &Module, events: &Observer, at: usize, steps: u64) -> Cut {
    let expected = events.events[at - 1];
    let options = InterpretOptions::default();
    let mut observer = Cut {
        at,
        ..Cut::default()
    };
    let mut session = ObservedSession::new(options, &mut observer);
    let report = Interpreter::with_module(module).execute_func_observed(f(), vec![], &mut session);
    assert!(matches!(report.exit(), ObservedExit::AdmissionRefused));
    assert_eq!(report.steps(), steps);
    let first = session
        .first_refusal()
        .expect("actual selected cut must be reached");
    assert_eq!(first.cause, "actual callee temporary cut");
    assert_eq!(first.progress, expected);
    let remaining = session.remaining_fuel();
    let retry = Interpreter::with_module(module).execute_func_observed(f(), vec![], &mut session);
    assert!(matches!(retry.exit(), ObservedExit::AdmissionRefused));
    assert_eq!(retry.steps(), 0);
    assert_eq!(session.remaining_fuel(), remaining);
    assert_eq!(session.first_refusal().unwrap().progress, expected);
    assert!(observer.stopped);
    observer
}

fn host_events(trace: &Observer, site: ExecutionSite) -> Vec<usize> {
    trace
        .events
        .iter()
        .enumerate()
        .filter(|(_, e)| e.site == site && e.phase == ExecutionPhase::HostAllocation)
        .map(|(index, _)| index + 1)
        .collect()
}

// Actual B-tree cleanup admits its removal bound (>1 for these nonempty
// environments) before popping the first map value. This selects work from
// the instruction's local temporaries, before that unrelated map drain.
fn leading_local_work(observer: &Cut, site: ExecutionSite) -> usize {
    observer
        .cleanup
        .iter()
        .take_while(|e| e.work <= 1)
        .filter(|e| e.site == site)
        .map(|e| e.work)
        .sum()
}

#[test]
fn actual_unique_dense_callee_output_is_retired_after_insertion_cut() {
    let module = dense();
    let (actual, baseline) = matching(&module, vec![], InterpretOptions::default());
    assert_eq!(actual.steps, 4);
    let InterpretValueKind::Array(value) = &actual.returns[0].kind else {
        panic!("real dense baseline")
    };
    assert_eq!(value.len(), 64);
    let at = *host_events(&baseline, callee_site(0))
        .last()
        .expect("actual output map insertion");
    let observed = cut(&module, &baseline, at, 2);
    assert!(
        leading_local_work(&observed, callee_site(0)) >= 64,
        "the never-inserted unique dense payload must drain before map cleanup"
    );
}

#[test]
fn actual_partial_constant_prefix_and_failed_rope_construction_are_owned() {
    let module = dense();
    let (_, baseline) = matching(&module, vec![], InterpretOptions::default());
    let literals: Vec<_> = baseline
        .events
        .iter()
        .enumerate()
        .filter(|(_, e)| {
            e.site == callee_site(0)
                && e.phase == ExecutionPhase::LiteralElement
                && e.copy_bytes == core::mem::size_of::<InterpretValue>()
        })
        .map(|(i, _)| i + 1)
        .collect();
    assert_eq!(literals.len(), 64);
    let partial = cut(&module, &baseline, literals[32], 2);
    assert!(leading_local_work(&partial, callee_site(0)) >= 32);
    let hosts = host_events(&baseline, callee_site(0));
    let node_construction = hosts[hosts.len() - 2];
    assert_eq!(
        baseline.events[node_construction - 1].work,
        2,
        "actual rope-node admission immediately precedes output insertion"
    );
    let rope = cut(&module, &baseline, node_construction, 2);
    assert!(leading_local_work(&rope, callee_site(0)) >= 64);
}

#[test]
fn actual_partial_undef_and_clone_buffers_drain_before_source_map() {
    let mut module = program();
    add(
        &mut module,
        0,
        vec![],
        vec![Ty::I32],
        vec![call(1, vec![], 0), returned(0)],
        false,
    );
    add(
        &mut module,
        1,
        vec![],
        vec![Ty::I32],
        vec![
            node(Inst::Undef { ty: Ty::I64 }, 0),
            node(
                Inst::Copy {
                    ty: Ty::I64,
                    operand: v(0),
                },
                1,
            ),
            number(7, 2),
            returned(2),
        ],
        false,
    );
    let (actual, baseline) = matching(&module, vec![], InterpretOptions::default());
    assert_eq!(
        actual.returns,
        vec![InterpretValue::int(Ty::I32, 7).unwrap()]
    );
    for (instruction, steps) in [(0, 2), (1, 3)] {
        let bytes: Vec<_> = baseline
            .events
            .iter()
            .enumerate()
            .filter(|(_, e)| {
                e.site == callee_site(instruction)
                    && e.phase == ExecutionPhase::LiteralElement
                    && e.copy_bytes == 1
            })
            .map(|(i, _)| i + 1)
            .collect();
        assert_eq!(bytes.len(), 8);
        let stopped = cut(&module, &baseline, bytes[4], steps);
        assert!(
            leading_local_work(&stopped, callee_site(instruction)) >= 4,
            "the four newly owned bytes precede any surviving SSA-map cleanup"
        );
    }
}

#[test]
fn actual_callee_store_image_drain_precedes_unrelated_value_map_cleanup() {
    let mut module = program();
    let ty = Ty::Array(TyId::new(0), 64);
    add(
        &mut module,
        0,
        vec![],
        vec![Ty::I32],
        vec![call(1, vec![], 0), returned(0)],
        false,
    );
    add(
        &mut module,
        1,
        vec![],
        vec![Ty::I32],
        vec![
            node(
                Inst::Const {
                    ty: ty.clone(),
                    value: Constant::Array((0..64).map(Constant::Int).collect()),
                },
                0,
            ),
            node(
                Inst::Alloca {
                    ty: ty.clone(),
                    count: None,
                    align: Some(1),
                },
                1,
            ),
            void(Inst::Store {
                ty,
                ptr: v(1),
                value: v(0),
                volatile: false,
                align: Some(1),
            }),
            number(7, 2),
            returned(2),
        ],
        false,
    );
    let (actual, baseline) = matching(&module, vec![], InterpretOptions::default());
    assert_eq!(
        actual.returns,
        vec![InterpretValue::int(Ty::I32, 7).unwrap()]
    );
    let site = callee_site(2);
    let last_byte = baseline
        .events
        .iter()
        .rposition(|e| e.site == site && e.phase == ExecutionPhase::LiteralElement)
        .expect("actual complete image mapping");
    let at = baseline
        .events
        .iter()
        .enumerate()
        .skip(last_byte + 1)
        .find(|(_, e)| e.site == site && e.phase == ExecutionPhase::SparseRun)
        .map(|(i, _)| i + 1)
        .expect("actual write access after unique image construction");
    let stopped = cut(&module, &baseline, at, 4);
    assert!(
        leading_local_work(&stopped, site) >= 64,
        "the new mapped image must drain before the nonempty SSA map removal bound"
    );
}

fn semantic_error_trace(module: &Module, code: InterpretErrorCode) -> Observer {
    let ordinary = Interpreter::with_module(module)
        .execute_func(f(), vec![])
        .unwrap_err();
    assert_eq!(ordinary.code, code);
    let mut observer = Observer::default();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    let report = Interpreter::with_module(module).execute_func_observed(f(), vec![], &mut session);
    assert!(
        matches!(report.exit(), ObservedExit::ExecutedError { site, error }
        if site.function == FuncId::new(1) && site.instruction_index == 0 && error.code == code)
    );
    assert!(session.first_refusal().is_none());
    observer
}

#[test]
fn actual_arity_and_char_discard_paths_keep_owned_retirement_after_cut() {
    for invalid_char in [false, true] {
        let mut module = program();
        add(
            &mut module,
            0,
            vec![],
            vec![Ty::I32],
            vec![call(1, vec![], 0), returned(0)],
            false,
        );
        let first = if invalid_char {
            node(
                Inst::Const {
                    ty: Ty::Char,
                    value: Constant::Int(65),
                },
                0,
            )
        } else {
            number(7, 0)
        };
        add(
            &mut module,
            1,
            vec![],
            vec![Ty::I32],
            vec![first, number(7, 1), returned(1)],
            false,
        );
        // The genuine matching positive is mandatory before either refusal.
        let (actual, _) = matching(&module, vec![], InterpretOptions::default());
        assert_eq!(
            actual.returns,
            vec![InterpretValue::int(Ty::I32, 7).unwrap()]
        );
        let code = if invalid_char {
            module.functions[1].blocks[0].body[0].inst = Inst::Const {
                ty: Ty::Char,
                value: Constant::Int(0xD800),
            };
            InterpretErrorCode::UndefinedBehavior
        } else {
            module.functions[1].blocks[0].body[0].results.clear();
            InterpretErrorCode::MalformedInstruction
        };
        let error_trace = semantic_error_trace(&module, code);
        let at = error_trace
            .events
            .iter()
            .position(|e| e.site == callee_site(0) && e.phase == ExecutionPhase::ScratchRetirement)
            .map(|i| i + 1)
            .expect("actual failed bind discards its scalar output");
        let stopped = cut(&module, &error_trace, at, 2);
        assert!(
            stopped
                .cleanup
                .first()
                .is_some_and(|e| e.site == callee_site(0) && e.work > 0),
            "the immediate next primitive discard poll must keep logical work after refusal"
        );
    }
}

#[test]
fn original_root_only_dense_insertion_retains_legacy_zero_work_retirement() {
    let mut module = program();
    let ty = Ty::Array(TyId::new(0), 64);
    add(
        &mut module,
        0,
        vec![],
        vec![ty.clone()],
        vec![
            node(
                Inst::Const {
                    ty,
                    value: Constant::Array((0..64).map(Constant::Int).collect()),
                },
                0,
            ),
            returned(0),
        ],
        false,
    );
    let ordinary = Interpreter::with_module(&module)
        .execute_func(f(), vec![])
        .unwrap();
    let mut baseline = Observer::default();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut baseline);
    let report = Interpreter::with_module(&module).execute_func_observed(f(), vec![], &mut session);
    assert!(matches!(report.exit(), ObservedExit::Returned(actual) if actual == &ordinary));
    let root_site = ExecutionSite::Instruction(InstructionSite {
        function: f(),
        block: b(),
        instruction_index: 0,
    });
    let at = *host_events(&baseline, root_site).last().unwrap();
    let stopped = cut(&module, &baseline, at, 1);
    assert!(!stopped.cleanup.is_empty());
    assert!(
        stopped.cleanup.iter().all(|e| e.work == 0),
        "this repair must not change the existing no-call/root cleanup policy"
    );
}
