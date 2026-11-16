// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Real ordinary/observed function-pointer dispatch and transport comparisons.
//! These complete ABI records remain explicit test DATA, not compiler captures.
use super::*;

fn argument(ty: &Ty, place: AbiBindingPlace) -> AbiArgument {
    if matches!(ty, Ty::Func(_)) {
        AbiArgument {
            size: 8,
            align: 8,
            mode: AbiPassMode::Direct(AbiScalar {
                register: AbiRegister {
                    class: AbiRegisterClass::Integer,
                    bytes: 8,
                },
                source_offset: 0,
                source_bytes: 8,
                value_bits: 64,
                attributes: AbiAttributes::default(),
            }),
            bindings: vec![AbiBinding {
                place,
                source_offset: 0,
                source_bytes: 8,
                carrier_offset: 0,
                carrier_bytes: 8,
            }],
        }
    } else {
        direct(ty, place)
    }
}
fn abi_for(params: &[Ty], returns: &[Ty]) -> SignatureAbi {
    let mut abi = descriptor(&[], &[]);
    abi.fixed_count = params.len() as u32;
    abi.arguments = params
        .iter()
        .enumerate()
        .map(|(i, ty)| argument(ty, AbiBindingPlace::Parameter(i as u32)))
        .collect();
    abi.result = match returns {
        [] => ignored(),
        [ty] => argument(ty, AbiBindingPlace::Result(0)),
        _ => panic!("fixture needs its actual explicit multi-result model"),
    };
    abi
}
fn typed(module: &mut Module, id: u32, params: Vec<Ty>, returns: Vec<Ty>, body: Vec<InstrNode>) {
    let abi = abi_for(&params, &returns);
    add(module, id, params, returns, body, false);
    module.func_types.last_mut().unwrap().abi = Some(abi);
}
fn function(signature: u32, target: u32, result: u32) -> InstrNode {
    node(
        Inst::Const {
            ty: Ty::Func(FuncTyId::new(signature)),
            value: Constant::FnDef(FuncId::new(target)),
        },
        result,
    )
}
fn indirect(pointer: u32, signature: u32, args: Vec<ValueId>, result: u32) -> InstrNode {
    node(
        Inst::CallIndirect {
            callee: v(pointer),
            sig: FuncTyId::new(signature),
            args,
            calling_conv: crate::CallingConv::C,
        },
        result,
    )
}
fn scalar_body(delta: i128) -> Vec<InstrNode> {
    vec![number(delta, 1), add_values(0, 1, 2), returned(2)]
}
fn simple() -> Module {
    let mut module = program();
    typed(
        &mut module,
        0,
        vec![Ty::I32],
        vec![Ty::I32],
        vec![
            function(1, 9, 1),
            indirect(1, 1, vec![v(0)], 2),
            returned(2),
        ],
    );
    typed(
        &mut module,
        9,
        vec![Ty::I32],
        vec![Ty::I32],
        scalar_body(10),
    );
    module
}
fn assert_error(
    module: &Module,
    args: Vec<InterpretValue>,
    expected: InterpretErrorCode,
) -> Observer {
    let ordinary = Interpreter::with_module(module)
        .execute_func(f(), args.clone())
        .unwrap_err();
    assert_eq!(ordinary.code, expected);
    let mut observer = Observer::default();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    let report = Interpreter::with_module(module).execute_func_observed(f(), args, &mut session);
    assert!(
        matches!(report.exit(), ObservedExit::ExecutedError { error, .. } if error.code == expected)
    );
    assert!(session.first_refusal().is_none());
    observer
}
fn site(function: u32, instruction: usize) -> ExecutionSite {
    ExecutionSite::Instruction(InstructionSite {
        function: FuncId::new(function),
        block: b(),
        instruction_index: instruction,
    })
}

#[test]
fn selected_function_values_and_nested_typed_callbacks_match_exact_results() {
    let mut module = program();
    let pointer = Ty::Func(FuncTyId::new(1));
    typed(
        &mut module,
        0,
        vec![Ty::Bool, Ty::I32],
        vec![Ty::I32],
        vec![
            function(1, 9, 2),
            function(1, 12, 3),
            node(
                Inst::Copy {
                    ty: pointer.clone(),
                    operand: v(2),
                },
                4,
            ),
            node(
                Inst::Select {
                    ty: pointer.clone(),
                    cond: v(0),
                    then_val: v(4),
                    else_val: v(3),
                },
                5,
            ),
            call(3, vec![v(5), v(1)], 6),
            indirect(5, 1, vec![v(6)], 7),
            returned(7),
        ],
    );
    typed(
        &mut module,
        9,
        vec![Ty::I32],
        vec![Ty::I32],
        scalar_body(10),
    );
    typed(
        &mut module,
        12,
        vec![Ty::I32],
        vec![Ty::I32],
        scalar_body(20),
    );
    typed(
        &mut module,
        3,
        vec![pointer, Ty::I32],
        vec![Ty::I32],
        vec![indirect(0, 1, vec![v(1)], 2), returned(2)],
    );
    for (choose_first, expected) in [(true, 27), (false, 47)] {
        let (actual, trace) = matching(
            &module,
            vec![InterpretValue::bool(choose_first), int(Ty::I32, 7)],
            InterpretOptions::default(),
        );
        assert_eq!(actual.returns, vec![int(Ty::I32, expected)]);
        assert_eq!(actual.steps, 15);
        let selected = if choose_first { 9 } else { 12 };
        let foreign = if choose_first { 12 } else { 9 };
        assert!(
            trace
                .events
                .iter()
                .any(|event| event.site == site(selected, 0))
        );
        assert!(!trace.events.iter().any(|event| matches!(event.site, ExecutionSite::Instruction(s) if s.function == FuncId::new(foreign))));
    }
}

#[test]
fn actual_typed_function_pointer_entry_and_result_carriers_survive_transport() {
    let mut entry = program();
    typed(
        &mut entry,
        0,
        vec![Ty::Func(FuncTyId::new(1)), Ty::I32],
        vec![Ty::I32],
        vec![indirect(0, 1, vec![v(1)], 2), returned(2)],
    );
    typed(&mut entry, 9, vec![Ty::I32], vec![Ty::I32], scalar_body(10));
    let pointer = InterpretValue {
        ty: Ty::Func(FuncTyId::new(1)),
        kind: InterpretValueKind::FnDef(FuncId::new(9)),
    };
    let (actual, _) = matching(
        &entry,
        vec![pointer.clone(), int(Ty::I32, 7)],
        InterpretOptions::default(),
    );
    assert_eq!(actual.returns, vec![int(Ty::I32, 17)]);
    assert_error(
        &entry,
        vec![
            InterpretValue {
                kind: InterpretValueKind::NullPtr,
                ..pointer
            },
            int(Ty::I32, 7),
        ],
        InterpretErrorCode::InvalidFunctionPointer,
    );

    let mut result = program();
    typed(
        &mut result,
        0,
        vec![Ty::I32],
        vec![Ty::I32],
        vec![
            function(2, 4, 1),
            indirect(1, 2, vec![], 2),
            indirect(2, 1, vec![v(0)], 3),
            returned(3),
        ],
    );
    typed(
        &mut result,
        9,
        vec![Ty::I32],
        vec![Ty::I32],
        scalar_body(10),
    );
    typed(
        &mut result,
        4,
        vec![],
        vec![Ty::Func(FuncTyId::new(1))],
        vec![function(1, 9, 0), returned(0)],
    );
    let (actual, _) = matching(&result, vec![int(Ty::I32, 7)], InterpretOptions::default());
    assert_eq!(actual.returns, vec![int(Ty::I32, 17)]);
    assert_eq!(actual.steps, 9);
}

fn memory_word(word: u64) -> Module {
    let mut module = program();
    let pointer = Ty::Func(FuncTyId::new(1));
    typed(
        &mut module,
        0,
        vec![Ty::I32],
        vec![Ty::I32],
        vec![
            function(1, 9, 1),
            node(
                Inst::Alloca {
                    ty: pointer.clone(),
                    count: None,
                    align: Some(8),
                },
                2,
            ),
            void(Inst::Store {
                ty: pointer.clone(),
                ptr: v(2),
                value: v(1),
                volatile: false,
                align: Some(8),
            }),
            node(
                Inst::Const {
                    ty: Ty::U64,
                    value: Constant::Int(i128::from(word)),
                },
                5,
            ),
            void(Inst::Store {
                ty: Ty::U64,
                ptr: v(2),
                value: v(5),
                volatile: false,
                align: Some(8),
            }),
            node(
                Inst::Load {
                    ty: pointer,
                    ptr: v(2),
                    volatile: false,
                    align: Some(8),
                },
                3,
            ),
            indirect(3, 1, vec![v(0)], 4),
            returned(4),
        ],
    );
    typed(
        &mut module,
        9,
        vec![Ty::I32],
        vec![Ty::I32],
        scalar_body(10),
    );
    module
}

#[test]
fn actual_module_roster_code_words_roundtrip_and_bad_or_uninitialized_words_refuse() {
    // FuncId9 is the second actual roster member: its code word is2, never9.
    let baseline = memory_word(2);
    assert_eq!(baseline.functions[1].id, FuncId::new(9));
    let (actual, _) = matching(
        &baseline,
        vec![int(Ty::I32, 7)],
        InterpretOptions::default(),
    );
    assert_eq!(actual.returns, vec![int(Ty::I32, 17)]);
    for word in [0, 9, 99] {
        assert_error(
            &memory_word(word),
            vec![int(Ty::I32, 7)],
            InterpretErrorCode::InvalidFunctionPointer,
        );
    }
    let mut poison = baseline.clone();
    poison.functions[0].blocks[0].body[3].inst = Inst::Undef { ty: Ty::U64 };
    assert_error(
        &poison,
        vec![int(Ty::I32, 7)],
        InterpretErrorCode::UndefinedBehavior,
    );
}

#[test]
fn exact_signature_ids_and_complete_actual_abi_comparisons_are_mandatory() {
    let mut baseline = simple();
    baseline.func_types.push(baseline.func_types[1].clone());
    baseline.functions[0].blocks[0].body[0] = function(2, 9, 1);
    baseline.functions[0].blocks[0].body[1] = indirect(1, 2, vec![v(0)], 2);
    let (actual, _) = matching(
        &baseline,
        vec![int(Ty::I32, 7)],
        InterpretOptions::default(),
    );
    assert_eq!(actual.returns, vec![int(Ty::I32, 17)]);
    for which in 0..4 {
        let mut changed = baseline.clone();
        let expected = match which {
            0 => {
                changed.functions[0].blocks[0].body[0] = function(0, 9, 1);
                InterpretErrorCode::SignatureMismatch
            }
            1 => {
                changed.functions[0].blocks[0].body[1] = indirect(1, 0, vec![v(0)], 2);
                InterpretErrorCode::SignatureMismatch
            }
            2 => {
                changed.functions[0].blocks[0].body[0] = function(2, 99, 1);
                InterpretErrorCode::InvalidFunctionPointer
            }
            _ => {
                changed.func_types[2]
                    .abi
                    .as_mut()
                    .unwrap()
                    .frontend
                    .revision
                    .push_str("_foreign");
                InterpretErrorCode::SignatureMismatch
            }
        };
        let trace = assert_error(&changed, vec![int(Ty::I32, 7)], expected);
        assert!(!trace.events.iter().any(|event| matches!(event.site, ExecutionSite::Instruction(s) if s.function == FuncId::new(9))), "a refused signature must not execute the actual target");
    }
}

#[test]
fn arguments_results_and_real_callee_char_failures_keep_their_actual_errors() {
    let baseline = simple();
    let (actual, _) = matching(
        &baseline,
        vec![int(Ty::I32, 7)],
        InterpretOptions::default(),
    );
    assert_eq!(actual.returns, vec![int(Ty::I32, 17)]);
    let mut args = baseline.clone();
    args.functions[0].blocks[0].body[1] = indirect(1, 1, vec![], 2);
    assert_error(
        &args,
        vec![int(Ty::I32, 7)],
        InterpretErrorCode::SignatureMismatch,
    );
    let mut results = baseline.clone();
    results.functions[0].blocks[0].body[1].results.clear();
    assert_error(
        &results,
        vec![int(Ty::I32, 7)],
        InterpretErrorCode::MalformedInstruction,
    );

    let mut character = program();
    typed(
        &mut character,
        0,
        vec![Ty::I32],
        vec![Ty::I32],
        vec![
            function(1, 9, 1),
            indirect(1, 1, vec![v(0)], 2),
            returned(2),
        ],
    );
    typed(
        &mut character,
        9,
        vec![Ty::I32],
        vec![Ty::I32],
        vec![
            node(
                Inst::Const {
                    ty: Ty::Char,
                    value: Constant::Int(65),
                },
                1,
            ),
            returned(0),
        ],
    );
    matching(
        &character,
        vec![int(Ty::I32, 7)],
        InterpretOptions::default(),
    );
    character.functions[1].blocks[0].body[0].inst = Inst::Const {
        ty: Ty::Char,
        value: Constant::Int(0xD800),
    };
    let trace = assert_error(
        &character,
        vec![int(Ty::I32, 7)],
        InterpretErrorCode::UndefinedBehavior,
    );
    assert!(trace.events.iter().any(|event| event.site == site(9, 0)));
}

#[test]
fn pointer_is_evaluated_before_arguments_but_validated_after_them() {
    let mut module = program();
    typed(
        &mut module,
        0,
        vec![Ty::Func(FuncTyId::new(1)), Ty::I32],
        vec![Ty::I32],
        vec![indirect(0, 1, vec![v(1)], 2), returned(2)],
    );
    typed(
        &mut module,
        9,
        vec![Ty::I32],
        vec![Ty::I32],
        scalar_body(10),
    );
    let pointer = InterpretValue {
        ty: Ty::Func(FuncTyId::new(1)),
        kind: InterpretValueKind::FnDef(FuncId::new(9)),
    };
    matching(
        &module,
        vec![pointer.clone(), int(Ty::I32, 7)],
        InterpretOptions::default(),
    );
    module.functions[0].blocks[0].body[0] = indirect(0, 1, vec![v(99)], 2);
    let arguments = vec![
        InterpretValue {
            kind: InterpretValueKind::NullPtr,
            ..pointer
        },
        int(Ty::I32, 7),
    ];
    let ordinary = Interpreter::with_module(&module)
        .execute_func(f(), arguments.clone())
        .unwrap_err();
    assert_ne!(
        ordinary.code,
        InterpretErrorCode::InvalidFunctionPointer,
        "missing argument lookup precedes null validation"
    );
    assert_error(&module, arguments, ordinary.code);
}

struct Stop {
    at: usize,
    seen: usize,
    stopped: bool,
    events: Vec<ExecutionProgress>,
    cleanup: usize,
}
impl ExecutionObserver for Stop {
    type Refusal = &'static str;
    fn admit(&mut self, event: ExecutionProgress) -> Result<(), Self::Refusal> {
        self.seen += 1;
        if self.stopped && event.phase == ExecutionPhase::ScratchRetirement {
            self.cleanup += event.work;
        }
        self.events.push(event);
        if self.seen == self.at {
            self.stopped = true;
        }
        if self.stopped {
            Err("original indirect call stopped")
        } else {
            Ok(())
        }
    }
}
fn stopped(
    module: &Module,
    args: Vec<InterpretValue>,
    baseline: &Observer,
    at: usize,
    steps: u64,
) -> Stop {
    let expected = baseline.events[at - 1];
    let mut observer = Stop {
        at,
        seen: 0,
        stopped: false,
        events: vec![],
        cleanup: 0,
    };
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    let report = Interpreter::with_module(module).execute_func_observed(f(), args, &mut session);
    assert!(matches!(report.exit(), ObservedExit::AdmissionRefused));
    assert_eq!(report.steps(), steps);
    assert_eq!(session.first_refusal().unwrap().progress, expected);
    assert_eq!(
        session.first_refusal().unwrap().cause,
        "original indirect call stopped"
    );
    let fuel = session.remaining_fuel();
    let retry = Interpreter::with_module(module).execute_func_observed(f(), vec![], &mut session);
    assert_eq!(retry.steps(), 0);
    assert!(matches!(retry.exit(), ObservedExit::AdmissionRefused));
    assert_eq!(session.remaining_fuel(), fuel);
    assert_eq!(session.first_refusal().unwrap().progress, expected);
    observer
}

#[test]
fn paid_complete_signature_comparison_can_stop_before_any_callee_dispatch() {
    let module = simple();
    let (_, baseline) = matching(&module, vec![int(Ty::I32, 7)], InterpretOptions::default());
    let at = baseline
        .events
        .iter()
        .enumerate()
        .filter(|(_, event)| event.site == site(0, 1) && event.phase == ExecutionPhase::Publication)
        .map(|(i, _)| i + 1)
        .next_back()
        .expect("actual borrowed full-signature comparison publishes its data result");
    let cut = stopped(&module, vec![int(Ty::I32, 7)], &baseline, at, 2);
    assert!(!cut.events.iter().any(
        |event| matches!(event.site, ExecutionSite::Instruction(s) if s.function == FuncId::new(9))
    ));
    assert!(
        cut.cleanup > 0,
        "actual pointer/argument temporaries retain owned cleanup"
    );
}

#[test]
fn indirect_unique_callee_output_retains_owned_cleanup_after_insertion_cut() {
    let mut module = program();
    let array = Ty::Array(TyId::new(0), 64);
    typed(
        &mut module,
        0,
        vec![],
        vec![array.clone()],
        vec![function(1, 9, 0), indirect(0, 1, vec![], 1), returned(1)],
    );
    typed(
        &mut module,
        9,
        vec![],
        vec![array.clone()],
        vec![
            node(
                Inst::Const {
                    ty: array,
                    value: Constant::Array((0..64).map(Constant::Int).collect()),
                },
                0,
            ),
            returned(0),
        ],
    );
    let (actual, baseline) = matching(&module, vec![], InterpretOptions::default());
    assert_eq!(actual.steps, 5);
    let at = baseline
        .events
        .iter()
        .enumerate()
        .filter(|(_, event)| {
            event.site == site(9, 0) && event.phase == ExecutionPhase::HostAllocation
        })
        .map(|(i, _)| i + 1)
        .next_back()
        .expect("actual unique64 callee output insertion");
    let cut = stopped(&module, vec![], &baseline, at, 3);
    assert!(
        cut.cleanup >= 64,
        "the actual new dense graph was never installed or inherited"
    );
}

#[test]
fn fuel_and_depth_are_shared_across_real_indirect_recursion() {
    let mut module = simple();
    matching(&module, vec![int(Ty::I32, 7)], InterpretOptions::default());
    let depth_options = InterpretOptions {
        fuel: 100,
        max_call_depth: 1,
        ..InterpretOptions::default()
    };
    matching(&module, vec![int(Ty::I32, 7)], depth_options);
    module.functions[1].blocks[0].body = vec![
        function(1, 9, 1),
        indirect(1, 1, vec![v(0)], 2),
        returned(2),
    ];
    for (options, steps) in [
        (
            InterpretOptions {
                fuel: 32,
                max_call_depth: 256,
                ..InterpretOptions::default()
            },
            32,
        ),
        (depth_options, 4),
    ] {
        let ordinary = Interpreter::with_module(&module)
            .with_options(options)
            .execute_func(f(), vec![int(Ty::I32, 7)])
            .unwrap_err();
        assert_eq!(ordinary.code, InterpretErrorCode::OutOfFuel);
        let mut observer = Observer::default();
        let mut session = ObservedSession::new(options, &mut observer);
        let report = Interpreter::with_module(&module)
            .with_options(options)
            .execute_func_observed(f(), vec![int(Ty::I32, 7)], &mut session);
        assert!(
            matches!(report.exit(), ObservedExit::InterpreterLimit { error, .. } if error.code == InterpretErrorCode::OutOfFuel)
        );
        assert_eq!(report.steps(), steps);
        assert_eq!(session.remaining_fuel(), options.fuel - steps);
        assert!(session.first_refusal().is_none());
    }
}

#[test]
fn declared_convention_host_and_unimplemented_unwind_never_become_calls() {
    let baseline = simple();
    matching(
        &baseline,
        vec![int(Ty::I32, 7)],
        InterpretOptions::default(),
    );
    for which in 0..3 {
        let mut changed = baseline.clone();
        match which {
            0 => {
                if let Inst::CallIndirect { calling_conv, .. } =
                    &mut changed.functions[0].blocks[0].body[1].inst
                {
                    *calling_conv = crate::CallingConv::CUnwind;
                }
            }
            1 => changed.functions[1].blocks.clear(),
            _ => {
                changed.functions[0].blocks[0].body[1].inst = Inst::CallIndirectCannotUnwind {
                    callee: v(1),
                    sig: FuncTyId::new(1),
                    args: vec![v(0)],
                    calling_conv: crate::CallingConv::C,
                }
            }
        }
        let mut observer = Observer::default();
        let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
        let report = Interpreter::with_module(&changed).execute_func_observed(
            f(),
            vec![int(Ty::I32, 7)],
            &mut session,
        );
        match which {
            0 => assert!(
                matches!(report.exit(), ObservedExit::ExecutedError { error, .. } if error.code == InterpretErrorCode::SignatureMismatch)
            ),
            _ => assert!(matches!(
                report.exit(),
                ObservedExit::UnsupportedObservation { .. }
            )),
        }
        assert!(session.first_refusal().is_none());
        assert!(!observer.events.iter().any(|event| matches!(event.site, ExecutionSite::Instruction(s) if s.function == FuncId::new(9))));
    }
}

#[test]
fn unused_function_pointer_only_records_keep_whole_module_validation() {
    let mut baseline = simple();
    baseline.func_types.push(baseline.func_types[1].clone());
    baseline.types.push(Ty::Func(FuncTyId::new(2)));
    let (actual, _) = matching(
        &baseline,
        vec![int(Ty::I32, 7)],
        InterpretOptions::default(),
    );
    assert_eq!(actual.returns, vec![int(Ty::I32, 17)]);
    for unsupported_contract in [false, true] {
        let mut changed = baseline.clone();
        if unsupported_contract {
            let AbiPassMode::Direct(scalar) =
                &mut changed.func_types[2].abi.as_mut().unwrap().arguments[0].mode
            else {
                panic!("actual direct fixture")
            };
            scalar.attributes.no_alias = true;
        } else {
            changed.func_types[2]
                .abi
                .as_mut()
                .unwrap()
                .target
                .pointer_bytes = 4;
        }
        let mut observer = Observer::default();
        let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
        let report = Interpreter::with_module(&changed).execute_func_observed(
            f(),
            vec![int(Ty::I32, 7)],
            &mut session,
        );
        if unsupported_contract {
            assert!(matches!(
                report.exit(),
                ObservedExit::UnsupportedObservation { .. }
            ));
        } else {
            assert!(
                matches!(report.exit(),ObservedExit::EntryRejected(error) if error.code==InterpretErrorCode::SignatureMismatch)
            );
        }
        assert_eq!(report.steps(), 0);
        assert!(session.first_refusal().is_none());
    }
}
