// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Actual public ordinary/observed dispatch comparisons. These explicit ABI
//! records are test DATA, never native compiler captures or target ABI proof.
use super::*;
use crate::signature_abi::*;

fn ignored() -> AbiArgument {
    AbiArgument {
        size: 0,
        align: 1,
        mode: AbiPassMode::Ignore,
        bindings: vec![],
    }
}
fn geometry(ty: &Ty) -> (u64, u16) {
    match ty {
        Ty::I32 => (4, 32),
        Ty::I8 | Ty::U8 => (1, 8),
        Ty::Ptr => (8, 64),
        Ty::Bool => (1, 1),
        Ty::Array(_, len) => (*len, u16::try_from(*len * 8).unwrap()),
        _ => panic!("explicit fixture type changed"),
    }
}
fn direct(ty: &Ty, place: AbiBindingPlace) -> AbiArgument {
    let (bytes, bits) = geometry(ty);
    let mode = if matches!(ty, Ty::Array(..)) {
        AbiPassMode::Cast {
            pad_i32: false,
            prefix: vec![],
            rest_offset: Some(0),
            rest: AbiUniform {
                unit: AbiRegister {
                    class: AbiRegisterClass::Integer,
                    bytes: 8,
                },
                total: bytes,
                consecutive: false,
            },
            attributes: AbiAttributes::default(),
        }
    } else {
        AbiPassMode::Direct(AbiScalar {
            register: AbiRegister {
                class: AbiRegisterClass::Integer,
                bytes,
            },
            source_offset: 0,
            source_bytes: bytes,
            value_bits: bits,
            attributes: AbiAttributes::default(),
        })
    };
    AbiArgument {
        size: bytes,
        align: 1,
        mode,
        bindings: vec![AbiBinding {
            place,
            source_offset: 0,
            source_bytes: bytes,
            carrier_offset: 0,
            carrier_bytes: bytes,
        }],
    }
}
fn descriptor(params: &[Ty], returns: &[Ty]) -> SignatureAbi {
    SignatureAbi {
        target: AbiTarget {
            triple: "aarch64-apple-darwin".into(),
            data_layout: "e-p:64:64-i64:64-i128:128".into(),
            abi: "darwinpcs".into(),
            cpu: "reference-model-test".into(),
            features: vec![],
            target_spec: "model-data-only".into(),
            pointer_bytes: 8,
            little_endian: true,
        },
        frontend: AbiFrontend {
            name: "observed-call-model-test".into(),
            revision: "not-a-compiler-capture".into(),
        },
        convention: "C".into(),
        lowered_convention: crate::CallingConv::C,
        source_abi: "C".into(),
        can_unwind: false,
        variadic: false,
        fixed_count: params.len() as u32,
        arguments: params
            .iter()
            .enumerate()
            .map(|(index, ty)| direct(ty, AbiBindingPlace::Parameter(index as u32)))
            .collect(),
        result: match returns {
            [] => ignored(),
            [ty] => direct(ty, AbiBindingPlace::Result(0)),
            _ => panic!("multi-result fixture needs its exact explicit pair"),
        },
    }
}
fn program() -> Module {
    let mut module = Module::new("observed_actual_direct_calls");
    module.types.push(Ty::U8);
    module.target_info = Some(crate::TargetInfo {
        triple: "aarch64-apple-darwin".into(),
        pointer_size: 8,
        endianness: crate::Endianness::Little,
        abi: Some("darwinpcs".into()),
        struct_passing: crate::StructPassingPolicy::NativeC,
    });
    module
}
fn add(
    module: &mut Module,
    id: u32,
    params: Vec<Ty>,
    returns: Vec<Ty>,
    body: Vec<InstrNode>,
    typed: bool,
) {
    let mut signature = FuncTy::unrecorded(params.clone(), returns.clone(), false);
    if typed {
        signature.abi = Some(descriptor(&params, &returns));
    }
    let ty = FuncTyId::new(module.func_types.len() as u32);
    module.func_types.push(signature);
    let mut function = Function::new(FuncId::new(id), format!("actual_function_{id}"), ty, b());
    let mut block = Block::new(b());
    block.params = params
        .into_iter()
        .enumerate()
        .map(|(index, ty)| (v(index as u32), ty))
        .collect();
    block.body = body;
    function.blocks.push(block);
    module.functions.push(function);
}
fn number(value: i128, result: u32) -> InstrNode {
    node(
        Inst::Const {
            ty: Ty::I32,
            value: Constant::Int(value),
        },
        result,
    )
}
fn call(callee: u32, args: Vec<ValueId>, result: u32) -> InstrNode {
    node(
        Inst::Call {
            callee: FuncId::new(callee),
            args,
        },
        result,
    )
}
fn add_values(lhs: u32, rhs: u32, result: u32) -> InstrNode {
    node(
        Inst::BinOp {
            op: crate::BinOp::Add,
            ty: Ty::I32,
            lhs: v(lhs),
            rhs: v(rhs),
        },
        result,
    )
}
fn returned(value: u32) -> InstrNode {
    void(Inst::Return {
        values: vec![v(value)],
    })
}
fn matching(
    module: &Module,
    arguments: Vec<InterpretValue>,
    options: InterpretOptions,
) -> (InterpretOutcome, Observer) {
    let expected = Interpreter::with_module(module)
        .with_options(options)
        .execute_func(f(), arguments.clone())
        .expect("actual ordinary direct-call baseline must succeed");
    let mut observer = Observer::default();
    let mut session = ObservedSession::new(options, &mut observer);
    let report = Interpreter::with_module(module)
        .with_options(options)
        .execute_func_observed(f(), arguments, &mut session);
    match report.exit() {
        ObservedExit::Returned(actual) => assert_eq!(actual, &expected),
        other => panic!("actual observed direct-call baseline must succeed: {other:?}"),
    };
    assert_eq!(session.remaining_fuel(), options.fuel - expected.steps);
    assert!(session.first_refusal().is_none());
    assert!(
        observer.events.iter().any(
            |event| matches!(event.site,ExecutionSite::Instruction(site) if site.function!=f())
        )
    );
    (expected, observer)
}
fn nested(typed: bool) -> Module {
    let mut module = program();
    add(
        &mut module,
        0,
        vec![Ty::I32],
        vec![Ty::I32],
        vec![
            number(20, 1),
            call(1, vec![v(0)], 2),
            add_values(2, 1, 3),
            call(1, vec![v(0)], 4),
            add_values(3, 4, 5),
            returned(5),
        ],
        typed,
    );
    add(
        &mut module,
        1,
        vec![Ty::I32],
        vec![Ty::I32],
        vec![
            number(1, 1),
            call(2, vec![v(0)], 2),
            add_values(2, 1, 3),
            returned(3),
        ],
        typed,
    );
    add(
        &mut module,
        2,
        vec![Ty::I32],
        vec![Ty::I32],
        vec![
            node(
                Inst::UnOp {
                    op: crate::UnOp::Not,
                    ty: Ty::I32,
                    operand: v(0),
                },
                1,
            ),
            returned(1),
        ],
        typed,
    );
    if typed {
        let argument = &mut module.func_types[1].abi.as_mut().unwrap().arguments[0];
        argument.size = 1;
        argument.bindings[0].source_bytes = 1;
        if let AbiPassMode::Direct(scalar) = &mut argument.mode {
            scalar.source_bytes = 1;
            scalar.value_bits = 8;
            scalar.attributes.extension = AbiExtension::Sign;
        }
    }
    module
}

#[test]
fn actual_nested_typed_boundaries_restore_caller_ssa_and_share_fuel() {
    let module = nested(true);
    let (outcome, observer) = matching(
        &module,
        vec![int(Ty::I32, 511)],
        InterpretOptions::default(),
    );
    assert_eq!(outcome.returns, vec![int(Ty::I32, 22)]);
    assert_eq!(outcome.steps, 18);
    for id in [1, 2] {
        assert!(observer.events.iter().any(|event|matches!(event.site,ExecutionSite::Instruction(site) if site.function==FuncId::new(id))));
    }
    // Independent unrecorded DATA fixture, not descriptor erasure or a weaker
    // observed substitute. Its different full-width semantics must also agree.
    let legacy = nested(false);
    let (legacy, _) = matching(
        &legacy,
        vec![int(Ty::I32, 511)],
        InterpretOptions::default(),
    );
    assert_eq!(legacy.returns, vec![int(Ty::I32, -1002)]);
}

#[test]
fn actual_direct_callee_reads_and_writes_the_same_live_memory() {
    let mut module = program();
    add(
        &mut module,
        0,
        vec![],
        vec![Ty::I32],
        vec![
            node(
                Inst::Alloca {
                    ty: Ty::I32,
                    count: None,
                    align: Some(4),
                },
                0,
            ),
            number(7, 1),
            void(Inst::Store {
                ty: Ty::I32,
                ptr: v(0),
                value: v(1),
                volatile: false,
                align: Some(4),
            }),
            number(1, 2),
            call(1, vec![v(0), v(2)], 3),
            node(
                Inst::Load {
                    ty: Ty::I32,
                    ptr: v(0),
                    volatile: false,
                    align: Some(4),
                },
                4,
            ),
            add_values(3, 4, 5),
            returned(5),
        ],
        true,
    );
    add(
        &mut module,
        1,
        vec![Ty::Ptr, Ty::I32],
        vec![Ty::I32],
        vec![
            node(
                Inst::Load {
                    ty: Ty::I32,
                    ptr: v(0),
                    volatile: false,
                    align: Some(4),
                },
                2,
            ),
            add_values(2, 1, 3),
            void(Inst::Store {
                ty: Ty::I32,
                ptr: v(0),
                value: v(3),
                volatile: false,
                align: Some(4),
            }),
            returned(3),
        ],
        true,
    );
    let (outcome, _) = matching(&module, vec![], InterpretOptions::default());
    assert_eq!(outcome.returns, vec![int(Ty::I32, 16)]);
    let mut missing = module.clone();
    missing.functions[0].blocks[0].body[0] = node(Inst::NullPtr, 0);
    let expected = Interpreter::with_module(&missing)
        .execute_func(f(), [])
        .unwrap_err();
    assert_eq!(expected.code, InterpretErrorCode::UndefinedBehavior);
    let report = run(&missing, vec![], &mut Observer::default());
    assert!(
        matches!(report.exit(),ObservedExit::ExecutedError {error,..} if error.code==InterpretErrorCode::UndefinedBehavior)
    );
}

#[test]
fn actual_direct_partial_register_carrier_keeps_padding_poison_in_callee() {
    let mut module = program();
    add(
        &mut module,
        0,
        vec![Ty::I32],
        vec![Ty::I8],
        vec![call(1, vec![v(0)], 1), returned(1)],
        true,
    );
    add(
        &mut module,
        1,
        vec![Ty::I32],
        vec![Ty::I8],
        vec![
            node(
                Inst::Alloca {
                    ty: Ty::I32,
                    count: None,
                    align: Some(4),
                },
                1,
            ),
            void(Inst::Store {
                ty: Ty::I32,
                ptr: v(1),
                value: v(0),
                volatile: false,
                align: Some(4),
            }),
            node(
                Inst::Load {
                    ty: Ty::I8,
                    ptr: v(1),
                    volatile: false,
                    align: Some(1),
                },
                2,
            ),
            returned(2),
        ],
        true,
    );
    let argument = &mut module.func_types[1].abi.as_mut().unwrap().arguments[0];
    argument.size = 1;
    argument.bindings[0].source_bytes = 1;
    if let AbiPassMode::Direct(scalar) = &mut argument.mode {
        scalar.source_bytes = 1;
        scalar.value_bits = 8;
    }
    let (outcome, _) = matching(&module, vec![int(Ty::I32, 7)], InterpretOptions::default());
    assert_eq!(outcome.returns, vec![int(Ty::I8, 7)]);
    let mut changed = module.clone();
    changed.func_types[1].returns = vec![Ty::I32];
    changed.func_types[1].abi.as_mut().unwrap().result =
        direct(&Ty::I32, AbiBindingPlace::Result(0));
    changed.functions[1].blocks[0].body[2] = node(
        Inst::Load {
            ty: Ty::I32,
            ptr: v(1),
            volatile: false,
            align: Some(4),
        },
        2,
    );
    assert_eq!(
        Interpreter::with_module(&changed)
            .execute_func(f(), [int(Ty::I32, 7)])
            .unwrap_err()
            .code,
        InterpretErrorCode::UndefinedBehavior
    );
    let report = run(&changed, vec![int(Ty::I32, 7)], &mut Observer::default());
    // The ordinary load transports poison. The full-width result descriptor
    // first requires those live bits at the callee's actual Return boundary.
    assert_eq!(report.steps(), 5);
    assert!(
        matches!(report.exit(),ObservedExit::ExecutedError {site,error} if site.function==FuncId::new(1) && site.instruction_index==3 && error.code==InterpretErrorCode::UndefinedBehavior),
        "actual partial-register result: {:?}",
        report.exit()
    );
}

#[test]
fn real_direct_target_arity_and_result_count_mutations_keep_actual_call_site() {
    let module = nested(true);
    matching(
        &module,
        vec![int(Ty::I32, 511)],
        InterpretOptions::default(),
    );
    for change in 0..3 {
        let mut changed = module.clone();
        let node = &mut changed.functions[0].blocks[0].body[1];
        match change {
            0 => {
                if let Inst::Call { callee, .. } = &mut node.inst {
                    *callee = FuncId::new(99);
                }
            }
            1 => {
                if let Inst::Call { args, .. } = &mut node.inst {
                    args.clear();
                }
            }
            2 => node.results.clear(),
            _ => unreachable!(),
        }
        let expected = Interpreter::with_module(&changed)
            .execute_func(f(), [int(Ty::I32, 511)])
            .unwrap_err();
        let code = [
            InterpretErrorCode::MissingFunction,
            InterpretErrorCode::SignatureMismatch,
            InterpretErrorCode::MalformedInstruction,
        ][change];
        assert_eq!(expected.code, code);
        let report = run(&changed, vec![int(Ty::I32, 511)], &mut Observer::default());
        assert!(
            matches!(report.exit(),ObservedExit::ExecutedError {site,error} if site.function==f() && site.instruction_index==1 && error.code==code)
        );
    }
}

#[test]
fn direct_call_depth_and_fuel_are_shared_with_every_real_callee() {
    let module = nested(true);
    matching(
        &module,
        vec![int(Ty::I32, 511)],
        InterpretOptions::default(),
    );
    let options = InterpretOptions {
        fuel: 7,
        ..InterpretOptions::default()
    };
    assert_eq!(
        Interpreter::with_module(&module)
            .with_options(options)
            .execute_func(f(), [int(Ty::I32, 511)])
            .unwrap_err()
            .code,
        InterpretErrorCode::OutOfFuel
    );
    let mut observer = Observer::default();
    let mut session = ObservedSession::new(options, &mut observer);
    let report = Interpreter::with_module(&module)
        .with_options(options)
        .execute_func_observed(f(), vec![int(Ty::I32, 511)], &mut session);
    assert!(
        matches!(report.exit(),ObservedExit::InterpreterLimit {error,..} if error.code==InterpretErrorCode::OutOfFuel)
    );
    assert_eq!(report.steps(), 7);
    assert_eq!(session.remaining_fuel(), 0);
    let again = Interpreter::with_module(&module)
        .with_options(options)
        .execute_func_observed(f(), vec![int(Ty::I32, 511)], &mut session);
    assert!(
        matches!(again.exit(),ObservedExit::InterpreterLimit {error,..} if error.code==InterpretErrorCode::OutOfFuel)
    );
    assert_eq!(again.steps(), 0);
    let depth = InterpretOptions {
        max_call_depth: 1,
        ..InterpretOptions::default()
    };
    let mut one = module.clone();
    for node in &mut one.functions[0].blocks[0].body {
        if let Inst::Call { callee, .. } = &mut node.inst {
            *callee = FuncId::new(2);
        }
    }
    matching(&one, vec![int(Ty::I32, 511)], depth);
    assert_eq!(
        Interpreter::with_module(&module)
            .with_options(depth)
            .execute_func(f(), [int(Ty::I32, 511)])
            .unwrap_err()
            .code,
        InterpretErrorCode::OutOfFuel
    );
    let mut observer = Observer::default();
    let mut session = ObservedSession::new(depth, &mut observer);
    let report = Interpreter::with_module(&module)
        .with_options(depth)
        .execute_func_observed(f(), vec![int(Ty::I32, 511)], &mut session);
    assert!(
        matches!(report.exit(),ObservedExit::InterpreterLimit {site:ExecutionSite::Instruction(site),error} if site.function==FuncId::new(1) && error.code==InterpretErrorCode::OutOfFuel)
    );
}

#[test]
fn callee_panic_and_original_cancellation_drain_saved_frames_without_catching() {
    let mut module = program();
    add(
        &mut module,
        0,
        vec![],
        vec![Ty::I32],
        vec![call(1, vec![], 0), returned(0)],
        true,
    );
    add(
        &mut module,
        1,
        vec![],
        vec![Ty::I32],
        vec![
            node(
                Inst::Const {
                    ty: Ty::Bool,
                    value: Constant::Bool(true),
                },
                0,
            ),
            void(Inst::Assert {
                cond: v(0),
                kind: crate::AssertKind::Unspecified,
                site: None,
            }),
            number(7, 1),
            returned(1),
        ],
        true,
    );
    matching(&module, vec![], InterpretOptions::default());
    let mut panic = module.clone();
    panic.functions[1].blocks[0].body[0] = node(
        Inst::Const {
            ty: Ty::Bool,
            value: Constant::Bool(false),
        },
        0,
    );
    let expected = Interpreter::with_module(&panic)
        .execute_func(f(), [])
        .unwrap_err();
    assert_eq!(expected.code, InterpretErrorCode::Panic);
    let report = run(&panic, vec![], &mut Observer::default());
    assert!(
        matches!(report.exit(),ObservedExit::ExecutedError {site,error} if site.function==FuncId::new(1) && site.instruction_index==1 && error.code==InterpretErrorCode::Panic && error.panic==expected.panic)
    );
    struct Cancel {
        stopped: bool,
        cleanup: usize,
    }
    impl ExecutionObserver for Cancel {
        type Refusal = &'static str;
        fn admit(&mut self, event: ExecutionProgress) -> Result<(), Self::Refusal> {
            if event.phase == ExecutionPhase::Instruction
                && matches!(event.site,ExecutionSite::Instruction(site) if site.function==FuncId::new(1) && site.instruction_index==1)
            {
                self.stopped = true;
            }
            if self.stopped && event.phase == ExecutionPhase::ScratchRetirement {
                self.cleanup += event.work;
            }
            if self.stopped {
                Err("original callee cancellation")
            } else {
                Ok(())
            }
        }
    }
    let mut observer = Cancel {
        stopped: false,
        cleanup: 0,
    };
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    let report = Interpreter::with_module(&module).execute_func_observed(f(), vec![], &mut session);
    assert!(matches!(report.exit(), ObservedExit::AdmissionRefused));
    assert_eq!(
        session.first_refusal().unwrap().cause,
        "original callee cancellation"
    );
    assert!(observer.cleanup != 0);
}

#[test]
fn final_publication_refusal_retires_actual_returned_call_graph_with_original_owner() {
    let mut module = program();
    let ty = Ty::Array(TyId::new(0), 64);
    add(
        &mut module,
        0,
        vec![ty.clone()],
        vec![ty.clone()],
        vec![call(1, vec![v(0)], 1), returned(1)],
        true,
    );
    add(
        &mut module,
        1,
        vec![ty.clone()],
        vec![ty.clone()],
        vec![returned(0)],
        true,
    );
    let value = InterpretValue {
        ty,
        kind: InterpretValueKind::Array(ArrayValue::from_vec(
            (0..64).map(|value| int(Ty::U8, value)).collect(),
        )),
    };
    matching(&module, vec![value.clone()], InterpretOptions::default());
    struct Stop {
        stopped: bool,
        cleanup: usize,
    }
    impl ExecutionObserver for Stop {
        type Refusal = &'static str;
        fn admit(&mut self, event: ExecutionProgress) -> Result<(), Self::Refusal> {
            if event.phase == ExecutionPhase::Publication
                && matches!(event.site,ExecutionSite::Instruction(site) if site.function==f() && site.instruction_index==1)
            {
                self.stopped = true;
            }
            if self.stopped && event.phase == ExecutionPhase::ScratchRetirement {
                self.cleanup += event.work;
            }
            if self.stopped {
                Err("original call publication stopped")
            } else {
                Ok(())
            }
        }
    }
    let mut observer = Stop {
        stopped: false,
        cleanup: 0,
    };
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    let report =
        Interpreter::with_module(&module).execute_func_observed(f(), vec![value], &mut session);
    assert!(matches!(report.exit(), ObservedExit::AdmissionRefused));
    let cause = session.first_refusal().unwrap();
    assert_eq!(cause.cause, "original call publication stopped");
    assert_eq!(cause.progress.phase, ExecutionPhase::Publication);
    assert!(observer.cleanup >= 64);
}

fn pair_results() -> Module {
    let mut module = program();
    let mut edge = void(Inst::Call {
        callee: FuncId::new(1),
        args: vec![v(0)],
    });
    edge.results = vec![v(1), v(2)];
    add(
        &mut module,
        0,
        vec![Ty::I32],
        vec![Ty::I32],
        vec![edge, add_values(1, 2, 3), returned(3)],
        true,
    );
    add(
        &mut module,
        1,
        vec![Ty::I32],
        vec![Ty::I32, Ty::I32],
        vec![
            number(1, 1),
            add_values(0, 1, 2),
            void(Inst::Return {
                values: vec![v(0), v(2)],
            }),
        ],
        false,
    );
    let scalar = |offset| AbiScalar {
        register: AbiRegister {
            class: AbiRegisterClass::Integer,
            bytes: 4,
        },
        source_offset: offset,
        source_bytes: 4,
        value_bits: 32,
        attributes: AbiAttributes::default(),
    };
    let mut abi = descriptor(&[Ty::I32], &[]);
    abi.result = AbiArgument {
        size: 8,
        align: 4,
        mode: AbiPassMode::Pair(scalar(0), scalar(4)),
        bindings: vec![
            AbiBinding {
                place: AbiBindingPlace::Result(0),
                source_offset: 0,
                source_bytes: 4,
                carrier_offset: 0,
                carrier_bytes: 4,
            },
            AbiBinding {
                place: AbiBindingPlace::Result(1),
                source_offset: 4,
                source_bytes: 4,
                carrier_offset: 0,
                carrier_bytes: 4,
            },
        ],
    };
    module.func_types[1].abi = Some(abi);
    module
}

#[test]
fn actual_multiple_lowered_call_results_bind_every_carrier_and_retire_partial_prefix() {
    let module = pair_results();
    let (outcome, _) = matching(&module, vec![int(Ty::I32, 7)], InterpretOptions::default());
    assert_eq!(outcome.returns, vec![int(Ty::I32, 15)]);
    let mut missing = module.clone();
    missing.functions[0].blocks[0].body[0].results.pop();
    assert_eq!(
        Interpreter::with_module(&missing)
            .execute_func(f(), [int(Ty::I32, 7)])
            .unwrap_err()
            .code,
        InterpretErrorCode::MalformedInstruction
    );
    let report = run(&missing, vec![int(Ty::I32, 7)], &mut Observer::default());
    assert!(
        matches!(report.exit(),ObservedExit::ExecutedError {site,error} if site.function==f() && site.instruction_index==0 && error.code==InterpretErrorCode::MalformedInstruction)
    );
    struct Stop {
        returned: bool,
        inserts: usize,
        stopped: bool,
        cleanup: usize,
    }
    impl ExecutionObserver for Stop {
        type Refusal = &'static str;
        fn admit(&mut self, event: ExecutionProgress) -> Result<(), Self::Refusal> {
            if event.phase == ExecutionPhase::Instruction
                && matches!(event.site,ExecutionSite::Instruction(site) if site.function==FuncId::new(1) && site.instruction_index==2)
            {
                self.returned = true;
            }
            if self.returned
                && event.phase == ExecutionPhase::HostAllocation
                && matches!(event.site,ExecutionSite::Instruction(site) if site.function==f() && site.instruction_index==0)
            {
                self.inserts += 1;
                if self.inserts == 2 {
                    self.stopped = true;
                }
            }
            if self.stopped && event.phase == ExecutionPhase::ScratchRetirement {
                self.cleanup += event.work;
            }
            if self.stopped {
                Err("second actual call result insertion stopped")
            } else {
                Ok(())
            }
        }
    }
    let mut observer = Stop {
        returned: false,
        inserts: 0,
        stopped: false,
        cleanup: 0,
    };
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    let report = Interpreter::with_module(&module).execute_func_observed(
        f(),
        vec![int(Ty::I32, 7)],
        &mut session,
    );
    assert!(matches!(report.exit(), ObservedExit::AdmissionRefused));
    assert_eq!(
        session.first_refusal().unwrap().cause,
        "second actual call result insertion stopped"
    );
    assert_eq!(observer.inserts, 2);
    assert!(observer.cleanup != 0);
}

#[test]
fn actual_direct_function_id_fallback_is_paid_and_unsupported_edges_execute_no_callee() {
    let mut module = program();
    add(
        &mut module,
        0,
        vec![Ty::I32],
        vec![Ty::I32],
        vec![call(9, vec![v(0)], 1), returned(1)],
        true,
    );
    add(
        &mut module,
        9,
        vec![Ty::I32],
        vec![Ty::I32],
        vec![number(1, 1), add_values(0, 1, 2), returned(2)],
        true,
    );
    let (outcome, observer) = matching(&module, vec![int(Ty::I32, 7)], InterpretOptions::default());
    assert_eq!(outcome.returns, vec![int(Ty::I32, 8)]);
    assert!(observer.events.iter().filter(|event|event.phase==ExecutionPhase::ModuleLookup && matches!(event.site,ExecutionSite::Instruction(site) if site.function==f() && site.instruction_index==0)).count()>=3);
    let mut unsupported = module.clone();
    unsupported.functions[0].blocks[0].body[0].inst = Inst::CallCannotUnwind {
        callee: FuncId::new(9),
        args: vec![v(0)],
    };
    assert_eq!(
        Interpreter::with_module(&unsupported)
            .execute_func(f(), [int(Ty::I32, 7)])
            .unwrap_err()
            .code,
        InterpretErrorCode::UnsupportedInstruction
    );
    let mut observer = Observer::default();
    let report = run(&unsupported, vec![int(Ty::I32, 7)], &mut observer);
    assert!(
        matches!(report.exit(),ObservedExit::UnsupportedObservation {site:ExecutionSite::Instruction(site),..} if site.function==f() && site.instruction_index==0)
    );
    assert!(!observer.events.iter().any(|event|event.phase==ExecutionPhase::Instruction && matches!(event.site,ExecutionSite::Instruction(site) if site.function==FuncId::new(9))));
}

#[test]
fn direct_frame_admission_refusal_precedes_ssa_move_and_any_callee_instruction() {
    let module = nested(true);
    matching(
        &module,
        vec![int(Ty::I32, 511)],
        InterpretOptions::default(),
    );
    struct Stop {
        stopped: bool,
        callee_steps: usize,
        cleanup: usize,
    }
    impl ExecutionObserver for Stop {
        type Refusal = &'static str;
        fn admit(&mut self, event: ExecutionProgress) -> Result<(), Self::Refusal> {
            if event.phase == ExecutionPhase::BlockParameters
                && event.copy_bytes != 0
                && matches!(event.site,ExecutionSite::Instruction(site) if site.function==f() && site.instruction_index==1)
            {
                self.stopped = true;
            }
            if event.phase == ExecutionPhase::Instruction
                && matches!(event.site,ExecutionSite::Instruction(site) if site.function!=f())
            {
                self.callee_steps += 1;
            }
            if self.stopped && event.phase == ExecutionPhase::ScratchRetirement {
                self.cleanup += event.work;
            }
            if self.stopped {
                Err("original call frame admission stopped")
            } else {
                Ok(())
            }
        }
    }
    let mut observer = Stop {
        stopped: false,
        callee_steps: 0,
        cleanup: 0,
    };
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    let report = Interpreter::with_module(&module).execute_func_observed(
        f(),
        vec![int(Ty::I32, 511)],
        &mut session,
    );
    assert!(matches!(report.exit(), ObservedExit::AdmissionRefused));
    assert_eq!(report.steps(), 2);
    let cause = session.first_refusal().unwrap();
    assert_eq!(cause.cause, "original call frame admission stopped");
    assert_eq!(cause.progress.phase, ExecutionPhase::BlockParameters);
    assert_eq!(observer.callee_steps, 0);
    assert!(observer.cleanup != 0);
}

#[test]
fn actual_iterative_call_chain_and_cyclic_fuel_cutoff_use_no_new_session() {
    let mut chain = program();
    for id in 0..16 {
        add(
            &mut chain,
            id,
            vec![Ty::I32],
            vec![Ty::I32],
            vec![call(id + 1, vec![v(0)], 1), returned(1)],
            true,
        );
    }
    add(
        &mut chain,
        16,
        vec![Ty::I32],
        vec![Ty::I32],
        vec![returned(0)],
        true,
    );
    eprintln!("deep-call control: starting ordinary and observed 17-function chain");
    let (outcome, _) = matching(&chain, vec![int(Ty::I32, 7)], InterpretOptions::default());
    eprintln!("deep-call control: 17-function comparison completed");
    assert_eq!(outcome.steps, 33);
    assert_eq!(outcome.returns, vec![int(Ty::I32, 7)]);
    let mut cycle = program();
    add(
        &mut cycle,
        0,
        vec![Ty::I32],
        vec![Ty::I32],
        vec![call(0, vec![v(0)], 1), returned(1)],
        true,
    );
    let options = InterpretOptions {
        fuel: 32,
        max_call_depth: 256,
        ..InterpretOptions::default()
    };
    eprintln!("deep-call control: starting ordinary 32-fuel cycle");
    assert_eq!(
        Interpreter::with_module(&cycle)
            .with_options(options)
            .execute_func(f(), [int(Ty::I32, 7)])
            .unwrap_err()
            .code,
        InterpretErrorCode::OutOfFuel
    );
    eprintln!("deep-call control: ordinary cycle completed; starting observed cycle");
    let mut observer = Observer::default();
    let mut session = ObservedSession::new(options, &mut observer);
    let report = Interpreter::with_module(&cycle)
        .with_options(options)
        .execute_func_observed(f(), vec![int(Ty::I32, 7)], &mut session);
    assert!(
        matches!(report.exit(),ObservedExit::InterpreterLimit {error,..} if error.code==InterpretErrorCode::OutOfFuel)
    );
    assert_eq!(report.steps(), 32);
    assert_eq!(session.remaining_fuel(), 0);
    assert!(session.first_refusal().is_none());
}

mod temporary_retirement;

mod owned_clone_front;

mod indirect;

mod byval;
