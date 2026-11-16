// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Actual public ordinary/observed byval comparisons. These explicit ABI
//! records are model DATA, not compiler captures or native ABI proofs.
use super::*;
use core::mem::size_of;

fn copied(module: &mut Module, function: usize, argument: usize, size: u64, align: u64) {
    module.func_types[function].abi.as_mut().unwrap().arguments[argument] = AbiArgument {
        size,
        align,
        mode: AbiPassMode::Indirect {
            attributes: AbiAttributes::default(),
            metadata_attributes: None,
            on_stack: false,
            caller_copy: true,
        },
        bindings: vec![AbiBinding {
            place: AbiBindingPlace::Parameter(argument as u32),
            source_offset: 0,
            source_bytes: size,
            carrier_offset: 0,
            carrier_bytes: 8,
        }],
    };
}
fn alloca(ty: Ty, align: u64, result: u32) -> InstrNode {
    node(
        Inst::Alloca {
            ty,
            count: None,
            align: Some(align),
        },
        result,
    )
}
fn store(ty: Ty, ptr: u32, value: u32, align: u64) -> InstrNode {
    void(Inst::Store {
        ty,
        ptr: v(ptr),
        value: v(value),
        volatile: false,
        align: Some(align),
    })
}
fn load(ty: Ty, ptr: u32, align: u64, result: u32) -> InstrNode {
    node(
        Inst::Load {
            ty,
            ptr: v(ptr),
            volatile: false,
            align: Some(align),
        },
        result,
    )
}
fn distinct(a: u32, b: u32, result: u32) -> InstrNode {
    node(
        Inst::ICmp {
            op: crate::ICmpOp::Ne,
            ty: Ty::Ptr,
            lhs: v(a),
            rhs: v(b),
        },
        result,
    )
}
fn selected(condition: u32, yes: u32, no: u32, result: u32) -> InstrNode {
    node(
        Inst::Select {
            ty: Ty::I32,
            cond: v(condition),
            then_val: v(yes),
            else_val: v(no),
        },
        result,
    )
}
fn isolation(indirect: bool) -> Module {
    let mut module = program();
    let mut body = vec![alloca(Ty::I32, 4, 0), number(7, 1), store(Ty::I32, 0, 1, 4)];
    if indirect {
        body.push(node(
            Inst::Const {
                ty: Ty::Func(FuncTyId::new(1)),
                value: Constant::FnDef(FuncId::new(1)),
            },
            6,
        ));
        body.push(node(
            Inst::CallIndirect {
                callee: v(6),
                sig: FuncTyId::new(1),
                args: vec![v(0), v(0)],
                calling_conv: crate::CallingConv::C,
            },
            2,
        ));
    } else {
        body.push(call(1, vec![v(0), v(0)], 2));
    }
    body.extend([load(Ty::I32, 0, 4, 3), add_values(2, 3, 4), returned(4)]);
    add(&mut module, 0, vec![], vec![Ty::I32], body, false);
    add(
        &mut module,
        1,
        vec![Ty::Ptr, Ty::Ptr],
        vec![Ty::I32],
        vec![
            number(99, 2),
            store(Ty::I32, 0, 2, 4),
            load(Ty::I32, 1, 4, 3),
            distinct(0, 1, 4),
            number(600, 5),
            selected(4, 3, 5, 6),
            returned(6),
        ],
        true,
    );
    copied(&mut module, 1, 0, 4, 4);
    module
}
fn error_matches(module: &Module, code: InterpretErrorCode) -> ObservedReport {
    let error = Interpreter::with_module(module)
        .execute_func(f(), [])
        .unwrap_err();
    assert_eq!(error.code, code, "ordinary original program: {error:?}");
    let report = run(module, vec![], &mut Observer::default());
    assert!(
        matches!(report.exit(), ObservedExit::ExecutedError {error,..}
        | ObservedExit::InterpreterLimit {error,..} | ObservedExit::EntryRejected(error)
        if error.code==code),
        "actual observed negative: {:?}",
        report.exit()
    );
    report
}

#[test]
fn plain_byval_direct_and_function_pointer_calls_isolate_the_actual_caller_object() {
    for indirect in [false, true] {
        let module = isolation(indirect);
        let (outcome, observer) = matching(&module, vec![], InterpretOptions::default());
        assert_eq!(outcome.returns, vec![int(Ty::I32, 14)]);
        assert!(
            observer
                .events
                .iter()
                .any(|e| e.site == ExecutionSite::Entry(FuncId::new(1)) && e.copy_bytes != 0)
        );
        assert!(
            observer
                .events
                .iter()
                .any(|e| e.phase == ExecutionPhase::ScratchRetirement
                    && e.work > 0
                    && e.copy_bytes == size_of::<InterpretPointer>())
        );
        // The otherwise identical non-byval execution mutates the caller and
        // sees aliasing. This is an actual semantic discriminator, not a copy
        // counter standing in for isolation.
        let mut alias = module.clone();
        alias.func_types[1].abi.as_mut().unwrap().arguments[0] =
            direct(&Ty::Ptr, AbiBindingPlace::Parameter(0));
        let (wrong, _) = matching(&alias, vec![], InterpretOptions::default());
        assert_eq!(wrong.returns, vec![int(Ty::I32, 699)]);
    }
}

#[test]
fn simultaneous_and_nested_copies_of_the_same_source_have_distinct_live_identities() {
    let mut simultaneous = isolation(false);
    copied(&mut simultaneous, 1, 1, 4, 4);
    let (outcome, _) = matching(&simultaneous, vec![], InterpretOptions::default());
    assert_eq!(outcome.returns, vec![int(Ty::I32, 14)]);
    let mut nested = isolation(false);
    // The actual middle-frame copy is now itself the leaf's copied source.
    nested.functions[1].blocks[0].body = vec![
        call(2, vec![v(0), v(0)], 2),
        load(Ty::I32, 0, 4, 3),
        add_values(2, 3, 4),
        returned(4),
    ];
    let leaf = isolation(false).functions[1].blocks[0].body.clone();
    add(
        &mut nested,
        2,
        vec![Ty::Ptr, Ty::Ptr],
        vec![Ty::I32],
        leaf,
        true,
    );
    copied(&mut nested, 2, 0, 4, 4);
    let (outcome, _) = matching(&nested, vec![], InterpretOptions::default());
    assert_eq!(outcome.returns, vec![int(Ty::I32, 21)]);
}

#[test]
fn actual_zero_size_identity_is_preserved_and_noncanonical_zero_byval_still_refuses() {
    let mut module = program();
    add(
        &mut module,
        0,
        vec![],
        vec![Ty::Bool],
        vec![
            alloca(Ty::Unit, 1, 0),
            alloca(Ty::Unit, 1, 1),
            call(1, vec![v(0), v(1)], 2),
            returned(2),
        ],
        false,
    );
    add(
        &mut module,
        1,
        vec![Ty::Ptr, Ty::Ptr],
        vec![Ty::Bool],
        vec![distinct(0, 1, 2), returned(2)],
        true,
    );
    let (outcome, _) = matching(&module, vec![], InterpretOptions::default());
    assert_eq!(outcome.returns, vec![InterpretValue::bool(true)]);
    // The canonical record grammar requires non-Ignore source storage. Keep
    // this exact earlier refusal instead of widening a validator for transport.
    copied(&mut module, 1, 0, 0, 1);
    copied(&mut module, 1, 1, 0, 1);
    let report = error_matches(&module, InterpretErrorCode::SignatureMismatch);
    assert!(matches!(report.exit(), ObservedExit::EntryRejected(_)));
    assert_eq!(report.steps(), 0);
}

#[test]
fn byval_returned_pointer_is_dead_before_caller_resumes_and_explicit_free_is_not_repeated() {
    let mut module = isolation(false);
    module.func_types[1].returns = vec![Ty::Ptr];
    module.func_types[1].abi.as_mut().unwrap().result =
        direct(&Ty::Ptr, AbiBindingPlace::Result(0));
    module.functions[1].blocks[0].body = vec![returned(0)];
    module.functions[0].blocks[0].body = vec![
        alloca(Ty::I32, 4, 0),
        number(7, 1),
        store(Ty::I32, 0, 1, 4),
        call(1, vec![v(0), v(0)], 2),
        load(Ty::I32, 2, 4, 3),
        returned(3),
    ];
    let mut identity = module.clone();
    identity.func_types[0].returns = vec![Ty::Bool];
    identity.functions[0].blocks[0].body[4] = distinct(2, 0, 3);
    let (outcome, _) = matching(&identity, vec![], InterpretOptions::default());
    assert_eq!(outcome.returns, vec![InterpretValue::bool(true)]);
    let report = error_matches(&module, InterpretErrorCode::UndefinedBehavior);
    assert!(
        matches!(report.exit(), ObservedExit::ExecutedError {site,..} if site.function==f() && site.instruction_index==4)
    );
    let mut freed = isolation(false);
    freed.functions[1].blocks[0].body = vec![
        void(Inst::Dealloc { ptr: v(0) }),
        number(11, 2),
        returned(2),
    ];
    let (outcome, _) = matching(&freed, vec![], InterpretOptions::default());
    assert_eq!(outcome.returns, vec![int(Ty::I32, 18)]);
}

#[test]
fn source_alignment_extent_liveness_and_all_original_operands_are_checked_before_copying() {
    let good = isolation(false);
    matching(&good, vec![], InterpretOptions::default());
    for mode in 0..4 {
        let mut bad = good.clone();
        let body = &mut bad.functions[0].blocks[0].body;
        match mode {
            0 => {
                body.insert(3, node(Inst::NullPtr, 8));
                if let Inst::Call { args, .. } = &mut body[4].inst {
                    args[0] = v(8);
                }
            }
            1 => body.insert(3, void(Inst::Dealloc { ptr: v(0) })),
            offset => {
                body.insert(
                    3,
                    node(
                        Inst::Const {
                            ty: Ty::I64,
                            value: Constant::Int(if offset == 2 { 1 } else { 4 }),
                        },
                        8,
                    ),
                );
                body.insert(
                    4,
                    node(
                        Inst::GEP {
                            pointee_ty: Ty::I8,
                            base: v(0),
                            indices: vec![v(8)],
                            inbounds: false,
                        },
                        9,
                    ),
                );
                if let Inst::Call { args, .. } = &mut body[5].inst {
                    args[0] = v(9);
                }
            }
        }
        error_matches(&bad, InterpretErrorCode::UndefinedBehavior);
    }
    let mut later_bad = good.clone();
    copied(&mut later_bad, 1, 1, 4, 4);
    later_bad.functions[0].blocks[0]
        .body
        .insert(3, node(Inst::NullPtr, 8));
    if let Inst::Call { args, .. } = &mut later_bad.functions[0].blocks[0].body[4].inst {
        args[1] = v(8);
    }
    let mut observer = Observer::default();
    let report = run(&later_bad, vec![], &mut observer);
    assert!(
        matches!(report.exit(),ObservedExit::ExecutedError {error,..} if error.code==InterpretErrorCode::UndefinedBehavior)
    );
    assert!(
        !observer
            .events
            .iter()
            .any(|e| e.site == ExecutionSite::Entry(FuncId::new(1))
                && e.phase == ExecutionPhase::EntryArguments
                && e.copy_bytes == size_of::<InterpretPointer>())
    );
}

#[test]
fn byval_preserves_partial_initializedness_instead_of_inventing_zero_padding() {
    let mut module = program();
    add(
        &mut module,
        0,
        vec![],
        vec![Ty::I32],
        vec![
            alloca(Ty::Array(TyId::new(0), 8), 4, 0),
            number(7, 1),
            store(Ty::I32, 0, 1, 4),
            call(1, vec![v(0)], 2),
            returned(2),
        ],
        false,
    );
    add(
        &mut module,
        1,
        vec![Ty::Ptr],
        vec![Ty::I32],
        vec![load(Ty::I32, 0, 4, 1), returned(1)],
        true,
    );
    copied(&mut module, 1, 0, 8, 4);
    let (outcome, _) = matching(&module, vec![], InterpretOptions::default());
    assert_eq!(outcome.returns, vec![int(Ty::I32, 7)]);
    let mut poison = module.clone();
    poison.func_types[0].returns = vec![Ty::I64];
    poison.func_types[1].returns = vec![Ty::I64];
    poison.func_types[1].abi.as_mut().unwrap().result = AbiArgument {
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
            place: AbiBindingPlace::Result(0),
            source_offset: 0,
            source_bytes: 8,
            carrier_offset: 0,
            carrier_bytes: 8,
        }],
    };
    poison.functions[1].blocks[0].body[0] = load(Ty::I64, 0, 4, 1);
    let report = error_matches(&poison, InterpretErrorCode::UndefinedBehavior);
    assert!(
        matches!(report.exit(),ObservedExit::ExecutedError {site,..} if site.function==FuncId::new(1) && site.instruction_index==1)
    );
}

#[test]
fn copies_have_owners_before_entry_bind_and_caller_result_binding_can_fail() {
    let good = isolation(false);
    matching(&good, vec![], InterpretOptions::default());
    for entry_fault in [true, false] {
        let mut bad = good.clone();
        if entry_fault {
            bad.functions[1].blocks[0].params.push((v(99), Ty::I32));
        } else {
            bad.functions[0].blocks[0].body[3].results.push(v(99));
        }
        let ordinary = Interpreter::with_module(&bad)
            .execute_func(f(), [])
            .unwrap_err();
        assert_eq!(ordinary.code, InterpretErrorCode::MalformedInstruction);
        let mut observer = Observer::default();
        let report = run(&bad, vec![], &mut observer);
        let expected = if entry_fault {
            InterpretErrorCode::SignatureMismatch
        } else {
            InterpretErrorCode::MalformedInstruction
        };
        assert!(
            matches!(report.exit(),ObservedExit::ExecutedError {error,..} if error.code==expected)
        );
        assert!(
            observer
                .events
                .iter()
                .any(|e| e.phase == ExecutionPhase::ScratchRetirement
                    && e.work > 0
                    && e.copy_bytes == size_of::<InterpretPointer>()),
            "actual copied storage must retire after bind failure"
        );
    }
    // Public entry cannot import an allocation merely by naming its ID. The
    // same source check protects root entry; no synthetic memory is installed.
    let mut observer = Observer::default();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    let input = InterpretValue {
        ty: Ty::Ptr,
        kind: InterpretValueKind::Ptr(InterpretPointer {
            allocation: 0,
            offset: 0,
        }),
    };
    let report = Interpreter::with_module(&good).execute_func_observed(
        FuncId::new(1),
        vec![input.clone(), input],
        &mut session,
    );
    assert!(
        matches!(report.exit(),ObservedExit::EntryRejected(error) if error.code==InterpretErrorCode::UndefinedBehavior)
    );
    assert_eq!(report.steps(), 0);
    assert_eq!(report.host_calls(), 0);
}

#[test]
fn unsupported_attribute_stack_borrowed_hidden_and_malformed_records_refuse_before_effects() {
    let good = isolation(false);
    matching(&good, vec![], InterpretOptions::default());
    for mutation in 0..8 {
        let mut bad = good.clone();
        let argument = &mut bad.func_types[1].abi.as_mut().unwrap().arguments[0];
        match mutation {
            0 => {
                if let AbiPassMode::Indirect { attributes, .. } = &mut argument.mode {
                    attributes.no_alias = true;
                }
            }
            1 => {
                if let AbiPassMode::Indirect { on_stack, .. } = &mut argument.mode {
                    *on_stack = true;
                }
            }
            2 => {
                if let AbiPassMode::Indirect { caller_copy, .. } = &mut argument.mode {
                    *caller_copy = false;
                }
            }
            3 => argument.bindings[0].carrier_bytes = 4,
            4 => argument.bindings[0].source_bytes = 3,
            5 => {
                if let AbiPassMode::Indirect {
                    metadata_attributes,
                    ..
                } = &mut argument.mode
                {
                    *metadata_attributes = Some(AbiAttributes::default());
                }
            }
            6 => {
                argument.bindings[0].place = AbiBindingPlace::HiddenResult(0);
            }
            7 => argument.align = 0,
            _ => unreachable!(),
        }
        let report = run(&bad, vec![], &mut Observer::default());
        assert!(
            matches!(
                report.exit(),
                ObservedExit::UnsupportedObservation {
                    site: ExecutionSite::Entry(_),
                    ..
                } | ObservedExit::EntryRejected(_)
            ),
            "mutation {mutation}: {:?}",
            report.exit()
        );
        assert_eq!(report.steps(), 0);
        assert_eq!(report.host_calls(), 0);
    }
}

fn dense() -> Module {
    let mut module = program();
    let ty = Ty::Array(TyId::new(0), 64);
    add(
        &mut module,
        0,
        vec![],
        vec![Ty::U8],
        vec![
            alloca(ty.clone(), 1, 0),
            node(
                Inst::Const {
                    ty: ty.clone(),
                    value: Constant::Array((0..64).map(Constant::Int).collect()),
                },
                1,
            ),
            store(ty, 0, 1, 1),
            call(1, vec![v(0)], 2),
            returned(2),
        ],
        false,
    );
    add(
        &mut module,
        1,
        vec![Ty::Ptr],
        vec![Ty::U8],
        vec![load(Ty::U8, 0, 1, 1), returned(1)],
        true,
    );
    copied(&mut module, 1, 0, 64, 1);
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
        if self.stopped && event.phase == ExecutionPhase::ScratchRetirement {
            self.cleanup.push(event);
        }
        if self.seen == self.at {
            self.stopped = true;
        }
        if self.stopped {
            Err("original byval copy cancelled")
        } else {
            Ok(())
        }
    }
}
#[test]
fn every_actual_entry_copy_cut_and_retirement_cut_drains_owned_work_without_publication_or_new_fuel()
 {
    let module = dense();
    let (outcome, baseline) = matching(&module, vec![], InterpretOptions::default());
    assert_eq!(outcome.returns, vec![int(Ty::U8, 0)]);
    let cuts: Vec<_> = baseline
        .events
        .iter()
        .enumerate()
        .filter(|(_, e)| {
            e.site == ExecutionSite::Entry(FuncId::new(1))
                || e.phase == ExecutionPhase::ScratchRetirement
                    && e.copy_bytes == size_of::<InterpretPointer>()
        })
        .map(|(i, e)| (i + 1, *e))
        .collect();
    assert!(!cuts.is_empty());
    for (at, expected) in cuts {
        let options = InterpretOptions::default();
        let mut observer = Cut {
            at,
            ..Cut::default()
        };
        let mut session = ObservedSession::new(options, &mut observer);
        let report =
            Interpreter::with_module(&module).execute_func_observed(f(), vec![], &mut session);
        assert!(
            matches!(report.exit(), ObservedExit::AdmissionRefused),
            "cut {at}: {:?}",
            report.exit()
        );
        assert_eq!(session.first_refusal().unwrap().progress, expected);
        assert_eq!(
            session.first_refusal().unwrap().cause,
            "original byval copy cancelled"
        );
        assert_eq!(session.remaining_fuel(), options.fuel - report.steps());
        let remaining = session.remaining_fuel();
        let again =
            Interpreter::with_module(&module).execute_func_observed(f(), vec![], &mut session);
        assert!(matches!(again.exit(), ObservedExit::AdmissionRefused));
        assert_eq!(again.steps(), 0);
        assert_eq!(session.remaining_fuel(), remaining);
        assert_eq!(session.first_refusal().unwrap().progress, expected);
        assert!(
            observer.cleanup.iter().any(|e| e.work != 0),
            "cut {at} must drain actual owned arguments/images/storage"
        );
    }
    // A real instruction-fuel failure inside the callee also retires its copy.
    let options = InterpretOptions {
        fuel: 4,
        ..InterpretOptions::default()
    };
    let ordinary = Interpreter::with_module(&module)
        .with_options(options)
        .execute_func(f(), [])
        .unwrap_err();
    assert_eq!(ordinary.code, InterpretErrorCode::OutOfFuel);
    let mut observer = Observer::default();
    let mut session = ObservedSession::new(options, &mut observer);
    let report = Interpreter::with_module(&module)
        .with_options(options)
        .execute_func_observed(f(), vec![], &mut session);
    assert!(
        matches!(report.exit(),ObservedExit::InterpreterLimit {error,..} if error.code==InterpretErrorCode::OutOfFuel)
    );
    assert_eq!(report.steps(), 4);
    assert_eq!(session.remaining_fuel(), 0);
    assert!(
        observer
            .events
            .iter()
            .any(|e| e.phase == ExecutionPhase::ScratchRetirement
                && e.copy_bytes == size_of::<InterpretPointer>()
                && e.work > 0)
    );
}
