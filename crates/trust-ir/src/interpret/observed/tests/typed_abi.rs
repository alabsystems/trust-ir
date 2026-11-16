// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Real observed entry/result transport controls. Fixtures are ABI DATA only,
//! not source-generated descriptors, host models, target truth or proof.
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
fn descriptor(arguments: Vec<AbiArgument>, result: AbiArgument) -> SignatureAbi {
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
            name: "observed-abi-model-test".into(),
            revision: "not-a-compiler-capture".into(),
        },
        convention: "C".into(),
        lowered_convention: crate::CallingConv::C,
        source_abi: "C".into(),
        can_unwind: false,
        variadic: false,
        fixed_count: arguments.len() as u32,
        arguments,
        result,
    }
}
fn direct(
    place: AbiBindingPlace,
    source: u64,
    carrier: u64,
    bits: u16,
    extension: AbiExtension,
) -> AbiArgument {
    AbiArgument {
        size: source,
        align: 1,
        mode: AbiPassMode::Direct(AbiScalar {
            register: AbiRegister {
                class: AbiRegisterClass::Integer,
                bytes: carrier,
            },
            source_offset: 0,
            source_bytes: source,
            value_bits: bits,
            attributes: AbiAttributes {
                extension,
                ..Default::default()
            },
        }),
        bindings: vec![AbiBinding {
            place,
            source_offset: 0,
            source_bytes: source,
            carrier_offset: 0,
            carrier_bytes: carrier,
        }],
    }
}
fn fixture(ty: Ty, bytes: u64, bits: u16) -> Module {
    let mut module = module(
        vec![ty.clone()],
        vec![ty],
        vec![void(Inst::Return { values: vec![v(0)] })],
    );
    module.target_info = Some(crate::TargetInfo {
        triple: "aarch64-apple-darwin".into(),
        pointer_size: 8,
        endianness: crate::Endianness::Little,
        abi: Some("darwinpcs".into()),
        struct_passing: crate::StructPassingPolicy::NativeC,
    });
    module.func_types[0].abi = Some(descriptor(
        vec![direct(
            AbiBindingPlace::Parameter(0),
            bytes,
            bytes,
            bits,
            AbiExtension::None,
        )],
        direct(
            AbiBindingPlace::Result(0),
            bytes,
            bytes,
            bits,
            AbiExtension::None,
        ),
    ));
    module
}
fn matching_outcome(module: &Module, arguments: Vec<InterpretValue>) -> Observer {
    let expected = Interpreter::with_module(module)
        .execute_func(f(), arguments.clone())
        .expect("real ordinary typed execution must succeed first");
    let mut observer = Observer::default();
    let report = run(module, arguments, &mut observer);
    match report.exit() {
        ObservedExit::Returned(actual) => assert_eq!(actual, &expected),
        other => panic!("real observed typed entry/result must succeed: {other:?}"),
    }
    observer
}

fn matching(module: &Module, arguments: Vec<InterpretValue>) -> Observer {
    let observer = matching_outcome(module, arguments);
    assert!(
        observer
            .events
            .iter()
            .any(|event| event.phase == ExecutionPhase::SparseRun)
    );
    assert!(observer.events.iter().any(|event| event.copy_bytes != 0));
    assert!(
        observer
            .events
            .iter()
            .any(|event| event.phase == ExecutionPhase::ScratchRetirement && event.work != 0)
    );
    observer
}
pub(super) fn matching_entry_positive() {
    let module = fixture(Ty::U8, 1, 8);
    matching(&module, vec![int(Ty::U8, 7)]);
}

#[test]
fn observed_typed_all_integer_widths_and_bool_match_actual_ordinary_execution() {
    for (ty, bytes, signed) in [
        (Ty::I8, 1, true),
        (Ty::I16, 2, true),
        (Ty::I32, 4, true),
        (Ty::I64, 8, true),
        (Ty::I128, 16, true),
        (Ty::U8, 1, false),
        (Ty::U16, 2, false),
        (Ty::U32, 4, false),
        (Ty::U64, 8, false),
        (Ty::U128, 16, false),
    ] {
        let raw = if bytes == 16 {
            (1u128 << 127) | 127
        } else {
            127
        };
        let value = InterpretValue {
            ty: ty.clone(),
            kind: InterpretValueKind::Int(
                InterpretInt::from_raw((bytes * 8) as u32, signed, raw).unwrap(),
            ),
        };
        matching(&fixture(ty, bytes, (bytes * 8) as u16), vec![value]);
    }
    for value in [false, true] {
        matching(&fixture(Ty::Bool, 1, 1), vec![InterpretValue::bool(value)]);
    }
}

#[test]
fn observed_defined_float_char_unit_and_null_pointer_boundaries_match_ordinary() {
    for (ty, bytes, bits, kind) in [
        (Ty::F16, 2, 16, InterpretValueKind::FloatBits(0x3c00)),
        (Ty::F32, 4, 32, InterpretValueKind::FloatBits(0x3f800000)),
        (
            Ty::F64,
            8,
            64,
            InterpretValueKind::FloatBits(0x3ff0000000000000),
        ),
        (Ty::Ptr, 8, 64, InterpretValueKind::NullPtr),
    ] {
        let value = InterpretValue {
            ty: ty.clone(),
            kind,
        };
        matching(&fixture(ty, bytes, bits), vec![value]);
    }
    let module = fixture(Ty::Char, 4, 32);
    let character = |raw| InterpretValue {
        ty: Ty::Char,
        kind: InterpretValueKind::Int(InterpretInt::from_raw(32, false, raw).unwrap()),
    };
    matching(&module, vec![character(0x10ffff)]);
    let invalid = character(0xd800);
    assert_eq!(
        Interpreter::with_module(&module)
            .execute_func(f(), [invalid.clone()])
            .unwrap_err()
            .code,
        InterpretErrorCode::UndefinedBehavior
    );
    let report = run(&module, vec![invalid], &mut Observer::default());
    assert!(
        matches!(report.exit(),ObservedExit::EntryRejected(error) if error.code==InterpretErrorCode::UndefinedBehavior)
    );
}

#[test]
fn observed_recorded_sign_zero_extension_and_padding_are_real_transport() {
    for (extension, expected) in [(AbiExtension::Sign, -1), (AbiExtension::Zero, 255)] {
        let mut module = fixture(Ty::I32, 4, 32);
        module.func_types[0].abi.as_mut().unwrap().arguments[0] =
            direct(AbiBindingPlace::Parameter(0), 1, 4, 8, extension);
        matching(&module, vec![int(Ty::I32, 511)]);
        let mut observer = Observer::default();
        let report = run(&module, vec![int(Ty::I32, 511)], &mut observer);
        assert!(
            matches!(report.exit(),ObservedExit::Returned(outcome) if outcome.returns==vec![int(Ty::I32,expected)])
        );
    }
    let mut module = fixture(Ty::I32, 4, 32);
    let abi = module.func_types[0].abi.as_mut().unwrap();
    abi.arguments[0] = direct(AbiBindingPlace::Parameter(0), 1, 4, 8, AbiExtension::None);
    abi.result = direct(AbiBindingPlace::Result(0), 1, 1, 8, AbiExtension::None);
    module.func_types[0].returns = vec![Ty::I8];
    module.functions[0].blocks[0].body = vec![
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
        void(Inst::Return { values: vec![v(2)] }),
    ];
    matching(&module, vec![int(Ty::I32, 7)]);
    let mut changed = module.clone();
    changed.func_types[0].returns = vec![Ty::I32];
    changed.func_types[0].abi.as_mut().unwrap().result =
        direct(AbiBindingPlace::Result(0), 4, 4, 32, AbiExtension::None);
    changed.functions[0].blocks[0].body[2] = node(
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
    assert!(
        matches!(report.exit(),ObservedExit::ExecutedError {error,..} if error.code==InterpretErrorCode::UndefinedBehavior)
    );
}

#[test]
fn observed_pair_cast_and_ignore_match_actual_source_carriers() {
    let ty = Ty::Array(TyId::new(0), 2);
    let value = InterpretValue {
        ty: ty.clone(),
        kind: InterpretValueKind::Array(ArrayValue::from_vec(vec![
            int(Ty::U8, 5),
            int(Ty::U8, 17),
        ])),
    };
    let mut module = fixture(ty, 2, 16);
    let scalar = |offset| AbiScalar {
        register: AbiRegister {
            class: AbiRegisterClass::Integer,
            bytes: 1,
        },
        source_offset: offset,
        source_bytes: 1,
        value_bits: 8,
        attributes: AbiAttributes::default(),
    };
    let abi = module.func_types[0].abi.as_mut().unwrap();
    abi.arguments[0].mode = AbiPassMode::Pair(scalar(0), scalar(1));
    abi.result.mode = AbiPassMode::Pair(scalar(0), scalar(1));
    matching(&module, vec![value.clone()]);
    let cast = AbiPassMode::Cast {
        pad_i32: true,
        prefix: vec![AbiRegister {
            class: AbiRegisterClass::Integer,
            bytes: 1,
        }],
        rest_offset: Some(1),
        rest: AbiUniform {
            unit: AbiRegister {
                class: AbiRegisterClass::Integer,
                bytes: 2,
            },
            total: 1,
            consecutive: false,
        },
        attributes: AbiAttributes::default(),
    };
    module.func_types[0].abi.as_mut().unwrap().arguments[0].mode = cast.clone();
    module.func_types[0].abi.as_mut().unwrap().result.mode = cast;
    matching(&module, vec![value]);
    let mut empty = fixture(Ty::Unit, 0, 1);
    empty.func_types[0].abi = Some(descriptor(vec![ignored()], ignored()));
    let omitted_unit = empty.clone();

    // Ignored source arguments/results contribute no lowered IR carrier.
    empty.func_types[0].params.clear();
    empty.func_types[0].returns.clear();
    empty.functions[0].blocks[0].params.clear();
    empty.functions[0].blocks[0].body = vec![void(Inst::Return { values: vec![] })];
    matching_outcome(&empty, vec![]);

    // Unit remains a real legacy carrier; Ignore cannot erase it in a typed
    // signature. Retain that original malformed input as a pre-entry refusal.
    let unit = InterpretValue {
        ty: Ty::Unit,
        kind: InterpretValueKind::Unit,
    };
    let mut legacy_unit = omitted_unit.clone();
    legacy_unit.func_types[0].abi = None;
    matching_outcome(&legacy_unit, vec![unit.clone()]);
    let error = Interpreter::with_module(&omitted_unit)
        .execute_func(f(), [unit.clone()])
        .unwrap_err();
    assert_eq!(error.code, InterpretErrorCode::SignatureMismatch);
    assert!(
        error
            .message
            .contains("omits a lowered parameter or result")
    );
    let report = run(&omitted_unit, vec![unit], &mut Observer::default());
    assert!(matches!(report.exit(), ObservedExit::EntryRejected(error)
        if error.code == InterpretErrorCode::SignatureMismatch));
    assert_eq!(report.steps(), 0);
    assert_eq!(report.host_calls(), 0);
}

#[test]
fn observed_cast_padding_stays_unowned_and_noundef_checks_actual_live_image() {
    let mut module = fixture(Ty::I32, 4, 32);
    let mut argument = direct(AbiBindingPlace::Parameter(0), 3, 4, 24, AbiExtension::None);
    argument.mode = AbiPassMode::Cast {
        pad_i32: true,
        prefix: vec![],
        rest_offset: Some(0),
        rest: AbiUniform {
            unit: AbiRegister {
                class: AbiRegisterClass::Integer,
                bytes: 4,
            },
            total: 3,
            consecutive: false,
        },
        attributes: AbiAttributes::default(),
    };
    let abi = module.func_types[0].abi.as_mut().unwrap();
    abi.arguments[0] = argument;
    abi.result = direct(AbiBindingPlace::Result(0), 1, 1, 8, AbiExtension::None);
    module.func_types[0].returns = vec![Ty::I8];
    module.functions[0].blocks[0].body = vec![
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
        void(Inst::Return { values: vec![v(2)] }),
    ];
    matching(&module, vec![int(Ty::I32, 0x110005)]);
    // These are LOWERED physical carrier bytes, not a fabricated Rust source
    // value. NoUndef absent permits transport-only poison; the body observes
    // only byte0. The high physical register byte remains poison independently.
    let partial = InterpretValue {
        ty: Ty::I32,
        kind: InterpretValueKind::PartialBytes(vec![Some(5), None, Some(17), Some(0)]),
    };
    matching(&module, vec![partial.clone()]);
    if let AbiPassMode::Cast { attributes, .. } =
        &mut module.func_types[0].abi.as_mut().unwrap().arguments[0].mode
    {
        attributes.no_undef = true;
    }
    assert_eq!(
        Interpreter::with_module(&module)
            .execute_func(f(), [partial.clone()])
            .unwrap_err()
            .code,
        InterpretErrorCode::UndefinedBehavior
    );
    let report = run(&module, vec![partial], &mut Observer::default());
    assert!(
        matches!(report.exit(),ObservedExit::EntryRejected(error) if error.code==InterpretErrorCode::UndefinedBehavior)
    );
}

#[test]
fn malformed_unused_target_and_subbyte_records_never_reach_body_effects() {
    let module = fixture(Ty::U8, 1, 8);
    matching(&module, vec![int(Ty::U8, 7)]);
    for change in 0..5 {
        let mut changed = module.clone();
        let mut unused = changed.func_types[0].clone();
        match change {
            0 => unused.abi.as_mut().unwrap().target.triple = "x86_64-unknown-linux-gnu".into(),
            1 => unused.abi.as_mut().unwrap().arguments[0].bindings[0].carrier_offset = 1,
            2 => {
                if let AbiPassMode::Direct(scalar) =
                    &mut unused.abi.as_mut().unwrap().arguments[0].mode
                {
                    scalar.value_bits = 1;
                }
            }
            3 => {
                if let AbiPassMode::Direct(scalar) =
                    &mut unused.abi.as_mut().unwrap().arguments[0].mode
                {
                    scalar.attributes.capture = AbiCapture::None;
                }
            }
            4 => {
                if let AbiPassMode::Direct(scalar) =
                    &mut unused.abi.as_mut().unwrap().arguments[0].mode
                {
                    scalar.attributes.no_alias = true;
                }
            }
            _ => unreachable!(),
        }
        changed.func_types.push(unused);
        let ordinary = Interpreter::with_module(&changed)
            .execute_func(f(), [int(Ty::U8, 7)])
            .unwrap_err();
        let report = run(&changed, vec![int(Ty::U8, 7)], &mut Observer::default());
        if change < 2 {
            assert_eq!(ordinary.code, InterpretErrorCode::SignatureMismatch);
            assert!(
                matches!(report.exit(),ObservedExit::EntryRejected(error) if error.code==InterpretErrorCode::SignatureMismatch)
            );
        } else {
            assert_eq!(ordinary.code, InterpretErrorCode::UnsupportedCall);
            assert!(matches!(
                report.exit(),
                ObservedExit::UnsupportedObservation { .. }
            ));
        }
        assert_eq!(report.steps(), 0);
    }
}

#[test]
fn actual_transport_cancellation_retains_first_cause_and_retires_without_publication() {
    let module = fixture(Ty::I32, 4, 32);
    matching(&module, vec![int(Ty::I32, 11)]);
    struct Cancel {
        entries: usize,
        sparse: usize,
        armed: bool,
        stopped: bool,
        cleanup: usize,
    }
    impl ExecutionObserver for Cancel {
        type Refusal = &'static str;
        fn admit(&mut self, event: ExecutionProgress) -> Result<(), Self::Refusal> {
            if event.phase == ExecutionPhase::EntryArguments {
                self.entries += 1;
                if self.entries == 2 {
                    self.armed = true;
                }
            }
            if self.armed && event.phase == ExecutionPhase::SparseRun {
                self.sparse += 1;
                if self.sparse == 4 {
                    self.stopped = true;
                }
            }
            if self.stopped && event.phase == ExecutionPhase::ScratchRetirement {
                self.cleanup += event.work;
            }
            if self.stopped {
                Err("same original cancellation")
            } else {
                Ok(())
            }
        }
    }
    let mut observer = Cancel {
        entries: 0,
        sparse: 0,
        armed: false,
        stopped: false,
        cleanup: 0,
    };
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    let report = Interpreter::with_module(&module).execute_func_observed(
        f(),
        vec![int(Ty::I32, 11)],
        &mut session,
    );
    assert!(matches!(report.exit(), ObservedExit::AdmissionRefused));
    assert_eq!(report.steps(), 0);
    let first = session.first_refusal().unwrap();
    assert_eq!(first.cause, "same original cancellation");
    assert_eq!(first.progress.phase, ExecutionPhase::SparseRun);
    let second = Interpreter::with_module(&module).execute_func_observed(
        f(),
        vec![int(Ty::I32, 11)],
        &mut session,
    );
    assert!(matches!(second.exit(), ObservedExit::AdmissionRefused));
    assert_eq!(second.steps(), 0);
    assert_eq!(
        session.first_refusal().unwrap().cause,
        "same original cancellation"
    );
    assert!(observer.armed && observer.stopped);
    assert!(observer.cleanup != 0);
}

#[test]
fn whole_module_storage_and_unused_legacy_facts_are_checked_before_typed_effects() {
    let module = fixture(Ty::U8, 1, 8);
    matching(&module, vec![int(Ty::U8, 7)]);
    for change in 0..3 {
        let mut changed = module.clone();
        match change {
            0 => changed
                .types
                .push(Ty::Storage(crate::StorageLayout::new(1, 3))),
            1 => {
                let mut unused = changed.functions[0].clone();
                unused.id = FuncId::new(1);
                unused.blocks[0].params[0].1 = Ty::Storage(crate::StorageLayout::new(8, 8));
                changed.functions.push(unused);
            }
            2 => {
                let mut unused = changed.functions[0].clone();
                unused.id = FuncId::new(1);
                unused.calling_conv = crate::CallingConv::CUnwind;
                changed.functions.push(unused);
            }
            _ => unreachable!(),
        }
        let ordinary = Interpreter::with_module(&changed)
            .execute_func(f(), [int(Ty::U8, 7)])
            .unwrap_err();
        let report = run(&changed, vec![int(Ty::U8, 7)], &mut Observer::default());
        if change < 2 {
            assert_eq!(ordinary.code, InterpretErrorCode::TypeError);
            assert!(matches!(
                report.exit(),
                ObservedExit::UnsupportedObservation { .. }
            ));
        } else {
            assert_eq!(ordinary.code, InterpretErrorCode::SignatureMismatch);
            assert!(
                matches!(report.exit(),ObservedExit::EntryRejected(error) if error.code==InterpretErrorCode::SignatureMismatch)
            );
        }
        assert_eq!(report.steps(), 0);
    }
}

#[test]
fn actual_transport_work_and_copy_quotas_stop_before_unadmitted_preparation() {
    let module = fixture(Ty::I32, 4, 32);
    matching(&module, vec![int(Ty::I32, 11)]);
    struct Quota {
        entries: usize,
        armed: bool,
        work: usize,
        copy: usize,
        copy_limit: bool,
        stopped: bool,
        cleanup: usize,
    }
    impl ExecutionObserver for Quota {
        type Refusal = &'static str;
        fn admit(&mut self, event: ExecutionProgress) -> Result<(), Self::Refusal> {
            if event.phase == ExecutionPhase::EntryArguments {
                self.entries += 1;
                if self.entries == 2 {
                    self.armed = true;
                }
            }
            if self.armed && !self.stopped {
                if self.copy_limit {
                    if event.copy_bytes > self.copy {
                        self.stopped = true;
                    } else {
                        self.copy -= event.copy_bytes;
                    }
                } else if event.work > self.work {
                    self.stopped = true;
                } else {
                    self.work -= event.work;
                }
            }
            if self.stopped && event.phase == ExecutionPhase::ScratchRetirement {
                self.cleanup += event.work;
            }
            if self.stopped {
                Err(if self.copy_limit {
                    "original copy quota"
                } else {
                    "original work quota"
                })
            } else {
                Ok(())
            }
        }
    }
    for copy_limit in [false, true] {
        let mut observer = Quota {
            entries: 0,
            armed: false,
            work: 10,
            copy: 32,
            copy_limit,
            stopped: false,
            cleanup: 0,
        };
        let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
        let report = Interpreter::with_module(&module).execute_func_observed(
            f(),
            vec![int(Ty::I32, 11)],
            &mut session,
        );
        assert!(matches!(report.exit(), ObservedExit::AdmissionRefused));
        assert_eq!(report.steps(), 0);
        assert_eq!(
            session.first_refusal().unwrap().cause,
            if copy_limit {
                "original copy quota"
            } else {
                "original work quota"
            }
        );
        assert!(observer.armed && observer.stopped);
        assert!(observer.cleanup != 0);
    }
}

#[test]
fn owned_boundary_image_retirement_reports_actual_work_after_original_cancellation() {
    struct Cleanup {
        cancel: bool,
        work: usize,
    }
    impl ExecutionObserver for Cleanup {
        type Refusal = &'static str;
        fn admit(&mut self, event: ExecutionProgress) -> Result<(), Self::Refusal> {
            if event.phase == ExecutionPhase::ScratchRetirement {
                self.work += event.work;
            }
            if self.cancel {
                Err("original cleanup cancellation")
            } else {
                Ok(())
            }
        }
    }
    let site = ExecutionSite::Entry(f());
    // Complete actual owned-image cleanup succeeds first; the canceled case
    // must drain the same real retained records under the SAME first owner.
    for cancel in [false, true] {
        let image = Image::literal((0..64).map(|value| Some(value as u8)).collect());
        let mut observer = Cleanup { cancel, work: 0 };
        let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
        if cancel {
            assert!(
                session
                    .admit(ExecutionProgress {
                        phase: ExecutionPhase::AbiScan,
                        site,
                        work: 1,
                        copy_bytes: 0
                    })
                    .is_err()
            );
        }
        image.retire_observed(&mut session.structural_owned(site));
        if cancel {
            assert_eq!(
                session.first_refusal().unwrap().cause,
                "original cleanup cancellation"
            );
        } else {
            assert!(session.first_refusal().is_none());
        }
        assert!(
            observer.work >= 64,
            "owned literal bytes were retired without their work observation"
        );
    }
}
