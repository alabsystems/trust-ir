// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::signature_abi::{AbiFrontend, AbiRegisterClass, AbiTarget, AbiUniform};
use std::sync::Mutex;

fn v(index: u32) -> ValueId {
    ValueId::new(index)
}
fn f(index: u32) -> FuncId {
    FuncId::new(index)
}
fn b() -> BlockId {
    BlockId::new(0)
}
fn node(inst: Inst, result: u32) -> InstrNode {
    InstrNode::new(inst).with_result(v(result))
}
fn void(inst: Inst) -> InstrNode {
    InstrNode::new(inst)
}
fn integer(ty: Ty, n: i128) -> InterpretValue {
    InterpretValue::int(ty, n).unwrap()
}
fn ignore() -> AbiArgument {
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
            name: "typed-abi-model-test".into(),
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
fn module(signature: FuncTy, body: Vec<InstrNode>) -> Module {
    let mut module = Module::new("typed-abi-operational-model");
    module.target_info = Some(crate::TargetInfo {
        triple: "aarch64-apple-darwin".into(),
        pointer_size: 8,
        endianness: crate::Endianness::Little,
        abi: Some("darwinpcs".into()),
        struct_passing: crate::StructPassingPolicy::NativeC,
    });
    let params = signature.params.clone();
    module.func_types.push(signature);
    let mut function = Function::new(f(0), "entry", FuncTyId::new(0), b());
    let mut block = Block::new(b());
    block.params = params
        .into_iter()
        .enumerate()
        .map(|(i, ty)| (v(i as u32), ty))
        .collect();
    block.body = body;
    function.blocks.push(block);
    module.functions.push(function);
    module
}
fn identity(ty: Ty, bytes: u64, bits: u16) -> Module {
    module(
        FuncTy {
            params: vec![ty.clone()],
            returns: vec![ty],
            is_vararg: false,
            abi: Some(descriptor(
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
            )),
        },
        vec![void(Inst::Return { values: vec![v(0)] })],
    )
}

#[test]
fn actual_typed_entry_matches_legacy_for_every_integer_width_and_boolean() {
    for (signed, ty, bytes) in [
        (true, Ty::I8, 1),
        (true, Ty::I16, 2),
        (true, Ty::I32, 4),
        (true, Ty::I64, 8),
        (true, Ty::I128, 16),
        (false, Ty::U8, 1),
        (false, Ty::U16, 2),
        (false, Ty::U32, 4),
        (false, Ty::U64, 8),
        (false, Ty::U128, 16),
    ] {
        let raw = if bytes == 16 {
            (1u128 << 127) | 127
        } else {
            127
        };
        let argument = InterpretValue {
            ty: ty.clone(),
            kind: InterpretValueKind::Int(
                InterpretInt::from_raw((bytes * 8) as u32, signed, raw).unwrap(),
            ),
        };
        let typed = identity(ty, bytes, (bytes * 8) as u16);
        let actual = Interpreter::with_module(&typed)
            .execute_func(f(0), [argument.clone()])
            .unwrap();
        let mut legacy = typed.clone();
        legacy.func_types[0].abi = None;
        let expected = Interpreter::with_module(&legacy)
            .execute_func(f(0), [argument])
            .unwrap();
        assert_eq!(actual, expected);
        assert_eq!(actual.returns[0].as_int().unwrap().raw, raw);
    }
    let typed = identity(Ty::Bool, 1, 1);
    for value in [false, true] {
        assert_eq!(
            Interpreter::with_module(&typed)
                .execute_func(f(0), [InterpretValue::bool(value)])
                .unwrap()
                .returns,
            vec![InterpretValue::bool(value)]
        );
    }
}

#[test]
fn real_entry_truncates_source_bits_then_applies_recorded_sign_or_zero_extension() {
    for (extension, expected) in [(AbiExtension::Sign, -1), (AbiExtension::Zero, 255)] {
        let mut typed = identity(Ty::I32, 4, 32);
        typed.func_types[0].abi.as_mut().unwrap().arguments[0] =
            direct(AbiBindingPlace::Parameter(0), 1, 4, 8, extension);
        let outcome = Interpreter::with_module(&typed)
            .execute_func(f(0), [integer(Ty::I32, 511)])
            .unwrap();
        assert_eq!(outcome.returns, vec![integer(Ty::I32, expected)]);
    }
}

#[test]
fn padding_is_poison_transport_and_is_never_synthesized_as_initialized_zero() {
    let mut typed = identity(Ty::I32, 4, 32);
    let abi = typed.func_types[0].abi.as_mut().unwrap();
    abi.arguments[0] = direct(AbiBindingPlace::Parameter(0), 1, 4, 8, AbiExtension::None);
    abi.result = direct(AbiBindingPlace::Result(0), 1, 1, 8, AbiExtension::None);
    typed.func_types[0].returns = vec![Ty::I8];
    typed.functions[0].blocks[0].body = vec![
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
    let outcome = Interpreter::with_module(&typed)
        .execute_func(f(0), [integer(Ty::I32, 7)])
        .unwrap();
    assert_eq!(outcome.returns, vec![integer(Ty::I8, 7)]);
    let mut inspect_padding = typed.clone();
    inspect_padding.func_types[0].returns = vec![Ty::I32];
    inspect_padding.func_types[0].abi.as_mut().unwrap().result =
        direct(AbiBindingPlace::Result(0), 4, 4, 32, AbiExtension::None);
    inspect_padding.functions[0].blocks[0].body[2] = node(
        Inst::Load {
            ty: Ty::I32,
            ptr: v(1),
            volatile: false,
            align: Some(4),
        },
        2,
    );
    assert_eq!(
        Interpreter::with_module(&inspect_padding)
            .execute_func(f(0), [integer(Ty::I32, 7)])
            .unwrap_err()
            .code,
        InterpretErrorCode::UndefinedBehavior
    );
    let partial = InterpretValue {
        ty: Ty::I32,
        kind: InterpretValueKind::PartialBytes(vec![None, Some(0), Some(0), Some(0)]),
    };
    assert_eq!(
        Interpreter::with_module(&typed)
            .execute_func(f(0), [partial])
            .unwrap_err()
            .code,
        InterpretErrorCode::UndefinedBehavior
    );
}

#[test]
fn pair_transport_reconstructs_one_real_aggregate_carrier() {
    let mut pair = direct(AbiBindingPlace::Parameter(0), 2, 2, 16, AbiExtension::None);
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
    pair.mode = AbiPassMode::Pair(scalar(0), scalar(1));
    let mut result = pair.clone();
    result.bindings[0].place = AbiBindingPlace::Result(0);
    let ty = Ty::Tuple(vec![Ty::U8, Ty::U8]);
    let typed = module(
        FuncTy {
            params: vec![ty.clone()],
            returns: vec![ty.clone()],
            is_vararg: false,
            abi: Some(descriptor(vec![pair], result)),
        },
        vec![void(Inst::Return { values: vec![v(0)] })],
    );
    let argument = InterpretValue {
        ty,
        kind: InterpretValueKind::Aggregate(vec![integer(Ty::U8, 5), integer(Ty::U8, 17)]),
    };
    assert_eq!(
        Interpreter::with_module(&typed)
            .execute_func(f(0), [argument.clone()])
            .unwrap()
            .returns,
        vec![argument]
    );
    // Scalar-only validation cannot see this second live aggregate field.
    // The actual module layout census must reject its omission before entry.
    let mut omitted = typed.clone();
    omitted.func_types[0].abi.as_mut().unwrap().arguments[0] =
        direct(AbiBindingPlace::Parameter(0), 1, 1, 8, AbiExtension::None);
    let argument = InterpretValue {
        ty: Ty::Tuple(vec![Ty::U8, Ty::U8]),
        kind: InterpretValueKind::Aggregate(vec![integer(Ty::U8, 5), integer(Ty::U8, 17)]),
    };
    assert_eq!(
        Interpreter::with_module(&omitted)
            .execute_func(f(0), [argument])
            .unwrap_err()
            .code,
        InterpretErrorCode::SignatureMismatch
    );
}

#[test]
fn cast_prefix_rest_and_alignment_register_preserve_uninitialized_padding() {
    let mut source = ByteStore::new(4, None);
    source.write(0, &Image::init_bytes(&[1, 2, 3]));
    let argument = AbiArgument {
        size: 4,
        align: 1,
        mode: AbiPassMode::Cast {
            pad_i32: true,
            prefix: vec![AbiRegister {
                class: AbiRegisterClass::Integer,
                bytes: 1,
            }],
            rest_offset: Some(1),
            rest: AbiUniform {
                unit: AbiRegister {
                    class: AbiRegisterClass::Integer,
                    bytes: 4,
                },
                total: 2,
                consecutive: true,
            },
            attributes: AbiAttributes::default(),
        },
        bindings: vec![AbiBinding {
            place: AbiBindingPlace::Parameter(0),
            source_offset: 0,
            source_bytes: 3,
            carrier_offset: 0,
            carrier_bytes: 3,
        }],
    };
    let registers = transport(&argument, &source, b()).unwrap();
    assert_eq!(registers.len(), 3);
    assert_eq!(registers[0].source_offset, None);
    assert_eq!(registers[0].image.to_vec(), vec![None; 4]);
    assert_eq!(registers[1].image.to_vec(), vec![Some(1)]);
    assert_eq!(
        registers[2].image.to_vec(),
        vec![Some(2), Some(3), None, None]
    );
    assert_eq!(source.read(3, 1).to_vec(), vec![None]);
}

#[derive(Default)]
struct Logger {
    values: Mutex<Vec<i128>>,
}
impl HostCalls for Logger {
    fn call(
        &self,
        callee: &Function,
        sig: &FuncTy,
        args: &[InterpretValue],
        _: &mut HostState,
    ) -> Option<InterpretResult<Vec<InterpretValue>>> {
        if !callee.is_declaration()
            || callee.name != "record_drop"
            || sig.params != [Ty::I32]
            || !sig.returns.is_empty()
            || sig.is_vararg
        {
            return None;
        }
        self.values
            .lock()
            .unwrap()
            .push(args[0].as_int()?.as_signed());
        Some(Ok(vec![]))
    }
    fn models_fixed_arity(&self, callee: &Function) -> bool {
        callee.name == "record_drop"
    }
}
fn logger_module(indirect: bool) -> Module {
    let mut module = module(
        FuncTy::unrecorded(vec![Ty::I32], vec![Ty::I32], false),
        vec![],
    );
    let signature = FuncTy {
        params: vec![Ty::I32],
        returns: vec![],
        is_vararg: false,
        abi: Some(descriptor(
            vec![direct(
                AbiBindingPlace::Parameter(0),
                4,
                4,
                32,
                AbiExtension::Sign,
            )],
            ignore(),
        )),
    };
    module.func_types.push(signature);
    module
        .functions
        .push(Function::new(f(1), "record_drop", FuncTyId::new(1), b()));
    let mut body = vec![];
    if indirect {
        body.push(node(
            Inst::Const {
                ty: Ty::Func(FuncTyId::new(1)),
                value: Constant::FnDef(f(1)),
            },
            1,
        ));
        body.push(void(Inst::CallIndirect {
            callee: v(1),
            sig: FuncTyId::new(1),
            args: vec![v(0)],
            calling_conv: crate::CallingConv::C,
        }));
    } else {
        body.push(void(Inst::Call {
            callee: f(1),
            args: vec![v(0)],
        }));
    }
    body.push(void(Inst::Return { values: vec![v(0)] }));
    module.functions[0].blocks[0].body = body;
    module
}

#[test]
fn actual_direct_and_function_pointer_calls_deliver_exact_logger_logical_i32() {
    for indirect in [false, true] {
        let module = logger_module(indirect);
        let logger = Logger::default();
        let outcome = Interpreter::with_module(&module)
            .with_host(&logger)
            .execute_func(f(0), [integer(Ty::I32, -17)])
            .unwrap();
        assert_eq!(outcome.returns, vec![integer(Ty::I32, -17)]);
        assert_eq!(outcome.host_calls, 1);
        assert_eq!(*logger.values.lock().unwrap(), vec![-17]);
        // Actual typed bodyless entry follows the same boundary, not a test
        // alternate interpreter or erased signature.
        Interpreter::with_module(&module)
            .with_host(&logger)
            .execute_func(f(1), [integer(Ty::I32, 23)])
            .unwrap();
        assert_eq!(*logger.values.lock().unwrap(), vec![-17, 23]);
    }
}

#[test]
fn unused_fnptr_target_and_standalone_legacy_contradictions_refuse_before_host_effects() {
    let valid = logger_module(false);
    let logger = Logger::default();
    Interpreter::with_module(&valid)
        .with_host(&logger)
        .execute_func(f(0), [integer(Ty::I32, 1)])
        .unwrap();
    for mutation in 0..4 {
        let mut module = valid.clone();
        match mutation {
            0 => {
                let mut unused = module.func_types[1].clone();
                unused.abi.as_mut().unwrap().target.pointer_bytes = 4;
                module.func_types.push(unused);
                module.types.push(Ty::Func(FuncTyId::new(2)));
            }
            1 => module.target_info.as_mut().unwrap().endianness = crate::Endianness::Big,
            2 => {
                module.functions[1].attrs.params = vec![crate::ParamAttrs {
                    ext: crate::ArgExt::ZeroExt,
                    ..Default::default()
                }]
            }
            3 => {
                let repeated =
                    module.func_types[1].abi.as_ref().unwrap().arguments[0].bindings[0].clone();
                module.func_types[1].abi.as_mut().unwrap().arguments[0]
                    .bindings
                    .push(repeated);
            }
            _ => unreachable!(),
        }
        let error = Interpreter::with_module(&module)
            .with_host(&logger)
            .execute_func(f(0), [integer(Ty::I32, 2)])
            .unwrap_err();
        assert_eq!(error.code, InterpretErrorCode::SignatureMismatch);
        assert_eq!(
            *logger.values.lock().unwrap(),
            vec![1],
            "mutation {mutation} reached host"
        );
    }
    let mut supplied = valid.functions[1].clone();
    supplied.attrs.params = vec![crate::ParamAttrs {
        ext: crate::ArgExt::ZeroExt,
        ..Default::default()
    }];
    assert_eq!(
        Interpreter::with_module(&valid)
            .with_host(&logger)
            .execute_function(&supplied, [integer(Ty::I32, 3)])
            .unwrap_err()
            .code,
        InterpretErrorCode::SignatureMismatch
    );
    assert_eq!(*logger.values.lock().unwrap(), vec![1]);
}

#[test]
fn actual_callee_writes_hidden_result_and_caller_reads_that_same_storage() {
    let mut module = module(
        FuncTy::unrecorded(vec![], vec![Ty::I32], false),
        vec![
            node(
                Inst::Alloca {
                    ty: Ty::I32,
                    count: None,
                    align: Some(4),
                },
                0,
            ),
            void(Inst::Call {
                callee: f(1),
                args: vec![v(0)],
            }),
            node(
                Inst::Load {
                    ty: Ty::I32,
                    ptr: v(0),
                    volatile: false,
                    align: Some(4),
                },
                1,
            ),
            void(Inst::Return { values: vec![v(1)] }),
        ],
    );
    let result = AbiArgument {
        size: 4,
        align: 4,
        mode: AbiPassMode::Indirect {
            attributes: AbiAttributes {
                pointee_size: 4,
                pointee_align: Some(4),
                ..Default::default()
            },
            metadata_attributes: None,
            on_stack: false,
            caller_copy: false,
        },
        bindings: vec![AbiBinding {
            place: AbiBindingPlace::HiddenResult(0),
            source_offset: 0,
            source_bytes: 4,
            carrier_offset: 0,
            carrier_bytes: 8,
        }],
    };
    module.func_types.push(FuncTy {
        params: vec![Ty::Ptr],
        returns: vec![],
        is_vararg: false,
        abi: Some(descriptor(vec![], result)),
    });
    let mut callee = Function::new(f(1), "write_actual_sret", FuncTyId::new(1), b());
    let mut block = Block::new(b()).with_param(v(0), Ty::Ptr);
    block.body = vec![
        node(
            Inst::Const {
                ty: Ty::I32,
                value: Constant::Int(99),
            },
            1,
        ),
        void(Inst::Store {
            ty: Ty::I32,
            ptr: v(0),
            value: v(1),
            volatile: false,
            align: Some(4),
        }),
        void(Inst::Return { values: vec![] }),
    ];
    callee.blocks.push(block);
    module.functions.push(callee);
    assert_eq!(
        Interpreter::with_module(&module)
            .execute_func(f(0), [])
            .unwrap()
            .returns,
        vec![integer(Ty::I32, 99)]
    );
    let mut unwritten = module.clone();
    unwritten.functions[1].blocks[0]
        .body
        .retain(|node| !matches!(node.inst, Inst::Store { .. }));
    assert_eq!(
        Interpreter::with_module(&unwritten)
            .execute_func(f(0), [])
            .unwrap_err()
            .code,
        InterpretErrorCode::UndefinedBehavior
    );
    let mut host_result = module.clone();
    host_result.functions[1].blocks.clear();
    let logger = Logger::default();
    assert_eq!(
        Interpreter::with_module(&host_result)
            .with_host(&logger)
            .execute_func(f(0), [])
            .unwrap_err()
            .code,
        InterpretErrorCode::UnsupportedCall
    );
    assert!(logger.values.lock().unwrap().is_empty());
}

fn state() -> ExecState {
    ExecState {
        values: BTreeMap::new(),
        provenance: provenance::State::default(),
        memory: MemoryState::default(),
        globals: BTreeMap::new(),
        frames: BTreeSet::new(),
        next_frame_id: 0,
        steps: 0,
        remaining_fuel: 10000,
        host: HostState::new(),
        host_calls: 0,
        drop_glue: None,
        unwind: UnwindState::default(),
    }
}
fn pointer(value: InterpretPointer) -> InterpretValue {
    InterpretValue {
        ty: Ty::Ptr,
        kind: InterpretValueKind::Ptr(value),
    }
}
fn byval(index: u32) -> AbiArgument {
    AbiArgument {
        size: 4,
        align: 4,
        mode: AbiPassMode::Indirect {
            attributes: AbiAttributes {
                no_alias: true,
                pointee_size: 4,
                pointee_align: Some(4),
                ..Default::default()
            },
            metadata_attributes: None,
            on_stack: false,
            caller_copy: true,
        },
        bindings: vec![AbiBinding {
            place: AbiBindingPlace::Parameter(index),
            source_offset: 0,
            source_bytes: 4,
            carrier_offset: 0,
            carrier_bytes: 8,
        }],
    }
}

#[test]
fn actual_byval_calls_are_isolated_and_retire_copies_on_success_and_fault() {
    let signature = FuncTy {
        params: vec![Ty::Ptr, Ty::Ptr],
        returns: vec![Ty::I32],
        is_vararg: false,
        abi: Some(descriptor(
            vec![byval(0), byval(1)],
            direct(AbiBindingPlace::Result(0), 4, 4, 32, AbiExtension::None),
        )),
    };
    let mut module = module(
        signature,
        vec![
            node(
                Inst::Const {
                    ty: Ty::I32,
                    value: Constant::Int(99),
                },
                2,
            ),
            void(Inst::Store {
                ty: Ty::I32,
                ptr: v(0),
                value: v(2),
                volatile: false,
                align: Some(4),
            }),
            node(
                Inst::Load {
                    ty: Ty::I32,
                    ptr: v(1),
                    volatile: false,
                    align: Some(4),
                },
                3,
            ),
            void(Inst::Return { values: vec![v(3)] }),
        ],
    );
    let mut state = state();
    let original = state.memory.alloc(4, 4, b()).unwrap();
    state
        .memory
        .write_image(
            original,
            &Image::init_bytes(&7i32.to_le_bytes()),
            4,
            b(),
            "test source",
        )
        .unwrap();
    let interpreter = Interpreter::with_module(&module);
    interpreter
        .preflight_typed_abi(&module.functions[0])
        .unwrap();
    let returns = interpreter
        .execute_function_boundary(
            b(),
            &module.functions[0],
            vec![pointer(original), pointer(original)],
            &mut state,
            32,
        )
        .unwrap();
    assert_eq!(returns, vec![integer(Ty::I32, 7)]);
    assert_eq!(
        state
            .memory
            .read_image(original, 4, 4, b(), "test source")
            .unwrap()
            .to_vec(),
        7i32.to_le_bytes().map(Some)
    );
    assert_eq!(
        state
            .memory
            .allocations
            .values()
            .filter(|cell| cell.alive)
            .count(),
        1
    );
    assert!(state.memory.abi_access.is_empty());
    module.functions[0].blocks[0].body = vec![void(Inst::Unreachable)];
    let interpreter = Interpreter::with_module(&module);
    assert!(
        interpreter
            .execute_function_boundary(
                b(),
                &module.functions[0],
                vec![pointer(original), pointer(original)],
                &mut state,
                32
            )
            .is_err()
    );
    assert_eq!(
        state
            .memory
            .allocations
            .values()
            .filter(|cell| cell.alive)
            .count(),
        1
    );
    assert!(state.memory.abi_access.is_empty());
    // Removing the recorded copies creates an unresolved alias case BEFORE
    // the callee runs. This is unavailable provenance, never a fabricated UB.
    for argument in &mut module.func_types[0].abi.as_mut().unwrap().arguments {
        if let AbiPassMode::Indirect { caller_copy, .. } = &mut argument.mode {
            *caller_copy = false;
        }
    }
    let interpreter = Interpreter::with_module(&module);
    assert_eq!(
        interpreter
            .execute_function_boundary(
                b(),
                &module.functions[0],
                vec![pointer(original), pointer(original)],
                &mut state,
                32
            )
            .unwrap_err()
            .code,
        InterpretErrorCode::UnsupportedCall
    );
    assert_eq!(
        state
            .memory
            .allocations
            .values()
            .filter(|cell| cell.alive)
            .count(),
        1
    );
    assert!(state.memory.abi_access.is_empty());
}

#[test]
fn actual_value_stack_carrier_uses_fresh_aligned_area_without_inventing_a_pointer_type() {
    let ty = Ty::Tuple(vec![Ty::I32, Ty::I32]);
    let mut argument = byval(0);
    argument.size = 16;
    argument.align = 16;
    argument.bindings[0].source_bytes = 16;
    argument.bindings[0].carrier_bytes = 8;
    if let AbiPassMode::Indirect {
        attributes,
        on_stack,
        caller_copy,
        ..
    } = &mut argument.mode
    {
        *on_stack = true;
        *caller_copy = false;
        attributes.pointee_size = 16;
        attributes.pointee_align = Some(16);
    }
    let signature = FuncTy {
        params: vec![ty.clone()],
        returns: vec![Ty::I32],
        is_vararg: false,
        abi: Some(descriptor(
            vec![argument],
            direct(AbiBindingPlace::Result(0), 4, 4, 32, AbiExtension::None),
        )),
    };
    let mut module = module(
        signature,
        vec![
            node(
                Inst::ExtractField {
                    ty: Ty::I32,
                    aggregate: v(0),
                    field: 1,
                },
                1,
            ),
            void(Inst::Return { values: vec![v(1)] }),
        ],
    );
    let value = InterpretValue {
        ty: ty.clone(),
        kind: InterpretValueKind::Aggregate(vec![integer(Ty::I32, 7), integer(Ty::I32, 19)]),
    };
    let public = Interpreter::with_module(&module)
        .execute_func(f(0), [value.clone()])
        .unwrap();
    assert_eq!(public.returns, vec![integer(Ty::I32, 19)]);
    let mut state = state();
    let interpreter = Interpreter::with_module(&module);
    interpreter
        .preflight_typed_abi(&module.functions[0])
        .unwrap();
    let returned = interpreter
        .execute_function_boundary(
            b(),
            &module.functions[0],
            vec![value.clone()],
            &mut state,
            32,
        )
        .unwrap();
    assert_eq!(returned, vec![integer(Ty::I32, 19)]);
    assert_eq!(value.ty, ty);
    assert_eq!(state.memory.allocations.len(), 1);
    let area = state.memory.allocations.values().next().unwrap();
    assert_eq!(area.base % 16, 0);
    assert_eq!(area.size, 16);
    assert!(!area.alive);
    assert_eq!(
        area.bytes.read(0, 8).to_vec(),
        7i32.to_le_bytes()
            .into_iter()
            .chain(19i32.to_le_bytes())
            .map(Some)
            .collect::<Vec<_>>()
    );
    assert_eq!(area.bytes.read(8, 8).to_vec(), vec![None; 8]);
    assert!(state.memory.abi_access.is_empty());
    module.functions[0].blocks[0].body = vec![void(Inst::Unreachable)];
    let interpreter = Interpreter::with_module(&module);
    assert!(
        interpreter
            .execute_function_boundary(
                b(),
                &module.functions[0],
                vec![value.clone()],
                &mut state,
                32
            )
            .is_err()
    );
    assert_eq!(
        state
            .memory
            .allocations
            .values()
            .filter(|cell| cell.alive)
            .count(),
        0
    );
    assert!(state.memory.abi_access.is_empty());
    // An incomplete carrier is not a guessed source layout or a pointer.
    module.func_types[0].abi.as_mut().unwrap().arguments[0].bindings[0].carrier_bytes = 4;
    assert_eq!(
        Interpreter::with_module(&module)
            .execute_func(f(0), [value])
            .unwrap_err()
            .code,
        InterpretErrorCode::UnsupportedCall
    );
}

#[test]
fn unsupported_unused_capture_contract_cannot_execute_an_earlier_logger() {
    let valid = logger_module(false);
    let logger = Logger::default();
    Interpreter::with_module(&valid)
        .with_host(&logger)
        .execute_func(f(0), [integer(Ty::I32, 1)])
        .unwrap();
    let mut invalid = valid.clone();
    let mut unused = invalid.func_types[1].clone();
    if let AbiPassMode::Direct(scalar) = &mut unused.abi.as_mut().unwrap().arguments[0].mode {
        scalar.attributes.capture = AbiCapture::None;
    }
    invalid.func_types.push(unused);
    assert_eq!(
        Interpreter::with_module(&invalid)
            .with_host(&logger)
            .execute_func(f(0), [integer(Ty::I32, 2)])
            .unwrap_err()
            .code,
        InterpretErrorCode::UnsupportedCall
    );
    assert_eq!(*logger.values.lock().unwrap(), vec![1]);
    let options = InterpretOptions {
        panic_strategy: PanicStrategy::Unwind,
        ..Default::default()
    };
    assert_eq!(
        Interpreter::with_module(&valid)
            .with_host(&logger)
            .with_options(options)
            .execute_func(f(0), [integer(Ty::I32, 3)])
            .unwrap_err()
            .code,
        InterpretErrorCode::UnsupportedCall
    );
    assert_eq!(*logger.values.lock().unwrap(), vec![1]);
}

struct Admit;
impl ExecutionObserver for Admit {
    type Refusal = ();
    fn admit(&mut self, _: ExecutionProgress) -> Result<(), Self::Refusal> {
        Ok(())
    }
}
#[test]
fn observed_execution_keeps_its_own_metered_refusal_without_unobserved_fallback() {
    let typed = identity(Ty::I32, 4, 32);
    let ordinary = Interpreter::with_module(&typed)
        .execute_func(f(0), [integer(Ty::I32, 17)])
        .unwrap();
    assert_eq!(ordinary.returns, vec![integer(Ty::I32, 17)]);
    let mut observer = Admit;
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    let observed_typed = Interpreter::with_module(&typed).execute_func_observed(
        f(0),
        vec![integer(Ty::I32, 17)],
        &mut session,
    );
    assert!(matches!(observed_typed.exit(),ObservedExit::Returned(outcome) if *outcome==ordinary));
    // Entry/result scalar transport is now modeled by the observed engine.
    // Keep its honest pre-entry refusal on an actual unsupported ABI family,
    // including UNUSED records, rather than requiring a dead blanket fence.
    let mut unsupported = typed.clone();
    unsupported.func_types.push(FuncTy {
        params: vec![Ty::Ptr],
        returns: vec![],
        is_vararg: false,
        abi: Some(descriptor(vec![byval(0)], ignore())),
    });
    let signature = unsupported.func_types.last().unwrap();
    signature.abi.as_ref().unwrap().validate(signature).unwrap();
    signature
        .abi
        .as_ref()
        .unwrap()
        .validate_target(unsupported.target_info.as_ref())
        .unwrap();
    assert_eq!(
        Interpreter::with_module(&unsupported)
            .execute_func(f(0), [integer(Ty::I32, 17)])
            .unwrap(),
        ordinary
    );
    let mut observer = Admit;
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    let withheld = Interpreter::with_module(&unsupported).execute_func_observed(
        f(0),
        vec![integer(Ty::I32, 17)],
        &mut session,
    );
    assert!(
        matches!(withheld.exit(),ObservedExit::UnsupportedObservation {site:ExecutionSite::Entry(function),..} if *function==f(0))
    );
    assert_eq!(withheld.steps(), 0);
    assert_eq!(withheld.host_calls(), 0);
    let mut legacy = typed.clone();
    legacy.func_types[0].abi = None;
    let mut observer = Admit;
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    let measured = Interpreter::with_module(&legacy).execute_func_observed(
        f(0),
        vec![integer(Ty::I32, 17)],
        &mut session,
    );
    assert!(matches!(measured.exit(),ObservedExit::Returned(outcome) if *outcome==ordinary));
}

fn readonly_pointer(index: u32, minimum: u64) -> AbiArgument {
    let mut argument = direct(
        AbiBindingPlace::Parameter(index),
        8,
        8,
        64,
        AbiExtension::None,
    );
    if let AbiPassMode::Direct(scalar) = &mut argument.mode {
        scalar.attributes.readonly = true;
        scalar.attributes.pointee_size = minimum;
        scalar.attributes.pointee_align = Some(4);
    }
    argument
}
fn readonly_call(initial: i128, delta: i128, write: bool, indirect: bool, nested: bool) -> Module {
    let mut module = module(
        FuncTy::unrecorded(vec![], vec![Ty::I32], false),
        vec![
            node(
                Inst::Alloca {
                    ty: Ty::Tuple(vec![Ty::I32, Ty::I32]),
                    count: None,
                    align: Some(4),
                },
                0,
            ),
            node(
                Inst::Const {
                    ty: Ty::I32,
                    value: Constant::Int(11),
                },
                1,
            ),
            void(Inst::Store {
                ty: Ty::I32,
                ptr: v(0),
                value: v(1),
                volatile: false,
                align: Some(4),
            }),
            node(
                Inst::Const {
                    ty: Ty::I64,
                    value: Constant::Int(4),
                },
                2,
            ),
            node(
                Inst::GEP {
                    pointee_ty: Ty::U8,
                    base: v(0),
                    indices: vec![v(2)],
                    inbounds: true,
                },
                3,
            ),
            node(
                Inst::Const {
                    ty: Ty::I32,
                    value: Constant::Int(22),
                },
                4,
            ),
            void(Inst::Store {
                ty: Ty::I32,
                ptr: v(3),
                value: v(4),
                volatile: false,
                align: Some(4),
            }),
        ],
    );
    let argument = if initial == 0 { v(0) } else { v(3) };
    if indirect {
        module.functions[0].blocks[0].body.push(node(
            Inst::Const {
                ty: Ty::Func(FuncTyId::new(1)),
                value: Constant::FnDef(f(1)),
            },
            5,
        ));
        module.functions[0].blocks[0].body.push(node(
            Inst::CallIndirect {
                callee: v(5),
                sig: FuncTyId::new(1),
                args: vec![argument],
                calling_conv: crate::CallingConv::C,
            },
            6,
        ));
    } else {
        module.functions[0].blocks[0].body.push(node(
            Inst::Call {
                callee: f(1),
                args: vec![argument],
            },
            6,
        ));
    }
    module.functions[0].blocks[0]
        .body
        .push(void(Inst::Return { values: vec![v(6)] }));
    module.func_types.push(FuncTy {
        params: vec![Ty::Ptr],
        returns: vec![Ty::I32],
        is_vararg: false,
        abi: Some(descriptor(
            vec![readonly_pointer(0, 4)],
            direct(AbiBindingPlace::Result(0), 4, 4, 32, AbiExtension::None),
        )),
    });
    let mut callee = Function::new(f(1), "readonly_minimum", FuncTyId::new(1), b());
    let mut block = Block::new(b()).with_param(v(0), Ty::Ptr);
    let writes = vec![
        node(
            Inst::Const {
                ty: Ty::I64,
                value: Constant::Int(delta),
            },
            1,
        ),
        node(
            Inst::GEP {
                pointee_ty: Ty::U8,
                base: v(0),
                indices: vec![v(1)],
                inbounds: true,
            },
            2,
        ),
        node(
            Inst::Const {
                ty: Ty::I32,
                value: Constant::Int(99),
            },
            3,
        ),
        void(Inst::Store {
            ty: Ty::I32,
            ptr: v(2),
            value: v(3),
            volatile: false,
            align: Some(4),
        }),
    ];
    if nested && write {
        block.body.push(void(Inst::Call {
            callee: f(2),
            args: vec![v(0)],
        }));
    } else if write {
        block.body.extend(writes.clone());
    }
    block.body.extend([
        node(
            Inst::Load {
                ty: Ty::I32,
                ptr: v(0),
                volatile: false,
                align: Some(4),
            },
            4,
        ),
        void(Inst::Return { values: vec![v(4)] }),
    ]);
    callee.blocks.push(block);
    module.functions.push(callee);
    if nested && write {
        module
            .func_types
            .push(FuncTy::unrecorded(vec![Ty::Ptr], vec![], false));
        let mut helper = Function::new(f(2), "ordinary_nested_writer", FuncTyId::new(2), b());
        let mut block = Block::new(b()).with_param(v(0), Ty::Ptr);
        block.body = writes;
        block.body.push(void(Inst::Return { values: vec![] }));
        helper.blocks.push(block);
        module.functions.push(helper);
    }
    module
}

#[test]
fn readonly_minimum_never_limits_derived_access_domain_and_guards_retire_after_calls() {
    for indirect in [false, true] {
        for (initial, delta, expected) in [(0, 4, 11), (4, -4, 22)] {
            let valid = readonly_call(initial, delta, false, indirect, false);
            assert_eq!(
                Interpreter::with_module(&valid)
                    .execute_func(f(0), [])
                    .unwrap()
                    .returns,
                vec![integer(Ty::I32, expected)]
            );
            for nested in [false, true] {
                let denied = readonly_call(initial, delta, true, indirect, nested);
                assert_eq!(
                    Interpreter::with_module(&denied)
                        .execute_func(f(0), [])
                        .unwrap_err()
                        .code,
                    InterpretErrorCode::UndefinedBehavior
                );
                let mut state = state();
                let interpreter = Interpreter::with_module(&denied);
                interpreter
                    .preflight_typed_abi(&denied.functions[0])
                    .unwrap();
                let error = interpreter
                    .execute_function_boundary(b(), &denied.functions[0], vec![], &mut state, 32)
                    .unwrap_err();
                assert_eq!(error.code, InterpretErrorCode::UndefinedBehavior);
                assert!(state.memory.abi_access.is_empty());
                let pointer =
                    expect_pointer(state.values.get(&v(0)).unwrap(), b(), "caller source").unwrap();
                let bytes = state
                    .memory
                    .read_image(pointer, 8, 4, b(), "unchanged readonly source")
                    .unwrap();
                assert_eq!(
                    bytes.to_vec(),
                    11i32
                        .to_le_bytes()
                        .into_iter()
                        .chain(22i32.to_le_bytes())
                        .map(Some)
                        .collect::<Vec<_>>()
                );
                state
                    .memory
                    .write_image(
                        pointer,
                        &Image::init_bytes(&33i32.to_le_bytes()),
                        4,
                        b(),
                        "guard retired after error",
                    )
                    .unwrap();
            }
        }
    }
}

#[test]
fn noalias_minima_do_not_prove_same_allocation_or_global_independence() {
    let make = |minimum, promised| {
        let mut a = readonly_pointer(0, minimum);
        let mut c = readonly_pointer(1, minimum);
        for argument in [&mut a, &mut c] {
            if let AbiPassMode::Direct(scalar) = &mut argument.mode {
                scalar.attributes.readonly = false;
                scalar.attributes.no_alias = promised;
            }
        }
        module(
            FuncTy {
                params: vec![Ty::Ptr, Ty::Ptr],
                returns: vec![Ty::I32],
                is_vararg: false,
                abi: Some(descriptor(
                    vec![a, c],
                    direct(AbiBindingPlace::Result(0), 4, 4, 32, AbiExtension::None),
                )),
            },
            vec![
                node(
                    Inst::Load {
                        ty: Ty::I32,
                        ptr: v(1),
                        volatile: false,
                        align: Some(4),
                    },
                    2,
                ),
                void(Inst::Return { values: vec![v(2)] }),
            ],
        )
    };
    for minimum in [4, 0] {
        let module = make(minimum, false);
        let interpreter = Interpreter::with_module(&module);
        interpreter
            .preflight_typed_abi(&module.functions[0])
            .unwrap();
        let mut state = state();
        let first = state.memory.alloc(8, 4, b()).unwrap();
        let separate = state.memory.alloc(4, 4, b()).unwrap();
        state
            .memory
            .write_image(
                first,
                &Image::init_bytes(&[7, 0, 0, 0, 19, 0, 0, 0]),
                4,
                b(),
                "first object",
            )
            .unwrap();
        state
            .memory
            .write_image(
                separate,
                &Image::init_bytes(&23i32.to_le_bytes()),
                4,
                b(),
                "separate object",
            )
            .unwrap();
        assert_eq!(
            interpreter
                .execute_function_boundary(
                    b(),
                    &module.functions[0],
                    vec![pointer(first), pointer(separate)],
                    &mut state,
                    32
                )
                .unwrap(),
            vec![integer(Ty::I32, 23)]
        );
        let promised_module = make(minimum, true);
        let promised = Interpreter::with_module(&promised_module);
        promised
            .preflight_typed_abi(&promised_module.functions[0])
            .unwrap();
        for (offset, expected) in [(0, 7), (4, 19)] {
            let alias = InterpretPointer {
                allocation: first.allocation,
                offset,
            };
            // A read-only overlap is valid, even at a zero minimum. Use the
            // actual owning state rather than forged pointers in a fresh run.
            assert_eq!(
                promised
                    .execute_function_boundary(
                        b(),
                        &promised_module.functions[0],
                        vec![pointer(first), pointer(alias)],
                        &mut state,
                        32
                    )
                    .unwrap(),
                vec![integer(Ty::I32, expected)]
            );
            assert!(state.memory.abi_access.is_empty());
        }
    }
    // A SOLE noalias argument still cannot establish independence from the
    // callee's own GlobalAddr. The valid unpromised program observes one cell.
    let mut global = module(
        FuncTy::unrecorded(vec![], vec![Ty::I32], false),
        vec![
            node(
                Inst::GlobalAddr {
                    global: GlobalId::new(0),
                },
                0,
            ),
            node(
                Inst::Call {
                    callee: f(1),
                    args: vec![v(0)],
                },
                1,
            ),
            void(Inst::Return { values: vec![v(1)] }),
        ],
    );
    global.globals.push(crate::Global {
        name: "shared_cell".into(),
        ty: Ty::I32,
        mutable: true,
        initializer: Some(Constant::Int(7)),
        linkage: crate::Linkage::Internal,
        tls: None,
        align: Some(4),
        section: None,
        visibility: Default::default(),
        retained: false,
    });
    global.func_types.push(FuncTy {
        params: vec![Ty::Ptr],
        returns: vec![Ty::I32],
        is_vararg: false,
        abi: Some(descriptor(
            vec![direct(
                AbiBindingPlace::Parameter(0),
                8,
                8,
                64,
                AbiExtension::None,
            )],
            direct(AbiBindingPlace::Result(0), 4, 4, 32, AbiExtension::None),
        )),
    });
    let mut callee = Function::new(f(1), "global_nonargument_alias", FuncTyId::new(1), b());
    let mut block = Block::new(b()).with_param(v(0), Ty::Ptr);
    block.body = vec![
        node(
            Inst::GlobalAddr {
                global: GlobalId::new(0),
            },
            1,
        ),
        node(
            Inst::Const {
                ty: Ty::I32,
                value: Constant::Int(99),
            },
            2,
        ),
        void(Inst::Store {
            ty: Ty::I32,
            ptr: v(0),
            value: v(2),
            volatile: false,
            align: Some(4),
        }),
        node(
            Inst::Load {
                ty: Ty::I32,
                ptr: v(1),
                volatile: false,
                align: Some(4),
            },
            3,
        ),
        void(Inst::Return { values: vec![v(3)] }),
    ];
    callee.blocks.push(block);
    global.functions.push(callee);
    assert_eq!(
        Interpreter::with_module(&global)
            .execute_func(f(0), [])
            .unwrap()
            .returns,
        vec![integer(Ty::I32, 99)]
    );
    if let AbiPassMode::Direct(scalar) =
        &mut global.func_types[1].abi.as_mut().unwrap().arguments[0].mode
    {
        scalar.attributes.no_alias = true;
    }
    assert_eq!(
        Interpreter::with_module(&global)
            .execute_func(f(0), [])
            .unwrap_err()
            .code,
        InterpretErrorCode::UndefinedBehavior
    );

    // Fresh byval noalias remains operational; losing the pointer's actual
    // basis through a raw-address cast is conservatively unavailable.
    let mut fresh = module(
        FuncTy {
            params: vec![Ty::Ptr],
            returns: vec![Ty::I32],
            is_vararg: false,
            abi: Some(descriptor(
                vec![byval(0)],
                direct(AbiBindingPlace::Result(0), 4, 4, 32, AbiExtension::None),
            )),
        },
        vec![
            node(
                Inst::Load {
                    ty: Ty::I32,
                    ptr: v(0),
                    volatile: false,
                    align: Some(4),
                },
                1,
            ),
            void(Inst::Return { values: vec![v(1)] }),
        ],
    );
    let mut fresh_state = state();
    let source = fresh_state.memory.alloc(4, 4, b()).unwrap();
    fresh_state
        .memory
        .write_image(
            source,
            &Image::init_bytes(&7i32.to_le_bytes()),
            4,
            b(),
            "fresh source",
        )
        .unwrap();
    assert_eq!(
        Interpreter::with_module(&fresh)
            .execute_function_boundary(
                b(),
                &fresh.functions[0],
                vec![pointer(source)],
                &mut fresh_state,
                32
            )
            .unwrap(),
        vec![integer(Ty::I32, 7)]
    );
    let mut raw = fresh.clone();
    raw.func_types[0].params.push(Ty::Ptr);
    raw.functions[0].blocks[0].params.push((v(7), Ty::Ptr));
    let abi = raw.func_types[0].abi.as_mut().unwrap();
    abi.fixed_count = 2;
    abi.arguments.push(direct(
        AbiBindingPlace::Parameter(1),
        8,
        8,
        64,
        AbiExtension::None,
    ));
    raw.functions[0].blocks[0].body = vec![
        node(
            Inst::Const {
                ty: Ty::I32,
                value: Constant::Int(99),
            },
            2,
        ),
        void(Inst::Store {
            ty: Ty::I32,
            ptr: v(0),
            value: v(2),
            volatile: false,
            align: Some(4),
        }),
        node(
            Inst::Load {
                ty: Ty::I32,
                ptr: v(7),
                volatile: false,
                align: Some(4),
            },
            3,
        ),
        void(Inst::Return { values: vec![v(3)] }),
    ];
    let mut raw_state = state();
    let original = raw_state.memory.alloc(4, 4, b()).unwrap();
    raw_state
        .memory
        .write_image(
            original,
            &Image::init_bytes(&7i32.to_le_bytes()),
            4,
            b(),
            "raw alias source",
        )
        .unwrap();
    let prospective = raw_state.memory.next_addr;
    let other = InterpretValue {
        ty: Ty::Ptr,
        kind: InterpretValueKind::DanglingPtr(prospective),
    };
    let interpreter = Interpreter::with_module(&raw);
    interpreter.preflight_typed_abi(&raw.functions[0]).unwrap();
    assert_eq!(
        interpreter
            .execute_function_boundary(
                b(),
                &raw.functions[0],
                vec![pointer(original), other],
                &mut raw_state,
                32
            )
            .unwrap_err()
            .code,
        InterpretErrorCode::UnsupportedCall
    );
    assert!(raw_state.memory.abi_access.is_empty());
    assert_eq!(
        raw_state
            .memory
            .allocations
            .values()
            .filter(|cell| cell.alive)
            .count(),
        1
    );
    fresh.functions[0].blocks[0].body = vec![
        node(
            Inst::Cast {
                op: CastOp::PtrToInt,
                src_ty: Ty::Ptr,
                dst_ty: Ty::Usize,
                operand: v(0),
            },
            1,
        ),
        node(
            Inst::Cast {
                op: CastOp::IntToPtr,
                src_ty: Ty::Usize,
                dst_ty: Ty::Ptr,
                operand: v(1),
            },
            2,
        ),
        node(
            Inst::Load {
                ty: Ty::I32,
                ptr: v(2),
                volatile: false,
                align: Some(4),
            },
            3,
        ),
        void(Inst::Return { values: vec![v(3)] }),
    ];
    assert_eq!(
        Interpreter::with_module(&fresh)
            .execute_function_boundary(
                b(),
                &fresh.functions[0],
                vec![pointer(source)],
                &mut fresh_state,
                32
            )
            .unwrap_err()
            .code,
        InterpretErrorCode::UnsupportedCall
    );
    assert!(fresh_state.memory.abi_access.is_empty());
    assert_eq!(
        fresh_state
            .memory
            .allocations
            .values()
            .filter(|cell| cell.alive)
            .count(),
        1
    );
}

#[test]
fn partially_live_byte_cannot_invent_initialized_bits_in_an_integer_carrier() {
    for extension in [AbiExtension::None, AbiExtension::Sign, AbiExtension::Zero] {
        let mut boolean = identity(Ty::Bool, 1, 1);
        if let AbiPassMode::Direct(scalar) =
            &mut boolean.func_types[0].abi.as_mut().unwrap().arguments[0].mode
        {
            scalar.attributes.extension = extension;
        }
        for value in [false, true] {
            assert_eq!(
                Interpreter::with_module(&boolean)
                    .execute_func(f(0), [InterpretValue::bool(value)])
                    .unwrap()
                    .returns,
                vec![InterpretValue::bool(value)]
            );
        }
    }
    for (extension, expected) in [(AbiExtension::Sign, 255), (AbiExtension::Zero, 1)] {
        let mut explicit = identity(Ty::U8, 1, 8);
        explicit.func_types[0].abi.as_mut().unwrap().arguments[0] =
            direct(AbiBindingPlace::Parameter(0), 1, 1, 1, extension);
        assert_eq!(
            Interpreter::with_module(&explicit)
                .execute_func(f(0), [integer(Ty::U8, 255)])
                .unwrap()
                .returns,
            vec![integer(Ty::U8, expected)]
        );
    }
    let mut unknown = identity(Ty::U8, 1, 8);
    unknown.func_types[0].abi.as_mut().unwrap().arguments[0] =
        direct(AbiBindingPlace::Parameter(0), 1, 1, 1, AbiExtension::None);
    assert_eq!(
        Interpreter::with_module(&unknown)
            .execute_func(f(0), [integer(Ty::U8, 255)])
            .unwrap_err()
            .code,
        InterpretErrorCode::UnsupportedCall
    );
    let mut logger_module = logger_module(false);
    let logger = Logger::default();
    Interpreter::with_module(&logger_module)
        .with_host(&logger)
        .execute_func(f(0), [integer(Ty::I32, 7)])
        .unwrap();
    logger_module.func_types.push(unknown.func_types[0].clone());
    assert_eq!(
        Interpreter::with_module(&logger_module)
            .with_host(&logger)
            .execute_func(f(0), [integer(Ty::I32, 8)])
            .unwrap_err()
            .code,
        InterpretErrorCode::UnsupportedCall
    );
    assert_eq!(*logger.values.lock().unwrap(), vec![7]);
}

fn borrow_unwind_module(end: bool, panic: bool) -> Module {
    let mut module = module(
        FuncTy::unrecorded(vec![], vec![Ty::I32], false),
        vec![
            node(
                Inst::Alloca {
                    ty: Ty::I32,
                    count: None,
                    align: Some(4),
                },
                0,
            ),
            node(
                Inst::Alloca {
                    ty: Ty::Ptr,
                    count: None,
                    align: Some(8),
                },
                1,
            ),
            node(
                Inst::Const {
                    ty: Ty::I32,
                    value: Constant::Int(7),
                },
                2,
            ),
            void(Inst::Store {
                ty: Ty::I32,
                ptr: v(0),
                value: v(2),
                volatile: false,
                align: Some(4),
            }),
            void(Inst::Invoke {
                callee: f(1),
                args: vec![v(0), v(1)],
                normal_dest: BlockId::new(1),
                normal_args: vec![],
                unwind_dest: BlockId::new(2),
            }),
        ],
    );
    let mut normal = Block::new(BlockId::new(1));
    normal.body = vec![
        node(
            Inst::Const {
                ty: Ty::I32,
                value: Constant::Int(9),
            },
            10,
        ),
        void(Inst::Return {
            values: vec![v(10)],
        }),
    ];
    let mut catch = Block::new(BlockId::new(2));
    catch.body = vec![
        InstrNode::new(Inst::LandingPad {
            is_cleanup: false,
            catch_type_indices: vec![0],
        })
        .with_results(vec![v(11), v(12)]),
        node(
            Inst::Const {
                ty: Ty::I32,
                value: Constant::Int(17),
            },
            13,
        ),
        void(Inst::Return {
            values: vec![v(13)],
        }),
    ];
    module.functions[0].blocks.extend([normal, catch]);
    let mut abi = descriptor(
        vec![
            byval(0),
            direct(AbiBindingPlace::Parameter(1), 8, 8, 64, AbiExtension::None),
        ],
        ignore(),
    );
    abi.can_unwind = true;
    abi.source_abi = "C-unwind".into();
    abi.lowered_convention = crate::CallingConv::CUnwind;
    module.func_types.push(FuncTy {
        params: vec![Ty::Ptr, Ty::Ptr],
        returns: vec![],
        is_vararg: false,
        abi: Some(abi),
    });
    let mut callee = Function::new(f(1), "borrow_copy_and_exit", FuncTyId::new(1), b());
    callee.calling_conv = crate::CallingConv::CUnwind;
    let mut block = Block::new(b())
        .with_param(v(0), Ty::Ptr)
        .with_param(v(1), Ty::Ptr);
    block.body = vec![
        node(Inst::Borrow { ptr: v(0) }, 2),
        void(Inst::Store {
            ty: Ty::Ptr,
            ptr: v(1),
            value: v(2),
            volatile: false,
            align: Some(8),
        }),
    ];
    if end {
        block.body.push(void(Inst::EndBorrow { borrow_ptr: v(2) }));
    }
    if panic {
        block.body.extend([
            node(
                Inst::Const {
                    ty: Ty::Bool,
                    value: Constant::Bool(false),
                },
                3,
            ),
            void(Inst::Assert {
                cond: v(3),
                kind: AssertKind::Unspecified,
                site: None,
            }),
        ]);
    }
    block.body.push(void(Inst::Return { values: vec![] }));
    callee.blocks.push(block);
    module.functions.push(callee);
    module
}

#[test]
fn failed_copy_retirement_is_noncatchable_and_preserves_borrow_and_original_exit() {
    let options = InterpretOptions {
        panic_strategy: PanicStrategy::Unwind,
        ..Default::default()
    };
    for (panic, expected) in [(false, 9), (true, 17)] {
        let valid = borrow_unwind_module(true, panic);
        assert_eq!(
            Interpreter::with_module(&valid)
                .with_options(options)
                .execute_func(f(0), [])
                .unwrap()
                .returns,
            vec![integer(Ty::I32, expected)]
        );
        let mut baseline_state = state();
        let interpreter = Interpreter::with_module(&valid).with_options(options);
        interpreter
            .preflight_typed_abi(&valid.functions[0])
            .unwrap();
        assert_eq!(
            interpreter
                .execute_function_boundary(
                    b(),
                    &valid.functions[0],
                    vec![],
                    &mut baseline_state,
                    32
                )
                .unwrap(),
            vec![integer(Ty::I32, expected)]
        );
        let copy = baseline_state.memory.allocations.get(&2).unwrap();
        assert!(!copy.alive);
        assert_eq!(copy.live_borrows, 0);
        assert!(baseline_state.memory.abi_access.is_empty());
        let invalid = borrow_unwind_module(false, panic);
        let mut failed_state = state();
        let interpreter = Interpreter::with_module(&invalid).with_options(options);
        interpreter
            .preflight_typed_abi(&invalid.functions[0])
            .unwrap();
        let error = interpreter
            .execute_function_boundary(b(), &invalid.functions[0], vec![], &mut failed_state, 32)
            .unwrap_err();
        assert_eq!(error.code, InterpretErrorCode::UnsupportedCall);
        assert!(error.message.contains("copy retirement unavailable"));
        assert!(error.message.contains("live borrow"));
        assert!(failed_state.unwind.in_flight.is_none());
        assert!(failed_state.memory.abi_access.is_empty());
        let copy = failed_state.memory.allocations.get(&2).unwrap();
        assert!(copy.alive);
        assert_eq!(
            copy.live_borrows, 1,
            "borrow floor was erased to retire copy"
        );
        if panic {
            assert!(error.message.contains("Panic"));
            assert!(error.message.contains("Unspecified"));
        }
        assert!(
            !failed_state.values.contains_key(&v(13)),
            "caller catch continued after failed retirement"
        );
    }
    for ended in [true, false] {
        let mut fault = borrow_unwind_module(ended, false);
        fault.functions[1].blocks[0].body.pop();
        fault.functions[1].blocks[0]
            .body
            .push(void(Inst::Unreachable));
        let error = Interpreter::with_module(&fault)
            .with_options(options)
            .execute_func(f(0), [])
            .unwrap_err();
        if ended {
            assert_eq!(error.code, InterpretErrorCode::UndefinedBehavior);
        } else {
            assert_eq!(error.code, InterpretErrorCode::UnsupportedCall);
            assert!(error.message.contains("UndefinedBehavior"));
            assert!(error.message.contains("live borrow"));
        }
    }
}

fn hidden_access_module(readonly: bool, no_free: bool, free: bool) -> Module {
    let mut module = module(
        FuncTy::unrecorded(vec![], vec![Ty::I32], false),
        vec![
            node(
                Inst::Alloca {
                    ty: Ty::I32,
                    count: None,
                    align: Some(4),
                },
                0,
            ),
            void(Inst::Call {
                callee: f(1),
                args: vec![v(0)],
            }),
            node(
                Inst::Load {
                    ty: Ty::I32,
                    ptr: v(0),
                    volatile: false,
                    align: Some(4),
                },
                1,
            ),
            void(Inst::Return { values: vec![v(1)] }),
        ],
    );
    let result = AbiArgument {
        size: 4,
        align: 4,
        mode: AbiPassMode::Indirect {
            attributes: AbiAttributes {
                readonly,
                no_free,
                writable: true,
                pointee_size: 4,
                pointee_align: Some(4),
                ..Default::default()
            },
            metadata_attributes: None,
            on_stack: false,
            caller_copy: false,
        },
        bindings: vec![AbiBinding {
            place: AbiBindingPlace::HiddenResult(0),
            source_offset: 0,
            source_bytes: 4,
            carrier_offset: 0,
            carrier_bytes: 8,
        }],
    };
    module.func_types.push(FuncTy {
        params: vec![Ty::Ptr],
        returns: vec![],
        is_vararg: false,
        abi: Some(descriptor(vec![], result)),
    });
    let mut callee = Function::new(f(1), "actual_hidden_access", FuncTyId::new(1), b());
    let mut block = Block::new(b()).with_param(v(0), Ty::Ptr);
    block.body = if free {
        vec![void(Inst::Dealloc { ptr: v(0) })]
    } else {
        vec![
            node(
                Inst::Const {
                    ty: Ty::I32,
                    value: Constant::Int(99),
                },
                1,
            ),
            void(Inst::Store {
                ty: Ty::I32,
                ptr: v(0),
                value: v(1),
                volatile: false,
                align: Some(4),
            }),
        ]
    };
    block.body.push(void(Inst::Return { values: vec![] }));
    callee.blocks.push(block);
    module.functions.push(callee);
    module
}

#[test]
fn hidden_pointer_contracts_are_installed_or_refused_before_body_effects() {
    let valid = hidden_access_module(false, true, false);
    assert_eq!(
        Interpreter::with_module(&valid)
            .execute_func(f(0), [])
            .unwrap()
            .returns,
        vec![integer(Ty::I32, 99)]
    );
    let mut baseline_state = state();
    let interpreter = Interpreter::with_module(&valid);
    assert_eq!(
        interpreter
            .execute_function_boundary(b(), &valid.functions[0], vec![], &mut baseline_state, 32)
            .unwrap(),
        vec![integer(Ty::I32, 99)]
    );
    assert!(baseline_state.memory.abi_access.is_empty());
    let readonly = hidden_access_module(true, false, false);
    assert_eq!(
        Interpreter::with_module(&readonly)
            .execute_func(f(0), [])
            .unwrap_err()
            .code,
        InterpretErrorCode::UnsupportedCall
    );
    let mut readonly_without_writable = readonly.clone();
    if let AbiPassMode::Indirect { attributes, .. } = &mut readonly_without_writable.func_types[1]
        .abi
        .as_mut()
        .unwrap()
        .result
        .mode
    {
        attributes.writable = false;
    }
    assert_eq!(
        Interpreter::with_module(&readonly_without_writable)
            .execute_func(f(0), [])
            .unwrap_err()
            .code,
        InterpretErrorCode::UndefinedBehavior
    );
    let no_free = hidden_access_module(false, true, true);
    let mut denied_state = state();
    let interpreter = Interpreter::with_module(&no_free);
    interpreter
        .preflight_typed_abi(&no_free.functions[0])
        .unwrap();
    assert_eq!(
        interpreter
            .execute_function_boundary(b(), &no_free.functions[0], vec![], &mut denied_state, 32)
            .unwrap_err()
            .code,
        InterpretErrorCode::UndefinedBehavior
    );
    assert!(denied_state.memory.allocations.get(&0).unwrap().alive);
    assert!(denied_state.memory.abi_access.is_empty());
    for free in [false, true] {
        let mut unwind = hidden_access_module(false, true, free);
        let abi = unwind.func_types[1].abi.as_mut().unwrap();
        abi.can_unwind = true;
        abi.source_abi = "C-unwind".into();
        abi.lowered_convention = crate::CallingConv::CUnwind;
        unwind.functions[1].calling_conv = crate::CallingConv::CUnwind;
        let body = &mut unwind.functions[1].blocks[0].body;
        body.pop();
        body.extend([
            node(
                Inst::Const {
                    ty: Ty::Bool,
                    value: Constant::Bool(false),
                },
                3,
            ),
            void(Inst::Assert {
                cond: v(3),
                kind: AssertKind::Unspecified,
                site: None,
            }),
            void(Inst::Return { values: vec![] }),
        ]);
        unwind.functions[0].blocks[0].body.truncate(1);
        unwind.functions[0].blocks[0].body.push(void(Inst::Invoke {
            callee: f(1),
            args: vec![v(0)],
            normal_dest: BlockId::new(1),
            normal_args: vec![],
            unwind_dest: BlockId::new(2),
        }));
        let mut normal = Block::new(BlockId::new(1));
        normal.body = vec![
            node(
                Inst::Const {
                    ty: Ty::I32,
                    value: Constant::Int(9),
                },
                9,
            ),
            void(Inst::Return { values: vec![v(9)] }),
        ];
        let mut catch = Block::new(BlockId::new(2));
        catch.body = vec![
            InstrNode::new(Inst::LandingPad {
                is_cleanup: false,
                catch_type_indices: vec![0],
            })
            .with_results(vec![v(10), v(11)]),
            node(
                Inst::Const {
                    ty: Ty::I32,
                    value: Constant::Int(17),
                },
                12,
            ),
            void(Inst::Return {
                values: vec![v(12)],
            }),
        ];
        unwind.functions[0].blocks.extend([normal, catch]);
        let options = InterpretOptions {
            panic_strategy: PanicStrategy::Unwind,
            ..Default::default()
        };
        let result = Interpreter::with_module(&unwind)
            .with_options(options)
            .execute_func(f(0), []);
        if free {
            assert_eq!(
                result.unwrap_err().code,
                InterpretErrorCode::UndefinedBehavior
            );
        } else {
            assert_eq!(result.unwrap().returns, vec![integer(Ty::I32, 17)]);
        }
    }
}

#[test]
fn readonly_covers_rc_mutations_while_nofree_keeps_nonfinal_release_distinct() {
    let mut argument = readonly_pointer(0, 4);
    let mut module = module(
        FuncTy {
            params: vec![Ty::Ptr],
            returns: vec![Ty::Bool],
            is_vararg: false,
            abi: Some(descriptor(
                vec![argument.clone()],
                direct(AbiBindingPlace::Result(0), 1, 1, 1, AbiExtension::None),
            )),
        },
        vec![
            node(Inst::IsUnique { ptr: v(0) }, 1),
            void(Inst::Return { values: vec![v(1)] }),
        ],
    );
    let mut state = state();
    let object = state.memory.alloc(4, 4, b()).unwrap();
    state.memory.record_origin(object, AllocOrigin::CleanHeap);
    state
        .memory
        .write_image(
            object,
            &Image::init_bytes(&7i32.to_le_bytes()),
            4,
            b(),
            "RC source",
        )
        .unwrap();
    let interpreter = Interpreter::with_module(&module);
    interpreter
        .preflight_typed_abi(&module.functions[0])
        .unwrap();
    assert_eq!(
        interpreter
            .execute_function_boundary(
                b(),
                &module.functions[0],
                vec![pointer(object)],
                &mut state,
                32
            )
            .unwrap(),
        vec![InterpretValue::bool(true)]
    );
    module.functions[0].blocks[0]
        .body
        .insert(0, void(Inst::Retain { ptr: v(0) }));
    assert_eq!(
        Interpreter::with_module(&module)
            .execute_function_boundary(
                b(),
                &module.functions[0],
                vec![pointer(object)],
                &mut state,
                32
            )
            .unwrap_err()
            .code,
        InterpretErrorCode::UndefinedBehavior
    );
    assert_eq!(
        state
            .memory
            .allocations
            .get(&object.allocation)
            .unwrap()
            .ref_count,
        1
    );
    assert!(state.memory.abi_access.is_empty());
    state.memory.retain(object, b()).unwrap();
    module.functions[0].blocks[0].body[0] = void(Inst::Release { ptr: v(0) });
    assert_eq!(
        Interpreter::with_module(&module)
            .execute_function_boundary(
                b(),
                &module.functions[0],
                vec![pointer(object)],
                &mut state,
                32
            )
            .unwrap_err()
            .code,
        InterpretErrorCode::UndefinedBehavior
    );
    assert_eq!(
        state
            .memory
            .allocations
            .get(&object.allocation)
            .unwrap()
            .ref_count,
        2
    );
    if let AbiPassMode::Direct(scalar) = &mut argument.mode {
        scalar.attributes.readonly = false;
        scalar.attributes.no_free = true;
    }
    module.func_types[0].abi.as_mut().unwrap().arguments[0] = argument;
    assert_eq!(
        Interpreter::with_module(&module)
            .execute_function_boundary(
                b(),
                &module.functions[0],
                vec![pointer(object)],
                &mut state,
                32
            )
            .unwrap(),
        vec![InterpretValue::bool(true)]
    );
    assert_eq!(
        state
            .memory
            .allocations
            .get(&object.allocation)
            .unwrap()
            .ref_count,
        1
    );
    assert_eq!(
        Interpreter::with_module(&module)
            .execute_function_boundary(
                b(),
                &module.functions[0],
                vec![pointer(object)],
                &mut state,
                32
            )
            .unwrap_err()
            .code,
        InterpretErrorCode::UndefinedBehavior
    );
    assert!(
        state
            .memory
            .allocations
            .get(&object.allocation)
            .unwrap()
            .alive
    );
    assert!(state.memory.abi_access.is_empty());
}

// These controls exercise live allocations in the SAME owning execution state.
// Copying public pointer coordinates into a fresh execute_func run supplies no
// allocation or lineage, so that would not test an operational ABI contract.
#[test]
fn dynamic_noalias_compares_modified_locations_and_actual_derived_accesses() {
    for minimum in [0, 4] {
        for delta in [0, 4] {
            let make = |promised| {
                let mut first = readonly_pointer(0, minimum);
                let mut second = readonly_pointer(1, minimum);
                for argument in [&mut first, &mut second] {
                    if let AbiPassMode::Direct(scalar) = &mut argument.mode {
                        scalar.attributes.readonly = false;
                        scalar.attributes.no_alias = promised;
                    }
                }
                module(
                    FuncTy {
                        params: vec![Ty::Ptr, Ty::Ptr],
                        returns: vec![Ty::I32],
                        is_vararg: false,
                        abi: Some(descriptor(
                            vec![first, second],
                            direct(AbiBindingPlace::Result(0), 4, 4, 32, AbiExtension::None),
                        )),
                    },
                    vec![
                        node(
                            Inst::Const {
                                ty: Ty::I64,
                                value: Constant::Int(delta),
                            },
                            2,
                        ),
                        node(
                            Inst::GEP {
                                pointee_ty: Ty::U8,
                                base: v(0),
                                indices: vec![v(2)],
                                inbounds: true,
                            },
                            3,
                        ),
                        node(
                            Inst::Const {
                                ty: Ty::I32,
                                value: Constant::Int(99),
                            },
                            4,
                        ),
                        void(Inst::Store {
                            ty: Ty::I32,
                            ptr: v(3),
                            value: v(4),
                            volatile: false,
                            align: Some(4),
                        }),
                        node(
                            Inst::Load {
                                ty: Ty::I32,
                                ptr: v(1),
                                volatile: false,
                                align: Some(4),
                            },
                            5,
                        ),
                        void(Inst::Return { values: vec![v(5)] }),
                    ],
                )
            };
            for promised in [false, true] {
                let module = make(promised);
                let interpreter = Interpreter::with_module(&module);
                interpreter
                    .preflight_typed_abi(&module.functions[0])
                    .unwrap();
                let mut owned = state();
                let object = owned.memory.alloc(8, 4, b()).unwrap();
                owned
                    .memory
                    .write_image(
                        object,
                        &Image::init_bytes(&[7, 0, 0, 0, 19, 0, 0, 0]),
                        4,
                        b(),
                        "owning object",
                    )
                    .unwrap();
                let alias = InterpretPointer {
                    allocation: object.allocation,
                    offset: delta as u64,
                };
                let result = interpreter.execute_function_boundary(
                    b(),
                    &module.functions[0],
                    vec![pointer(object), pointer(alias)],
                    &mut owned,
                    32,
                );
                if promised {
                    assert_eq!(
                        result.unwrap_err().code,
                        InterpretErrorCode::UndefinedBehavior
                    );
                } else {
                    assert_eq!(result.unwrap(), vec![integer(Ty::I32, 99)]);
                }
                assert_eq!(owned.provenance.checkpoint(), 0);
            }
            // The same allocation is not itself a contradiction: a write at0 and
            // a read at4 are disjoint modified-location domains.
            let module = make(true);
            let interpreter = Interpreter::with_module(&module);
            let mut owned = state();
            let object = owned.memory.alloc(12, 4, b()).unwrap();
            owned
                .memory
                .write_image(
                    object,
                    &Image::init_bytes(&[7, 0, 0, 0, 19, 0, 0, 0, 23, 0, 0, 0]),
                    4,
                    b(),
                    "disjoint lanes",
                )
                .unwrap();
            let separate_lane = InterpretPointer {
                allocation: object.allocation,
                offset: 8,
            };
            assert_eq!(
                interpreter
                    .execute_function_boundary(
                        b(),
                        &module.functions[0],
                        vec![pointer(object), pointer(separate_lane)],
                        &mut owned,
                        32
                    )
                    .unwrap(),
                vec![integer(Ty::I32, 23)]
            );
        }
    }
}

#[test]
fn readonly_and_nofree_follow_the_actual_based_on_copy_not_numeric_identity() {
    for guarded in [0, 1] {
        let first = readonly_pointer(0, 4);
        let second = direct(AbiBindingPlace::Parameter(1), 8, 8, 64, AbiExtension::None);
        let module = module(
            FuncTy {
                params: vec![Ty::Ptr, Ty::Ptr],
                returns: vec![Ty::I32],
                is_vararg: false,
                abi: Some(descriptor(
                    vec![first, second],
                    direct(AbiBindingPlace::Result(0), 4, 4, 32, AbiExtension::None),
                )),
            },
            vec![
                node(
                    Inst::Const {
                        ty: Ty::I32,
                        value: Constant::Int(99),
                    },
                    2,
                ),
                void(Inst::Store {
                    ty: Ty::I32,
                    ptr: v(guarded),
                    value: v(2),
                    volatile: false,
                    align: Some(4),
                }),
                node(
                    Inst::Load {
                        ty: Ty::I32,
                        ptr: v(0),
                        volatile: false,
                        align: Some(4),
                    },
                    3,
                ),
                void(Inst::Return { values: vec![v(3)] }),
            ],
        );
        let mut owned = state();
        let object = owned.memory.alloc(4, 4, b()).unwrap();
        owned
            .memory
            .write_image(
                object,
                &Image::init_bytes(&7i32.to_le_bytes()),
                4,
                b(),
                "readonly object",
            )
            .unwrap();
        let interpreter = Interpreter::with_module(&module);
        interpreter
            .preflight_typed_abi(&module.functions[0])
            .unwrap();
        let result = interpreter.execute_function_boundary(
            b(),
            &module.functions[0],
            vec![pointer(object), pointer(object)],
            &mut owned,
            32,
        );
        if guarded == 0 {
            assert_eq!(
                result.unwrap_err().code,
                InterpretErrorCode::UndefinedBehavior
            );
            assert_eq!(
                owned
                    .memory
                    .read_image(object, 4, 4, b(), "denied write")
                    .unwrap()
                    .to_vec(),
                7i32.to_le_bytes().map(Some)
            );
        } else {
            assert_eq!(result.unwrap(), vec![integer(Ty::I32, 99)]);
        }
    }
    for freed in [0, 1] {
        let mut first = readonly_pointer(0, 0);
        if let AbiPassMode::Direct(scalar) = &mut first.mode {
            scalar.attributes.readonly = false;
            scalar.attributes.no_free = true;
        }
        let module = module(
            FuncTy {
                params: vec![Ty::Ptr, Ty::Ptr],
                returns: vec![],
                is_vararg: false,
                abi: Some(descriptor(
                    vec![
                        first,
                        direct(AbiBindingPlace::Parameter(1), 8, 8, 64, AbiExtension::None),
                    ],
                    ignore(),
                )),
            },
            vec![
                void(Inst::Dealloc { ptr: v(freed) }),
                void(Inst::Return { values: vec![] }),
            ],
        );
        let mut owned = state();
        let object = owned.memory.alloc(4, 4, b()).unwrap();
        let result = Interpreter::with_module(&module).execute_function_boundary(
            b(),
            &module.functions[0],
            vec![pointer(object), pointer(object)],
            &mut owned,
            32,
        );
        if freed == 0 {
            assert_eq!(
                result.unwrap_err().code,
                InterpretErrorCode::UndefinedBehavior
            );
            assert!(owned.memory.allocations[&object.allocation].alive);
        } else {
            assert!(result.unwrap().is_empty());
            assert!(!owned.memory.allocations[&object.allocation].alive);
        }
    }
}

fn lineage_pipeline(readonly: bool, write: bool) -> Module {
    let mut argument = readonly_pointer(0, 4);
    if let AbiPassMode::Direct(scalar) = &mut argument.mode {
        scalar.attributes.readonly = readonly;
        scalar.attributes.no_alias = true;
    }
    let mut module = module(
        FuncTy {
            params: vec![Ty::Ptr, Ty::Bool],
            returns: vec![Ty::I32],
            is_vararg: false,
            abi: Some(descriptor(
                vec![
                    argument,
                    direct(AbiBindingPlace::Parameter(1), 1, 1, 1, AbiExtension::None),
                ],
                direct(AbiBindingPlace::Result(0), 4, 4, 32, AbiExtension::None),
            )),
        },
        vec![
            node(
                Inst::Alloca {
                    ty: Ty::Ptr,
                    count: None,
                    align: Some(8),
                },
                2,
            ),
            node(
                Inst::Alloca {
                    ty: Ty::Ptr,
                    count: None,
                    align: Some(8),
                },
                3,
            ),
            void(Inst::Store {
                ty: Ty::Ptr,
                ptr: v(2),
                value: v(0),
                volatile: false,
                align: Some(8),
            }),
            node(
                Inst::Const {
                    ty: Ty::Usize,
                    value: Constant::Int(8),
                },
                4,
            ),
            void(Inst::MemCopy {
                dst: v(3),
                src: v(2),
                bytes: v(4),
                overlap: false,
            }),
            node(
                Inst::Load {
                    ty: Ty::Ptr,
                    ptr: v(3),
                    volatile: false,
                    align: Some(8),
                },
                5,
            ),
            node(
                Inst::Cast {
                    op: CastOp::PtrToInt,
                    src_ty: Ty::Ptr,
                    dst_ty: Ty::Usize,
                    operand: v(5),
                },
                6,
            ),
            node(
                Inst::Cast {
                    op: CastOp::IntToPtr,
                    src_ty: Ty::Usize,
                    dst_ty: Ty::Ptr,
                    operand: v(6),
                },
                7,
            ),
            node(
                Inst::Copy {
                    ty: Ty::Ptr,
                    operand: v(7),
                },
                8,
            ),
            node(
                Inst::Select {
                    ty: Ty::Ptr,
                    cond: v(1),
                    then_val: v(8),
                    else_val: v(0),
                },
                9,
            ),
            void(Inst::Br {
                target: BlockId::new(1),
                args: vec![v(9)],
            }),
        ],
    );
    let mut join = Block::new(BlockId::new(1)).with_param(v(10), Ty::Ptr);
    join.body = vec![
        node(
            Inst::Call {
                callee: f(1),
                args: vec![v(10)],
            },
            11,
        ),
        void(Inst::Return {
            values: vec![v(11)],
        }),
    ];
    module.functions[0].blocks.push(join);
    module
        .func_types
        .push(FuncTy::unrecorded(vec![Ty::Ptr], vec![Ty::I32], false));
    let mut helper = Function::new(f(1), "real_nested_helper", FuncTyId::new(1), b());
    let mut block = Block::new(b()).with_param(v(0), Ty::Ptr);
    if write {
        block.body.extend([
            node(
                Inst::Const {
                    ty: Ty::I32,
                    value: Constant::Int(99),
                },
                1,
            ),
            void(Inst::Store {
                ty: Ty::I32,
                ptr: v(0),
                value: v(1),
                volatile: false,
                align: Some(4),
            }),
        ]);
    }
    block.body.extend([
        node(
            Inst::Load {
                ty: Ty::I32,
                ptr: v(0),
                volatile: false,
                align: Some(4),
            },
            2,
        ),
        void(Inst::Return { values: vec![v(2)] }),
    ]);
    helper.blocks.push(block);
    module.functions.push(helper);
    module
}

#[test]
fn real_memory_copy_integer_roundtrip_select_phi_and_nested_call_keep_lineage() {
    for indirect in [false, true] {
        for overlap in [false, true] {
            for choice in [false, true] {
                for (readonly, write, expected) in [
                    (false, true, Some(99)),
                    (true, false, Some(7)),
                    (true, true, None),
                ] {
                    let mut module = lineage_pipeline(readonly, write);
                    if overlap {
                        module.functions[0].blocks[0].body[4].inst = Inst::MemCopy {
                            dst: v(2),
                            src: v(2),
                            bytes: v(4),
                            overlap: true,
                        };
                        if let Inst::Load { ptr, .. } =
                            &mut module.functions[0].blocks[0].body[5].inst
                        {
                            *ptr = v(2);
                        }
                    }
                    if indirect {
                        module.functions[0].blocks[1].body[0].inst = Inst::CallIndirect {
                            callee: v(20),
                            sig: FuncTyId::new(1),
                            args: vec![v(10)],
                            calling_conv: crate::CallingConv::C,
                        };
                        module.functions[0].blocks[1].body.insert(
                            0,
                            node(
                                Inst::Const {
                                    ty: Ty::Func(FuncTyId::new(1)),
                                    value: Constant::FnDef(f(1)),
                                },
                                20,
                            ),
                        );
                    }
                    let interpreter = Interpreter::with_module(&module);
                    interpreter
                        .preflight_typed_abi(&module.functions[0])
                        .unwrap();
                    let mut owned = state();
                    let object = owned.memory.alloc(4, 4, b()).unwrap();
                    owned
                        .memory
                        .write_image(
                            object,
                            &Image::init_bytes(&7i32.to_le_bytes()),
                            4,
                            b(),
                            "pipeline source",
                        )
                        .unwrap();
                    let result = interpreter.execute_function_boundary(
                        b(),
                        &module.functions[0],
                        vec![pointer(object), InterpretValue::bool(choice)],
                        &mut owned,
                        32,
                    );
                    if let Some(expected) = expected {
                        assert_eq!(result.unwrap(), vec![integer(Ty::I32, expected)]);
                    } else {
                        assert_eq!(
                            result.unwrap_err().code,
                            InterpretErrorCode::UndefinedBehavior
                        );
                    }
                    assert_eq!(owned.provenance.checkpoint(), 0);
                }
            }
        }
    }
}

#[test]
fn nested_typed_retag_does_not_grant_another_parameter_basis_by_matching_address() {
    let mut first = readonly_pointer(0, 4);
    let mut second = readonly_pointer(1, 4);
    for argument in [&mut first, &mut second] {
        if let AbiPassMode::Direct(scalar) = &mut argument.mode {
            scalar.attributes.readonly = false;
            scalar.attributes.no_alias = true;
        }
    }
    let mut module = module(
        FuncTy {
            params: vec![Ty::Ptr, Ty::Ptr],
            returns: vec![Ty::I32],
            is_vararg: false,
            abi: Some(descriptor(
                vec![first.clone(), second],
                direct(AbiBindingPlace::Result(0), 4, 4, 32, AbiExtension::None),
            )),
        },
        vec![
            void(Inst::Call {
                callee: f(1),
                args: vec![v(0)],
            }),
            node(
                Inst::Load {
                    ty: Ty::I32,
                    ptr: v(1),
                    volatile: false,
                    align: Some(4),
                },
                2,
            ),
            void(Inst::Return { values: vec![v(2)] }),
        ],
    );
    module.func_types.push(FuncTy {
        params: vec![Ty::Ptr],
        returns: vec![],
        is_vararg: false,
        abi: Some(descriptor(vec![first], ignore())),
    });
    let mut callee = Function::new(f(1), "nested_retag", FuncTyId::new(1), b());
    let mut block = Block::new(b()).with_param(v(0), Ty::Ptr);
    block.body = vec![
        node(
            Inst::Const {
                ty: Ty::I32,
                value: Constant::Int(99),
            },
            1,
        ),
        void(Inst::Store {
            ty: Ty::I32,
            ptr: v(0),
            value: v(1),
            volatile: false,
            align: Some(4),
        }),
        void(Inst::Return { values: vec![] }),
    ];
    callee.blocks.push(block);
    module.functions.push(callee);
    for same in [false, true] {
        let mut owned = state();
        let first = owned.memory.alloc(4, 4, b()).unwrap();
        let second = if same {
            first
        } else {
            owned.memory.alloc(4, 4, b()).unwrap()
        };
        owned
            .memory
            .write_image(
                first,
                &Image::init_bytes(&7i32.to_le_bytes()),
                4,
                b(),
                "first",
            )
            .unwrap();
        owned
            .memory
            .write_image(
                second,
                &Image::init_bytes(&19i32.to_le_bytes()),
                4,
                b(),
                "second",
            )
            .unwrap();
        let result = Interpreter::with_module(&module).execute_function_boundary(
            b(),
            &module.functions[0],
            vec![pointer(first), pointer(second)],
            &mut owned,
            32,
        );
        if same {
            assert_eq!(
                result.unwrap_err().code,
                InterpretErrorCode::UndefinedBehavior
            );
        } else {
            assert_eq!(result.unwrap(), vec![integer(Ty::I32, 19)]);
        }
        assert_eq!(owned.provenance.checkpoint(), 0);
    }
}

#[test]
fn unknown_integer_derivation_refuses_instead_of_guessing_an_argument_basis() {
    let mut argument = readonly_pointer(0, 4);
    if let AbiPassMode::Direct(scalar) = &mut argument.mode {
        scalar.attributes.readonly = false;
        scalar.attributes.no_alias = true;
    }
    let module = module(
        FuncTy {
            params: vec![Ty::Ptr],
            returns: vec![Ty::I32],
            is_vararg: false,
            abi: Some(descriptor(
                vec![argument],
                direct(AbiBindingPlace::Result(0), 4, 4, 32, AbiExtension::None),
            )),
        },
        vec![
            node(
                Inst::Cast {
                    op: CastOp::PtrToInt,
                    src_ty: Ty::Ptr,
                    dst_ty: Ty::Usize,
                    operand: v(0),
                },
                1,
            ),
            node(
                Inst::Cast {
                    op: CastOp::IntToPtr,
                    src_ty: Ty::Usize,
                    dst_ty: Ty::Ptr,
                    operand: v(1),
                },
                4,
            ),
            node(
                Inst::Load {
                    ty: Ty::I32,
                    ptr: v(4),
                    volatile: false,
                    align: Some(4),
                },
                5,
            ),
            void(Inst::Return { values: vec![v(5)] }),
        ],
    );
    let mut owned = state();
    let object = owned.memory.alloc(4, 4, b()).unwrap();
    owned
        .memory
        .write_image(
            object,
            &Image::init_bytes(&7i32.to_le_bytes()),
            4,
            b(),
            "address source",
        )
        .unwrap();
    assert_eq!(
        Interpreter::with_module(&module)
            .execute_function_boundary(
                b(),
                &module.functions[0],
                vec![pointer(object)],
                &mut owned,
                32
            )
            .unwrap(),
        vec![integer(Ty::I32, 7)]
    );
    let mut mixed = module.clone();
    mixed.functions[0].blocks[0].body.splice(
        1..1,
        [
            node(
                Inst::Const {
                    ty: Ty::Usize,
                    value: Constant::Int(0),
                },
                2,
            ),
            node(
                Inst::BinOp {
                    op: BinOp::Add,
                    ty: Ty::Usize,
                    lhs: v(1),
                    rhs: v(2),
                },
                3,
            ),
        ],
    );
    if let Inst::Cast { operand, .. } = &mut mixed.functions[0].blocks[0].body[3].inst {
        *operand = v(3);
    }
    let steps_before = owned.steps;
    let fuel_before = owned.remaining_fuel;
    let error = Interpreter::with_module(&mixed)
        .execute_function_boundary(
            b(),
            &mixed.functions[0],
            vec![pointer(object)],
            &mut owned,
            32,
        )
        .unwrap_err();
    assert_eq!(error.code, InterpretErrorCode::UnsupportedCall);
    assert_eq!(
        error.message,
        "typed ABI provenance: numeric address cannot reconstruct protected pointer provenance"
    );
    // The actual IntToPtr refuses before the subsequent Load can consume an
    // unknown basis, even though add-zero kept the numeric address unchanged.
    assert_eq!(owned.steps - steps_before, 4);
    assert_eq!(fuel_before - owned.remaining_fuel, 4);
    assert_eq!(
        owned
            .memory
            .read_image(object, 4, 4, b(), "denied numeric reconstruction")
            .unwrap()
            .to_vec(),
        7i32.to_le_bytes().map(Some)
    );
    assert_eq!(owned.provenance.checkpoint(), 0);
}

struct RcLineageHost;
impl HostCalls for RcLineageHost {
    fn call(
        &self,
        _: &Function,
        _: &FuncTy,
        _: &[InterpretValue],
        _: &mut HostState,
    ) -> Option<InterpretResult<Vec<InterpretValue>>> {
        None
    }
    fn rc_op(&self, callee: &Function, _: &FuncTy) -> Option<HostRcOp> {
        (callee.name == "actual_rc_retain").then_some(HostRcOp {
            role: HostRcRole::Retain,
            origin: AllocOrigin::CleanHeap,
        })
    }
}
#[test]
fn actual_host_rc_access_uses_the_same_based_on_fact_as_the_instruction() {
    for readonly in [false, true] {
        let mut argument = readonly_pointer(0, 4);
        if let AbiPassMode::Direct(scalar) = &mut argument.mode {
            scalar.attributes.readonly = readonly;
        }
        let mut module = module(
            FuncTy {
                params: vec![Ty::Ptr],
                returns: vec![Ty::Bool],
                is_vararg: false,
                abi: Some(descriptor(
                    vec![argument],
                    direct(AbiBindingPlace::Result(0), 1, 1, 1, AbiExtension::None),
                )),
            },
            vec![
                void(Inst::Call {
                    callee: f(1),
                    args: vec![v(0)],
                }),
                node(Inst::IsUnique { ptr: v(0) }, 1),
                void(Inst::Return { values: vec![v(1)] }),
            ],
        );
        module
            .func_types
            .push(FuncTy::unrecorded(vec![Ty::Ptr], vec![], false));
        module.functions.push(Function::new(
            f(1),
            "actual_rc_retain",
            FuncTyId::new(1),
            b(),
        ));
        let mut owned = state();
        let object = owned.memory.alloc(4, 4, b()).unwrap();
        owned.memory.record_origin(object, AllocOrigin::CleanHeap);
        owned
            .memory
            .write_image(
                object,
                &Image::init_bytes(&7i32.to_le_bytes()),
                4,
                b(),
                "host RC object",
            )
            .unwrap();
        let result = Interpreter::with_module(&module)
            .with_host(&RcLineageHost)
            .execute_function_boundary(
                b(),
                &module.functions[0],
                vec![pointer(object)],
                &mut owned,
                32,
            );
        if readonly {
            assert_eq!(
                result.unwrap_err().code,
                InterpretErrorCode::UndefinedBehavior
            );
            assert_eq!(owned.memory.allocations[&object.allocation].ref_count, 1);
        } else {
            assert_eq!(result.unwrap(), vec![InterpretValue::bool(false)]);
            assert_eq!(owned.memory.allocations[&object.allocation].ref_count, 2);
        }
        assert_eq!(owned.host_calls, 1);
        assert_eq!(owned.provenance.checkpoint(), 0);
    }
}

#[test]
fn implied_dereferenceable_read_and_writable_store_participate_in_noalias() {
    for writable in [false, true] {
        for minimum in [0, 4] {
            let mut first = readonly_pointer(0, minimum);
            if let AbiPassMode::Direct(scalar) = &mut first.mode {
                scalar.attributes.readonly = false;
                scalar.attributes.no_free = true;
                scalar.attributes.no_alias = true;
                scalar.attributes.writable = writable;
            }
            let mut second = direct(AbiBindingPlace::Parameter(1), 8, 8, 64, AbiExtension::None);
            if let AbiPassMode::Direct(scalar) = &mut second.mode {
                scalar.attributes.pointee_size = minimum;
            }
            let module = module(
                FuncTy {
                    params: vec![Ty::Ptr, Ty::Ptr],
                    returns: vec![],
                    is_vararg: false,
                    abi: Some(descriptor(vec![first, second], ignore())),
                },
                vec![
                    void(Inst::Dealloc { ptr: v(1) }),
                    void(Inst::Return { values: vec![] }),
                ],
            );
            let mut owned = state();
            let object = owned.memory.alloc(4, 4, b()).unwrap();
            let result = Interpreter::with_module(&module).execute_function_boundary(
                b(),
                &module.functions[0],
                vec![pointer(object), pointer(object)],
                &mut owned,
                32,
            );
            if minimum == 0 {
                assert!(result.unwrap().is_empty());
                assert!(!owned.memory.allocations[&object.allocation].alive);
            } else {
                assert_eq!(
                    result.unwrap_err().code,
                    InterpretErrorCode::UndefinedBehavior
                );
                assert!(owned.memory.allocations[&object.allocation].alive);
            }
            assert_eq!(owned.provenance.checkpoint(), 0);
        }
    }
    // Even without a body store, writable includes an actual implicit store
    // for noalias reasoning. Two dereferenceable reads alone are still valid.
    for writable in [false, true] {
        let mut first = readonly_pointer(0, 4);
        if let AbiPassMode::Direct(scalar) = &mut first.mode {
            scalar.attributes.readonly = false;
            scalar.attributes.no_alias = true;
            scalar.attributes.writable = writable;
        }
        let mut second = readonly_pointer(1, 4);
        if let AbiPassMode::Direct(scalar) = &mut second.mode {
            scalar.attributes.readonly = false;
        }
        let module = module(
            FuncTy {
                params: vec![Ty::Ptr, Ty::Ptr],
                returns: vec![],
                is_vararg: false,
                abi: Some(descriptor(vec![first, second], ignore())),
            },
            vec![void(Inst::Return { values: vec![] })],
        );
        let mut owned = state();
        let object = owned.memory.alloc(4, 4, b()).unwrap();
        let result = Interpreter::with_module(&module).execute_function_boundary(
            b(),
            &module.functions[0],
            vec![pointer(object), pointer(object)],
            &mut owned,
            32,
        );
        if writable {
            assert_eq!(
                result.unwrap_err().code,
                InterpretErrorCode::UndefinedBehavior
            );
        } else {
            assert!(result.unwrap().is_empty());
        }
    }
    for writable in [false, true] {
        let mut first = readonly_pointer(0, 4);
        let mut second = readonly_pointer(1, 4);
        if let AbiPassMode::Direct(scalar) = &mut first.mode {
            scalar.attributes.readonly = false;
            scalar.attributes.writable = writable;
        }
        if let AbiPassMode::Direct(scalar) = &mut second.mode {
            scalar.attributes.readonly = false;
            scalar.attributes.no_alias = true;
        }
        let module = module(
            FuncTy {
                params: vec![Ty::Ptr, Ty::Ptr],
                returns: vec![],
                is_vararg: false,
                abi: Some(descriptor(vec![first, second], ignore())),
            },
            vec![void(Inst::Return { values: vec![] })],
        );
        let mut owned = state();
        let object = owned.memory.alloc(4, 4, b()).unwrap();
        let result = Interpreter::with_module(&module).execute_function_boundary(
            b(),
            &module.functions[0],
            vec![pointer(object), pointer(object)],
            &mut owned,
            32,
        );
        if writable {
            assert_eq!(
                result.unwrap_err().code,
                InterpretErrorCode::UndefinedBehavior
            );
        } else {
            assert!(result.unwrap().is_empty());
        }
        assert_eq!(owned.provenance.checkpoint(), 0);
    }
}

#[derive(Default)]
struct OpaqueAddressHost(Mutex<usize>);
impl HostCalls for OpaqueAddressHost {
    fn call(
        &self,
        callee: &Function,
        sig: &FuncTy,
        _: &[InterpretValue],
        _: &mut HostState,
    ) -> Option<InterpretResult<Vec<InterpretValue>>> {
        if callee.name != "opaque_pointer_use"
            || sig.params != [Ty::Ptr]
            || sig.returns != [Ty::Usize]
        {
            return None;
        }
        *self.0.lock().unwrap() += 1;
        Some(Ok(vec![integer(Ty::Usize, 17)]))
    }
}
#[test]
fn opaque_host_cannot_drop_constrained_address_lineage_before_future_access() {
    let host = OpaqueAddressHost::default();
    for readonly in [false, true] {
        let mut argument = readonly_pointer(0, 4);
        if let AbiPassMode::Direct(scalar) = &mut argument.mode {
            scalar.attributes.readonly = readonly;
        }
        let mut module = module(
            FuncTy {
                params: vec![Ty::Ptr],
                returns: vec![Ty::Usize],
                is_vararg: false,
                abi: Some(descriptor(
                    vec![argument],
                    direct(AbiBindingPlace::Result(0), 8, 8, 64, AbiExtension::None),
                )),
            },
            vec![
                node(
                    Inst::Call {
                        callee: f(1),
                        args: vec![v(0)],
                    },
                    1,
                ),
                void(Inst::Return { values: vec![v(1)] }),
            ],
        );
        module
            .func_types
            .push(FuncTy::unrecorded(vec![Ty::Ptr], vec![Ty::Usize], false));
        module.functions.push(Function::new(
            f(1),
            "opaque_pointer_use",
            FuncTyId::new(1),
            b(),
        ));
        let mut owned = state();
        let object = owned.memory.alloc(4, 4, b()).unwrap();
        let result = Interpreter::with_module(&module)
            .with_host(&host)
            .execute_function_boundary(
                b(),
                &module.functions[0],
                vec![pointer(object)],
                &mut owned,
                32,
            );
        if readonly {
            let error = result.unwrap_err();
            assert_eq!(error.code, InterpretErrorCode::UnsupportedCall);
            assert!(
                error
                    .message
                    .contains("host has no declared address/lineage")
            );
            assert_eq!(owned.host_calls, 0);
        } else {
            assert_eq!(result.unwrap(), vec![integer(Ty::Usize, 17)]);
            assert_eq!(owned.host_calls, 1);
        }
        assert_eq!(*host.0.lock().unwrap(), 1);
        assert_eq!(owned.provenance.checkpoint(), 0);
    }
}

fn inactive_shadow_overwrite(seed: bool, action: u32) -> Module {
    let mut module = module(
        FuncTy::unrecorded(vec![], vec![Ty::I32], false),
        vec![
            node(
                Inst::Alloca {
                    ty: Ty::I32,
                    count: None,
                    align: Some(4),
                },
                0,
            ),
            node(
                Inst::Alloca {
                    ty: Ty::Ptr,
                    count: None,
                    align: Some(8),
                },
                1,
            ),
            node(
                Inst::Const {
                    ty: Ty::I32,
                    value: Constant::Int(7),
                },
                2,
            ),
            void(Inst::Store {
                ty: Ty::I32,
                ptr: v(0),
                value: v(2),
                volatile: false,
                align: Some(4),
            }),
            void(Inst::Store {
                ty: Ty::Ptr,
                ptr: v(1),
                value: v(0),
                volatile: false,
                align: Some(8),
            }),
            node(
                Inst::Alloca {
                    ty: Ty::Ptr,
                    count: None,
                    align: Some(8),
                },
                3,
            ),
            void(Inst::Store {
                ty: Ty::Ptr,
                ptr: v(3),
                value: v(0),
                volatile: false,
                align: Some(8),
            }),
        ],
    );
    if seed {
        module.functions[0].blocks[0].body.push(void(Inst::Call {
            callee: f(1),
            args: vec![v(0), v(1)],
        }));
    }
    match action {
        0 => {}
        1 => module.functions[0].blocks[0].body.push(void(Inst::Store {
            ty: Ty::Ptr,
            ptr: v(1),
            value: v(0),
            volatile: false,
            align: Some(8),
        })),
        2 => module.functions[0].blocks[0].body.extend([
            node(
                Inst::Const {
                    ty: Ty::I64,
                    value: Constant::Int(4),
                },
                4,
            ),
            node(
                Inst::GEP {
                    pointee_ty: Ty::U8,
                    base: v(1),
                    indices: vec![v(4)],
                    inbounds: true,
                },
                5,
            ),
            node(
                Inst::Const {
                    ty: Ty::U32,
                    value: Constant::Int(0),
                },
                6,
            ),
            void(Inst::Store {
                ty: Ty::U32,
                ptr: v(5),
                value: v(6),
                volatile: false,
                align: Some(4),
            }),
        ]),
        3 | 4 => module.functions[0].blocks[0].body.extend([
            node(
                Inst::Const {
                    ty: Ty::Usize,
                    value: Constant::Int(if action == 3 { 8 } else { 4 }),
                },
                4,
            ),
            void(Inst::MemCopy {
                dst: v(1),
                src: v(3),
                bytes: v(4),
                overlap: false,
            }),
        ]),
        _ => unreachable!(),
    }
    module.functions[0].blocks[0].body.extend([
        node(
            Inst::Call {
                callee: f(2),
                args: vec![v(1)],
            },
            7,
        ),
        void(Inst::Return { values: vec![v(7)] }),
    ]);
    module.func_types.push(FuncTy {
        params: vec![Ty::Ptr, Ty::Ptr],
        returns: vec![],
        is_vararg: false,
        abi: Some(descriptor(
            vec![
                readonly_pointer(0, 4),
                direct(AbiBindingPlace::Parameter(1), 8, 8, 64, AbiExtension::None),
            ],
            ignore(),
        )),
    });
    let mut seeder = Function::new(f(1), "real_unknown_shadow_seed", FuncTyId::new(1), b());
    let mut block = Block::new(b())
        .with_param(v(0), Ty::Ptr)
        .with_param(v(1), Ty::Ptr);
    block.body = vec![
        node(
            Inst::Cast {
                op: CastOp::PtrToInt,
                src_ty: Ty::Ptr,
                dst_ty: Ty::Usize,
                operand: v(0),
            },
            2,
        ),
        node(
            Inst::Const {
                ty: Ty::Usize,
                value: Constant::Int(0),
            },
            3,
        ),
        node(
            Inst::BinOp {
                op: BinOp::Add,
                ty: Ty::Usize,
                lhs: v(2),
                rhs: v(3),
            },
            4,
        ),
        void(Inst::Store {
            ty: Ty::Usize,
            ptr: v(1),
            value: v(4),
            volatile: false,
            align: Some(8),
        }),
        void(Inst::Return { values: vec![] }),
    ];
    seeder.blocks.push(block);
    module.functions.push(seeder);
    module.func_types.push(FuncTy {
        params: vec![Ty::Ptr],
        returns: vec![Ty::I32],
        is_vararg: false,
        abi: Some(descriptor(
            vec![readonly_pointer(0, 8)],
            direct(AbiBindingPlace::Result(0), 4, 4, 32, AbiExtension::None),
        )),
    });
    let mut reader = Function::new(f(2), "actual_new_scope_reader", FuncTyId::new(2), b());
    let mut block = Block::new(b()).with_param(v(0), Ty::Ptr);
    block.body = vec![
        node(
            Inst::Load {
                ty: Ty::Ptr,
                ptr: v(0),
                volatile: false,
                align: Some(8),
            },
            1,
        ),
        node(
            Inst::Load {
                ty: Ty::I32,
                ptr: v(1),
                volatile: false,
                align: Some(4),
            },
            2,
        ),
        void(Inst::Return { values: vec![v(2)] }),
    ];
    reader.blocks.push(block);
    module.functions.push(reader);
    module
}

#[test]
fn inactive_real_writes_replace_only_the_actual_overwritten_shadow_bytes() {
    for seed in [false, true] {
        for action in 0..5 {
            let module = inactive_shadow_overwrite(seed, action);
            let result = Interpreter::with_module(&module).execute_func(f(0), []);
            if !seed || action == 1 || action == 3 {
                assert_eq!(result.unwrap().returns, vec![integer(Ty::I32, 7)]);
            } else {
                let error = result.unwrap_err();
                assert_eq!(error.code, InterpretErrorCode::UnsupportedCall);
                assert!(error.message.contains("unresolved based-on lineage"));
            }
        }
    }
}

#[test]
fn empty_shadow_records_do_not_block_ordinary_atomic_work_or_plain_abi_copies() {
    for seed in [false, true] {
        for action in 0..5 {
            let mut module = inactive_shadow_overwrite(seed, action);
            let body = &mut module.functions[0].blocks[0].body;
            let at = body.len() - 2;
            body.splice(
                at..at,
                [
                    node(
                        Inst::Const {
                            ty: Ty::I32,
                            value: Constant::Int(0),
                        },
                        8,
                    ),
                    node(
                        Inst::AtomicRMW {
                            op: crate::inst::AtomicRMWOp::Add,
                            ty: Ty::I32,
                            ptr: v(0),
                            value: v(8),
                            ordering: crate::inst::Ordering::SeqCst,
                        },
                        9,
                    ),
                ],
            );
            let result = Interpreter::with_module(&module).execute_func(f(0), []);
            if !seed || action == 1 || action == 3 {
                assert_eq!(result.unwrap().returns, vec![integer(Ty::I32, 7)]);
            } else {
                assert_eq!(
                    result.unwrap_err().code,
                    InterpretErrorCode::UnsupportedCall
                );
            }
        }
    }
    // ABI preparation copies an unshadowed source too. That must not leave an
    // empty per-allocation map after the private copy is retired.
    let mut module = module(
        FuncTy::unrecorded(vec![], vec![Ty::I32], false),
        vec![
            node(
                Inst::Alloca {
                    ty: Ty::I32,
                    count: None,
                    align: Some(4),
                },
                0,
            ),
            node(
                Inst::Const {
                    ty: Ty::I32,
                    value: Constant::Int(7),
                },
                1,
            ),
            void(Inst::Store {
                ty: Ty::I32,
                ptr: v(0),
                value: v(1),
                volatile: false,
                align: Some(4),
            }),
            void(Inst::Call {
                callee: f(1),
                args: vec![v(0)],
            }),
            node(
                Inst::Const {
                    ty: Ty::I32,
                    value: Constant::Int(0),
                },
                2,
            ),
            node(
                Inst::AtomicRMW {
                    op: crate::inst::AtomicRMWOp::Add,
                    ty: Ty::I32,
                    ptr: v(0),
                    value: v(2),
                    ordering: crate::inst::Ordering::SeqCst,
                },
                3,
            ),
            void(Inst::Return { values: vec![v(3)] }),
        ],
    );
    module.func_types.push(FuncTy {
        params: vec![Ty::Ptr],
        returns: vec![],
        is_vararg: false,
        abi: Some(descriptor(vec![byval(0)], ignore())),
    });
    let mut callee = Function::new(f(1), "copy_unshadowed_source", FuncTyId::new(1), b());
    let mut body = Block::new(b()).with_param(v(0), Ty::Ptr);
    body.body.push(void(Inst::Return { values: vec![] }));
    callee.blocks.push(body);
    module.functions.push(callee);
    assert_eq!(
        Interpreter::with_module(&module)
            .execute_func(f(0), [])
            .unwrap()
            .returns,
        vec![integer(Ty::I32, 7)]
    );
}

fn capture_store_module(
    capture: AbiCapture,
    write: bool,
    use_original: bool,
    unwind: bool,
) -> Module {
    let mut module = module(
        FuncTy::unrecorded(vec![], vec![Ty::I32], false),
        vec![
            node(
                Inst::Alloca {
                    ty: Ty::I32,
                    count: None,
                    align: Some(4),
                },
                0,
            ),
            node(
                Inst::Alloca {
                    ty: Ty::Ptr,
                    count: None,
                    align: Some(8),
                },
                1,
            ),
            node(
                Inst::Const {
                    ty: Ty::I32,
                    value: Constant::Int(7),
                },
                2,
            ),
            void(Inst::Store {
                ty: Ty::I32,
                ptr: v(0),
                value: v(2),
                volatile: false,
                align: Some(4),
            }),
        ],
    );
    let mut argument = readonly_pointer(0, 4);
    if let AbiPassMode::Direct(scalar) = &mut argument.mode {
        scalar.attributes.readonly = false;
        scalar.attributes.capture = capture;
    }
    let mut abi = descriptor(
        vec![
            argument,
            direct(AbiBindingPlace::Parameter(1), 8, 8, 64, AbiExtension::None),
        ],
        ignore(),
    );
    if unwind {
        abi.can_unwind = true;
        abi.source_abi = "C-unwind".into();
        abi.lowered_convention = crate::CallingConv::CUnwind;
    }
    module.func_types.push(FuncTy {
        params: vec![Ty::Ptr, Ty::Ptr],
        returns: vec![],
        is_vararg: false,
        abi: Some(abi),
    });
    let mut callee = Function::new(f(1), "actual_capture_store", FuncTyId::new(1), b());
    if unwind {
        callee.calling_conv = crate::CallingConv::CUnwind;
    }
    let mut body = Block::new(b())
        .with_param(v(0), Ty::Ptr)
        .with_param(v(1), Ty::Ptr);
    body.body.push(void(Inst::Store {
        ty: Ty::Ptr,
        ptr: v(1),
        value: v(0),
        volatile: false,
        align: Some(8),
    }));
    if unwind {
        body.body.extend([
            node(
                Inst::Const {
                    ty: Ty::Bool,
                    value: Constant::Bool(false),
                },
                2,
            ),
            void(Inst::Assert {
                cond: v(2),
                kind: AssertKind::Unspecified,
                site: None,
            }),
        ]);
    }
    body.body.push(void(Inst::Return { values: vec![] }));
    callee.blocks.push(body);
    module.functions.push(callee);
    let mut continuation = vec![node(
        Inst::Load {
            ty: Ty::Ptr,
            ptr: v(1),
            volatile: false,
            align: Some(8),
        },
        3,
    )];
    let used = if use_original { v(0) } else { v(3) };
    if write {
        continuation.extend([
            node(
                Inst::Const {
                    ty: Ty::I32,
                    value: Constant::Int(99),
                },
                4,
            ),
            void(Inst::Store {
                ty: Ty::I32,
                ptr: used,
                value: v(4),
                volatile: false,
                align: Some(4),
            }),
        ]);
    }
    continuation.extend([
        node(
            Inst::Load {
                ty: Ty::I32,
                ptr: used,
                volatile: false,
                align: Some(4),
            },
            5,
        ),
        void(Inst::Return { values: vec![v(5)] }),
    ]);
    if unwind {
        module.functions[0].blocks[0].body.push(void(Inst::Invoke {
            callee: f(1),
            args: vec![v(0), v(1)],
            normal_dest: BlockId::new(1),
            normal_args: vec![],
            unwind_dest: BlockId::new(2),
        }));
        let mut normal = Block::new(BlockId::new(1));
        normal.body = vec![void(Inst::Unreachable)];
        let mut catch = Block::new(BlockId::new(2));
        catch.body.push(
            InstrNode::new(Inst::LandingPad {
                is_cleanup: false,
                catch_type_indices: vec![0],
            })
            .with_results(vec![v(8), v(9)]),
        );
        catch.body.extend(continuation);
        module.functions[0].blocks.extend([normal, catch]);
    } else {
        module.functions[0].blocks[0].body.push(void(Inst::Call {
            callee: f(1),
            args: vec![v(0), v(1)],
        }));
        module.functions[0].blocks[0].body.extend(continuation);
    }
    module
}

#[test]
fn captured_pointer_permissions_expire_after_return_and_real_unwind() {
    for unwind in [false, true] {
        for capture in [AbiCapture::Any, AbiCapture::Address, AbiCapture::ReadOnly] {
            for write in [false, true] {
                let module = capture_store_module(capture, write, false, unwind);
                let options = InterpretOptions {
                    panic_strategy: if unwind {
                        PanicStrategy::Unwind
                    } else {
                        PanicStrategy::Abort
                    },
                    ..Default::default()
                };
                let result = Interpreter::with_module(&module)
                    .with_options(options)
                    .execute_func(f(0), []);
                if capture == AbiCapture::Any || capture == AbiCapture::ReadOnly && !write {
                    assert_eq!(
                        result.unwrap().returns,
                        vec![integer(Ty::I32, if write { 99 } else { 7 })]
                    );
                } else {
                    let error = result.unwrap_err();
                    assert_eq!(error.code, InterpretErrorCode::UndefinedBehavior);
                    assert!(error.message.contains("capture permissions expired"));
                }
                // A different caller copy at the SAME address keeps its permissions.
                let independent = capture_store_module(capture, true, true, unwind);
                assert_eq!(
                    Interpreter::with_module(&independent)
                        .with_options(options)
                        .execute_func(f(0), [])
                        .unwrap()
                        .returns,
                    vec![integer(Ty::I32, 99)]
                );
            }
        }
    }
}

#[test]
fn captures_address_may_store_and_return_without_any_later_dereference() {
    let mut module = capture_store_module(AbiCapture::Address, false, false, false);
    let body = &mut module.functions[0].blocks[0].body;
    body.truncate(5);
    body.extend([
        node(
            Inst::Const {
                ty: Ty::I32,
                value: Constant::Int(17),
            },
            6,
        ),
        void(Inst::Return { values: vec![v(6)] }),
    ]);
    let mut owned = state();
    let interpreter = Interpreter::with_module(&module);
    interpreter
        .preflight_typed_abi(&module.functions[0])
        .unwrap();
    assert_eq!(
        interpreter
            .execute_function_boundary(b(), &module.functions[0], vec![], &mut owned, 32)
            .unwrap(),
        vec![integer(Ty::I32, 17)]
    );
    let source = expect_pointer(
        owned.values.get(&v(0)).unwrap(),
        b(),
        "actual source pointer",
    )
    .unwrap();
    // A public copy of coordinates cannot re-import the retired private fact.
    let mut pointer_reader = module.clone();
    pointer_reader
        .func_types
        .push(FuncTy::unrecorded(vec![Ty::Ptr], vec![Ty::I32], false));
    let mut reader = Function::new(f(2), "reader", FuncTyId::new(2), b());
    let mut block = Block::new(b()).with_param(v(0), Ty::Ptr);
    block.body = vec![
        node(
            Inst::Load {
                ty: Ty::I32,
                ptr: v(0),
                volatile: false,
                align: Some(4),
            },
            1,
        ),
        void(Inst::Return { values: vec![v(1)] }),
    ];
    reader.blocks.push(block);
    pointer_reader.functions.push(reader);
    let error = Interpreter::with_module(&pointer_reader)
        .execute_function_boundary(
            b(),
            &pointer_reader.functions[2],
            vec![pointer(source)],
            &mut owned,
            32,
        )
        .unwrap_err();
    assert_eq!(error.code, InterpretErrorCode::UnsupportedCall);
    assert!(error.message.contains("public copied pointer coordinates"));
}

#[test]
fn captures_none_has_real_non_escaping_positive_and_targeted_address_negatives() {
    let escaped = capture_store_module(AbiCapture::None, false, false, false);
    let mut local = escaped.clone();
    local.functions[1].blocks[0].body = vec![
        node(
            Inst::Alloca {
                ty: Ty::Ptr,
                count: None,
                align: Some(8),
            },
            2,
        ),
        void(Inst::Store {
            ty: Ty::Ptr,
            ptr: v(2),
            value: v(0),
            volatile: false,
            align: Some(8),
        }),
        node(Inst::NullPtr, 3),
        void(Inst::Store {
            ty: Ty::Ptr,
            ptr: v(2),
            value: v(3),
            volatile: false,
            align: Some(8),
        }),
        void(Inst::Return { values: vec![] }),
    ];
    let caller = &mut local.functions[0].blocks[0].body;
    caller.truncate(5);
    caller.extend([
        node(
            Inst::Load {
                ty: Ty::I32,
                ptr: v(0),
                volatile: false,
                align: Some(4),
            },
            6,
        ),
        void(Inst::Return { values: vec![v(6)] }),
    ]);
    assert_eq!(
        Interpreter::with_module(&local)
            .execute_func(f(0), [])
            .unwrap()
            .returns,
        vec![integer(Ty::I32, 7)]
    );
    let error = Interpreter::with_module(&escaped)
        .execute_func(f(0), [])
        .unwrap_err();
    assert_eq!(error.code, InterpretErrorCode::UnsupportedCall);
    assert!(error.message.contains("potentially caller-visible memory"));
    let mut comparison = local.clone();
    comparison.functions[1].blocks[0].body.insert(
        0,
        node(
            Inst::Cast {
                op: CastOp::PtrToInt,
                src_ty: Ty::Ptr,
                dst_ty: Ty::Usize,
                operand: v(0),
            },
            7,
        ),
    );
    let error = Interpreter::with_module(&comparison)
        .execute_func(f(0), [])
        .unwrap_err();
    assert_eq!(error.code, InterpretErrorCode::UnsupportedCall);
    assert!(
        error
            .message
            .contains("address inspection needs an independence proof")
    );
    let mut argument = direct(AbiBindingPlace::Parameter(0), 8, 8, 64, AbiExtension::None);
    if let AbiPassMode::Direct(scalar) = &mut argument.mode {
        scalar.attributes.capture = AbiCapture::None;
    }
    let returned = module(
        FuncTy {
            params: vec![Ty::Ptr],
            returns: vec![Ty::Ptr],
            is_vararg: false,
            abi: Some(descriptor(
                vec![argument],
                direct(AbiBindingPlace::Result(0), 8, 8, 64, AbiExtension::None),
            )),
        },
        vec![void(Inst::Return { values: vec![v(0)] })],
    );
    let mut owned = state();
    let object = owned.memory.alloc(4, 4, b()).unwrap();
    let error = Interpreter::with_module(&returned)
        .execute_function_boundary(
            b(),
            &returned.functions[0],
            vec![pointer(object)],
            &mut owned,
            32,
        )
        .unwrap_err();
    assert_eq!(error.code, InterpretErrorCode::UndefinedBehavior);
    assert!(error.message.contains("returns the pointer's address"));
}

fn fresh_allocator(pipeline: bool, expose: bool) -> Module {
    let mut result = direct(AbiBindingPlace::Result(0), 8, 8, 64, AbiExtension::None);
    if let AbiPassMode::Direct(scalar) = &mut result.mode {
        scalar.attributes.no_alias = true;
    }
    let mut module = module(
        FuncTy {
            params: vec![Ty::Ptr],
            returns: vec![Ty::Ptr],
            is_vararg: false,
            abi: Some(descriptor(
                vec![direct(
                    AbiBindingPlace::Parameter(0),
                    8,
                    8,
                    64,
                    AbiExtension::None,
                )],
                result,
            )),
        },
        vec![
            node(
                Inst::HeapAlloc {
                    ty: Ty::I32,
                    count: None,
                    align: Some(4),
                    origin: AllocOrigin::RustHeap,
                },
                1,
            ),
            node(
                Inst::Const {
                    ty: Ty::I32,
                    value: Constant::Int(7),
                },
                2,
            ),
            void(Inst::Store {
                ty: Ty::I32,
                ptr: v(1),
                value: v(2),
                volatile: false,
                align: Some(4),
            }),
        ],
    );
    if expose {
        module.functions[0].blocks[0].body.push(void(Inst::Store {
            ty: Ty::Ptr,
            ptr: v(0),
            value: v(1),
            volatile: false,
            align: Some(8),
        }));
    }
    let mut returned = v(1);
    if pipeline {
        module.functions[0].blocks[0].body.extend([
            node(
                Inst::Alloca {
                    ty: Ty::Ptr,
                    count: None,
                    align: Some(8),
                },
                3,
            ),
            node(
                Inst::Alloca {
                    ty: Ty::Ptr,
                    count: None,
                    align: Some(8),
                },
                4,
            ),
            void(Inst::Store {
                ty: Ty::Ptr,
                ptr: v(3),
                value: v(1),
                volatile: false,
                align: Some(8),
            }),
            node(
                Inst::Const {
                    ty: Ty::Usize,
                    value: Constant::Int(8),
                },
                5,
            ),
            void(Inst::MemCopy {
                dst: v(4),
                src: v(3),
                bytes: v(5),
                overlap: false,
            }),
            node(
                Inst::Load {
                    ty: Ty::Ptr,
                    ptr: v(4),
                    volatile: false,
                    align: Some(8),
                },
                6,
            ),
            node(
                Inst::Cast {
                    op: CastOp::PtrToInt,
                    src_ty: Ty::Ptr,
                    dst_ty: Ty::Usize,
                    operand: v(6),
                },
                7,
            ),
            node(
                Inst::Cast {
                    op: CastOp::IntToPtr,
                    src_ty: Ty::Usize,
                    dst_ty: Ty::Ptr,
                    operand: v(7),
                },
                8,
            ),
        ]);
        returned = v(8);
    }
    module.functions[0].blocks[0].body.push(void(Inst::Return {
        values: vec![returned],
    }));
    module
}

#[test]
fn noalias_result_uses_actual_heap_birth_and_complete_scalar_pointer_lineage() {
    for pipeline in [false, true] {
        let module = fresh_allocator(pipeline, false);
        let interpreter = Interpreter::with_module(&module);
        interpreter
            .preflight_typed_abi(&module.functions[0])
            .unwrap();
        let mut owned = state();
        let slot = owned.memory.alloc(8, 8, b()).unwrap();
        let returned = interpreter
            .execute_function_boundary(
                b(),
                &module.functions[0],
                vec![pointer(slot)],
                &mut owned,
                32,
            )
            .unwrap();
        let object = expect_pointer(&returned[0], b(), "fresh result").unwrap();
        assert_ne!(object.allocation, slot.allocation);
        assert_eq!(
            owned.memory.allocations[&object.allocation].origin,
            Some(AllocOrigin::RustHeap)
        );
        assert_eq!(
            owned
                .memory
                .read_image(object, 4, 4, b(), "fresh payload")
                .unwrap()
                .to_vec(),
            7i32.to_le_bytes().map(Some)
        );
        let mut stack = module.clone();
        stack.functions[0].blocks[0].body[0].inst = Inst::Alloca {
            ty: Ty::I32,
            count: None,
            align: Some(4),
        };
        let mut denied = state();
        let slot = denied.memory.alloc(8, 8, b()).unwrap();
        let error = Interpreter::with_module(&stack)
            .execute_function_boundary(
                b(),
                &stack.functions[0],
                vec![pointer(slot)],
                &mut denied,
                32,
            )
            .unwrap_err();
        assert_eq!(error.code, InterpretErrorCode::UnsupportedCall);
        assert!(error.message.contains("new live heap allocation"));
    }
}

#[test]
fn noalias_result_rejects_actual_caller_and_global_aliases_and_retained_escape() {
    for expose in [false, true] {
        let module = fresh_allocator(false, expose);
        let mut owned = state();
        let slot = owned.memory.alloc(8, 8, b()).unwrap();
        let result = Interpreter::with_module(&module).execute_function_boundary(
            b(),
            &module.functions[0],
            vec![pointer(slot)],
            &mut owned,
            32,
        );
        if expose {
            let error = result.unwrap_err();
            assert_eq!(error.code, InterpretErrorCode::UnsupportedCall);
            assert!(error.message.contains("fresh-result isolation"));
        } else {
            assert_eq!(result.unwrap().len(), 1);
        }
    }
    let mut old = fresh_allocator(false, false);
    old.functions[0].blocks[0].body = vec![void(Inst::Return { values: vec![v(0)] })];
    let mut ordinary = old.clone();
    if let AbiPassMode::Direct(scalar) =
        &mut ordinary.func_types[0].abi.as_mut().unwrap().result.mode
    {
        scalar.attributes.no_alias = false;
    }
    let mut baseline = state();
    let object = baseline.memory.alloc(8, 8, b()).unwrap();
    assert_eq!(
        Interpreter::with_module(&ordinary)
            .execute_function_boundary(
                b(),
                &ordinary.functions[0],
                vec![pointer(object)],
                &mut baseline,
                32
            )
            .unwrap(),
        vec![pointer(object)]
    );
    let mut denied = state();
    let object = denied.memory.alloc(8, 8, b()).unwrap();
    assert_eq!(
        Interpreter::with_module(&old)
            .execute_function_boundary(
                b(),
                &old.functions[0],
                vec![pointer(object)],
                &mut denied,
                32
            )
            .unwrap_err()
            .code,
        InterpretErrorCode::UndefinedBehavior
    );
    let mut global = fresh_allocator(false, false);
    global.globals.push(crate::Global {
        name: "existing_global".into(),
        ty: Ty::I32,
        mutable: true,
        initializer: Some(Constant::Int(7)),
        linkage: crate::Linkage::Internal,
        tls: None,
        align: Some(4),
        section: None,
        visibility: Default::default(),
        retained: false,
    });
    global.functions[0].blocks[0].body = vec![
        node(
            Inst::GlobalAddr {
                global: GlobalId::new(0),
            },
            1,
        ),
        void(Inst::Return { values: vec![v(1)] }),
    ];
    let mut ordinary = global.clone();
    if let AbiPassMode::Direct(scalar) =
        &mut ordinary.func_types[0].abi.as_mut().unwrap().result.mode
    {
        scalar.attributes.no_alias = false;
    }
    let mut baseline = state();
    let slot = baseline.memory.alloc(8, 8, b()).unwrap();
    assert_eq!(
        Interpreter::with_module(&ordinary)
            .execute_function_boundary(
                b(),
                &ordinary.functions[0],
                vec![pointer(slot)],
                &mut baseline,
                32
            )
            .unwrap()
            .len(),
        1
    );
    let mut denied = state();
    let slot = denied.memory.alloc(8, 8, b()).unwrap();
    assert_eq!(
        Interpreter::with_module(&global)
            .execute_function_boundary(
                b(),
                &global.functions[0],
                vec![pointer(slot)],
                &mut denied,
                32
            )
            .unwrap_err()
            .code,
        InterpretErrorCode::UndefinedBehavior
    );
}

#[test]
fn fresh_result_cannot_be_reconstructed_from_a_matching_numeric_address() {
    let module = fresh_allocator(false, false);
    let mut baseline = state();
    let slot = baseline.memory.alloc(8, 8, b()).unwrap();
    let result = Interpreter::with_module(&module)
        .execute_function_boundary(
            b(),
            &module.functions[0],
            vec![pointer(slot)],
            &mut baseline,
            32,
        )
        .unwrap();
    let actual = expect_pointer(&result[0], b(), "actual allocation result").unwrap();
    let address = baseline
        .memory
        .address(actual, b(), "actual allocation address")
        .unwrap();
    let mut forged = module.clone();
    forged.functions[0].blocks[0].body.pop();
    forged.functions[0].blocks[0].body.extend([
        node(
            Inst::Const {
                ty: Ty::Usize,
                value: Constant::Int(address as i128),
            },
            3,
        ),
        node(
            Inst::Cast {
                op: CastOp::IntToPtr,
                src_ty: Ty::Usize,
                dst_ty: Ty::Ptr,
                operand: v(3),
            },
            4,
        ),
        void(Inst::Return { values: vec![v(4)] }),
    ]);
    let mut denied = state();
    let slot = denied.memory.alloc(8, 8, b()).unwrap();
    let error = Interpreter::with_module(&forged)
        .execute_function_boundary(
            b(),
            &forged.functions[0],
            vec![pointer(slot)],
            &mut denied,
            32,
        )
        .unwrap_err();
    assert_eq!(error.code, InterpretErrorCode::UnsupportedCall);
    assert!(error.message.contains("numeric address cannot reconstruct"));
}

#[test]
fn hidden_result_noalias_is_an_actual_parameter_contract_not_a_fresh_return() {
    let mut module = hidden_access_module(false, true, false);
    if let AbiPassMode::Indirect { attributes, .. } =
        &mut module.func_types[1].abi.as_mut().unwrap().result.mode
    {
        attributes.no_alias = true;
    }
    assert!(module.func_types[1].returns.is_empty());
    assert_eq!(
        Interpreter::with_module(&module)
            .execute_func(f(0), [])
            .unwrap()
            .returns,
        vec![integer(Ty::I32, 99)]
    );
    // The same hidden parameter cannot independently alias caller storage
    // used by the callee. The original complete result record is retained.
    module.globals.push(crate::Global {
        name: "independent".into(),
        ty: Ty::I32,
        mutable: true,
        initializer: Some(Constant::Int(7)),
        linkage: crate::Linkage::Internal,
        tls: None,
        align: Some(4),
        section: None,
        visibility: Default::default(),
        retained: false,
    });
    module.functions[0].blocks[0].body[0].inst = Inst::GlobalAddr {
        global: GlobalId::new(0),
    };
    module.functions[1].blocks[0].body.insert(
        0,
        node(
            Inst::GlobalAddr {
                global: GlobalId::new(0),
            },
            3,
        ),
    );
    module.functions[1].blocks[0].body.insert(
        1,
        node(
            Inst::Load {
                ty: Ty::I32,
                ptr: v(3),
                volatile: false,
                align: Some(4),
            },
            4,
        ),
    );
    assert_eq!(
        Interpreter::with_module(&module)
            .execute_func(f(0), [])
            .unwrap_err()
            .code,
        InterpretErrorCode::UndefinedBehavior
    );
}

#[test]
fn returned_capture_facts_cross_real_call_results_and_cannot_be_refreshed_by_retagging() {
    for capture in [AbiCapture::Any, AbiCapture::Address, AbiCapture::ReadOnly] {
        for write in [false, true] {
            for nested in [false, true] {
                let mut module = module(
                    FuncTy::unrecorded(vec![], vec![Ty::I32], false),
                    vec![
                        node(
                            Inst::Alloca {
                                ty: Ty::I32,
                                count: None,
                                align: Some(4),
                            },
                            0,
                        ),
                        node(
                            Inst::Const {
                                ty: Ty::I32,
                                value: Constant::Int(7),
                            },
                            1,
                        ),
                        void(Inst::Store {
                            ty: Ty::I32,
                            ptr: v(0),
                            value: v(1),
                            volatile: false,
                            align: Some(4),
                        }),
                        node(
                            Inst::Call {
                                callee: f(1),
                                args: vec![v(0)],
                            },
                            2,
                        ),
                    ],
                );
                let mut argument = readonly_pointer(0, 4);
                if let AbiPassMode::Direct(scalar) = &mut argument.mode {
                    scalar.attributes.readonly = false;
                    scalar.attributes.capture = capture;
                }
                module.func_types.push(FuncTy {
                    params: vec![Ty::Ptr],
                    returns: vec![Ty::Ptr],
                    is_vararg: false,
                    abi: Some(descriptor(
                        vec![argument],
                        direct(AbiBindingPlace::Result(0), 8, 8, 64, AbiExtension::None),
                    )),
                });
                let mut identity = Function::new(f(1), "capture_identity", FuncTyId::new(1), b());
                let mut body = Block::new(b()).with_param(v(0), Ty::Ptr);
                body.body.push(void(Inst::Return { values: vec![v(0)] }));
                identity.blocks.push(body);
                module.functions.push(identity);
                let mut consumer = Vec::new();
                if write {
                    consumer.extend([
                        node(
                            Inst::Const {
                                ty: Ty::I32,
                                value: Constant::Int(99),
                            },
                            3,
                        ),
                        void(Inst::Store {
                            ty: Ty::I32,
                            ptr: v(2),
                            value: v(3),
                            volatile: false,
                            align: Some(4),
                        }),
                    ]);
                }
                consumer.extend([
                    node(
                        Inst::Load {
                            ty: Ty::I32,
                            ptr: v(2),
                            volatile: false,
                            align: Some(4),
                        },
                        4,
                    ),
                    void(Inst::Return { values: vec![v(4)] }),
                ]);
                if nested {
                    let mut argument = readonly_pointer(0, 4);
                    if let AbiPassMode::Direct(scalar) = &mut argument.mode {
                        scalar.attributes.readonly = false;
                    }
                    module.func_types.push(FuncTy {
                        params: vec![Ty::Ptr],
                        returns: vec![Ty::I32],
                        is_vararg: false,
                        abi: Some(descriptor(
                            vec![argument],
                            direct(AbiBindingPlace::Result(0), 4, 4, 32, AbiExtension::None),
                        )),
                    });
                    let mut helper =
                        Function::new(f(2), "actual_any_capture_consumer", FuncTyId::new(2), b());
                    let mut body = Block::new(b()).with_param(v(2), Ty::Ptr);
                    body.body = consumer;
                    helper.blocks.push(body);
                    module.functions.push(helper);
                    module.functions[0].blocks[0].body.extend([
                        node(
                            Inst::Call {
                                callee: f(2),
                                args: vec![v(2)],
                            },
                            5,
                        ),
                        void(Inst::Return { values: vec![v(5)] }),
                    ]);
                } else {
                    module.functions[0].blocks[0].body.extend(consumer);
                }
                let result = Interpreter::with_module(&module).execute_func(f(0), []);
                if capture == AbiCapture::Any || capture == AbiCapture::ReadOnly && !write {
                    assert_eq!(
                        result.unwrap().returns,
                        vec![integer(Ty::I32, if write { 99 } else { 7 })]
                    );
                } else {
                    assert_eq!(
                        result.unwrap_err().code,
                        InterpretErrorCode::UndefinedBehavior
                    );
                }
            }
        }
    }
}

#[test]
fn transitive_pointer_images_cannot_hide_capture_or_fresh_result_exposure() {
    let plain = capture_store_module(AbiCapture::Address, false, true, false);
    assert_eq!(
        Interpreter::with_module(&plain)
            .execute_func(f(0), [])
            .unwrap()
            .returns,
        vec![integer(Ty::I32, 7)]
    );
    let mut none = capture_store_module(AbiCapture::None, false, true, false);
    none.functions[1].blocks[0].body = vec![
        node(
            Inst::Alloca {
                ty: Ty::Ptr,
                count: None,
                align: Some(8),
            },
            2,
        ),
        void(Inst::Store {
            ty: Ty::Ptr,
            ptr: v(2),
            value: v(0),
            volatile: false,
            align: Some(8),
        }),
        void(Inst::Store {
            ty: Ty::Ptr,
            ptr: v(1),
            value: v(2),
            volatile: false,
            align: Some(8),
        }),
        void(Inst::Return { values: vec![] }),
    ];
    let error = Interpreter::with_module(&none)
        .execute_func(f(0), [])
        .unwrap_err();
    assert_eq!(error.code, InterpretErrorCode::UnsupportedCall);
    assert!(error.message.contains("potentially caller-visible memory"));
    for expose in [false, true] {
        let mut module = fresh_allocator(false, false);
        module.functions[0].blocks[0].body.pop();
        module.functions[0].blocks[0].body.extend([
            node(
                Inst::HeapAlloc {
                    ty: Ty::Ptr,
                    count: None,
                    align: Some(8),
                    origin: AllocOrigin::RustHeap,
                },
                3,
            ),
            void(Inst::Store {
                ty: Ty::Ptr,
                ptr: v(3),
                value: v(1),
                volatile: false,
                align: Some(8),
            }),
        ]);
        if expose {
            module.functions[0].blocks[0].body.push(void(Inst::Store {
                ty: Ty::Ptr,
                ptr: v(0),
                value: v(3),
                volatile: false,
                align: Some(8),
            }));
        }
        module.functions[0].blocks[0]
            .body
            .push(void(Inst::Return { values: vec![v(1)] }));
        let mut owned = state();
        let slot = owned.memory.alloc(8, 8, b()).unwrap();
        let result = Interpreter::with_module(&module).execute_function_boundary(
            b(),
            &module.functions[0],
            vec![pointer(slot)],
            &mut owned,
            32,
        );
        if expose {
            let error = result.unwrap_err();
            assert_eq!(error.code, InterpretErrorCode::UnsupportedCall);
            assert!(error.message.contains("fresh-result isolation"));
        } else {
            assert_eq!(result.unwrap().len(), 1);
        }
    }
    let failed = capture_store_module(AbiCapture::None, false, false, true);
    let options = InterpretOptions {
        panic_strategy: PanicStrategy::Unwind,
        ..Default::default()
    };
    let error = Interpreter::with_module(&failed)
        .with_options(options)
        .execute_func(f(0), [])
        .unwrap_err();
    assert_eq!(error.code, InterpretErrorCode::UnsupportedCall);
    assert!(error.message.contains("Panic"));
    assert!(error.message.contains("abandoned in-flight"));
}

#[test]
fn fresh_reachability_uses_original_caller_objects_before_private_abi_copies() {
    let mut module = fresh_allocator(false, true);
    let mut argument = byval(0);
    argument.size = 8;
    argument.align = 8;
    argument.bindings[0].source_bytes = 8;
    if let AbiPassMode::Indirect { attributes, .. } = &mut argument.mode {
        attributes.pointee_size = 8;
        attributes.pointee_align = Some(8);
    }
    module.func_types[0].abi.as_mut().unwrap().arguments[0] = argument;
    let mut baseline = state();
    let original = baseline.memory.alloc(8, 8, b()).unwrap();
    baseline
        .memory
        .write_image(
            original,
            &Image::init_bytes(&[0; 8]),
            8,
            b(),
            "original caller slot",
        )
        .unwrap();
    let interpreter = Interpreter::with_module(&module);
    interpreter
        .preflight_typed_abi(&module.functions[0])
        .unwrap();
    let result = interpreter
        .execute_function_boundary(
            b(),
            &module.functions[0],
            vec![pointer(original)],
            &mut baseline,
            32,
        )
        .unwrap();
    let fresh = expect_pointer(&result[0], b(), "real heap output").unwrap();
    assert_eq!(
        baseline.memory.allocations[&fresh.allocation].origin,
        Some(AllocOrigin::RustHeap)
    );
    assert_eq!(
        baseline
            .memory
            .read_image(original, 8, 8, b(), "caller remained isolated")
            .unwrap()
            .to_vec(),
        vec![Some(0); 8]
    );
    assert!(
        !baseline.memory.allocations[&1].alive,
        "actual private ABI copy was not retired"
    );
    // Returning the temporary itself has no heap-birth proof. It must not be
    // mislabeled as an alias of the ORIGINAL caller argument either.
    let mut temporary = module.clone();
    temporary.functions[0].blocks[0]
        .body
        .last_mut()
        .unwrap()
        .inst = Inst::Return { values: vec![v(0)] };
    let mut denied = state();
    let original = denied.memory.alloc(8, 8, b()).unwrap();
    denied
        .memory
        .write_image(
            original,
            &Image::init_bytes(&[0; 8]),
            8,
            b(),
            "original caller slot",
        )
        .unwrap();
    let error = Interpreter::with_module(&temporary)
        .execute_function_boundary(
            b(),
            &temporary.functions[0],
            vec![pointer(original)],
            &mut denied,
            32,
        )
        .unwrap_err();
    assert_eq!(error.code, InterpretErrorCode::UnsupportedCall);
    assert!(error.message.contains("no retained allocation producer"));
    assert!(!error.message.contains("caller argument or actual global"));
}

fn capture_returned_root(capture: AbiCapture, store_parameter: bool, two_hops: bool) -> Module {
    let mut module = module(
        FuncTy::unrecorded(vec![], vec![Ty::I32], false),
        vec![
            node(
                Inst::Alloca {
                    ty: Ty::I32,
                    count: None,
                    align: Some(4),
                },
                0,
            ),
            node(
                Inst::Const {
                    ty: Ty::I32,
                    value: Constant::Int(7),
                },
                1,
            ),
            void(Inst::Store {
                ty: Ty::I32,
                ptr: v(0),
                value: v(1),
                volatile: false,
                align: Some(4),
            }),
            node(
                Inst::Call {
                    callee: f(1),
                    args: vec![v(0)],
                },
                2,
            ),
            node(
                Inst::Const {
                    ty: Ty::I32,
                    value: Constant::Int(17),
                },
                3,
            ),
            void(Inst::Return { values: vec![v(3)] }),
        ],
    );
    let mut argument = readonly_pointer(0, 4);
    if let AbiPassMode::Direct(scalar) = &mut argument.mode {
        scalar.attributes.capture = capture;
    }
    module.func_types.push(FuncTy {
        params: vec![Ty::Ptr],
        returns: vec![Ty::Ptr],
        is_vararg: false,
        abi: Some(descriptor(
            vec![argument],
            direct(AbiBindingPlace::Result(0), 8, 8, 64, AbiExtension::None),
        )),
    });
    let mut callee = Function::new(f(1), "actual_returned_pointer_root", FuncTyId::new(1), b());
    let mut body = Block::new(b()).with_param(v(0), Ty::Ptr);
    body.body.push(node(
        Inst::HeapAlloc {
            ty: Ty::Ptr,
            count: None,
            align: Some(8),
            origin: AllocOrigin::RustHeap,
        },
        1,
    ));
    body.body.push(node(Inst::NullPtr, 2));
    body.body.push(void(Inst::Store {
        ty: Ty::Ptr,
        ptr: v(1),
        value: if store_parameter { v(0) } else { v(2) },
        volatile: false,
        align: Some(8),
    }));
    let returned = if two_hops {
        body.body.extend([
            node(
                Inst::HeapAlloc {
                    ty: Ty::Ptr,
                    count: None,
                    align: Some(8),
                    origin: AllocOrigin::RustHeap,
                },
                3,
            ),
            void(Inst::Store {
                ty: Ty::Ptr,
                ptr: v(3),
                value: v(1),
                volatile: false,
                align: Some(8),
            }),
        ]);
        v(3)
    } else {
        v(1)
    };
    body.body.push(void(Inst::Return {
        values: vec![returned],
    }));
    callee.blocks.push(body);
    module.functions.push(callee);
    module
}

#[test]
fn returned_complete_pointer_roots_participate_in_none_capture_exposure() {
    for two_hops in [false, true] {
        let any = capture_returned_root(AbiCapture::Any, true, two_hops);
        assert_eq!(
            Interpreter::with_module(&any)
                .execute_func(f(0), [])
                .unwrap()
                .returns,
            vec![integer(Ty::I32, 17)]
        );
        let nonescaping = capture_returned_root(AbiCapture::None, false, two_hops);
        assert_eq!(
            Interpreter::with_module(&nonescaping)
                .execute_func(f(0), [])
                .unwrap()
                .returns,
            vec![integer(Ty::I32, 17)]
        );
        let escaped = capture_returned_root(AbiCapture::None, true, two_hops);
        let error = Interpreter::with_module(&escaped)
            .execute_func(f(0), [])
            .unwrap_err();
        assert_eq!(error.code, InterpretErrorCode::UnsupportedCall);
        assert!(error.message.contains("potentially caller-visible memory"));
    }
}

// The module owner caches only immutable policy facts. These execute the same
// actual boundaries as uncached interpreters; no typed ABI verdict is reusable
// across per-interpreter panic options or explicitly supplied functions.
fn cache_probe_arguments(
    argument: InterpretValue,
    consumed: &std::cell::Cell<usize>,
) -> impl Iterator<Item = InterpretValue> + '_ {
    std::iter::once(argument).inspect(move |_| consumed.set(consumed.get() + 1))
}

#[test]
fn cached_typed_scalar_and_boolean_entries_match_uncached_on_repeated_calls() {
    let scalar = identity(Ty::I32, 4, 32);
    let owner = crate::interpret::InterpreterModule::new(&scalar);
    for value in [-17, 0, 127, -17] {
        let argument = integer(Ty::I32, value);
        let expected = Interpreter::with_module(&scalar)
            .execute_func(f(0), [argument.clone()])
            .unwrap();
        let actual = owner
            .interpreter()
            .execute_func(f(0), [argument.clone()])
            .unwrap();
        assert_eq!(actual, expected);
        assert_eq!(actual.returns, vec![argument]);
        assert_eq!(actual.steps, 1);
        assert_eq!(actual.host_calls, 0);
    }
    let boolean = identity(Ty::Bool, 1, 1);
    let owner = crate::interpret::InterpreterModule::new(&boolean);
    for value in [false, true, false, true] {
        let argument = InterpretValue::bool(value);
        let expected = Interpreter::with_module(&boolean)
            .execute_func(f(0), [argument.clone()])
            .unwrap();
        let actual = owner
            .interpreter()
            .execute_func(f(0), [argument.clone()])
            .unwrap();
        assert_eq!(actual, expected);
        assert_eq!(actual.returns, vec![argument]);
        assert_eq!(actual.steps, 1);
        assert_eq!(actual.host_calls, 0);
    }
}

#[test]
fn cached_typed_abi_preflight_rechecks_current_panic_options_before_arguments() {
    let module = identity(Ty::I32, 4, 32);
    let owner = crate::interpret::InterpreterModule::new(&module);
    let warm = owner
        .interpreter()
        .execute_func(f(0), [integer(Ty::I32, 7)])
        .unwrap();
    assert_eq!(
        warm,
        Interpreter::with_module(&module)
            .execute_func(f(0), [integer(Ty::I32, 7)])
            .unwrap()
    );
    assert_eq!(warm.returns, vec![integer(Ty::I32, 7)]);

    let options = InterpretOptions {
        panic_strategy: PanicStrategy::Unwind,
        ..Default::default()
    };
    let cached_consumed = std::cell::Cell::new(0);
    let uncached_consumed = std::cell::Cell::new(0);
    let actual = owner
        .interpreter()
        .with_options(options)
        .execute_func(
            f(0),
            cache_probe_arguments(integer(Ty::I32, 8), &cached_consumed),
        )
        .unwrap_err();
    let expected = Interpreter::with_module(&module)
        .with_options(options)
        .execute_func(
            f(0),
            cache_probe_arguments(integer(Ty::I32, 8), &uncached_consumed),
        )
        .unwrap_err();
    assert_eq!(actual, expected);
    assert_eq!(actual.code, InterpretErrorCode::UnsupportedCall);
    assert_eq!(
        actual.message,
        "typed ABI: typed no-unwind boundary needs an abort-on-crossing model"
    );
    assert_eq!(actual.block, Some(b()));
    assert_eq!(cached_consumed.get(), 0);
    assert_eq!(uncached_consumed.get(), 0);

    // Refusing one interpreter's options cannot poison the shared owner.
    let recovered = owner
        .interpreter()
        .execute_func(f(0), [integer(Ty::I32, 9)])
        .unwrap();
    assert_eq!(
        recovered,
        Interpreter::with_module(&module)
            .execute_func(f(0), [integer(Ty::I32, 9)])
            .unwrap()
    );
    assert_eq!(recovered.returns, vec![integer(Ty::I32, 9)]);
}

#[test]
fn cached_typed_abi_preflight_keeps_unused_fnptr_storage_priority_and_error_blocks() {
    let valid = identity(Ty::I32, 4, 32);
    let owner = crate::interpret::InterpreterModule::new(&valid);
    let positive = owner
        .interpreter()
        .execute_func(f(0), [integer(Ty::I32, 11)])
        .unwrap();
    assert_eq!(
        positive,
        Interpreter::with_module(&valid)
            .execute_func(f(0), [integer(Ty::I32, 11)])
            .unwrap()
    );
    assert_eq!(positive.returns, vec![integer(Ty::I32, 11)]);

    for fnptr_only in [false, true] {
        let mut invalid = valid.clone();
        let mut unused = invalid.func_types[0].clone();
        unused.abi.as_mut().unwrap().target.pointer_bytes = 4;
        invalid.func_types.push(unused);
        if fnptr_only {
            invalid.types.push(Ty::Func(FuncTyId::new(1)));
        }
        invalid
            .types
            .push(Ty::Storage(crate::StorageLayout::new(3, 2)));
        assert!(invalid.first_storage_violation().is_some());
        let owner = crate::interpret::InterpreterModule::new(&invalid);
        // Both calls use the same cached module marker but retain this call's
        // supplied coordinates. No function body names the bad signature.
        for entry in [b(), BlockId::new(17)] {
            let mut supplied = invalid.functions[0].clone();
            supplied.entry = entry;
            supplied.blocks[0].id = entry;
            let cached_consumed = std::cell::Cell::new(0);
            let uncached_consumed = std::cell::Cell::new(0);
            let actual = owner
                .interpreter()
                .execute_function(
                    &supplied,
                    cache_probe_arguments(integer(Ty::I32, 12), &cached_consumed),
                )
                .unwrap_err();
            let expected = Interpreter::with_module(&invalid)
                .execute_function(
                    &supplied,
                    cache_probe_arguments(integer(Ty::I32, 12), &uncached_consumed),
                )
                .unwrap_err();
            assert_eq!(actual, expected, "FnPtr-only descriptor: {fnptr_only}");
            assert_eq!(actual.code, InterpretErrorCode::SignatureMismatch);
            assert_eq!(
                actual.message,
                "typed ABI: typed signature ABI target disagrees with the module target"
            );
            assert_eq!(actual.block, Some(entry));
            assert_eq!(cached_consumed.get(), 0);
            assert_eq!(uncached_consumed.get(), 0);
        }
    }
    // Once descriptors are valid, storage remains an independent refusal.
    let mut storage = valid.clone();
    storage
        .types
        .push(Ty::Storage(crate::StorageLayout::new(3, 2)));
    let owner = crate::interpret::InterpreterModule::new(&storage);
    for entry in [b(), BlockId::new(23)] {
        let mut supplied = storage.functions[0].clone();
        supplied.entry = entry;
        supplied.blocks[0].id = entry;
        let cached_consumed = std::cell::Cell::new(0);
        let uncached_consumed = std::cell::Cell::new(0);
        let actual = owner
            .interpreter()
            .execute_function(
                &supplied,
                cache_probe_arguments(integer(Ty::I32, 13), &cached_consumed),
            )
            .unwrap_err();
        let expected = Interpreter::with_module(&storage)
            .execute_function(
                &supplied,
                cache_probe_arguments(integer(Ty::I32, 13), &uncached_consumed),
            )
            .unwrap_err();
        assert_eq!(actual, expected);
        assert_eq!(actual.code, InterpretErrorCode::TypeError);
        assert_eq!(
            actual.message,
            "storage-only geometry cannot be a typed value or malformed layout"
        );
        assert_eq!(actual.block, Some(entry));
        assert_eq!(cached_consumed.get(), 0);
        assert_eq!(uncached_consumed.get(), 0);
    }
}

#[test]
fn cached_typed_abi_preflight_checks_foreign_supplied_attributes_before_effects() {
    let module = logger_module(false);
    let owner = crate::interpret::InterpreterModule::new(&module);
    let cached_logger = Logger::default();
    let uncached_logger = Logger::default();
    let warm = owner
        .interpreter()
        .with_host(&cached_logger)
        .execute_func(f(0), [integer(Ty::I32, 1)])
        .unwrap();
    assert_eq!(
        warm,
        Interpreter::with_module(&module)
            .with_host(&uncached_logger)
            .execute_func(f(0), [integer(Ty::I32, 1)])
            .unwrap()
    );
    assert_eq!(warm.returns, vec![integer(Ty::I32, 1)]);
    assert_eq!(warm.host_calls, 1);
    assert_eq!(*cached_logger.values.lock().unwrap(), vec![1]);
    assert_eq!(*uncached_logger.values.lock().unwrap(), vec![1]);

    let mut supplied = module.functions[1].clone();
    supplied.entry = BlockId::new(29);
    supplied.attrs.params = vec![crate::ParamAttrs {
        ext: crate::ArgExt::ZeroExt,
        ..Default::default()
    }];
    let cached_consumed = std::cell::Cell::new(0);
    let uncached_consumed = std::cell::Cell::new(0);
    let actual = owner
        .interpreter()
        .with_host(&cached_logger)
        .execute_function(
            &supplied,
            cache_probe_arguments(integer(Ty::I32, 2), &cached_consumed),
        )
        .unwrap_err();
    let expected = Interpreter::with_module(&module)
        .with_host(&uncached_logger)
        .execute_function(
            &supplied,
            cache_probe_arguments(integer(Ty::I32, 2), &uncached_consumed),
        )
        .unwrap_err();
    assert_eq!(actual, expected);
    assert_eq!(actual.code, InterpretErrorCode::SignatureMismatch);
    assert_eq!(
        actual.message,
        "typed ABI: function attributes disagree with typed ABI carrier attributes"
    );
    assert_eq!(actual.block, Some(supplied.entry));
    assert_eq!(cached_consumed.get(), 0);
    assert_eq!(uncached_consumed.get(), 0);
    assert_eq!(*cached_logger.values.lock().unwrap(), vec![1]);
    assert_eq!(*uncached_logger.values.lock().unwrap(), vec![1]);

    let recovered = owner
        .interpreter()
        .with_host(&cached_logger)
        .execute_func(f(0), [integer(Ty::I32, 3)])
        .unwrap();
    assert_eq!(
        recovered,
        Interpreter::with_module(&module)
            .with_host(&uncached_logger)
            .execute_func(f(0), [integer(Ty::I32, 3)])
            .unwrap()
    );
    assert_eq!(recovered.returns, vec![integer(Ty::I32, 3)]);
    assert_eq!(*cached_logger.values.lock().unwrap(), vec![1, 3]);
    assert_eq!(*uncached_logger.values.lock().unwrap(), vec![1, 3]);
}
