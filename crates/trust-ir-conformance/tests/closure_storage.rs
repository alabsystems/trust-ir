//! Stored closure capture images preserve checked targets, bytes and provenance.
use trust_ir::interpret::{InterpretValue, Interpreter};
use trust_ir::{
    Block, BlockId, CallingConv, ClosureTy, Endianness, FuncTyId, Function, InstrNode,
    StructPassingPolicy, TargetInfo, ValueId,
};
use trust_ir::{ClosureLayoutDescriptor, ClosureTyId, Constant, FuncId, FuncTy, Inst, Module, Ty};

fn fixture() -> Module {
    fixture_with_capture(Ty::U32, Constant::Int(41))
}

fn fixture_with_capture(capture: Ty, initial: Constant) -> Module {
    let mut module = Module::new("closure_storage");
    let cid = ClosureTyId::new(0);
    module.target_info = Some(TargetInfo {
        triple: "aarch64-apple-darwin".into(),
        pointer_size: 8,
        endianness: Endianness::Little,
        abi: None,
        struct_passing: StructPassingPolicy::Unclassified,
    });
    module.func_types = vec![
        FuncTy {
            params: vec![],
            returns: vec![capture.clone()],
            is_vararg: false,
            abi: None,
        },
        FuncTy {
            params: vec![capture.clone()],
            returns: vec![capture.clone()],
            is_vararg: false,
            abi: None,
        },
    ];
    module.closure_types = vec![ClosureTy {
        func: FuncTyId::new(0),
        captures: vec![capture.clone()],
    }];
    // Padding is deliberately uninitialized, and must not become a required
    // field or an invented function-pointer word during the round trip.
    module.closure_layouts = vec![ClosureLayoutDescriptor {
        origin: None,
        closure: cid,
        size: 8,
        align: 4,
        capture_offsets: vec![4],
    }];
    let v = ValueId::new;
    let mut body = Function::new(FuncId::new(1), "body", FuncTyId::new(1), BlockId::new(0));
    body.blocks = vec![Block::new(BlockId::new(0)).with_param(v(0), capture.clone())];
    body.blocks[0].body = vec![InstrNode::new(Inst::Return { values: vec![v(0)] })];
    let mut caller = Function::new(FuncId::new(0), "caller", FuncTyId::new(0), BlockId::new(0));
    let node = |inst, result| InstrNode::new(inst).with_result(v(result));
    caller.blocks = vec![Block::new(BlockId::new(0))];
    caller.blocks[0].body = vec![
        node(
            Inst::Const {
                ty: capture,
                value: initial,
            },
            0,
        ),
        node(
            Inst::MakeClosure {
                ty: cid,
                func: body.id,
                captures: vec![v(0)],
            },
            1,
        ),
        node(
            Inst::Alloca {
                ty: Ty::Closure(cid),
                count: None,
                align: None,
            },
            2,
        ),
        InstrNode::new(Inst::Store {
            ty: Ty::Closure(cid),
            ptr: v(2),
            value: v(1),
            volatile: false,
            align: None,
        }),
        node(
            Inst::Load {
                ty: Ty::Closure(cid),
                ptr: v(2),
                volatile: false,
                align: None,
            },
            3,
        ),
        node(
            Inst::CallIndirect {
                callee: v(3),
                sig: FuncTyId::new(0),
                args: vec![],
                calling_conv: CallingConv::C,
            },
            4,
        ),
        InstrNode::new(Inst::Return { values: vec![v(4)] }),
    ];
    module.functions = vec![caller, body];
    module
}

#[test]
fn nominal_frame_origin_round_trips_and_old_frames_keep_their_encoding() {
    use trust_ir::binary::{CLOSURE_ORIGIN_FORMAT_VERSION, deserialize_module, serialize_module};
    let plain = fixture();
    let old_bytes = serialize_module(&plain).unwrap();
    assert!(
        u32::from_le_bytes(old_bytes[8..12].try_into().unwrap()) < CLOSURE_ORIGIN_FORMAT_VERSION
    );
    let mut nominal = plain.clone();
    nominal.closure_layouts[0].origin = Some(trust_ir::ty::TypeOrigin::Clean {
        decl: "Original.Closure".into(),
        env_digest: trust_ir::proof::ProofDigest::sha256([7; 32]),
    });
    let bytes = serialize_module(&nominal).unwrap();
    assert_eq!(
        u32::from_le_bytes(bytes[8..12].try_into().unwrap()),
        CLOSURE_ORIGIN_FORMAT_VERSION
    );
    let decoded = deserialize_module(&bytes).unwrap();
    assert_eq!(decoded.closure_layouts, nominal.closure_layouts);
    assert_ne!(nominal.stable_digest(), plain.stable_digest());
    assert_eq!(serialize_module(&decoded).unwrap(), bytes);
    let mut downgraded = bytes.clone();
    downgraded[8..12].copy_from_slice(&(CLOSURE_ORIGIN_FORMAT_VERSION - 1).to_le_bytes());
    assert!(
        deserialize_module(&downgraded).is_err(),
        "old readers must not erase an origin"
    );
    nominal.closure_layouts[0].origin = None;
    assert_eq!(serialize_module(&nominal).unwrap(), old_bytes);
}

#[test]
fn nominal_frame_origin_text_is_lossless() {
    let mut module = fixture();
    module.closure_layouts[0].origin = Some(trust_ir::ty::TypeOrigin::Clean {
        decl: "Original.Closure".into(),
        env_digest: trust_ir::proof::ProofDigest::sha256([7; 32]),
    });
    let text = module.to_string();
    let decoded = trust_ir::parser::parse_module(&text).unwrap();
    assert_eq!(decoded.closure_layouts, module.closure_layouts);
}

#[test]
fn one_nominal_origin_cannot_describe_conflicting_unused_frames() {
    let mut module = fixture();
    let origin = trust_ir::ty::TypeOrigin::Clean {
        decl: "Original.Closure".into(),
        env_digest: trust_ir::proof::ProofDigest::sha256([7; 32]),
    };
    module.closure_layouts[0].origin = Some(origin.clone());
    module.closure_types.push(module.closure_types[0].clone());
    module.closure_layouts.push(ClosureLayoutDescriptor {
        closure: ClosureTyId::new(1),
        size: 4,
        align: 4,
        capture_offsets: vec![0],
        origin: Some(origin),
    });
    assert!(module.validate_closure_layouts().is_err());
    assert!(module.closure_storage_binding(ClosureTyId::new(0)).is_err());
}

#[test]
fn nominal_origin_serde_retains_old_trailing_field_compatibility() {
    let mut frame = fixture().closure_layouts.remove(0);
    let plain = serde_json::to_value(&frame).unwrap();
    assert!(plain.get("origin").is_none());
    let old = rmp_serde::to_vec(&frame).unwrap();
    assert_eq!(
        rmp_serde::from_slice::<ClosureLayoutDescriptor>(&old).unwrap(),
        frame
    );
    frame.origin = Some(trust_ir::ty::TypeOrigin::Clean {
        decl: "Original.Closure".into(),
        env_digest: trust_ir::proof::ProofDigest::sha256([7; 32]),
    });
    let json = serde_json::to_string(&frame).unwrap();
    assert_eq!(
        serde_json::from_str::<ClosureLayoutDescriptor>(&json).unwrap(),
        frame
    );
    let bytes = rmp_serde::to_vec(&frame).unwrap();
    assert_eq!(
        rmp_serde::from_slice::<ClosureLayoutDescriptor>(&bytes).unwrap(),
        frame
    );
}

#[test]
fn stored_closure_retains_target_captures_and_padding() {
    let module = fixture();
    let result = Interpreter::with_module(&module)
        .execute_func(FuncId::new(0), [])
        .unwrap();
    assert_eq!(result.host_calls, 0);
    assert_eq!(
        result.returns,
        vec![InterpretValue::int(Ty::U32, 41).unwrap()]
    );
}

#[test]
fn stored_capture_preserves_the_original_allocation_and_later_writes() {
    let mut module = fixture();
    let cid = ClosureTyId::new(0);
    let v = ValueId::new;
    let node = |inst, result| InstrNode::new(inst).with_result(v(result));
    module.closure_types[0].captures = vec![Ty::Ptr];
    module.closure_layouts[0] = ClosureLayoutDescriptor {
        origin: None,
        closure: cid,
        size: 8,
        align: 8,
        capture_offsets: vec![0],
    };
    module.func_types[1].params = vec![Ty::Ptr];
    module.functions[1].blocks[0].params = vec![(v(0), Ty::Ptr)];
    module.functions[1].blocks[0].body = vec![
        node(
            Inst::Load {
                ty: Ty::U32,
                ptr: v(0),
                volatile: false,
                align: None,
            },
            1,
        ),
        InstrNode::new(Inst::Return { values: vec![v(1)] }),
    ];
    let body = &mut module.functions[0].blocks[0].body;
    let Inst::MakeClosure { captures, .. } = &mut body[1].inst else {
        panic!()
    };
    *captures = vec![v(5)];
    body.splice(
        1..1,
        [
            node(
                Inst::Alloca {
                    ty: Ty::U32,
                    count: None,
                    align: None,
                },
                5,
            ),
            InstrNode::new(Inst::Store {
                ty: Ty::U32,
                ptr: v(5),
                value: v(0),
                volatile: false,
                align: None,
            }),
        ],
    );
    body.splice(
        6..6,
        [
            node(
                Inst::Const {
                    ty: Ty::U32,
                    value: Constant::Int(9),
                },
                6,
            ),
            InstrNode::new(Inst::Store {
                ty: Ty::U32,
                ptr: v(5),
                value: v(6),
                volatile: false,
                align: None,
            }),
        ],
    );
    let result = Interpreter::with_module(&module)
        .execute_func(FuncId::new(0), [])
        .unwrap();
    assert_eq!(result.host_calls, 0);
    assert_eq!(
        result.returns,
        vec![InterpretValue::int(Ty::U32, 9).unwrap()]
    );
}

#[test]
fn conflicting_or_missing_target_and_changed_layout_refuse_storage() {
    let mut module = fixture();
    module.functions[0].blocks[0].body.insert(
        0,
        InstrNode::new(Inst::MakeClosure {
            ty: ClosureTyId::new(0),
            func: FuncId::new(0),
            captures: vec![ValueId::new(0)],
        })
        .with_result(ValueId::new(99)),
    );
    assert_eq!(
        module
            .closure_storage_binding(ClosureTyId::new(0))
            .unwrap_err(),
        "conflicting closure storage targets"
    );
    let mut module = fixture();
    module.functions[0].blocks[0]
        .body
        .retain(|node| !matches!(node.inst, Inst::MakeClosure { .. }));
    assert!(module.closure_storage_binding(ClosureTyId::new(0)).is_err());
    let mut module = fixture();
    module.closure_layouts[0].capture_offsets[0] = 7;
    assert!(module.closure_storage_binding(ClosureTyId::new(0)).is_err());
}

#[test]
fn changed_capture_bytes_are_read_from_storage_without_changing_the_target() {
    let mut module = fixture_with_capture(Ty::Bool, Constant::Bool(true));
    let v = ValueId::new;
    let node = |inst, result| InstrNode::new(inst).with_result(v(result));
    // Corrupt an actual covered byte after the typed Store. Byte 4 is the
    // boolean capture; bytes 0..4 remain ordinary don't-care padding.
    module.functions[0].blocks[0].body.splice(
        4..4,
        [
            node(
                Inst::Const {
                    ty: Ty::U8,
                    value: Constant::Int(0),
                },
                20,
            ),
            node(
                Inst::Const {
                    ty: Ty::U64,
                    value: Constant::Int(4),
                },
                21,
            ),
            node(
                Inst::GEP {
                    pointee_ty: Ty::U8,
                    base: v(2),
                    indices: vec![v(21)],
                    inbounds: true,
                },
                22,
            ),
            InstrNode::new(Inst::Store {
                ty: Ty::U8,
                ptr: v(22),
                value: v(20),
                volatile: false,
                align: None,
            }),
        ],
    );
    let result = Interpreter::with_module(&module)
        .execute_func(FuncId::new(0), [])
        .unwrap();
    assert_eq!(result.host_calls, 0);
    assert_eq!(result.returns, vec![InterpretValue::bool(false)]);
}

#[test]
fn changing_the_unique_constructor_target_changes_the_executed_body() {
    let mut module = fixture();
    let mut alternate = module.functions[1].clone();
    alternate.id = FuncId::new(2);
    alternate.name = "alternate".into();
    alternate.blocks[0].body = vec![
        InstrNode::new(Inst::Const {
            ty: Ty::U32,
            value: Constant::Int(99),
        })
        .with_result(ValueId::new(1)),
        InstrNode::new(Inst::Return {
            values: vec![ValueId::new(1)],
        }),
    ];
    module.functions.push(alternate);
    let Inst::MakeClosure { func, .. } = &mut module.functions[0].blocks[0].body[1].inst else {
        panic!("fixture constructor");
    };
    *func = FuncId::new(2);
    let result = Interpreter::with_module(&module)
        .execute_func(FuncId::new(0), [])
        .unwrap();
    assert_eq!(result.host_calls, 0);
    assert_eq!(
        result.returns,
        vec![InterpretValue::int(Ty::U32, 99).unwrap()]
    );
}

#[test]
fn wrong_target_signature_and_duplicate_function_identity_refuse_storage() {
    let mut module = fixture();
    module.functions[1].ty = FuncTyId::new(0);
    assert!(module.closure_storage_binding(ClosureTyId::new(0)).is_err());
    let mut module = fixture();
    module.functions.push(module.functions[1].clone());
    assert!(module.closure_storage_binding(ClosureTyId::new(0)).is_err());
}
