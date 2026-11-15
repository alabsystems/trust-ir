//! Storage must preserve nominal target/layout identity through ordinary merge.
use trust_ir::interpret::{InterpretValue, Interpreter};
use trust_ir::{
    Block, BlockId, CallingConv, ClosureLayoutDescriptor, ClosureTy, ClosureTyId, Constant,
    Endianness, FuncId, FuncTy, FuncTyId, Function, Inst, InstrNode, Module, StructPassingPolicy,
    TargetInfo, Ty, ValueId,
};
use trust_ir_build::merge::{MergePolicy, merge_into};

fn fixture(caller_name: &str, target_name: &str, alternate: bool) -> Module {
    let mut module = Module::new(caller_name);
    let closure = ClosureTyId::new(0);
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
            returns: vec![Ty::U32],
            is_vararg: false,
            abi: None,
        },
        FuncTy {
            params: vec![Ty::U32],
            returns: vec![Ty::U32],
            is_vararg: false,
            abi: None,
        },
    ];
    module.closure_types = vec![ClosureTy {
        func: FuncTyId::new(0),
        captures: vec![Ty::U32],
    }];
    module.closure_layouts = vec![ClosureLayoutDescriptor {
        origin: None,
        closure,
        size: 4,
        align: 4,
        capture_offsets: vec![0],
    }];
    let v = ValueId::new;
    let node = |inst, result| InstrNode::new(inst).with_result(v(result));
    let mut body = Function::new(
        FuncId::new(1),
        target_name,
        FuncTyId::new(1),
        BlockId::new(0),
    );
    body.blocks = vec![Block::new(BlockId::new(0)).with_param(v(0), Ty::U32)];
    if alternate {
        body.blocks[0].body.push(node(
            Inst::Const {
                ty: Ty::U32,
                value: Constant::Int(99),
            },
            1,
        ));
    }
    body.blocks[0].body.push(InstrNode::new(Inst::Return {
        values: vec![v(u32::from(alternate))],
    }));
    let mut caller = Function::new(
        FuncId::new(0),
        caller_name,
        FuncTyId::new(0),
        BlockId::new(0),
    );
    caller.blocks = vec![Block::new(BlockId::new(0))];
    caller.blocks[0].body = vec![
        node(
            Inst::Const {
                ty: Ty::U32,
                value: Constant::Int(41),
            },
            0,
        ),
        node(
            Inst::MakeClosure {
                ty: closure,
                func: body.id,
                captures: vec![v(0)],
            },
            1,
        ),
        node(
            Inst::Alloca {
                ty: Ty::Closure(closure),
                count: None,
                align: None,
            },
            2,
        ),
        InstrNode::new(Inst::Store {
            ty: Ty::Closure(closure),
            ptr: v(2),
            value: v(1),
            volatile: false,
            align: None,
        }),
        node(
            Inst::Load {
                ty: Ty::Closure(closure),
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
fn equal_capture_shapes_do_not_merge_distinct_stored_targets() {
    let mut first = fixture("caller_a", "body_a", false);
    let second = fixture("caller_b", "body_b", true);
    let remap = merge_into(&mut first, &second, &MergePolicy::EXECUTION_IMAGE).unwrap();
    assert_ne!(
        remap.closure(ClosureTyId::new(0)),
        Some(ClosureTyId::new(0))
    );
    for (name, expected) in [("caller_a", 41), ("caller_b", 99)] {
        let caller = first.function_by_name(name).unwrap();
        let result = Interpreter::with_module(&first)
            .execute_func(caller.id, [])
            .unwrap();
        assert_eq!(result.host_calls, 0);
        assert_eq!(
            result.returns,
            vec![InterpretValue::int(Ty::U32, expected).unwrap()]
        );
    }
}

#[test]
fn identical_stored_target_and_layout_keep_existing_interning() {
    let mut first = fixture("caller_a", "shared_body", false);
    let second = fixture("caller_b", "shared_body", false);
    first.closure_storage_binding(ClosureTyId::new(0)).unwrap();
    second.closure_storage_binding(ClosureTyId::new(0)).unwrap();
    let remap = merge_into(&mut first, &second, &MergePolicy::EXECUTION_IMAGE).unwrap();
    // Arena rows retain append-only slots even when references intern to an
    // existing row. Assert the actual source-to-destination binding.
    assert_eq!(
        remap.closure(ClosureTyId::new(0)),
        Some(ClosureTyId::new(0))
    );
    let caller = first.function_by_name("caller_b").unwrap();
    let result = Interpreter::with_module(&first)
        .execute_func(caller.id, [])
        .unwrap();
    assert_eq!(
        result.returns,
        vec![InterpretValue::int(Ty::U32, 41).unwrap()]
    );
}

#[test]
fn distinct_nominal_origins_remain_distinct_even_with_one_target_and_frame() {
    let mut first = fixture("caller_a", "shared_body", false);
    let mut second = fixture("caller_b", "shared_body", false);
    for (module, name) in [
        (&mut first, "First.Closure"),
        (&mut second, "Second.Closure"),
    ] {
        module.closure_layouts[0].origin = Some(trust_ir::ty::TypeOrigin::Clean {
            decl: name.into(),
            env_digest: trust_ir::proof::ProofDigest::sha256([7; 32]),
        });
    }
    let remap = merge_into(&mut first, &second, &MergePolicy::EXECUTION_IMAGE).unwrap();
    assert_ne!(
        remap.closure(ClosureTyId::new(0)),
        Some(ClosureTyId::new(0))
    );
    assert_ne!(
        first.closure_layouts[0].origin,
        first.closure_layouts[1].origin
    );
}
