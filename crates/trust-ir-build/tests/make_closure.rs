//! Runtime closure construction keeps live SSA captures and validates its complete target.
use trust_ir::interpret::Interpreter;
use trust_ir::{
    Block, BlockId, ClosureTy, Constant, FuncId, FuncTy, Function, Inst, InstrNode, Module, Ty,
    ValueId,
};
use trust_ir_build::{ValidationError, validate_module};
fn v(n: u32) -> ValueId {
    ValueId::new(n)
}
fn node(inst: Inst, result: u32) -> InstrNode {
    InstrNode::new(inst).with_result(v(result))
}

fn fixture() -> Module {
    let mut m = Module::new("runtime_capture");
    let app = m
        .add_func_type(FuncTy {
            params: vec![Ty::I32],
            returns: vec![Ty::Ptr],
            abi: None,
            is_vararg: false,
        })
        .unwrap();
    let physical = m
        .add_func_type(FuncTy {
            params: vec![Ty::Ptr, Ty::I32],
            returns: vec![Ty::Ptr],
            abi: None,
            is_vararg: false,
        })
        .unwrap();
    let host = m
        .add_func_type(FuncTy {
            params: vec![],
            returns: vec![Ty::I32],
            abi: None,
            is_vararg: false,
        })
        .unwrap();
    let closure = m
        .add_closure_type(ClosureTy {
            func: app,
            captures: vec![Ty::Ptr],
        })
        .unwrap();
    let mut f = Function::new(FuncId::new(0), "host", host, BlockId::new(0));
    let mut b = Block::new(BlockId::new(0));
    b.body = vec![
        node(
            Inst::Alloca {
                ty: Ty::I32,
                count: None,
                align: Some(4),
            },
            0,
        ),
        node(
            Inst::MakeClosure {
                ty: closure,
                func: FuncId::new(1),
                captures: vec![v(0)],
            },
            1,
        ),
        node(
            Inst::Const {
                ty: Ty::I32,
                value: Constant::Int(42),
            },
            2,
        ),
        node(
            Inst::CallIndirect {
                callee: v(1),
                sig: app,
                args: vec![v(2)],
                calling_conv: trust_ir::CallingConv::C,
            },
            3,
        ),
        node(
            Inst::Load {
                ty: Ty::I32,
                ptr: v(0),
                volatile: false,
                align: Some(4),
            },
            4,
        ),
        node(
            Inst::Const {
                ty: Ty::I32,
                value: Constant::Int(99),
            },
            5,
        ),
        InstrNode::new(Inst::Store {
            ty: Ty::I32,
            ptr: v(3),
            value: v(5),
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
            6,
        ),
        InstrNode::new(Inst::Return { values: vec![v(6)] }),
    ];
    f.blocks.push(b);
    m.try_add_function(f).unwrap();
    let mut f = Function::new(
        FuncId::new(1),
        "write_and_return_capture",
        physical,
        BlockId::new(0),
    );
    let mut b = Block::new(BlockId::new(0));
    b.params = vec![(v(0), Ty::Ptr), (v(1), Ty::I32)];
    b.body = vec![
        InstrNode::new(Inst::Store {
            ty: Ty::I32,
            ptr: v(0),
            value: v(1),
            volatile: false,
            align: Some(4),
        }),
        InstrNode::new(Inst::Return { values: vec![v(0)] }),
    ];
    f.blocks.push(b);
    m.try_add_function(f).unwrap();
    m
}
#[test]
fn live_pointer_capture_and_return_preserve_the_same_allocation() {
    let m = fixture();
    assert!(validate_module(&m).is_empty(), "{:?}", validate_module(&m));
    let out = Interpreter::with_module(&m)
        .execute_func(FuncId::new(0), [])
        .unwrap();
    assert_eq!(out.returns[0].as_int().unwrap().as_signed(), 99);
}
#[test]
fn construction_refuses_missing_captures_and_physical_targets() {
    for case in 0..4 {
        let mut m = fixture();
        if let Inst::MakeClosure { ty, func, captures } = &mut m.functions[0].blocks[0].body[1].inst
        {
            match case {
                0 => captures.clear(),
                1 => *func = FuncId::new(98),
                2 => *ty = trust_ir::value::ClosureTyId::new(98),
                3 => *func = FuncId::new(0),
                _ => unreachable!(),
            }
        }
        let errors = validate_module(&m);
        assert!(
            errors
                .iter()
                .any(|e| matches!(e, ValidationError::InvalidMakeClosure { .. })),
            "case {case}: {errors:?}"
        );
        assert!(
            Interpreter::with_module(&m)
                .execute_func(FuncId::new(0), [])
                .is_err(),
            "case {case}"
        );
    }
}
#[test]
fn construction_refuses_capture_operand_type_mismatch() {
    let mut m = fixture();
    // The slot becomes an i32 operand rather than an address; no implicit cast.
    m.functions[0].blocks[0].body[0] = node(
        Inst::Const {
            ty: Ty::I32,
            value: Constant::Int(0),
        },
        0,
    );
    assert!(
        validate_module(&m)
            .iter()
            .any(|e| matches!(e, ValidationError::OperandTypeMismatch { .. }))
    );
    assert!(
        Interpreter::with_module(&m)
            .execute_func(FuncId::new(0), [])
            .is_err()
    );
}
#[cfg(all(feature = "binary", feature = "serde"))]
#[test]
fn construction_survives_wire_transports_and_requires_its_wire_version() {
    let m = fixture();
    let bytes = trust_ir::binary::serialize_module(&m).unwrap();
    let (back, version) = trust_ir::binary::deserialize_module_with_wire_version(&bytes).unwrap();
    assert_eq!(version.get(), trust_ir::binary::MAKE_CLOSURE_FORMAT_VERSION);
    assert_eq!(back, m);
    let mut old_header = bytes.clone();
    old_header[8..12].copy_from_slice(&62u32.to_le_bytes());
    assert!(trust_ir::binary::deserialize_module(&old_header).is_err());
    let json = serde_json::to_vec(&m).unwrap();
    assert_eq!(serde_json::from_slice::<Module>(&json).unwrap(), m);
    let mp = rmp_serde::to_vec(&m).unwrap();
    assert_eq!(rmp_serde::from_slice::<Module>(&mp).unwrap(), m);
    let text = trust_ir::format::canonical(&m);
    let back = trust_ir::parser::parse_module(&text).unwrap();
    assert!(trust_ir::diff::diff(&m, &back).is_empty());
    assert_eq!(
        Interpreter::with_module(&back)
            .execute_func(FuncId::new(0), [])
            .unwrap()
            .returns[0]
            .as_int()
            .unwrap()
            .as_signed(),
        99
    );
}

#[test]
fn module_merge_remaps_both_constructor_type_and_function() {
    let src = fixture();
    let mut dst = Module::new("destination");
    let sig = dst
        .add_func_type(FuncTy {
            params: vec![],
            returns: vec![],
            abi: None,
            is_vararg: false,
        })
        .unwrap();
    dst.add_closure_type(ClosureTy {
        func: sig,
        captures: vec![Ty::Bool],
    })
    .unwrap();
    let mut reserved = Function::new(FuncId::new(0), "reserved", sig, BlockId::new(0));
    let mut block = Block::new(BlockId::new(0));
    block
        .body
        .push(InstrNode::new(Inst::Return { values: vec![] }));
    reserved.blocks.push(block);
    dst.try_add_function(reserved).unwrap();
    let remap = trust_ir_build::merge_into(
        &mut dst,
        &src,
        &trust_ir_build::MergePolicy::VERIFICATION_IMAGE,
    )
    .unwrap();
    let host = remap.func(FuncId::new(0)).unwrap();
    let target = remap.func(FuncId::new(1)).unwrap();
    let closure = remap.closure(trust_ir::value::ClosureTyId::new(0)).unwrap();
    assert_ne!(host, FuncId::new(0));
    assert_ne!(closure, trust_ir::value::ClosureTyId::new(0));
    assert!(
        matches!(dst.function_by_id(host).unwrap().blocks[0].body[1].inst,
        Inst::MakeClosure { ty, func, .. } if ty == closure && func == target)
    );
    assert!(
        validate_module(&dst).is_empty(),
        "{:?}",
        validate_module(&dst)
    );
    assert_eq!(
        Interpreter::with_module(&dst)
            .execute_func(host, [])
            .unwrap()
            .returns[0]
            .as_int()
            .unwrap()
            .as_signed(),
        99
    );
}
