//! Ordinary shared consumers of geometry-only possibly-uninitialized storage.
//! No native ABI, source refinement, active-field or initialization authority.
use trust_ir::interpret::{InterpretErrorCode, Interpreter};
use trust_ir::{
    CastOp, Endianness, FieldDef, FuncId, Inst, Module, StorageLayout, StructDef, StructId,
    StructPassingPolicy, StructRepr, TargetInfo, Ty,
};
use trust_ir_build::{ModuleBuilder, ValidationError, validate_module};

fn storage(size: u64, align: u64) -> Ty {
    Ty::Storage(StorageLayout::new(size, align))
}
fn target(module: &mut Module, bytes: u32) {
    module.target_info = Some(TargetInfo {
        triple: if bytes == 4 {
            "wasm32-unknown-unknown"
        } else {
            "aarch64-apple-darwin"
        }
        .into(),
        pointer_size: bytes,
        endianness: Endianness::Little,
        abi: None,
        struct_passing: StructPassingPolicy::Unclassified,
    });
}
fn raw(bytes: u32) -> (Module, FuncId) {
    let mut m = ModuleBuilder::new("storage_geometry");
    let sig = m.add_func_type(vec![], vec![Ty::U64]);
    let root = m.declare_function("root", sig);
    {
        let mut b = m.define_function(root).unwrap();
        let block = b.create_block();
        b.switch_to_block(block);
        let allocation = b.alloca(storage(160, 8));
        let one = b.uconst(Ty::Usize, 1);
        let second = b.gep(storage(80, 8), allocation, vec![one]);
        let answer = b.uconst(Ty::U64, 7);
        b.store(Ty::U64, second, answer);
        let loaded = b.load(Ty::U64, second);
        b.ret(vec![loaded]);
        b.build();
    }
    let mut module = m.build().unwrap();
    target(&mut module, bytes);
    (module, root)
}
fn run(module: &Module, root: FuncId) -> u128 {
    let errors = validate_module(module);
    assert!(errors.is_empty(), "{errors:?}");
    let result = Interpreter::with_module(module)
        .execute_func(root, [])
        .unwrap();
    assert_eq!(result.host_calls, 0);
    result.returns[0].as_int().unwrap().as_unsigned()
}
#[test]
fn fresh_storage_addresses_a_real_initialized_scalar_without_materializing_storage() {
    for bytes in [4, 8] {
        let (module, root) = raw(bytes);
        assert_eq!(run(&module, root), 7);
        assert!(!module.type_contains_storage_by_value(&Ty::PtrConst(Box::new(storage(80, 8)))));
        assert!(module.type_contains_storage_by_value(&Ty::Tuple(vec![storage(80, 8)])));
    }
}
#[test]
fn aggregate_field_has_exact_geometry_but_parent_is_not_a_value() {
    let mut m = ModuleBuilder::new("parent_with_storage");
    let parent = m.add_struct(StructDef {
        id: StructId::new(0),
        name: "parent".into(),
        fields: vec![
            FieldDef {
                name: "head".into(),
                ty: Ty::U64,
                offset: Some(0),
            },
            FieldDef {
                name: "backing".into(),
                ty: storage(80, 8),
                offset: Some(8),
            },
            FieldDef {
                name: "tail".into(),
                ty: Ty::U64,
                offset: Some(88),
            },
        ],
        size: Some(96),
        align: Some(8),
        repr: StructRepr::Rust,
        origin: None,
    });
    let sig = m.add_func_type(vec![], vec![Ty::U64]);
    let root = m.declare_function("root", sig);
    {
        let mut b = m.define_function(root).unwrap();
        let entry = b.create_block();
        b.switch_to_block(entry);
        let slot = b.alloca(Ty::Struct(parent));
        let tail = b.gep_byte_offset(slot, 88);
        let seven = b.uconst(Ty::U64, 7);
        b.store(Ty::U64, tail, seven);
        let answer = b.load(Ty::U64, tail);
        b.ret(vec![answer]);
        b.build();
    }
    let mut module = m.build().unwrap();
    target(&mut module, 8);
    assert_eq!(
        module
            .ty_layout_shape(&Ty::Struct(parent))
            .unwrap()
            .size_bits,
        768
    );
    assert_eq!(run(&module, root), 7);
    assert_eq!(module.struct_field_offset_bits(parent, 2).unwrap(), 704);
    module.func_types[0].params.push(Ty::Struct(parent));
    assert!(
        validate_module(&module)
            .iter()
            .any(|e| matches!(e, ValidationError::InvalidStorageUse { .. }))
    );
}
#[test]
fn no_typed_load_store_copy_or_constant_can_turn_storage_into_a_value() {
    for operation in [0, 1, 2, 3] {
        let (mut module, root) = raw(8);
        let block = &mut module.functions[root.as_usize()].blocks[0];
        let node = block
            .body
            .iter_mut()
            .find(|n| matches!(n.inst, Inst::Load { .. }))
            .unwrap();
        let ptr = match node.inst {
            Inst::Load { ptr, .. } => ptr,
            _ => unreachable!(),
        };
        node.inst = match operation {
            0 => Inst::Load {
                ty: storage(80, 8),
                ptr,
                volatile: false,
                align: None,
            },
            1 => Inst::Store {
                ty: storage(80, 8),
                ptr,
                value: ptr,
                volatile: false,
                align: None,
            },
            2 => Inst::Copy {
                ty: storage(80, 8),
                operand: ptr,
            },
            _ => Inst::Const {
                ty: storage(80, 8),
                value: trust_ir::constant::Constant::Bytes {
                    data: vec![0; 80],
                    utf8: false,
                },
            },
        };
        assert!(
            validate_module(&module)
                .iter()
                .any(|e| matches!(e, ValidationError::InvalidStorageUse { .. }))
        );
        assert_eq!(
            Interpreter::with_module(&module)
                .execute_func(root, [])
                .unwrap_err()
                .code,
            InterpretErrorCode::TypeError
        );
    }
}
#[test]
fn unused_abi_is_refused_and_pointer_pointees_are_distinct() {
    let (mut module, root) = raw(8);
    module
        .add_func_type(trust_ir::FuncTy::unrecorded(
            vec![storage(80, 8)],
            vec![],
            false,
        ))
        .unwrap();
    assert!(module.first_storage_violation().is_some());
    assert!(
        Interpreter::with_module(&module)
            .execute_func(root, [])
            .is_err()
    );
    let (mut clean, _) = raw(8);
    clean
        .add_func_type(trust_ir::FuncTy::unrecorded(
            vec![Ty::PtrConst(Box::new(storage(80, 8)))],
            vec![],
            false,
        ))
        .unwrap();
    assert!(clean.first_storage_violation().is_none());
    for ty in [storage(8, 8), Ty::Tuple(vec![storage(8, 8)])] {
        assert!(
            clean
                .layout_sensitive_cast_evidence(CastOp::Bitcast, &ty, &Ty::U64)
                .is_err()
        );
    }
}
#[test]
fn malformed_target_geometry_never_allocates_or_supplies_layout() {
    for (size, align) in [(80, 0), (80, 3), (79, 8), (u64::MAX, 1), (0, u64::MAX)] {
        let (mut module, root) = raw(8);
        let node = module.functions[root.as_usize()].blocks[0]
            .body
            .iter_mut()
            .find(|n| matches!(n.inst, Inst::Alloca { .. }))
            .unwrap();
        if let Inst::Alloca { ty, .. } = &mut node.inst {
            *ty = storage(size, align)
        }
        assert!(module.ty_layout_shape(&storage(size, align)).is_err());
        assert!(matches!(
            trust_ir::binary::serialize_module(&module),
            Err(trust_ir::binary::BinaryProjectionError::InvalidStorageGeometry(_))
        ));
        assert!(module.first_storage_violation().is_some());
        assert!(
            Interpreter::with_module(&module)
                .execute_func(root, [])
                .is_err()
        );
    }
    let (mut module, _) = raw(4);
    module.types.push(storage(1_u64 << 32, 8));
    assert!(module.first_storage_violation().is_some());
}

#[test]
fn storage_wire_identity_roundtrips_without_reusing_an_old_version() {
    let (module, root) = raw(8);
    let bytes = trust_ir::binary::serialize_module(&module).unwrap();
    assert_eq!(u32::from_le_bytes(bytes[8..12].try_into().unwrap()), 64);
    let recovered = trust_ir::binary::deserialize_module(&bytes).unwrap();
    assert_eq!(run(&recovered, root), 7);
    assert_eq!(
        trust_ir::binary::serialize_module(&recovered).unwrap(),
        bytes
    );
    let mut old_header = bytes.clone();
    old_header[8..12].copy_from_slice(&63_u32.to_le_bytes());
    assert!(trust_ir::binary::deserialize_module(&old_header).is_err());
    let a = storage(80, 8);
    let b = storage(88, 8);
    let c = storage(80, 16);
    assert_ne!(a, b);
    assert_ne!(a, c);
}

#[test]
fn storage_geometry_does_not_grant_initialized_bytes_or_extend_bounds() {
    let (mut uninitialized, root) = raw(8);
    let body = &mut uninitialized.functions[root.as_usize()].blocks[0].body;
    body.retain(|node| !matches!(node.inst, Inst::Store { .. }));
    let read = body
        .iter_mut()
        .find(|node| matches!(node.inst, Inst::Load { .. }))
        .unwrap();
    if let Inst::Load { volatile, .. } = &mut read.inst {
        *volatile = true;
    }
    assert!(validate_module(&uninitialized).is_empty());
    assert_eq!(
        Interpreter::with_module(&uninitialized)
            .execute_func(root, [])
            .unwrap_err()
            .code,
        InterpretErrorCode::UndefinedBehavior
    );

    let (mut out_of_bounds, root) = raw(8);
    let body = &mut out_of_bounds.functions[root.as_usize()].blocks[0].body;
    let one = body
        .iter_mut()
        .find(|node| matches!(node.inst, Inst::Const { ty: Ty::Usize, .. }))
        .unwrap();
    if let Inst::Const { value, .. } = &mut one.inst {
        *value = trust_ir::constant::Constant::Int(2);
    }
    assert!(validate_module(&out_of_bounds).is_empty());
    assert_eq!(
        Interpreter::with_module(&out_of_bounds)
            .execute_func(root, [])
            .unwrap_err()
            .code,
        InterpretErrorCode::UndefinedBehavior
    );
}
