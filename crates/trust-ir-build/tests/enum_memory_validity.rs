// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! A well-formed module can create an invalid enum image through raw bytes.
//! Its load is runtime UB, independently of whether inactive bytes are initialized.

use trust_ir::interpret::{InterpretErrorCode, InterpretValue, InterpretValueKind, Interpreter};
use trust_ir::ty::{
    EnumLayoutDescriptor, EnumTagEncoding, EnumTagRepr, FieldStorageLayout,
    UninhabitedVariantLayout,
};
use trust_ir::{
    Block, BlockId, Constant, EnumDef, EnumId, EnumVariant, FuncId, FuncTy, Function, Inst,
    InstrNode, Module, Ty, ValueId,
};
use trust_ir_build::{validate::ValidationError, validate_module};

const ENUM: EnumId = EnumId::new(7);

fn value(id: u32) -> ValueId {
    ValueId::new(id)
}

fn result(inst: Inst, id: u32) -> InstrNode {
    InstrNode::new(inst).with_result(value(id))
}

fn constant(ty: Ty, number: i128, id: u32) -> InstrNode {
    result(
        Inst::Const {
            ty,
            value: Constant::Int(number),
        },
        id,
    )
}

/// Geometry from the physical byte-model producer's reserved-tag control:
/// U8 tag at 16, live U32 at 4, dead Never reserving eight bytes at 8.
fn raw_enum_load(tag: u8, initialize_all: bool) -> Module {
    let mut module = Module::new("enum_memory_validity");
    let mut definition = EnumDef::new(
        ENUM,
        "Physical",
        vec![
            EnumVariant {
                name: "Live".into(),
                fields: vec![Ty::U32],
                field_names: vec![],
            },
            EnumVariant {
                name: "Dead".into(),
                fields: vec![Ty::Never],
                field_names: vec![],
            },
        ],
    )
    .with_repr(EnumTagRepr::U8)
    .with_discriminants(vec![Some(3), Some(19)]);
    definition.layout = Some(EnumLayoutDescriptor {
        encoding: EnumTagEncoding::DirectWithUninhabited {
            tag_offset: 16,
            variants: vec![UninhabitedVariantLayout {
                variant: 1,
                size: 32,
                align: 8,
                fields: vec![FieldStorageLayout { size: 8, align: 8 }],
            }],
        },
        size: 32,
        align: 8,
        variant_field_offsets: vec![vec![4], vec![8]],
    });
    module.add_enum(definition);
    let signature = module
        .add_func_type(FuncTy::unrecorded(vec![], vec![Ty::Enum(ENUM)], false))
        .unwrap();
    let mut function = Function::new(FuncId::new(0), "load", signature, BlockId::new(0));
    let mut block = Block::new(BlockId::new(0));
    block.body.push(result(
        Inst::Alloca {
            ty: Ty::Enum(ENUM),
            count: None,
            align: None,
        },
        0,
    ));
    if initialize_all {
        block.body.push(constant(Ty::U8, 0, 1));
        block.body.push(constant(Ty::U64, 32, 2));
        block.body.push(InstrNode::new(Inst::MemSet {
            dst: value(0),
            byte: value(1),
            bytes: value(2),
        }));
    }
    block.body.push(constant(Ty::U64, 16, 3));
    block.body.push(result(
        Inst::GEP {
            pointee_ty: Ty::U8,
            base: value(0),
            indices: vec![value(3)],
            inbounds: false,
        },
        4,
    ));
    block.body.push(constant(Ty::U8, i128::from(tag), 5));
    block.body.push(InstrNode::new(Inst::Store {
        ty: Ty::U8,
        ptr: value(4),
        value: value(5),
        volatile: false,
        align: None,
    }));
    block.body.push(result(
        Inst::Load {
            ty: Ty::Enum(ENUM),
            ptr: value(0),
            volatile: false,
            align: None,
        },
        6,
    ));
    block.body.push(InstrNode::new(Inst::Return {
        values: vec![value(6)],
    }));
    function.blocks.push(block);
    module.try_add_function(function).unwrap();
    module
}

#[test]
fn valid_module_reserved_and_unknown_memory_tags_are_ub() {
    for tag in [19, 255] {
        for initialize_all in [false, true] {
            let module = raw_enum_load(tag, initialize_all);
            assert_eq!(validate_module(&module), [], "valid raw byte program");
            let error = Interpreter::with_module(&module)
                .execute_func(FuncId::new(0), [])
                .unwrap_err();
            assert_eq!(
                error.code,
                InterpretErrorCode::UndefinedBehavior,
                "{error:?}"
            );
            assert!(
                error.message.contains(if tag == 19 {
                    "uninhabited"
                } else {
                    "does not match"
                }),
                "{error:?}"
            );
        }
    }
}

#[test]
fn live_memory_tag_still_loads_and_requires_its_payload() {
    for initialize_all in [false, true] {
        let module = raw_enum_load(3, initialize_all);
        assert_eq!(validate_module(&module), []);
        let result = Interpreter::with_module(&module).execute_func(FuncId::new(0), []);
        if initialize_all {
            let output = result.unwrap();
            assert_eq!(
                output.returns,
                vec![InterpretValue {
                    ty: Ty::Enum(ENUM),
                    kind: InterpretValueKind::Aggregate(vec![
                        InterpretValue::int(Ty::U8, 3).unwrap(),
                        InterpretValue::int(Ty::U32, 0).unwrap(),
                    ]),
                }]
            );
        } else {
            let error = result.unwrap_err();
            assert_eq!(error.code, InterpretErrorCode::UndefinedBehavior);
            assert!(error.message.contains("uninitialized"), "{error:?}");
        }
    }
}

#[test]
fn malformed_reserved_geometry_remains_a_type_error() {
    let mut module = raw_enum_load(19, true);
    let EnumTagEncoding::DirectWithUninhabited { variants, .. } =
        &mut module.enums[0].layout.as_mut().unwrap().encoding
    else {
        unreachable!()
    };
    variants[0].fields[0].align = 3;
    assert!(!validate_module(&module).is_empty());
    let error = Interpreter::with_module(&module)
        .execute_func(FuncId::new(0), [])
        .unwrap_err();
    assert_eq!(error.code, InterpretErrorCode::TypeError, "{error:?}");
}

#[test]
fn impossible_typed_constructor_remains_a_type_error() {
    let mut module = raw_enum_load(3, true);
    let load = module.functions[0].blocks[0]
        .body
        .iter_mut()
        .find(|node| matches!(node.inst, Inst::Load { .. }))
        .unwrap();
    load.inst = Inst::Const {
        ty: Ty::Enum(ENUM),
        value: Constant::Aggregate(vec![Constant::Int(19), Constant::Int(0)]),
    };
    assert!(
        validate_module(&module)
            .iter()
            .any(|error| matches!(error, ValidationError::UninhabitedVariantConstructed { .. }))
    );
    let error = Interpreter::with_module(&module)
        .execute_func(FuncId::new(0), [])
        .unwrap_err();
    assert_eq!(error.code, InterpretErrorCode::TypeError, "{error:?}");
    assert!(error.message.contains("uninhabited"), "{error:?}");
}
