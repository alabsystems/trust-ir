// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Crystal lane (E3b): the validator's PLACEMENT rule for `Constant::Uninit`, an unwritten
//! struct/tuple lane. It is admitted as a direct lane of an `Inst::Const` struct or tuple
//! aggregate, at any lane type, and refused as a whole constant, nested one aggregate deeper,
//! under any other aggregate kind, in a global initializer and in a switch case.

use trust_ir::ty::{FieldDef, StructDef};
use trust_ir::value::StructId;
use trust_ir::{
    Block, BlockId, Constant, FuncId, FuncTy, Function, Global, Inst, InstrNode, Linkage, Module,
    Ty, ValueId,
};
use trust_ir_build::{ValidationError, validate_module};

/// `Option<u64>` laid out as the Trust bridge lays out a flat enum: `{ isize, u64 }`.
fn with_option_struct(module: &mut Module) -> Ty {
    module.add_struct(StructDef {
        id: StructId::new(0),
        name: "core::option::Option".into(),
        fields: vec![
            FieldDef {
                name: "tag".into(),
                ty: Ty::Isize,
                offset: None,
            },
            FieldDef {
                name: "payload".into(),
                ty: Ty::U64,
                offset: None,
            },
        ],
        size: None,
        align: None,
        repr: Default::default(),
        origin: None,
    });
    Ty::Struct(StructId::new(0))
}

/// One function: `%0 = const <ty> <value>; ret %0`.
fn const_module(ty: impl FnOnce(&mut Module) -> Ty, value: Constant) -> Module {
    let mut module = Module::new("uninit_lanes");
    let ty = ty(&mut module);
    let signature = module
        .add_func_type(FuncTy {
            params: vec![],
            returns: vec![ty.clone()],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut function = Function::new(FuncId::new(0), "seed", signature, BlockId::new(0));
    let mut entry = Block::new(BlockId::new(0));
    entry
        .body
        .push(InstrNode::new(Inst::Const { ty, value }).with_result(ValueId::new(0)));
    entry.body.push(InstrNode::new(Inst::Return {
        values: vec![ValueId::new(0)],
    }));
    function.blocks.push(entry);
    module
        .try_add_function(function)
        .expect("Module::try_add_function: test fixture");
    module
}

fn placement_errors(module: &Module) -> Vec<ValidationError> {
    validate_module(module)
        .into_iter()
        .filter(|e| {
            matches!(e, ValidationError::ConstTypeMismatch { expected, .. }
            if expected.contains("uninit"))
        })
        .collect()
}

#[test]
fn a_direct_lane_of_a_struct_or_tuple_constant_is_admitted_at_any_lane_type() {
    let none = const_module(
        with_option_struct,
        Constant::Aggregate(vec![Constant::Int(0), Constant::Uninit]),
    );
    assert_eq!(
        validate_module(&none),
        vec![],
        "the None seed is a valid module"
    );
    let every_lane = const_module(
        with_option_struct,
        Constant::Aggregate(vec![Constant::Uninit, Constant::Uninit]),
    );
    assert_eq!(validate_module(&every_lane), vec![]);
    let tuple = const_module(
        |_| Ty::Tuple(vec![Ty::Ptr, Ty::Bool, Ty::F64]),
        Constant::Aggregate(vec![
            Constant::Uninit,
            Constant::Bool(true),
            Constant::Uninit,
        ]),
    );
    assert_eq!(validate_module(&tuple), vec![]);
}

#[test]
fn a_whole_uninit_constant_is_refused() {
    let whole = const_module(|_| Ty::U64, Constant::Uninit);
    assert_eq!(
        placement_errors(&whole).len(),
        1,
        "{:?}",
        validate_module(&whole)
    );
    let whole_struct = const_module(with_option_struct, Constant::Uninit);
    assert_eq!(placement_errors(&whole_struct).len(), 1);
}

#[test]
fn an_uninit_one_aggregate_deeper_is_refused() {
    let nested = const_module(
        |m| Ty::Tuple(vec![with_option_struct(m), Ty::U64]),
        Constant::Aggregate(vec![
            Constant::Aggregate(vec![Constant::Int(0), Constant::Uninit]),
            Constant::Int(1),
        ]),
    );
    assert_eq!(
        placement_errors(&nested).len(),
        1,
        "{:?}",
        validate_module(&nested)
    );
}

#[test]
fn an_uninit_under_any_other_aggregate_kind_is_refused() {
    let vector = const_module(
        |_| Ty::Vector(Box::new(Ty::I32), 4),
        Constant::Vector(vec![
            Constant::Int(0),
            Constant::Uninit,
            Constant::Int(0),
            Constant::Int(0),
        ]),
    );
    assert_eq!(
        placement_errors(&vector).len(),
        1,
        "{:?}",
        validate_module(&vector)
    );
}

#[test]
fn an_uninit_in_a_global_initializer_is_refused() {
    let mut module = Module::new("uninit_global");
    let ty = with_option_struct(&mut module);
    module.globals.push(Global {
        name: "none".into(),
        ty,
        mutable: false,
        initializer: Some(Constant::Aggregate(vec![
            Constant::Int(0),
            Constant::Uninit,
        ])),
        linkage: Linkage::Internal,
        tls: None,
        align: None,
        section: None,
        visibility: Default::default(),
        retained: false,
    });
    assert_eq!(
        placement_errors(&module).len(),
        1,
        "{:?}",
        validate_module(&module)
    );
}
