// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Contract tests for scalar/vector boolean logic.
//!
//! `and`/`or`/`xor` are bitwise on integers and logical on booleans. These
//! tests keep structural validation and the reference interpreter on the same
//! contract, including the boolean comparisons that commonly feed a logical
//! operation.

use trust_ir::constant::Constant;
use trust_ir::inst::{BinOp, ICmpOp, UnOp};
use trust_ir::interpret::{InterpretValue, Interpreter};
use trust_ir::ty::Ty;
use trust_ir::{FuncId, InterpretValueKind};
use trust_ir_build::builder::ModuleBuilder;
use trust_ir_build::validate::{ValidationError, validate_module};

#[test]
fn discriminant_validity_bool_or_validates_and_executes() {
    let mut mb = ModuleBuilder::new("bool_or");
    let ft = mb.add_func_type(vec![Ty::I64], vec![Ty::Bool]);
    let mut fb = mb.function("disc_valid", ft);
    let entry = fb.create_block();
    let disc = fb.add_block_param(entry, Ty::I64);
    fb.switch_to_block(entry);

    let zero = fb.const_value(Ty::I64, Constant::Int(0));
    let one = fb.const_value(Ty::I64, Constant::Int(1));
    let is_none = fb.icmp(ICmpOp::Eq, Ty::I64, disc, zero);
    let is_some = fb.icmp(ICmpOp::Eq, Ty::I64, disc, one);
    let valid = fb.binop(BinOp::Or, Ty::Bool, is_none, is_some);
    fb.ret(vec![valid]);
    fb.build();

    let module = mb.build().expect("ModuleBuilder::build: test fixture");
    assert_eq!(validate_module(&module), []);

    for (disc, expected) in [(0, true), (1, true), (2, false)] {
        let outcome = Interpreter::with_module(&module)
            .execute_func(
                FuncId::new(0),
                [InterpretValue::int(Ty::I64, disc).unwrap()],
            )
            .expect("validated scalar-bool logic must execute");
        assert_eq!(outcome.returns[0].as_bool(), Some(expected));
    }
}

#[test]
fn scalar_bool_logic_and_comparison_execute_all_truth_tables() {
    let mut mb = ModuleBuilder::new("bool_truth_tables");
    let ft = mb.add_func_type(
        vec![Ty::Bool, Ty::Bool],
        vec![Ty::Bool, Ty::Bool, Ty::Bool, Ty::Bool],
    );
    let mut fb = mb.function("logic", ft);
    let entry = fb.create_block();
    let lhs = fb.add_block_param(entry, Ty::Bool);
    let rhs = fb.add_block_param(entry, Ty::Bool);
    fb.switch_to_block(entry);
    let and = fb.binop(BinOp::And, Ty::Bool, lhs, rhs);
    let or = fb.binop(BinOp::Or, Ty::Bool, lhs, rhs);
    let xor = fb.binop(BinOp::Xor, Ty::Bool, lhs, rhs);
    let ne = fb.icmp(ICmpOp::Ne, Ty::Bool, lhs, rhs);
    fb.ret(vec![and, or, xor, ne]);
    fb.build();

    let module = mb.build().expect("ModuleBuilder::build: test fixture");
    assert_eq!(validate_module(&module), []);

    for lhs in [false, true] {
        for rhs in [false, true] {
            let outcome = Interpreter::with_module(&module)
                .execute_func(
                    FuncId::new(0),
                    [InterpretValue::bool(lhs), InterpretValue::bool(rhs)],
                )
                .expect("validated scalar-bool truth table must execute");
            let got: Vec<bool> = outcome
                .returns
                .iter()
                .map(|value| value.as_bool().expect("bool return"))
                .collect();
            assert_eq!(got, [lhs & rhs, lhs | rhs, lhs ^ rhs, lhs != rhs]);
        }
    }
}

#[test]
fn vector_bool_logic_and_not_execute_lane_wise() {
    let v4bool = Ty::Vector(Box::new(Ty::Bool), 4);
    let mut mb = ModuleBuilder::new("bool_vector_logic");
    let ft = mb.add_func_type(
        vec![],
        vec![
            v4bool.clone(),
            v4bool.clone(),
            v4bool.clone(),
            v4bool.clone(),
        ],
    );
    let mut fb = mb.function("logic", ft);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    let lhs = fb.const_value(
        v4bool.clone(),
        Constant::v4_bool_mask([false, false, true, true]),
    );
    let rhs = fb.const_value(
        v4bool.clone(),
        Constant::v4_bool_mask([false, true, false, true]),
    );
    let and = fb.binop(BinOp::And, v4bool.clone(), lhs, rhs);
    let or = fb.binop(BinOp::Or, v4bool.clone(), lhs, rhs);
    let xor = fb.binop(BinOp::Xor, v4bool.clone(), lhs, rhs);
    let not = fb.unop(UnOp::Not, v4bool.clone(), lhs);
    fb.ret(vec![and, or, xor, not]);
    fb.build();

    let module = mb.build().expect("ModuleBuilder::build: test fixture");
    assert_eq!(validate_module(&module), []);
    let outcome = Interpreter::with_module(&module)
        .execute_func(FuncId::new(0), [])
        .expect("validated vector-bool logic must execute");

    let got: Vec<Vec<bool>> = outcome
        .returns
        .iter()
        .map(|value| match &value.kind {
            InterpretValueKind::Vector(lanes) => lanes
                .iter()
                .map(|lane| lane.as_bool().expect("bool lane"))
                .collect(),
            other => panic!("expected bool vector, got {other:?}"),
        })
        .collect();
    assert_eq!(
        got,
        [
            vec![false, false, false, true],
            vec![false, true, true, true],
            vec![false, true, true, false],
            vec![true, true, false, false],
        ]
    );
}

#[test]
fn float_logic_remains_fail_closed() {
    let mut mb = ModuleBuilder::new("float_or");
    let ft = mb.add_func_type(vec![Ty::F64, Ty::F64], vec![Ty::F64]);
    let mut fb = mb.function("f", ft);
    let entry = fb.create_block();
    let lhs = fb.add_block_param(entry, Ty::F64);
    let rhs = fb.add_block_param(entry, Ty::F64);
    fb.switch_to_block(entry);
    let result = fb.binop(BinOp::Or, Ty::F64, lhs, rhs);
    fb.ret(vec![result]);
    fb.build();

    let errors = validate_module(&mb.build().expect("ModuleBuilder::build: test fixture"));
    assert!(errors.iter().any(|error| matches!(
        error,
        ValidationError::BinOpRequiresInteger { op, ty, .. }
            if op == "or" && ty == "f64"
    )));
}
