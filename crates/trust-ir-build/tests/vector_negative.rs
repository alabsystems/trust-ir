// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use trust_ir::Global;
use trust_ir::constant::Constant;
use trust_ir::inst::ICmpOp;
use trust_ir::ty::Ty;
use trust_ir_build::builder::ModuleBuilder;
use trust_ir_build::validate::{ValidationError, validate_module};

#[test]
fn validate_rejects_vector_select_scalar_bool_condition() {
    let mut mb = ModuleBuilder::new("bad_select");
    let v4i32 = Ty::v4_i32();
    let ft = mb.add_func_type(
        vec![Ty::Bool, v4i32.clone(), v4i32.clone()],
        vec![v4i32.clone()],
    );
    let mut fb = mb.function("test", ft);
    let entry = fb.create_block();
    let cond = fb.add_block_param(entry, Ty::Bool);
    let then_val = fb.add_block_param(entry, v4i32.clone());
    let else_val = fb.add_block_param(entry, v4i32.clone());
    fb.switch_to_block(entry);

    let selected = fb.select(v4i32, cond, then_val, else_val);
    fb.ret(vec![selected]);
    fb.build();

    let module = mb.build();
    let errors = validate_module(&module);
    assert!(
        errors.iter().any(|e| matches!(
            e,
            ValidationError::SelectConditionTypeMismatch { expected, actual, .. }
                if expected == "<4 x bool>" && actual == "bool"
        )),
        "expected scalar bool select rejection, got {errors:?}"
    );
}

#[test]
fn validate_rejects_vector_select_mismatched_lane_counts() {
    let mut mb = ModuleBuilder::new("bad_select");
    let v4i32 = Ty::v4_i32();
    let v2bool = Ty::v2_bool();
    let ft = mb.add_func_type(
        vec![v2bool.clone(), v4i32.clone(), v4i32.clone()],
        vec![v4i32.clone()],
    );
    let mut fb = mb.function("test", ft);
    let entry = fb.create_block();
    let cond = fb.add_block_param(entry, v2bool);
    let then_val = fb.add_block_param(entry, v4i32.clone());
    let else_val = fb.add_block_param(entry, v4i32.clone());
    fb.switch_to_block(entry);

    let selected = fb.select(v4i32, cond, then_val, else_val);
    fb.ret(vec![selected]);
    fb.build();

    let module = mb.build();
    let errors = validate_module(&module);
    assert!(
        errors.iter().any(|e| matches!(
            e,
            ValidationError::SelectConditionTypeMismatch { expected, actual, .. }
                if expected == "<4 x bool>" && actual == "<2 x bool>"
        )),
        "expected mismatched lane count select rejection, got {errors:?}"
    );
}

#[test]
fn validate_rejects_icmp_result_mismatch() {
    let mut mb = ModuleBuilder::new("bad_icmp");
    let v4i32 = Ty::v4_i32();
    let ft = mb.add_func_type(vec![v4i32.clone(), v4i32.clone()], vec![Ty::Bool]);
    let mut fb = mb.function("test", ft);
    let entry = fb.create_block();
    let lhs = fb.add_block_param(entry, v4i32.clone());
    let rhs = fb.add_block_param(entry, v4i32);
    fb.switch_to_block(entry);

    // ICmp over <4 x i32> must use <4 x i32> as instruction type,
    // which then implies <4 x bool> result.
    // If we use 'bool' as instruction type, it means we are comparing two bools.
    // Since operands are <4 x i32>, it will fail operand type check.
    let cmp = fb.icmp(ICmpOp::Eq, Ty::Bool, lhs, rhs);
    fb.ret(vec![cmp]);
    fb.build();

    let module = mb.build();
    let errors = validate_module(&module);
    assert!(
        errors.iter().any(|e| matches!(
            e,
            ValidationError::OperandTypeMismatch { op, expected, actual, .. }
                if op == "icmp" && actual == "<4 x i32>" && expected == "bool"
        )),
        "expected icmp operand mismatch rejection, got {errors:?}"
    );
}

#[test]
fn validate_rejects_vector_binop_mismatched_lanes() {
    let mut mb = ModuleBuilder::new("bad_binop");
    let v4i32 = Ty::v4_i32();
    let v2i32 = Ty::Vector(Box::new(Ty::I32), 2);
    let ft = mb.add_func_type(vec![v4i32.clone(), v2i32.clone()], vec![v4i32.clone()]);
    let mut fb = mb.function("test", ft);
    let entry = fb.create_block();
    let lhs = fb.add_block_param(entry, v4i32.clone());
    let rhs = fb.add_block_param(entry, v2i32);
    fb.switch_to_block(entry);

    let add = fb.add(v4i32, lhs, rhs);
    fb.ret(vec![add]);
    fb.build();

    let module = mb.build();
    let errors = validate_module(&module);
    assert!(
        errors.iter().any(|e| matches!(
            e,
            ValidationError::OperandTypeMismatch { op, expected, actual, .. }
                if op == "add" && actual == "<2 x i32>" && expected == "<4 x i32>"
        )),
        "expected binop lane mismatch rejection, got {errors:?}"
    );
}

#[test]
fn validate_rejects_malformed_extract_element() {
    let mut mb = ModuleBuilder::new("bad_extract");
    let v4i32 = Ty::v4_i32();
    let ft = mb.add_func_type(vec![v4i32.clone(), Ty::I32], vec![v4i32.clone()]);
    let mut fb = mb.function("test", ft);
    let entry = fb.create_block();
    let vec_val = fb.add_block_param(entry, v4i32);
    let index = fb.add_block_param(entry, Ty::I32);
    fb.switch_to_block(entry);

    // Extract result must be scalar element type, not vector
    let extract = fb.extract_element(Ty::Vector(Box::new(Ty::I32), 4), vec_val, index);
    fb.ret(vec![extract]);
    fb.build();

    let module = mb.build();
    let errors = validate_module(&module);
    assert!(
        errors.iter().any(|e| matches!(
            e,
            ValidationError::InvalidVectorElementOp { op, reason, .. }
                if op == "extract_element" && reason.contains("result type must match vector lane type i32, got <4 x i32>")
        )),
        "expected extract result mismatch rejection, got {errors:?}"
    );
}

#[test]
fn validate_rejects_extract_element_non_integer_index() {
    let mut mb = ModuleBuilder::new("bad_extract_index");
    let v4i32 = Ty::v4_i32();
    let ft = mb.add_func_type(vec![v4i32.clone(), Ty::Bool], vec![Ty::I32]);
    let mut fb = mb.function("test", ft);
    let entry = fb.create_block();
    let vec_val = fb.add_block_param(entry, v4i32);
    let index = fb.add_block_param(entry, Ty::Bool);
    fb.switch_to_block(entry);

    let extract = fb.extract_element(Ty::I32, vec_val, index);
    fb.ret(vec![extract]);
    fb.build();

    let module = mb.build();
    let errors = validate_module(&module);
    assert!(
        errors.iter().any(|e| matches!(
            e,
            ValidationError::InvalidVectorElementOp { op, reason, .. }
                if op == "extract_element" && reason.contains("index must be integer, got bool")
        )),
        "expected extract non-integer index rejection, got {errors:?}"
    );
}

#[test]
fn validate_rejects_extract_element_out_of_range_constant() {
    let mut mb = ModuleBuilder::new("bad_extract_range");
    let v4i32 = Ty::v4_i32();
    let ft = mb.add_func_type(vec![v4i32.clone()], vec![Ty::I32]);
    let mut fb = mb.function("test", ft);
    let entry = fb.create_block();
    let vec_val = fb.add_block_param(entry, v4i32);
    fb.switch_to_block(entry);

    let index = fb.iconst(Ty::I32, 4);
    let extract = fb.extract_element(Ty::I32, vec_val, index);
    fb.ret(vec![extract]);
    fb.build();

    let module = mb.build();
    let errors = validate_module(&module);
    assert!(
        errors.iter().any(|e| matches!(
            e,
            ValidationError::InvalidVectorElementOp { op, reason, .. }
                if op == "extract_element" && reason.contains("constant lane index 4 is out of range for 4 lanes")
        )),
        "expected extract out of range rejection, got {errors:?}"
    );
}

#[test]
fn validate_rejects_insert_element_scalar_mismatch() {
    let mut mb = ModuleBuilder::new("bad_insert");
    let v4i32 = Ty::v4_i32();
    let ft = mb.add_func_type(vec![v4i32.clone(), Ty::I64, Ty::I32], vec![v4i32.clone()]);
    let mut fb = mb.function("test", ft);
    let entry = fb.create_block();
    let vec_val = fb.add_block_param(entry, v4i32.clone());
    let val_to_insert = fb.add_block_param(entry, Ty::I64);
    let index = fb.add_block_param(entry, Ty::I32);
    fb.switch_to_block(entry);

    let insert = fb.insert_element(v4i32, vec_val, index, val_to_insert);
    fb.ret(vec![insert]);
    fb.build();

    let module = mb.build();
    let errors = validate_module(&module);
    assert!(
        errors.iter().any(|e| matches!(
            e,
            ValidationError::InvalidVectorElementOp { op, reason, .. }
                if op == "insert_element" && reason.contains("inserted value must match vector lane type i32, got i64")
        )),
        "expected insert scalar mismatch rejection, got {errors:?}"
    );
}

#[test]
fn validate_rejects_zero_lane_vector() {
    let mut mb = ModuleBuilder::new("zero_lanes");
    let v0i32 = Ty::Vector(Box::new(Ty::I32), 0);
    mb.add_global(trust_ir::Global {
        name: "BAD_VEC".to_string(),
        ty: v0i32,
        mutable: false,
        initializer: None,
        linkage: trust_ir::Linkage::Internal,
        tls: None,
        align: None,
    });

    let module = mb.build();
    let errors = validate_module(&module);
    assert!(
        errors.iter().any(|e| matches!(
            e,
            ValidationError::InvalidModuleVectorType { reason, .. }
                if reason == "lane count must be nonzero"
        )),
        "expected zero-lane rejection, got {errors:?}"
    );
}

#[test]
fn validate_rejects_nested_vector() {
    let mut mb = ModuleBuilder::new("nested_vec");
    let nested = Ty::Vector(Box::new(Ty::Vector(Box::new(Ty::I32), 4)), 2);
    mb.add_global(trust_ir::Global {
        name: "BAD_NESTED".to_string(),
        ty: nested,
        mutable: false,
        initializer: None,
        linkage: trust_ir::Linkage::Internal,
        tls: None,
        align: None,
    });

    let module = mb.build();
    let errors = validate_module(&module);
    assert!(
        errors.iter().any(|e| matches!(
            e,
            ValidationError::InvalidModuleVectorType { reason, .. }
                if reason == "nested vector lanes are not supported"
        )),
        "expected nested vector rejection, got {errors:?}"
    );
}

#[test]
fn validate_rejects_vector_constant_wrong_lane_count() {
    let mut mb = ModuleBuilder::new("bad_const");
    let v4i32 = Ty::v4_i32();

    // Constant with 3 lanes instead of 4
    mb.add_global(Global {
        name: "BAD_CONST".to_string(),
        ty: v4i32,
        mutable: false,
        initializer: Some(Constant::Vector(vec![
            Constant::Int(1),
            Constant::Int(2),
            Constant::Int(3),
        ])),
        linkage: trust_ir::Linkage::Internal,
        tls: None,
        align: None,
    });

    let module = mb.build();
    let errors = validate_module(&module);
    assert!(
        errors.iter().any(|e| matches!(
            e,
            ValidationError::ConstTypeMismatch { location, expected, actual }
                if location == "global 'BAD_CONST'" && expected == "<4 x i32>" && actual == "vector[3]"
        )),
        "expected vector constant lane count mismatch rejection, got {errors:?}"
    );
}

#[test]
fn validate_rejects_vector_constant_array_payload() {
    let mut mb = ModuleBuilder::new("bad_const_array");
    let v4i32 = Ty::v4_i32();

    // Using Constant::Array instead of Constant::Vector
    mb.add_global(Global {
        name: "BAD_ARRAY".to_string(),
        ty: v4i32,
        mutable: false,
        initializer: Some(Constant::Array(vec![
            Constant::Int(1),
            Constant::Int(2),
            Constant::Int(3),
            Constant::Int(4),
        ])),
        linkage: trust_ir::Linkage::Internal,
        tls: None,
        align: None,
    });

    let module = mb.build();
    let errors = validate_module(&module);
    assert!(
        errors.iter().any(|e| matches!(
            e,
            ValidationError::ConstTypeMismatch { location, expected, actual }
                if location == "global 'BAD_ARRAY'" && expected == "<4 x i32>" && actual == "array[4]"
        )),
        "expected vector constant array payload rejection, got {errors:?}"
    );
}

/// audit #12: a malformed GPU-dialect op (not the vector dialect) must now be
/// caught by `validate_module`. Previously only the vector dialect was
/// re-validated, so a parsed/deserialized gpu/avx512/ane op slipped through.
#[test]
fn validate_rejects_unknown_gpu_dialect_op() {
    use trust_ir::dialect::DialectInst;

    let mut mb = ModuleBuilder::new("bad_gpu_dialect");
    let ft = mb.add_func_type(vec![], vec![]);
    let mut fb = mb.function("test", ft);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    // `dialect_op` does not eagerly validate, so this ill-formed op survives
    // into the module and must be rejected by validate_module.
    fb.dialect_op(DialectInst::new("gpu", "definitely_not_a_gpu_op").with_result_ty(Ty::U32));
    fb.ret(vec![]);
    fb.build();

    let module = mb.build();
    let errors = validate_module(&module);
    assert!(
        errors.iter().any(|e| matches!(
            e,
            ValidationError::InvalidVectorDialectOp { op, .. } if op.starts_with("gpu.")
        )),
        "expected unknown gpu dialect op rejection, got {errors:?}"
    );
}
