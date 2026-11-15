// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0
//
// F-161: a `Bitcast` / `Transmute` with a bool lane stored by value on either
// side is refused BY NAME, in both validator entry points, in both
// directions, and the reference interpreter refuses it too.
//
// A bool lane is one bit of value (`Ty::bit_width`: `<8 x bool>` is 8) in
// one byte of storage (`Module::ty_layout_shape`: `<8 x bool>` is 64).
// `validate_function` compared value widths and `validate_module`'s layout
// pass compared storage sizes, so — measured before this refusal — the
// function-only validator admitted `bitcast <8 x bool> -> u8` (and
// `<64 x bool> -> ptr`) while the module validator admitted
// `bitcast <8 x bool> -> u64`, and the reference interpreter executes
// neither (`eval_bitcast`: "Bitcast: unsupported source type" /
// "bit width mismatch 8 vs 64"); the Lean `semCast .Bitcast` arm answers
// "Bitcast: unsupported operand type" for any vector or bool operand. The
// two sizing paths are each correct on their own axis (pinned in
// `trust-ir/tests/bool_lane_width_vs_layout.rs`); the reinterpret lane was
// the one consumer that treated them as the same number.

use trust_ir::constant::Constant;
use trust_ir::inst::ICmpOp;
use trust_ir::interpret::Interpreter;
use trust_ir::ty::Ty;
use trust_ir::{CastOp, FuncId, Module};
use trust_ir_build::builder::ModuleBuilder;
use trust_ir_build::validate::{ValidationError, validate_function, validate_module};

fn v_bool(lanes: u32) -> Ty {
    Ty::Vector(Box::new(Ty::Bool), lanes)
}

/// One function: `cast(operand: src) -> dst` through `op`.
fn cast_module(op: CastOp, src: Ty, dst: Ty) -> Module {
    let mut mb = ModuleBuilder::new("bool_lane_cast");
    let ft = mb.add_func_type(vec![src.clone()], vec![dst.clone()]);
    let mut fb = mb.function("cast", ft);
    let entry = fb.create_block();
    let operand = fb.add_block_param(entry, src.clone());
    fb.switch_to_block(entry);
    let out = fb.cast(op, src, dst, operand);
    fb.ret(vec![out]);
    fb.build();
    mb.build().expect("ModuleBuilder::build: test fixture")
}

/// The reason string of every `CastLayoutUnsupported` in `errors`.
fn layout_refusals(errors: &[ValidationError]) -> Vec<String> {
    errors
        .iter()
        .filter_map(|e| match e {
            ValidationError::CastLayoutUnsupported { reason, .. } => Some(reason.clone()),
            _ => None,
        })
        .collect()
}

fn any_cast_error(errors: &[ValidationError]) -> bool {
    errors.iter().any(|e| {
        matches!(
            e,
            ValidationError::CastIncompatible { .. }
                | ValidationError::CastLayoutUnsupported { .. }
        )
    })
}

/// The refused shapes: the two the measurement exposed (`<8 x bool>` to the
/// 8-bit and to the 64-bit integer), the reverse direction, the scalar, the
/// pointer forgery, a nested bool vector, and `Transmute`.
fn refused_cases() -> Vec<(CastOp, Ty, Ty)> {
    vec![
        (CastOp::Bitcast, v_bool(8), Ty::U8),
        (CastOp::Bitcast, v_bool(8), Ty::U64),
        (CastOp::Bitcast, Ty::U8, v_bool(8)),
        (CastOp::Bitcast, Ty::U64, v_bool(8)),
        (CastOp::Bitcast, Ty::Bool, Ty::U8),
        (CastOp::Bitcast, v_bool(16), Ty::U16),
        (CastOp::Bitcast, v_bool(64), Ty::Ptr),
        (CastOp::Bitcast, Ty::Vector(Box::new(v_bool(4)), 2), Ty::U8),
        (CastOp::Transmute, v_bool(8), Ty::U64),
    ]
}

#[test]
fn function_only_validator_refuses_a_bool_lane_reinterpret_by_name() {
    for (op, src, dst) in refused_cases() {
        let module = cast_module(op, src.clone(), dst.clone());
        let errors = validate_function(&module.functions[0]);
        let reasons = layout_refusals(&errors);
        assert!(
            reasons
                .iter()
                .any(|r| r.contains("a bool lane is one bit of value in one byte of storage")),
            "{op} {src} -> {dst}: validate_function must refuse by name, got {errors:?}"
        );
    }
}

#[test]
fn module_validator_refuses_the_same_casts_in_the_same_spelling() {
    for (op, src, dst) in refused_cases() {
        let module = cast_module(op, src.clone(), dst.clone());
        let function_reasons = layout_refusals(&validate_function(&module.functions[0]));
        let module_reasons = layout_refusals(&validate_module(&module));
        assert!(
            module_reasons
                .iter()
                .any(|r| r.contains("a bool lane is one bit of value in one byte of storage")),
            "{op} {src} -> {dst}: validate_module must refuse by name, got {module_reasons:?}"
        );
        // One rule, one spelling: the module pass (through
        // `LayoutError::BoolLaneReinterpret`) and the function-only arm say
        // the same words for the same node.
        assert_eq!(
            function_reasons.first(),
            module_reasons.first(),
            "{op} {src} -> {dst}: the two entry points must give one reason"
        );
    }
}

/// The identity cast is not a reinterpretation; a pointer TO a bool lane is
/// an address; and no non-bool reinterpret changed.
#[test]
fn identity_pointer_and_non_bool_reinterprets_are_unchanged() {
    let unchanged = [
        (CastOp::Bitcast, v_bool(8), v_bool(8)),
        (CastOp::Bitcast, Ty::PtrConst(Box::new(v_bool(8))), Ty::U64),
        (CastOp::Bitcast, Ty::U64, Ty::F64),
        (CastOp::Bitcast, Ty::v4_i32(), Ty::v2_i64()),
    ];
    for (op, src, dst) in unchanged {
        let module = cast_module(op, src.clone(), dst.clone());
        let function_errors = validate_function(&module.functions[0]);
        let module_errors = validate_module(&module);
        assert!(
            !any_cast_error(&function_errors),
            "{op} {src} -> {dst}: validate_function must still admit it, got {function_errors:?}"
        );
        assert!(
            !any_cast_error(&module_errors),
            "{op} {src} -> {dst}: validate_module must still admit it, got {module_errors:?}"
        );
    }
}

/// `mask() -> dst`: an `<8 x bool>` mask produced by `<8 x i8> icmp sge`
/// on constants, bitcast to `dst`. No parameters, so the interpreter can run
/// it as-is.
fn mask_bitcast_module(dst: Ty) -> Module {
    let mut mb = ModuleBuilder::new("mask_bitcast");
    let v8i8 = Ty::Vector(Box::new(Ty::I8), 8);
    let ft = mb.add_func_type(vec![], vec![dst.clone()]);
    let mut fb = mb.function("mask", ft);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    let lhs = fb.const_value(
        v8i8.clone(),
        Constant::Vector(
            [0, -1, 2, -3, 4, -5, 6, -7]
                .into_iter()
                .map(Constant::Int)
                .collect(),
        ),
    );
    let rhs = fb.const_value(v8i8.clone(), Constant::Vector(vec![Constant::Int(0); 8]));
    let mask = fb.icmp(ICmpOp::Sge, v8i8, lhs, rhs);
    let out = fb.cast(CastOp::Bitcast, v_bool(8), dst, mask);
    fb.ret(vec![out]);
    fb.build();
    mb.build().expect("ModuleBuilder::build: test fixture")
}

/// The referee (`docs/SPEC_RATIFICATIONS.md` §4) refuses BOTH directions the
/// two validator paths used to split on — so the refusal above makes the
/// validator agree with the interpreter, not the other way round.
#[test]
fn the_reference_interpreter_refuses_both_directions() {
    let to_u8 = mask_bitcast_module(Ty::U8);
    let error = Interpreter::with_module(&to_u8)
        .execute_func(FuncId::new(0), [])
        .expect_err("bitcast <8 x bool> -> u8 must not execute");
    assert!(
        error
            .message
            .contains("Bitcast: unsupported source type <8 x bool>"),
        "unexpected message: {}",
        error.message
    );

    let to_u64 = mask_bitcast_module(Ty::U64);
    let error = Interpreter::with_module(&to_u64)
        .execute_func(FuncId::new(0), [])
        .expect_err("bitcast <8 x bool> -> u64 must not execute");
    assert!(
        error.message.contains("bit width mismatch 8 vs 64"),
        "unexpected message: {}",
        error.message
    );

    // And the validator now says the same as the referee for both.
    for module in [&to_u8, &to_u64] {
        assert!(
            !layout_refusals(&validate_module(module)).is_empty(),
            "the module validator must refuse what the interpreter refuses"
        );
        assert!(
            !layout_refusals(&validate_function(&module.functions[0])).is_empty(),
            "the function-only validator must refuse what the interpreter refuses"
        );
    }
}
