// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0
//
// WS2.15 (closes the f16 part of F-036): binary16 (`F16`) arithmetic,
// comparison, constants, casts, bitcasts and memory images execute in the
// reference interpreter.
//
// Before: every `F16` operation was `UnsupportedFloat` ("f16 arithmetic is
// not executable" / "... require an explicit half-precision codec"), so no
// differential evidence existed for any binary16 body (critic unexercised
// #5, `crit.unex05`). Now each binary16 operation is computed in binary32
// and rounded ONCE to binary16 by `trust_ir::interpret::f64_to_f16_bits`
// (round to nearest, ties to even, gradual underflow, overflow to ±inf) —
// exact because 24 >= 2*11 + 2 makes the intermediate rounding innocuous —
// and the table below pins that rounding bit for bit at the edges.
//
// The proven subset keeps `F16` EXCLUDED (bridge.rs): the Lean model still
// refuses binary16 (`unsupported.float`), and a type is admitted to the
// subset only when both engines agree on it. That is the WS2.23 follow-up
// (binary16 reuses the binary32 rounder with p = 11); nothing here claims it.
//
// Row ports (roadmap F-036, `docs/roadmap/two-language-completion-findings.json`):
// * `crit.unex05` — `crit_unex05_f16_arithmetic_compare_and_constants_execute`.
// * `producer-rust-thir/f128-and-f16` —
//   `producer_rust_thir_f128_and_f16_f16_executes_and_f128_has_no_type`.
// * `goal-g1-g8/g4-reference-interpreter-differential` (binary16 half) —
//   `goal_g4_reference_interpreter_differential_f16_against_an_exact_oracle`.
// * `trust-ir-self-declared/interpreter-unsupported-constructs` (f16 half) —
//   `trust_ir_self_declared_interpreter_unsupported_constructs_f16_is_no_longer_one`.

use trust_ir::inst::{BinOp, CastOp, FCmpOp, UnOp};
use trust_ir::interpret::{
    InterpretErrorCode, InterpretValue, InterpretValueKind, Interpreter, f16_bits_to_f64,
    f64_to_f16_bits,
};
use trust_ir::value::{FuncId, ValueId};
use trust_ir::{Module, Ty};
use trust_ir_build::{FunctionBuilder, ModuleBuilder, validate_module};

mod common;
use common::Rng;

// ───────────────────────────── harness ─────────────────────────────

fn build_nullary<F>(ret_tys: Vec<Ty>, body: F) -> (Module, FuncId)
where
    F: FnOnce(&mut FunctionBuilder<'_>) -> Vec<ValueId>,
{
    let mut mb = ModuleBuilder::new("ws2_15_f16");
    let ft = mb.add_func_type(vec![], ret_tys);
    let fid = {
        let mut fb = mb.function("f", ft);
        let entry = fb.create_block();
        fb.switch_to_block(entry);
        let rets = body(&mut fb);
        fb.ret(rets);
        fb.build()
    };
    (mb.build().expect("ModuleBuilder::build: test fixture"), fid)
}

fn run(module: &Module, fid: FuncId) -> Vec<InterpretValue> {
    assert_eq!(validate_module(module), vec![], "fixture validates");
    Interpreter::with_module(module)
        .execute_func(fid, [])
        .expect("execution succeeds")
        .returns
}

fn float_bits(value: &InterpretValue) -> u64 {
    match value.kind {
        InterpretValueKind::FloatBits(bits) => bits,
        ref other => panic!("expected a float value, got {other:?}"),
    }
}

/// The bit pattern of an `F16` return: the interpreter stores floats as
/// `FloatBits`, so this is bit-exact end to end.
fn f16_return(value: &InterpretValue) -> u16 {
    assert_eq!(value.ty, Ty::F16);
    u16::try_from(float_bits(value)).expect("an F16 return carries 16 bits")
}

/// An `F16` constant from its BIT PATTERN: `fconst` takes the `f64` carrier
/// (`Constant::Float`), and every binary16 value is exact in it.
fn h(fb: &mut FunctionBuilder<'_>, bits: u16) -> ValueId {
    fb.fconst(Ty::F16, f16_bits_to_f64(bits))
}

/// One row's operation. Operands are binary16 bit patterns, so nothing is
/// parsed and no host float type is involved.
#[derive(Clone, Debug)]
enum F16Row {
    /// `BinOp op F16` over two binary16 operands.
    Bin(BinOp, u16, u16),
    /// `UnOp op F16` of one binary16 operand.
    Un(UnOp, u16),
    /// `Cast FPTrunc F64 -> F16` of a binary64 operand.
    TruncF64(u64),
    /// `Cast FPTrunc F32 -> F16` of a binary32 operand.
    TruncF32(u32),
    /// `Cast UIToFP src -> F16` of an unsigned integer.
    UiToFp(Ty, i128),
    /// `Cast SIToFP src -> F16` of a signed integer.
    SiToFp(Ty, i128),
    /// `Cast Bitcast U16 -> F16` of a 16-bit integer.
    BitcastFromU16(u16),
}

/// (row name, operation, expected binary16 bits). The rows are the edges a
/// rounder gets wrong: the overflow tie, ties to even in both directions,
/// sticky bits past a tie, the subnormal floor and gradual underflow, the
/// signed zeros, and the integer conversions whose `f64` intermediate is
/// exact only because of the reasoning in `interpret.rs`.
const F16_CROSS_ENGINE_TABLE: &[(&str, F16Row, u16)] = &[
    // 1.5 + 2.25 = 3.75.
    (
        "fadd_1_5_plus_2_25",
        F16Row::Bin(BinOp::FAdd, 0x3E00, 0x4080),
        0x4380,
    ),
    // 65504 + 8 = 65512: below the halfway point to 2^16, rounds down.
    (
        "fadd_max_plus_8_rounds_down",
        F16Row::Bin(BinOp::FAdd, 0x7BFF, 0x4800),
        0x7BFF,
    ),
    // 65504 + 16 = 65520: EXACTLY halfway between 65504 (odd significand)
    // and 2^16 (out of the format); ties to even rounds up -> +inf. An
    // implementation that saturates, truncates, or never performs the final
    // rounding answers 65504 here.
    (
        "fadd_max_plus_16_ties_to_inf",
        F16Row::Bin(BinOp::FAdd, 0x7BFF, 0x4C00),
        0x7C00,
    ),
    (
        "fadd_max_plus_32_overflows",
        F16Row::Bin(BinOp::FAdd, 0x7BFF, 0x5000),
        0x7C00,
    ),
    (
        "fsub_neg_max_minus_16_ties_to_neg_inf",
        F16Row::Bin(BinOp::FSub, 0xFBFF, 0x4C00),
        0xFC00,
    ),
    // 2^-14 - 2^-24 = the largest subnormal (exact).
    (
        "fsub_min_normal_minus_min_subnormal",
        F16Row::Bin(BinOp::FSub, 0x0400, 0x0001),
        0x03FF,
    ),
    // 2^-14 * 0.5 = 2^-15, a subnormal result.
    (
        "fmul_subnormal_result",
        F16Row::Bin(BinOp::FMul, 0x0400, 0x3800),
        0x0200,
    ),
    // 2^-24 * 0.5 = 2^-25: halfway between 0 and the smallest subnormal,
    // ties to even -> +0.
    (
        "fmul_underflow_ties_to_zero",
        F16Row::Bin(BinOp::FMul, 0x0001, 0x3800),
        0x0000,
    ),
    // 5 * 2^-24 * 0.75 = 3.75 * 2^-24 -> 4 * 2^-24 (above the halfway point).
    (
        "fmul_subnormal_rounds_up",
        F16Row::Bin(BinOp::FMul, 0x0005, 0x3A00),
        0x0004,
    ),
    // 3 * 2^-24 * 0.75 = 2.25 * 2^-24 -> 2 * 2^-24 (below).
    (
        "fmul_subnormal_rounds_down",
        F16Row::Bin(BinOp::FMul, 0x0003, 0x3A00),
        0x0002,
    ),
    // 1/3 = 0x3555 (the discarded bits 0101... are below the halfway point).
    (
        "fdiv_one_third",
        F16Row::Bin(BinOp::FDiv, 0x3C00, 0x4200),
        0x3555,
    ),
    (
        "fdiv_one_by_zero_is_inf",
        F16Row::Bin(BinOp::FDiv, 0x3C00, 0x0000),
        0x7C00,
    ),
    (
        "fdiv_neg_one_by_zero_is_neg_inf",
        F16Row::Bin(BinOp::FDiv, 0xBC00, 0x0000),
        0xFC00,
    ),
    // 1023 * 2^-24 (largest subnormal) / 2 = 511.5 * 2^-24 -> 512 (tie, even).
    (
        "fdiv_subnormal_ties_to_even",
        F16Row::Bin(BinOp::FDiv, 0x03FF, 0x4000),
        0x0200,
    ),
    // fmod(5.25, 2) = 1.25, exact.
    (
        "frem_5_25_by_2",
        F16Row::Bin(BinOp::FRem, 0x4540, 0x4000),
        0x3D00,
    ),
    (
        "fmin_1_5_2_25",
        F16Row::Bin(BinOp::FMin, 0x3E00, 0x4080),
        0x3E00,
    ),
    (
        "fmax_1_5_2_25",
        F16Row::Bin(BinOp::FMax, 0x3E00, 0x4080),
        0x4080,
    ),
    // Signed zeros: 1 - 1 = +0, -1 * 0 = -0, (+0) + (-0) = +0.
    (
        "fsub_one_minus_one_is_pos_zero",
        F16Row::Bin(BinOp::FSub, 0x3C00, 0x3C00),
        0x0000,
    ),
    (
        "fmul_neg_one_by_zero_is_neg_zero",
        F16Row::Bin(BinOp::FMul, 0xBC00, 0x0000),
        0x8000,
    ),
    (
        "fadd_pos_zero_neg_zero_is_pos_zero",
        F16Row::Bin(BinOp::FAdd, 0x0000, 0x8000),
        0x0000,
    ),
    // FNeg/FAbs are sign-bit operations: a NaN payload survives them.
    (
        "fneg_keeps_nan_payload",
        F16Row::Un(UnOp::FNeg, 0x7E2A),
        0xFE2A,
    ),
    (
        "fabs_keeps_nan_payload",
        F16Row::Un(UnOp::FAbs, 0xFE2A),
        0x7E2A,
    ),
    (
        "fneg_pos_zero_is_neg_zero",
        F16Row::Un(UnOp::FNeg, 0x0000),
        0x8000,
    ),
    // sqrt(2) = 1.4140625 (0x3DA8); the next binary16 value 1.4150390625 is
    // further from 1.41421356.
    ("fsqrt_two", F16Row::Un(UnOp::FSqrt, 0x4000), 0x3DA8),
    ("ffloor_neg_1_5", F16Row::Un(UnOp::FFloor, 0xBE00), 0xC000),
    ("fceil_1_5", F16Row::Un(UnOp::FCeil, 0x3E00), 0x4000),
    ("ftrunc_neg_1_5", F16Row::Un(UnOp::FTrunc, 0xBE00), 0xBC00),
    // 1 + 2^-11 ties to even (1.0); one sticky bit further rounds up — a
    // truncating rounder gets the second one wrong, a ties-away rounder
    // the first.
    (
        "fptrunc_f64_one_plus_half_ulp_ties_even",
        F16Row::TruncF64(0x3FF0_0200_0000_0000),
        0x3C00,
    ),
    (
        "fptrunc_f64_one_plus_half_ulp_sticky",
        F16Row::TruncF64(0x3FF0_0200_0000_0001),
        0x3C01,
    ),
    // 1 + 3*2^-11 is the midpoint between 1 + 2^-10 (odd) and 1 + 2^-9
    // (even): ties to even rounds UP.
    (
        "fptrunc_f64_ties_even_upward",
        F16Row::TruncF64(0x3FF0_0600_0000_0000),
        0x3C02,
    ),
    (
        "fptrunc_f64_65520_ties_to_inf",
        F16Row::TruncF64(0x40EF_FE00_0000_0000),
        0x7C00,
    ),
    (
        "fptrunc_f64_65519_rounds_down",
        F16Row::TruncF64(0x40EF_FDE0_0000_0000),
        0x7BFF,
    ),
    // 2^-25 is the tie between 0 and the smallest subnormal -> +0; the next
    // binary64 value rounds up to 2^-24.
    (
        "fptrunc_f64_half_min_subnormal_ties_to_zero",
        F16Row::TruncF64(0x3E60_0000_0000_0000),
        0x0000,
    ),
    (
        "fptrunc_f64_above_half_min_subnormal",
        F16Row::TruncF64(0x3E60_0000_0000_0001),
        0x0001,
    ),
    (
        "fptrunc_f64_negative_underflow_keeps_sign",
        F16Row::TruncF64(0xBE50_0000_0000_0000),
        0x8000,
    ),
    (
        "fptrunc_f64_neg_zero",
        F16Row::TruncF64(0x8000_0000_0000_0000),
        0x8000,
    ),
    (
        "fptrunc_f64_neg_inf",
        F16Row::TruncF64(0xFFF0_0000_0000_0000),
        0xFC00,
    ),
    // The same two ties from binary32 (which widens exactly first).
    (
        "fptrunc_f32_one_plus_half_ulp_ties_even",
        F16Row::TruncF32(0x3F80_1000),
        0x3C00,
    ),
    (
        "fptrunc_f32_one_plus_half_ulp_sticky",
        F16Row::TruncF32(0x3F80_1001),
        0x3C01,
    ),
    (
        "fptrunc_f32_max_f32_overflows",
        F16Row::TruncF32(0x7F7F_FFFF),
        0x7C00,
    ),
    // Integer conversions. 2049 is the midpoint between 2048 (even) and
    // 2050 (odd) -> 2048; 2051 is the midpoint between 2050 (odd) and 2052
    // (even) -> 2052; the negative twin of the second rounds to -2052, which
    // a round-half-up rounder gets wrong.
    (
        "uitofp_u32_2049_ties_to_even_down",
        F16Row::UiToFp(Ty::U32, 2049),
        0x6800,
    ),
    (
        "uitofp_u32_2051_ties_to_even_up",
        F16Row::UiToFp(Ty::U32, 2051),
        0x6802,
    ),
    (
        "sitofp_i32_minus_2051_ties_to_even",
        F16Row::SiToFp(Ty::I32, -2051),
        0xE802,
    ),
    (
        "uitofp_u16_65520_ties_to_inf",
        F16Row::UiToFp(Ty::U16, 65520),
        0x7C00,
    ),
    (
        "uitofp_u16_65519_rounds_down",
        F16Row::UiToFp(Ty::U16, 65519),
        0x7BFF,
    ),
    // Past 2^53 the binary64 intermediate is inexact, and the result is
    // still exactly what the exact value rounds to (inf).
    (
        "uitofp_u64_past_2_pow_53_is_inf",
        F16Row::UiToFp(Ty::U64, (1i128 << 53) + 1),
        0x7C00,
    ),
    (
        "sitofp_i64_past_2_pow_53_is_neg_inf",
        F16Row::SiToFp(Ty::I64, -((1i128 << 53) + 1)),
        0xFC00,
    ),
    ("sitofp_i8_minus_2", F16Row::SiToFp(Ty::I8, -2), 0xC000),
    (
        "uitofp_u128_max_is_inf",
        F16Row::UiToFp(Ty::U128, i128::MAX),
        0x7C00,
    ),
    // A bitcast reinterprets the 16 bits, including a signalling NaN's.
    ("bitcast_u16_1_5", F16Row::BitcastFromU16(0x3E00), 0x3E00),
    (
        "bitcast_u16_signalling_nan",
        F16Row::BitcastFromU16(0x7C01),
        0x7C01,
    ),
];

fn f16_row_bits(row: &F16Row) -> u16 {
    let (m, f) = build_nullary(vec![Ty::F16], |fb| match row {
        &F16Row::Bin(op, lhs, rhs) => {
            let a = h(fb, lhs);
            let b = h(fb, rhs);
            vec![fb.binop(op, Ty::F16, a, b)]
        }
        &F16Row::Un(op, operand) => {
            let x = h(fb, operand);
            vec![fb.unop(op, Ty::F16, x)]
        }
        &F16Row::TruncF64(bits) => {
            let x = fb.fconst(Ty::F64, f64::from_bits(bits));
            vec![fb.cast(CastOp::FPTrunc, Ty::F64, Ty::F16, x)]
        }
        &F16Row::TruncF32(bits) => {
            let x = fb.fconst(Ty::F32, f64::from(f32::from_bits(bits)));
            vec![fb.cast(CastOp::FPTrunc, Ty::F32, Ty::F16, x)]
        }
        F16Row::UiToFp(src, value) => {
            let x = fb.iconst(src.clone(), *value);
            vec![fb.cast(CastOp::UIToFP, src.clone(), Ty::F16, x)]
        }
        F16Row::SiToFp(src, value) => {
            let x = fb.iconst(src.clone(), *value);
            vec![fb.cast(CastOp::SIToFP, src.clone(), Ty::F16, x)]
        }
        &F16Row::BitcastFromU16(bits) => {
            let x = fb.uconst(Ty::U16, u128::from(bits));
            vec![fb.cast(CastOp::Bitcast, Ty::U16, Ty::F16, x)]
        }
    });
    f16_return(&run(&m, f)[0])
}

// ───────────────────────────── positive ─────────────────────────────

/// `crit.unex05` (f16 part), ported: binary16 arithmetic, comparison and
/// constants execute — `1.5 + 2.25 = 3.75`, bit for bit.
#[test]
fn crit_unex05_f16_arithmetic_compare_and_constants_execute() {
    let (m, f) = build_nullary(vec![Ty::F16, Ty::Bool, Ty::Bool, Ty::F16], |fb| {
        let a = fb.fconst(Ty::F16, 1.5);
        let b = fb.fconst(Ty::F16, 2.25);
        let sum = fb.binop(BinOp::FAdd, Ty::F16, a, b);
        let lt = fb.fcmp(FCmpOp::OLt, Ty::F16, a, b);
        let ge = fb.fcmp(FCmpOp::OGe, Ty::F16, a, b);
        vec![sum, lt, ge, b]
    });
    let returns = run(&m, f);
    assert_eq!(
        f16_return(&returns[0]),
        0x4380,
        "1.5 + 2.25 = 3.75 at binary16"
    );
    assert_eq!(returns[1].as_bool(), Some(true));
    assert_eq!(returns[2].as_bool(), Some(false));
    assert_eq!(
        f16_return(&returns[3]),
        0x4080,
        "the 2.25 constant narrowed once"
    );
}

/// The bit-exact edge table: every row's interpreter result equals the
/// committed binary16 pattern.
#[test]
fn f16_cross_engine_table_interpreter_bits() {
    for (name, row, expected) in F16_CROSS_ENGINE_TABLE {
        let got = f16_row_bits(row);
        assert_eq!(
            got, *expected,
            "{name}: interpreter gave {got:#06x}, the table says {expected:#06x}"
        );
    }
}

/// NaN results are only required to be *a* NaN (docs/ub-numerics-policy.md
/// §2): pinned as NaN-ness, never as a payload.
#[test]
fn f16_nan_results_are_nans_and_compare_unordered() {
    let (m, f) = build_nullary(
        vec![Ty::F16, Ty::F16, Ty::F16, Ty::Bool, Ty::Bool, Ty::Bool],
        |fb| {
            let inf = h(fb, 0x7C00);
            let zero = h(fb, 0x0000);
            let nan = h(fb, 0x7E00);
            let one = h(fb, 0x3C00);
            let inf_minus_inf = fb.binop(BinOp::FSub, Ty::F16, inf, inf);
            let zero_by_zero = fb.binop(BinOp::FDiv, Ty::F16, zero, zero);
            let nan_plus_one = fb.binop(BinOp::FAdd, Ty::F16, nan, one);
            let oeq = fb.fcmp(FCmpOp::OEq, Ty::F16, nan, nan);
            let une = fb.fcmp(FCmpOp::UNe, Ty::F16, nan, one);
            let ult = fb.fcmp(FCmpOp::ULt, Ty::F16, one, nan);
            vec![inf_minus_inf, zero_by_zero, nan_plus_one, oeq, une, ult]
        },
    );
    let returns = run(&m, f);
    for (index, what) in ["inf - inf", "0 / 0", "NaN + 1"].iter().enumerate() {
        let bits = f16_return(&returns[index]);
        assert!(
            bits & 0x7C00 == 0x7C00 && bits & 0x03FF != 0,
            "{what} is a NaN, got {bits:#06x}"
        );
    }
    assert_eq!(returns[3].as_bool(), Some(false), "OEq(NaN, NaN)");
    assert_eq!(returns[4].as_bool(), Some(true), "UNe(NaN, 1)");
    assert_eq!(returns[5].as_bool(), Some(true), "ULt(1, NaN)");
}

/// Widening casts, float->int casts (raw and saturating) and the float->int
/// bitcast see the binary16 VALUE / pattern exactly.
#[test]
fn f16_casts_out_are_exact() {
    let (m, f) = build_nullary(
        vec![Ty::F32, Ty::F64, Ty::U32, Ty::I32, Ty::U8, Ty::I8, Ty::U16],
        |fb| {
            let one_and_half = h(fb, 0x3E00);
            let max = h(fb, 0x7BFF);
            let minus_two = h(fb, 0xC000);
            let neg_inf = h(fb, 0xFC00);
            let pos_inf = h(fb, 0x7C00);
            // A signalling NaN cannot be spelled through the `f64` constant
            // carrier (narrowing quiets it, as `as f32` does); bitcast it in.
            let snan_bits = fb.uconst(Ty::U16, 0x7C01);
            let snan = fb.cast(CastOp::Bitcast, Ty::U16, Ty::F16, snan_bits);
            vec![
                fb.cast(CastOp::FPExt, Ty::F16, Ty::F32, one_and_half),
                fb.cast(CastOp::FPExt, Ty::F16, Ty::F64, one_and_half),
                fb.cast(CastOp::FPToUI, Ty::F16, Ty::U32, max),
                fb.cast(CastOp::FPToSI, Ty::F16, Ty::I32, minus_two),
                fb.cast(CastOp::FPToUISat, Ty::F16, Ty::U8, neg_inf),
                fb.cast(CastOp::FPToSISat, Ty::F16, Ty::I8, pos_inf),
                fb.cast(CastOp::Bitcast, Ty::F16, Ty::U16, snan),
            ]
        },
    );
    let returns = run(&m, f);
    assert_eq!(float_bits(&returns[0]), u64::from(1.5f32.to_bits()));
    assert_eq!(float_bits(&returns[1]), 1.5f64.to_bits());
    assert_eq!(returns[2].as_int().unwrap().as_unsigned(), 65504);
    assert_eq!(returns[3].as_int().unwrap().as_signed(), -2);
    assert_eq!(returns[4].as_int().unwrap().as_unsigned(), 0);
    assert_eq!(returns[5].as_int().unwrap().as_signed(), 127);
    assert_eq!(returns[6].as_int().unwrap().as_unsigned(), 0x7C01);
}

/// The binary16 memory image is the two little-endian bytes of the pattern:
/// a typed store and load round-trip it, and an integer reload of the same
/// bytes sees the pattern.
#[test]
fn f16_memory_image_is_two_bytes() {
    let (m, f) = build_nullary(vec![Ty::F16, Ty::U16], |fb| {
        let slot = fb.alloca(Ty::F16);
        let value = h(fb, 0xBE00);
        fb.store(Ty::F16, slot, value);
        let reloaded = fb.load(Ty::F16, slot);
        let as_int = fb.load(Ty::U16, slot);
        vec![reloaded, as_int]
    });
    let returns = run(&m, f);
    assert_eq!(f16_return(&returns[0]), 0xBE00);
    assert_eq!(returns[1].as_int().unwrap().as_unsigned(), 0xBE00);
}

/// Risk item: the `F16` constant's canonicalization must match every codec.
/// A `Constant::Float(f64)` is the carrier in all four formats; each
/// round-trip decodes to a module whose execution gives the same bits.
#[test]
fn f16_constants_survive_every_codec_and_execute_the_same() {
    let (m, f) = build_nullary(vec![Ty::F16, Ty::F16], |fb| {
        // 2.25 (exact) and 1 + 2^-11 + 2^-20 (narrowed with a sticky bit).
        let exact = fb.fconst(Ty::F16, 2.25);
        let sticky = fb.fconst(Ty::F16, 1.0 + 2f64.powi(-11) + 2f64.powi(-20));
        let sum = fb.binop(BinOp::FAdd, Ty::F16, exact, sticky);
        vec![sticky, sum]
    });
    let bits = |module: &Module| -> Vec<u16> { run(module, f).iter().map(f16_return).collect() };
    let expected = bits(&m);
    assert_eq!(
        expected,
        vec![0x3C01, 0x4280],
        "1.0009765625 and 2.25 + 1.0009765625 = 3.25"
    );

    let binary = trust_ir::binary::serialize_module(&m).expect("serialize_module: test fixture");
    let from_binary = trust_ir::binary::deserialize_module(&binary).expect("binary decode");
    assert_eq!(bits(&from_binary), expected, "binary");

    let json = serde_json::to_string(&m).expect("json");
    let from_json = serde_json::from_str::<Module>(&json).expect("json decode");
    assert_eq!(bits(&from_json), expected, "json");

    let msgpack = rmp_serde::to_vec(&m).expect("msgpack");
    let from_msgpack = rmp_serde::from_slice::<Module>(&msgpack).expect("msgpack decode");
    assert_eq!(bits(&from_msgpack), expected, "msgpack");

    let text = trust_ir::format::canonical(&m);
    let from_text = trust_ir::parser::parse_module(&text).expect("text parse");
    assert_eq!(bits(&from_text), expected, "text");
}

// ───────────────────────────── negative / named ─────────────────────────────

/// `trust-ir-self-declared/interpreter-unsupported-constructs` (f16 half),
/// ported: the interpreter's self-declared unsupported list no longer
/// contains binary16. `UnsupportedFloat` keeps its stable code (it is the
/// Lean mirror), but no `F16` operation produces it any more: the unit test
/// that used to pin the refusal now pins execution, and the seven former
/// refusal sites (binop, unop, fcmp, constant, bitcast, cast in, cast out)
/// are each exercised by the table above.
#[test]
fn trust_ir_self_declared_interpreter_unsupported_constructs_f16_is_no_longer_one() {
    assert_eq!(
        InterpretErrorCode::UnsupportedFloat.as_str(),
        "unsupported_float"
    );
    let sites: [F16Row; 7] = [
        F16Row::Bin(BinOp::FMul, 0x4000, 0x4000),
        F16Row::Un(UnOp::FSqrt, 0x4400),
        F16Row::TruncF64(0x4008_0000_0000_0000),
        F16Row::TruncF32(0x4040_0000),
        F16Row::UiToFp(Ty::U8, 3),
        F16Row::SiToFp(Ty::I8, -3),
        F16Row::BitcastFromU16(0x4200),
    ];
    let expected = [0x4400u16, 0x4000, 0x4200, 0x4200, 0x4200, 0xC200, 0x4200];
    for (row, want) in sites.iter().zip(expected) {
        assert_eq!(f16_row_bits(row), want, "{row:?}");
    }
    // The comparison site.
    let (m, f) = build_nullary(vec![Ty::Bool], |fb| {
        let a = h(fb, 0x4000);
        let b = h(fb, 0x4200);
        vec![fb.fcmp(FCmpOp::OLt, Ty::F16, a, b)]
    });
    assert_eq!(run(&m, f)[0].as_bool(), Some(true));
}

/// `producer-rust-thir/f128-and-f16`, ported: the f16 half executes; the
/// f128 half has no `Ty` — `f128` is refused by the text parser as an unknown
/// type, and `LIMITATIONS.md` ratifies it out of scope (unstable Rust; the
/// WS8 F-127 decision gate owns any future width).
#[test]
fn producer_rust_thir_f128_and_f16_f16_executes_and_f128_has_no_type() {
    let (m, f) = build_nullary(vec![Ty::F16], |fb| {
        let a = h(fb, 0x4000);
        vec![fb.binop(BinOp::FMul, Ty::F16, a, a)]
    });
    assert_eq!(f16_return(&run(&m, f)[0]), 0x4400);

    let text = trust_ir::format::canonical(&m);
    assert!(text.contains("f16"), "the fixture spells its type:\n{text}");
    let f128 = text.replace("f16", "f128");
    let error = trust_ir::parser::parse_module(&f128).expect_err("f128 is not a type");
    assert!(
        error.to_string().contains("f128"),
        "the refusal names the unknown type: {error}"
    );
    let limitations = std::fs::read_to_string(
        std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../../LIMITATIONS.md"),
    )
    .expect("LIMITATIONS.md");
    assert!(
        limitations.contains("`f128`") && limitations.contains("F-127"),
        "LIMITATIONS.md ratifies f128 out of scope with the F-127 cross-reference"
    );
}

// ───────────────────────────── mutation control ─────────────────────────────

/// When `x` lies EXACTLY halfway between two adjacent binary16 values, those
/// two patterns ordered by value (`+inf` counts as the neighbour past the
/// largest finite value, at the 65520 overflow tie); `None` otherwise.
fn tie_neighbours(x: f64) -> Option<(u16, u16)> {
    if !x.is_finite() {
        return None;
    }
    let nearest = f64_to_f16_bits(x);
    let v = f16_bits_to_f64(nearest);
    if v == x {
        return None;
    }
    // The other neighbour is one pattern away in magnitude order.
    let other = if v.is_infinite() {
        (nearest & 0x8000) | 0x7BFF
    } else if x.abs() > v.abs() {
        nearest + 1
    } else {
        nearest - 1
    };
    let w = f16_bits_to_f64(other);
    let distance = |y: f64| {
        if y.is_infinite() {
            (x.abs() - 65536.0).abs()
        } else {
            (x - y).abs()
        }
    };
    if distance(v) != distance(w) {
        return None;
    }
    Some(if v < w {
        (nearest, other)
    } else {
        (other, nearest)
    })
}

/// The table is not satisfiable by a wrong rounder: each mutant below
/// disagrees with at least one row. Each mutant is applied to the EXACT
/// binary64 value of the row's result (every row's exact result is a
/// binary64 value, chosen so), and the mutants are the plausible mistakes: a
/// truncating rounder, ties away from zero, ties toward +inf, saturation
/// instead of overflow, and "no final rounding" (binary32 bits reinterpreted
/// through a narrowing that drops low bits).
#[test]
fn f16_cross_engine_table_discriminates_rounding_mutants() {
    fn exact(row: &F16Row) -> Option<f64> {
        Some(match row {
            &F16Row::Bin(op, lhs, rhs) => {
                let (a, b) = (f16_bits_to_f64(lhs), f16_bits_to_f64(rhs));
                match op {
                    BinOp::FAdd => a + b,
                    BinOp::FSub => a - b,
                    BinOp::FMul => a * b,
                    BinOp::FDiv => a / b,
                    BinOp::FRem => a % b,
                    BinOp::FMin => a.min(b),
                    BinOp::FMax => a.max(b),
                    _ => unreachable!(),
                }
            }
            F16Row::Un(_, _) | F16Row::BitcastFromU16(_) => return None,
            &F16Row::TruncF64(bits) => f64::from_bits(bits),
            &F16Row::TruncF32(bits) => f64::from(f32::from_bits(bits)),
            F16Row::UiToFp(_, value) | F16Row::SiToFp(_, value) => *value as f64,
        })
    }
    type Rounder = fn(f64) -> u16;
    let mutants: [(&str, Rounder); 5] = [
        ("truncate toward zero", |x| {
            let r = f64_to_f16_bits(x);
            let back = f16_bits_to_f64(r);
            if back.is_finite() && back.abs() > x.abs() && r & 0x7FFF != 0 {
                r - 1
            } else if back.is_infinite() && x.is_finite() {
                (r & 0x8000) | 0x7BFF
            } else {
                r
            }
        }),
        ("ties away from zero", |x| match tie_neighbours(x) {
            Some((lo, hi)) => {
                if f16_bits_to_f64(hi).abs() > f16_bits_to_f64(lo).abs() {
                    hi
                } else {
                    lo
                }
            }
            None => f64_to_f16_bits(x),
        }),
        ("ties toward +inf", |x| match tie_neighbours(x) {
            Some((_, hi)) => hi,
            None => f64_to_f16_bits(x),
        }),
        ("saturate instead of overflow", |x| {
            if x.is_finite() && x.abs() >= 65520.0 {
                (f64_to_f16_bits(x) & 0x8000) | 0x7BFF
            } else {
                f64_to_f16_bits(x)
            }
        }),
        (
            "no final rounding (binary32 bits narrowed by truncation)",
            |x| {
                let bits = (x as f32).to_bits();
                let sign = ((bits >> 31) as u16) << 15;
                let exponent = ((bits >> 23) & 0xFF) as i32 - 127;
                let fraction = ((bits >> 13) & 0x3FF) as u16;
                if !(-14..=15).contains(&exponent) {
                    return f64_to_f16_bits(x);
                }
                sign | (((exponent + 15) as u16) << 10) | fraction
            },
        ),
    ];
    for (mutant, round) in mutants {
        let caught = F16_CROSS_ENGINE_TABLE
            .iter()
            .filter_map(|(name, row, expected)| {
                exact(row).and_then(|x| (round(x) != *expected).then_some(*name))
            })
            .collect::<Vec<_>>();
        assert!(
            !caught.is_empty(),
            "mutant `{mutant}` satisfies every row it applies to; the table does not \
             discriminate it"
        );
    }
    // The reference rounder itself agrees with every row (the interpreter is
    // exercised through the instructions in `f16_cross_engine_table_interpreter_bits`).
    for (name, row, expected) in F16_CROSS_ENGINE_TABLE {
        if let Some(x) = exact(row) {
            assert_eq!(f64_to_f16_bits(x), *expected, "{name}: rounder");
        }
    }
}

// ───────────────────────────── differential oracle ─────────────────────────────

/// A finite binary16 value as an exact integer multiple of 2^-24 (its sign
/// carried by the integer): normal `(1024 + frac) * 2^(e - 1)`, subnormal
/// `frac`.
fn units(bits: u16) -> i128 {
    let exponent = i32::from((bits >> 10) & 0x1F);
    let fraction = i128::from(bits & 0x3FF);
    assert_ne!(exponent, 0x1F, "finite operand");
    let magnitude = if exponent == 0 {
        fraction
    } else {
        (1024 + fraction) << (exponent - 1)
    };
    if bits & 0x8000 != 0 {
        -magnitude
    } else {
        magnitude
    }
}

/// Round the exact value `numerator * 2^-scale` (plus a sticky "there is
/// more below" bit) to binary16, ties to even — an INDEPENDENT rounder
/// written over integers, with no float arithmetic at all, for the
/// differential oracle below. Every caller passes a `scale` of at least 24,
/// so the binary16 unit `2^-24` is never finer than the numerator's, which
/// keeps the dropped-bit count non-negative (asserted).
fn oracle_round(negative: bool, numerator: u128, scale: u32, sticky: bool) -> u16 {
    let sign: u16 = if negative { 0x8000 } else { 0 };
    if numerator == 0 {
        // A sticky remainder alone is below `2^-scale <= 2^-24`, and every
        // caller with `sticky` uses scale 64, so it rounds to zero.
        return sign;
    }
    let msb = 127 - numerator.leading_zeros() as i32;
    let exponent = msb - scale as i32;
    // Bits dropped below the binary16 precision: 11 significand bits in the
    // normal range, the fixed `2^-24` unit below it.
    let drop = if exponent >= -14 {
        msb - 10
    } else {
        scale as i32 - 24
    };
    assert!(drop >= 0, "the numerator is at least as fine as binary16");
    let drop = drop as u32;
    let mut kept = numerator >> drop;
    if drop > 0 {
        let remainder = numerator & ((1u128 << drop) - 1);
        let half = 1u128 << (drop - 1);
        let round_up = remainder > half || (remainder == half && (sticky || kept & 1 == 1));
        if round_up {
            kept += 1;
        }
    }
    if exponent < -14 {
        // `kept` is the unit count; a carry into bit 10 IS the smallest
        // normal's pattern.
        return sign | kept as u16;
    }
    let (mut mantissa, mut e) = (kept, exponent);
    if mantissa == 1 << 11 {
        mantissa >>= 1;
        e += 1;
    }
    if e > 15 {
        return sign | 0x7C00;
    }
    sign | (((e + 15) as u16) << 10) | (mantissa as u16 & 0x3FF)
}

/// `goal-g1-g8/g4-reference-interpreter-differential` (binary16 half),
/// ported: the interpreter's binary16 `+ - * /` agree with an exact
/// integer-arithmetic oracle on thousands of seeded operand pairs, finite
/// results only (a NaN result is compared as NaN-ness; ±inf and ±0 as bits).
#[test]
fn goal_g4_reference_interpreter_differential_f16_against_an_exact_oracle() {
    fn oracle(op: BinOp, lhs: u16, rhs: u16) -> Option<u16> {
        let (a, b) = (units(lhs), units(rhs));
        match op {
            BinOp::FAdd | BinOp::FSub => {
                let sum = if op == BinOp::FAdd { a + b } else { a - b };
                if sum == 0 {
                    // IEEE: an exact zero sum is +0 under round-to-nearest,
                    // unless both operands are -0 (a - (+0) with a = -0).
                    let neg = (lhs & 0x7FFF == 0 && rhs & 0x7FFF == 0)
                        && lhs & 0x8000 != 0
                        && (op == BinOp::FAdd) == (rhs & 0x8000 != 0);
                    return Some(if neg { 0x8000 } else { 0x0000 });
                }
                Some(oracle_round(sum < 0, sum.unsigned_abs(), 24, false))
            }
            BinOp::FMul => {
                let product = a * b;
                let negative = (lhs ^ rhs) & 0x8000 != 0;
                Some(oracle_round(negative, product.unsigned_abs(), 48, false))
            }
            BinOp::FDiv => {
                if b == 0 {
                    return None;
                }
                let negative = (lhs ^ rhs) & 0x8000 != 0;
                if a == 0 {
                    return Some(if negative { 0x8000 } else { 0 });
                }
                // a / b = (|a| * 2^64 / |b|) * 2^-64; the remainder is the
                // sticky bit.
                let scaled = a.unsigned_abs() << 64;
                let quotient = scaled / b.unsigned_abs();
                let sticky = scaled % b.unsigned_abs() != 0;
                Some(oracle_round(negative, quotient, 64, sticky))
            }
            _ => unreachable!(),
        }
    }
    let mut rng = Rng::new(0x2f16_0215);
    let mut compared = 0u32;
    for _ in 0..3000 {
        // Bias toward the edges: a quarter of the operands come from the
        // subnormal range, a quarter from the top binade.
        let pick = |rng: &mut Rng| -> u16 {
            let sign = u16::from(rng.bool()) << 15;
            match rng.bounded(4) {
                0 => sign | rng.bounded(0x400) as u16,
                1 => sign | 0x7800 | rng.bounded(0x400) as u16,
                _ => {
                    let bits = rng.bounded(0x10000) as u16;
                    if bits & 0x7C00 == 0x7C00 {
                        bits & !0x7C00
                    } else {
                        bits
                    }
                }
            }
        };
        let (lhs, rhs) = (pick(&mut rng), pick(&mut rng));
        for op in [BinOp::FAdd, BinOp::FSub, BinOp::FMul, BinOp::FDiv] {
            let Some(expected) = oracle(op, lhs, rhs) else {
                continue;
            };
            let got = f16_row_bits(&F16Row::Bin(op, lhs, rhs));
            assert_eq!(
                got, expected,
                "{op:?} {lhs:#06x} {rhs:#06x}: interpreter {got:#06x}, oracle {expected:#06x}"
            );
            compared += 1;
        }
    }
    assert!(compared > 10_000, "compared {compared} pairs");
}

// ───────────────────────── review: adversarial shapes ─────────────────────────

/// A `<4 x f16>` add rounds EACH lane once: the overflow tie, the
/// round-down beside it, the positive fixture and a signed-zero lane in one
/// vector value. A lane path that reached binary16 through the binary64 arm
/// (no final rounding) or through a per-lane width confusion would differ in
/// at least the second lane.
#[test]
fn f16_vector_lanes_each_round_once() {
    use trust_ir::Constant;
    let vec_ty = Ty::Vector(Box::new(Ty::F16), 4);
    let lanes = |bits: [u16; 4]| {
        Constant::Vector(
            bits.iter()
                .map(|b| Constant::Float(f16_bits_to_f64(*b)))
                .collect(),
        )
    };
    let (m, f) = build_nullary(vec![vec_ty.clone()], |fb| {
        let a = fb.const_value(vec_ty.clone(), lanes([0x7BFF, 0x7BFF, 0x3E00, 0x0000]));
        let b = fb.const_value(vec_ty.clone(), lanes([0x4800, 0x4C00, 0x4080, 0x8000]));
        vec![fb.binop(BinOp::FAdd, vec_ty.clone(), a, b)]
    });
    let out = run(&m, f);
    let InterpretValueKind::Vector(values) = &out[0].kind else {
        panic!("expected a vector, got {:?}", out[0].kind);
    };
    let got: Vec<u16> = values.iter().map(f16_return).collect();
    assert_eq!(
        got,
        vec![0x7BFF, 0x7C00, 0x4380, 0x0000],
        "max+8 -> 65504, max+16 -> +inf (tie to even), 1.5+2.25 = 3.75, (+0)+(-0) = +0"
    );
}

/// A host model that answers an `F16` declaration with a pattern wider than
/// 16 bits is refused as a malformed result (the same rule `F32` has at 32
/// bits): a buggy host cannot smuggle a 64-bit pattern into a binary16 slot,
/// where every consumer would silently read only its low half.
#[test]
fn a_host_result_at_f16_wider_than_sixteen_bits_is_malformed() {
    use trust_ir::Function;
    use trust_ir::interpret::{HostCalls, HostState, InterpretResult};
    use trust_ir::ty::FuncTy;

    struct WideHost(u64);
    impl HostCalls for WideHost {
        fn call(
            &self,
            _callee: &Function,
            _sig: &FuncTy,
            _args: &[InterpretValue],
            _host: &mut HostState,
        ) -> Option<InterpretResult<Vec<InterpretValue>>> {
            Some(Ok(vec![InterpretValue {
                ty: Ty::F16,
                kind: InterpretValueKind::FloatBits(self.0),
            }]))
        }
    }

    let mut mb = ModuleBuilder::new_with_target_info(
        "ws2_15_f16_host",
        trust_ir::TargetInfo {
            triple: "aarch64-apple-darwin".into(),
            pointer_size: 8,
            endianness: trust_ir::Endianness::Little,
            abi: Some("aapcs64".into()),
            struct_passing: trust_ir::StructPassingPolicy::NativeC,
        },
    );
    let ext_sig = mb.add_func_type(vec![], vec![Ty::F16]);
    let ext = mb.declare_function("half_source", ext_sig);
    let caller = {
        let mut fb = mb.function("caller", ext_sig);
        let entry = fb.create_block();
        fb.switch_to_block(entry);
        let x = fb.call(ext, vec![]);
        fb.ret(vec![x]);
        fb.build()
    };
    let module = mb.build().expect("ModuleBuilder::build: test fixture");
    assert_eq!(validate_module(&module), vec![]);

    let good = WideHost(0x4380);
    let out = Interpreter::with_module(&module)
        .with_host(&good)
        .execute_func(caller, [])
        .expect("a 16-bit pattern is a well-formed F16 host result");
    assert_eq!(f16_return(&out.returns[0]), 0x4380);

    let wide = WideHost(0x0001_4380);
    let error = Interpreter::with_module(&module)
        .with_host(&wide)
        .execute_func(caller, [])
        .expect_err("a 17-bit pattern is not a binary16 value");
    assert_eq!(error.code, InterpretErrorCode::TypeError, "{error:?}");
    assert!(
        error
            .message
            .contains("host result 0 is not a well-formed f16 value"),
        "{}",
        error.message
    );
}

/// `FSqrt` at binary16, EXHAUSTIVE over every finite non-negative pattern,
/// against an integer square-root oracle with a sticky remainder (no float
/// arithmetic): the binary32 `sqrt` followed by one binary16 rounding must be
/// the correctly rounded binary16 square root everywhere, not just at the
/// one table row — the innocuous-double-rounding argument (24 >= 2·11 + 2)
/// covers `sqrt`, and this is the check that it was applied, not assumed.
#[test]
fn f16_sqrt_is_correctly_rounded_for_every_finite_pattern() {
    fn isqrt(n: u128) -> u128 {
        if n < 2 {
            return n;
        }
        let mut x = 1u128 << (n.ilog2() / 2 + 1);
        loop {
            let y = (x + n / x) / 2;
            if y >= x {
                return x;
            }
            x = y;
        }
    }
    // `v = units * 2^-24`; `sqrt(v) = sqrt(units * 2^80) * 2^-52`, and the
    // 40 extra doubling bits leave 2^41 units with 2^121 < 2^128 headroom.
    for bits in 0x0000..=0x7BFFu16 {
        let scaled = units(bits).unsigned_abs() << 80;
        let root = isqrt(scaled);
        let sticky = root * root != scaled;
        let expected = oracle_round(false, root, 52, sticky);
        let got = f16_row_bits(&F16Row::Un(UnOp::FSqrt, bits));
        assert_eq!(
            got, expected,
            "sqrt {bits:#06x}: interpreter {got:#06x}, oracle {expected:#06x}"
        );
    }
    // The two other finite operands: -0 keeps its sign, and a negative value
    // is a NaN.
    assert_eq!(f16_row_bits(&F16Row::Un(UnOp::FSqrt, 0x8000)), 0x8000);
    let nan = f16_row_bits(&F16Row::Un(UnOp::FSqrt, 0xBC00));
    assert_eq!(nan & 0x7C00, 0x7C00);
    assert_ne!(nan & 0x03FF, 0);
}

/// `FDiv` across the whole 1024-point significand grid of the dividend
/// against a spread of divisors, in two dividend binades: `[1, 2)`, where
/// every quotient is a normal binary16 value, and `[2^-14, 2^-13)`, where
/// every quotient is a binary16 SUBNORMAL while the binary32 intermediate is
/// still normal — the case where the destination's effective precision is
/// below 11 and the innocuous-double-rounding bound is at its loosest. Each
/// row is checked against the exact integer oracle (`(a << 64) / b` with a
/// sticky remainder), so a rounder that got gradual underflow wrong through
/// division, not just through the table's constant rows, is caught here.
#[test]
fn f16_div_is_correctly_rounded_across_the_significand_grid() {
    fn oracle(lhs: u16, rhs: u16) -> u16 {
        let (a, b) = (units(lhs).unsigned_abs(), units(rhs).unsigned_abs());
        let scaled = a << 64;
        oracle_round(false, scaled / b, 64, scaled % b != 0)
    }
    let divisors: [u16; 16] = [
        0x3C00, 0x3C01, 0x3C02, 0x3C03, 0x3D55, 0x3E00, 0x3E01, 0x3EAB, 0x3F00, 0x3FFD, 0x3FFE,
        0x3FFF, 0x4000, 0x4001, 0x43FF, 0x7BFF,
    ];
    let mut compared = 0u32;
    for base in [0x3C00u16, 0x0400] {
        for significand in 0..0x400u16 {
            let lhs = base | significand;
            for rhs in divisors {
                let expected = oracle(lhs, rhs);
                let got = f16_row_bits(&F16Row::Bin(BinOp::FDiv, lhs, rhs));
                assert_eq!(
                    got, expected,
                    "{lhs:#06x} / {rhs:#06x}: interpreter {got:#06x}, oracle {expected:#06x}"
                );
                compared += 1;
            }
        }
    }
    assert_eq!(compared, 2 * 1024 * 16);
}

// ─────────────────── second review: adversarial shapes ───────────────────

/// `FCopySign` (WS3.20, landed beside this item) at `F16`. The first cut of
/// the binary16 binop arm listed only the rounded ops, so `fcopysign f16`
/// fell to the catch-all and was refused as a `TypeError` "integer binop" —
/// a legitimate, validating module refused under a false reason. It is a
/// sign-bit operation on the pattern (IEEE 754 §5.5.1): no rounding, the NaN
/// payload kept, and a SIGNALLING NaN not quieted (which a route through the
/// binary32 widening and `f64_to_f16_bits` would do).
#[test]
fn f16_copysign_is_a_sign_bit_operation_on_the_pattern() {
    let (m, f) = build_nullary(vec![Ty::F16, Ty::F16, Ty::F16, Ty::F16], |fb| {
        let one_and_half = h(fb, 0x3E00);
        let neg_zero = h(fb, 0x8000);
        let pos_one = h(fb, 0x3C00);
        let neg_one = h(fb, 0xBC00);
        let snan_bits = fb.uconst(Ty::U16, 0x7C01);
        let snan = fb.cast(CastOp::Bitcast, Ty::U16, Ty::F16, snan_bits);
        let qnan_bits = fb.uconst(Ty::U16, 0xFE2A);
        let qnan = fb.cast(CastOp::Bitcast, Ty::U16, Ty::F16, qnan_bits);
        let max = h(fb, 0x7BFF);
        vec![
            fb.binop(BinOp::FCopySign, Ty::F16, one_and_half, neg_zero),
            fb.binop(BinOp::FCopySign, Ty::F16, snan, neg_one),
            fb.binop(BinOp::FCopySign, Ty::F16, qnan, pos_one),
            fb.binop(BinOp::FCopySign, Ty::F16, max, qnan),
        ]
    });
    let bits: Vec<u16> = run(&m, f).iter().map(f16_return).collect();
    assert_eq!(bits, vec![0xBE00, 0xFC01, 0x7E2A, 0xFBFF]);
}

/// A `FPTrunc F64 -> F16` must round ONCE from the binary64 value. The
/// operand `1 + 2^-11 + 2^-40` sits just ABOVE the binary16 tie between
/// `1.0` and `1 + 2^-10`, so the correct answer rounds up (`0x3C01`); an
/// implementation that narrows through binary32 first loses the `2^-40`
/// sticky bit (below the binary32 ulp at 1.0), lands exactly ON the tie, and
/// rounds to even (`0x3C00`). The same trap from binary32 cannot fire (the
/// widening is exact), which the second lane pins.
#[test]
fn f16_fptrunc_from_f64_does_not_double_round_through_binary32() {
    let (m, f) = build_nullary(vec![Ty::F16, Ty::F16, Ty::F16], |fb| {
        let above_tie = fb.fconst(Ty::F64, 1.0 + 2f64.powi(-11) + 2f64.powi(-40));
        let on_tie = fb.fconst(Ty::F64, 1.0 + 2f64.powi(-11));
        let f32_above = fb.fconst(Ty::F32, f64::from(1.0f32 + 2f32.powi(-11) + 2f32.powi(-23)));
        vec![
            fb.cast(CastOp::FPTrunc, Ty::F64, Ty::F16, above_tie),
            fb.cast(CastOp::FPTrunc, Ty::F64, Ty::F16, on_tie),
            fb.cast(CastOp::FPTrunc, Ty::F32, Ty::F16, f32_above),
        ]
    });
    let bits: Vec<u16> = run(&m, f).iter().map(f16_return).collect();
    assert_eq!(bits, vec![0x3C01, 0x3C00, 0x3C01]);
}

/// Integer -> `F16` at the overflow edge, from every integer width class:
/// `65519` is below the `65520` tie (-> `65504`), `65520` is the tie (-> `+inf`),
/// and the extreme 64/128-bit values overflow to the signed infinity rather
/// than wrapping, saturating to `65504`, or erroring. `-2049` is a tie at the
/// 2048 binade (spacing 2) and rounds to the even neighbour `-2048`.
#[test]
fn f16_int_to_float_rounds_once_at_the_edges() {
    let (m, f) = build_nullary(vec![Ty::F16; 6], |fb| {
        let below = fb.iconst(Ty::I32, 65519);
        let tie = fb.uconst(Ty::U32, 65520);
        let umax = fb.uconst(Ty::U64, u128::from(u64::MAX));
        let imin = fb.iconst(Ty::I128, i128::MIN);
        let neg_tie = fb.iconst(Ty::I16, -2049);
        let small = fb.uconst(Ty::U8, 255);
        vec![
            fb.cast(CastOp::SIToFP, Ty::I32, Ty::F16, below),
            fb.cast(CastOp::UIToFP, Ty::U32, Ty::F16, tie),
            fb.cast(CastOp::UIToFP, Ty::U64, Ty::F16, umax),
            fb.cast(CastOp::SIToFP, Ty::I128, Ty::F16, imin),
            fb.cast(CastOp::SIToFP, Ty::I16, Ty::F16, neg_tie),
            fb.cast(CastOp::UIToFP, Ty::U8, Ty::F16, small),
        ]
    });
    let bits: Vec<u16> = run(&m, f).iter().map(f16_return).collect();
    assert_eq!(bits, vec![0x7BFF, 0x7C00, 0x7C00, 0xFC00, 0xE800, 0x5BF8]);
}

/// `FMin`/`FMax` at `F16` agree with the binary32/binary64 arms on a NaN
/// operand (the non-NaN operand wins), and return the operand's exact
/// pattern — a subnormal comes back unrounded.
#[test]
fn f16_min_max_return_the_non_nan_operand_exactly() {
    let (m, f) = build_nullary(vec![Ty::F16, Ty::F16, Ty::F16], |fb| {
        let nan_bits = fb.uconst(Ty::U16, 0x7E00);
        let nan = fb.cast(CastOp::Bitcast, Ty::U16, Ty::F16, nan_bits);
        let two = h(fb, 0x4000);
        let tiny = h(fb, 0x0001);
        let neg_tiny = h(fb, 0x8001);
        vec![
            fb.binop(BinOp::FMin, Ty::F16, nan, two),
            fb.binop(BinOp::FMax, Ty::F16, tiny, nan),
            fb.binop(BinOp::FMin, Ty::F16, tiny, neg_tiny),
        ]
    });
    let bits: Vec<u16> = run(&m, f).iter().map(f16_return).collect();
    assert_eq!(bits, vec![0x4000, 0x0001, 0x8001]);
}
