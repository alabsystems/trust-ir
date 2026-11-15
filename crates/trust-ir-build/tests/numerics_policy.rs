// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0
//
// Locks the reference interpreter to the ratified numerics/UB policy
// (docs/ub-numerics-policy.md): the LLVM/Rust model where out-of-domain
// shifts and divisions are undefined behavior (not masked / not total),
// `Add/Sub/Mul` wrap two's-complement, integer division truncates toward
// zero, and the `Overflow` flag is computed against operand signedness.
//
// These tests are the verifiable half of the interpreter<->Lean
// reconciliation: the Lean semantics in TrustIr/Semantics/Arith.lean must be
// brought into agreement with what is asserted here (tracked in
// docs/ub-numerics-policy.md section 7).

use trust_ir::Module;
use trust_ir::inst::{BinOp, CastOp, OverflowOp};
use trust_ir::interpret::{InterpretErrorCode, InterpretValueKind, Interpreter};
use trust_ir::ty::Ty;
use trust_ir::value::FuncId;
use trust_ir_build::ModuleBuilder;

/// Build a zero-argument function whose body is produced by `body`, which
/// returns the `ValueId`s to return and the function's return types.
fn build_nullary<F>(ret_tys: Vec<Ty>, body: F) -> (Module, FuncId)
where
    F: FnOnce(&mut trust_ir_build::FunctionBuilder<'_>) -> Vec<trust_ir::value::ValueId>,
{
    let mut mb = ModuleBuilder::new("numerics_policy");
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

fn run_signed(module: &Module, fid: FuncId) -> Result<i128, InterpretErrorCode> {
    match Interpreter::with_module(module).execute_func(fid, []) {
        Ok(outcome) => Ok(outcome.returns[0].as_int().expect("int return").as_signed()),
        Err(e) => Err(e.code),
    }
}

fn run_bool(module: &Module, fid: FuncId) -> bool {
    let outcome = Interpreter::with_module(module)
        .execute_func(fid, [])
        .expect("execution succeeds");
    match outcome.returns[0].kind {
        InterpretValueKind::Bool(b) => b,
        ref other => panic!("expected bool return, got {other:?}"),
    }
}

fn run_f64_bits(module: &Module, fid: FuncId) -> u64 {
    let outcome = Interpreter::with_module(module)
        .execute_func(fid, [])
        .expect("execution succeeds");
    match outcome.returns[0].kind {
        InterpretValueKind::FloatBits(bits) => bits,
        ref other => panic!("expected float return, got {other:?}"),
    }
}

/// Interpreter `FRem` on `f64` operand BIT PATTERNS, returning the result's
/// bit pattern (the interpreter stores floats as `FloatBits`, so this is
/// bit-exact end to end).
fn frem_f64_bits(lhs: u64, rhs: u64) -> u64 {
    let (m, f) = build_nullary(vec![Ty::F64], |fb| {
        let a = fb.fconst(Ty::F64, f64::from_bits(lhs));
        let b = fb.fconst(Ty::F64, f64::from_bits(rhs));
        vec![fb.binop(BinOp::FRem, Ty::F64, a, b)]
    });
    run_f64_bits(&m, f)
}

#[test]
fn shift_amount_at_or_above_width_is_ub() {
    // i32 << 32 : shift amount == bit width -> UB (NOT masked to 0).
    let (m, f) = build_nullary(vec![Ty::I32], |fb| {
        let x = fb.iconst(Ty::I32, 1);
        let amt = fb.iconst(Ty::I32, 32);
        vec![fb.binop(BinOp::Shl, Ty::I32, x, amt)]
    });
    assert_eq!(
        run_signed(&m, f),
        Err(InterpretErrorCode::UndefinedBehavior)
    );
}

#[test]
fn sdiv_int_min_by_minus_one_is_ub() {
    let (m, f) = build_nullary(vec![Ty::I32], |fb| {
        let min = fb.iconst(Ty::I32, i128::from(i32::MIN));
        let neg1 = fb.iconst(Ty::I32, -1);
        vec![fb.binop(BinOp::SDiv, Ty::I32, min, neg1)]
    });
    assert_eq!(
        run_signed(&m, f),
        Err(InterpretErrorCode::UndefinedBehavior)
    );
}

#[test]
fn division_by_zero_is_ub() {
    let (m, f) = build_nullary(vec![Ty::I32], |fb| {
        let x = fb.iconst(Ty::I32, 10);
        let zero = fb.iconst(Ty::I32, 0);
        vec![fb.binop(BinOp::SDiv, Ty::I32, x, zero)]
    });
    assert_eq!(
        run_signed(&m, f),
        Err(InterpretErrorCode::UndefinedBehavior)
    );
}

#[test]
fn sdiv_truncates_toward_zero() {
    // -7 / 2 == -3 (truncating), NOT -4 (flooring/Euclidean).
    let (m, f) = build_nullary(vec![Ty::I32], |fb| {
        let a = fb.iconst(Ty::I32, -7);
        let b = fb.iconst(Ty::I32, 2);
        vec![fb.binop(BinOp::SDiv, Ty::I32, a, b)]
    });
    assert_eq!(run_signed(&m, f), Ok(-3));
}

#[test]
fn srem_has_dividend_sign_truncating() {
    // -7 % 3 == -1 (truncating), NOT 2 (Euclidean).
    let (m, f) = build_nullary(vec![Ty::I32], |fb| {
        let a = fb.iconst(Ty::I32, -7);
        let b = fb.iconst(Ty::I32, 3);
        vec![fb.binop(BinOp::SRem, Ty::I32, a, b)]
    });
    assert_eq!(run_signed(&m, f), Ok(-1));
}

#[test]
fn add_wraps_twos_complement() {
    // i8: 127 + 1 == -128 (wrapping).
    let (m, f) = build_nullary(vec![Ty::I8], |fb| {
        let a = fb.iconst(Ty::I8, 127);
        let b = fb.iconst(Ty::I8, 1);
        vec![fb.binop(BinOp::Add, Ty::I8, a, b)]
    });
    assert_eq!(run_signed(&m, f), Ok(-128));
}

#[test]
fn overflow_flag_uses_signed_semantics_for_signed_type() {
    // i8 AddOverflow 127 + 1 overflows the signed range.
    let (m, f) = build_nullary(vec![Ty::Bool], |fb| {
        let a = fb.iconst(Ty::I8, 127);
        let b = fb.iconst(Ty::I8, 1);
        let (_v, flag) = fb.overflow(OverflowOp::AddOverflow, Ty::I8, a, b);
        vec![flag]
    });
    assert!(run_bool(&m, f), "127+1 must flag signed overflow for i8");
}

#[test]
fn overflow_flag_uses_unsigned_semantics_for_unsigned_type() {
    // u8 AddOverflow 200 + 100 overflows the unsigned range (== 300 > 255),
    // while the same bit pattern would NOT be a signed overflow. The flag must
    // follow the operand's (unsigned) type.
    let (m, f) = build_nullary(vec![Ty::Bool], |fb| {
        let a = fb.iconst(Ty::U8, 200);
        let b = fb.iconst(Ty::U8, 100);
        let (_v, flag) = fb.overflow(OverflowOp::AddOverflow, Ty::U8, a, b);
        vec![flag]
    });
    assert!(
        run_bool(&m, f),
        "200+100 must flag unsigned overflow for u8"
    );
}

// ---------------------------------------------------------------------------
// Assert condition typing (docs/ub-numerics-policy.md §4).
//
// `Assert` requires a Bool condition. A non-bool condition (including a
// nonzero integer) is a TYPE ERROR, not a truthiness test — matching
// validation (validate.rs check_predicate_is_bool). The Lean semantics is
// locked to the same behavior by the assert_*_stable fixtures in
// Semantics/ExecutableFixtures.lean.
// ---------------------------------------------------------------------------

#[test]
fn assert_true_bool_passes() {
    let (m, f) = build_nullary(vec![Ty::I32], |fb| {
        let cond = fb.bool_const(true);
        fb.assert(cond);
        vec![fb.iconst(Ty::I32, 7)]
    });
    assert_eq!(run_signed(&m, f), Ok(7));
}

#[test]
fn assert_false_bool_is_panic_trap() {
    // panic = abort: a failed Assert is a deterministic trap (Panic), never a
    // silent continue and never UB.
    let (m, f) = build_nullary(vec![Ty::I32], |fb| {
        let cond = fb.bool_const(false);
        fb.assert(cond);
        vec![fb.iconst(Ty::I32, 7)]
    });
    assert_eq!(run_signed(&m, f), Err(InterpretErrorCode::Panic));
}

#[test]
fn assert_nonzero_int_condition_is_type_error_not_pass() {
    let (m, f) = build_nullary(vec![Ty::I32], |fb| {
        let cond = fb.iconst(Ty::I32, 1);
        fb.assert(cond);
        vec![fb.iconst(Ty::I32, 7)]
    });
    assert_eq!(run_signed(&m, f), Err(InterpretErrorCode::TypeError));
}

#[test]
fn assert_zero_int_condition_is_type_error_not_panic() {
    let (m, f) = build_nullary(vec![Ty::I32], |fb| {
        let cond = fb.iconst(Ty::I32, 0);
        fb.assert(cond);
        vec![fb.iconst(Ty::I32, 7)]
    });
    assert_eq!(run_signed(&m, f), Err(InterpretErrorCode::TypeError));
}

// ---------------------------------------------------------------------------
// FRem differential lock (docs/ub-numerics-policy.md §2).
//
// `FRem` is C `fmod` / LLVM `frem` / Rust `%`: the truncating remainder with
// the dividend's sign, which is EXACTLY specified (the true remainder is
// always representable in the operand format). The bit patterns asserted here
// are the libm fmod results; the Lean semantics computes the same values with
// exact integer arithmetic (`floatFRem` in Semantics/Arith.lean) and locks
// the SAME operand/result bits via the `frem_*_stable` native_decide fixtures
// in Semantics/ExecutableFixtures.lean. If either engine drifts, one side of
// this differential pair fails.
// ---------------------------------------------------------------------------

#[test]
fn frem_is_truncating_fmod_bit_exact() {
    // (name, lhs bits, rhs bits, expected fmod bits)
    let cases: &[(&str, u64, u64, u64)] = &[
        // 5.25 % 2.0 = 1.25
        (
            "pos_simple",
            0x4015000000000000,
            0x4000000000000000,
            0x3ff4000000000000,
        ),
        // -7.5 % 2.25 = -0.75 (dividend's sign)
        (
            "neg_dividend",
            0xc01e000000000000,
            0x4002000000000000,
            0xbfe8000000000000,
        ),
        // 7.5 % -2.25 = +0.75 (divisor's sign ignored)
        (
            "neg_divisor",
            0x401e000000000000,
            0xc002000000000000,
            0x3fe8000000000000,
        ),
        // -5.5 % -2.0 = -1.5
        (
            "both_negative",
            0xc016000000000000,
            0xc000000000000000,
            0xbff8000000000000,
        ),
        // 6.75 % 1.1 = 0.14999999999999947 (non-dyadic decimal divisor)
        (
            "non_dyadic_divisor",
            0x401b000000000000,
            0x3ff199999999999a,
            0x3fc3333333333320,
        ),
        // 1e308 % 3.0 = 2.0 (a rounded x - trunc(x/y)*y formula collapses to 0)
        (
            "huge_dividend",
            0x7fe1ccf385ebc8a0,
            0x4008000000000000,
            0x4000000000000000,
        ),
        // 1e308 % 1e-308 = 3.498445546245627e-309 (subnormal result; a rounded
        // formula overflows the intermediate quotient to inf)
        (
            "huge_by_tiny",
            0x7fe1ccf385ebc8a0,
            0x000730d67819e8d2,
            0x00028401cf53d610,
        ),
        // 1.0 % (3 * 2^-1074) = 2^-1074 (minimum positive subnormal)
        (
            "subnormal_divisor",
            0x3ff0000000000000,
            0x0000000000000003,
            0x0000000000000001,
        ),
        // -0.0 % 3.0 = -0.0 (zero dividend keeps its sign)
        (
            "neg_zero_dividend",
            0x8000000000000000,
            0x4008000000000000,
            0x8000000000000000,
        ),
        // -6.0 % 3.0 = -0.0 (a zero REMAINDER keeps the dividend's sign)
        (
            "zero_rem_neg_dividend",
            0xc018000000000000,
            0x4008000000000000,
            0x8000000000000000,
        ),
        // 5.0 % inf = 5.0 (finite % infinite returns the dividend)
        (
            "finite_by_inf",
            0x4014000000000000,
            0x7ff0000000000000,
            0x4014000000000000,
        ),
    ];
    for &(name, lhs, rhs, expected) in cases {
        let got = frem_f64_bits(lhs, rhs);
        assert_eq!(
            got, expected,
            "{name}: fmod(0x{lhs:016x}, 0x{rhs:016x}) = 0x{got:016x}, expected 0x{expected:016x}"
        );
        // The asserted bits are what this platform's libm fmod produces.
        let libm = (f64::from_bits(lhs) % f64::from_bits(rhs)).to_bits();
        assert_eq!(got, libm, "{name}: interpreter disagrees with libm fmod");
    }
}

#[test]
fn frem_domain_errors_are_nan_values_not_ub() {
    // inf % 3.0 and 5.0 % 0.0 are NaN VALUES (C fmod domain error), not UB.
    // NaN payload/sign bits are platform noise and are deliberately not pinned.
    for &(name, lhs, rhs) in &[
        ("inf_dividend", 0x7ff0000000000000u64, 0x4008000000000000u64),
        ("mod_zero", 0x4014000000000000, 0x0000000000000000),
        ("nan_dividend", 0x7ff8000000000000, 0x4008000000000000),
    ] {
        let got = frem_f64_bits(lhs, rhs);
        assert!(
            f64::from_bits(got).is_nan(),
            "{name}: expected NaN, got 0x{got:016x}"
        );
    }
}

/// Mirror of the Lean `floatFRem` exact integer algorithm
/// (lean/trust_ir-semantics/TrustIr/Semantics/Arith.lean): decompose both
/// operands into normalized dyadics `m * 2^e` with `m` in `[2^52, 2^53)`,
/// take the integer remainder `(mx << (ex - ey)) % my`, and rescale. The
/// only difference is that the shift is folded modulo `my` (mod-pow) so the
/// big integer is never materialized — `(mx << s) % my == (mx * 2^s) % my`.
fn lean_frem_exact_alg(x: f64, y: f64) -> f64 {
    fn dyadic_norm(f: f64) -> (u64, i64) {
        let bits = f.to_bits();
        let biased = ((bits >> 52) & 0x7ff) as i64;
        let frac = bits & ((1u64 << 52) - 1);
        let (mut m, mut e) = if biased == 0 {
            (frac, -1074)
        } else {
            (frac | (1u64 << 52), biased - 1075)
        };
        while m < (1u64 << 52) {
            m <<= 1;
            e -= 1;
        }
        (m, e)
    }
    fn ldexp_exact(r: u64, e: i64) -> f64 {
        // r < 2^53 converts exactly; split the scale so each step's
        // power-of-two factor is a normal number (the product is exact
        // because the final value is representable).
        let step = |v: f64, e: i64| v * f64::from_bits(((e + 1023) as u64) << 52);
        if (-1022..=1023).contains(&e) {
            step(r as f64, e)
        } else if e < -1022 {
            step(step(r as f64, -1022), e + 1022)
        } else {
            step(step(r as f64, 1023), e - 1023)
        }
    }
    if x.is_nan() || y.is_nan() {
        return f64::NAN;
    }
    if x.is_infinite() || y == 0.0 {
        return f64::NAN;
    }
    if y.is_infinite() || x == 0.0 {
        return x;
    }
    let (ax, ay) = (x.abs(), y.abs());
    if ax < ay {
        return x;
    }
    let (mx, ex) = dyadic_norm(ax);
    let (my, ey) = dyadic_norm(ay);
    debug_assert!(ex >= ey, "|x| >= |y| forces ex >= ey");
    // r = (mx << (ex - ey)) % my via mod-pow; products < 2^106 fit in u128.
    let myu = u128::from(my);
    let mut pow2: u128 = 1;
    let mut base: u128 = 2 % myu;
    let mut s = (ex - ey) as u64;
    while s > 0 {
        if s & 1 == 1 {
            pow2 = pow2 * base % myu;
        }
        base = base * base % myu;
        s >>= 1;
    }
    let r = ((u128::from(mx) % myu) * pow2 % myu) as u64;
    let mag = ldexp_exact(r, ey);
    if x < 0.0 { -mag } else { mag }
}

#[test]
fn frem_exact_integer_algorithm_matches_libm_fmod() {
    // The exactness claim behind the Lean floatFRem: the integer algorithm is
    // bit-identical to libm fmod. Locked over a structured edge sweep plus
    // 2,000,000 deterministic pseudo-random f64 bit-pattern pairs.
    let agree = |a: f64, b: f64| {
        let r = a % b;
        let n = lean_frem_exact_alg(a, b);
        (r.is_nan() && n.is_nan()) || r.to_bits() == n.to_bits()
    };

    let edges: &[f64] = &[
        0.0,
        -0.0,
        f64::from_bits(1),                  // min positive subnormal
        f64::from_bits(0x000fffffffffffff), // max subnormal
        f64::MIN_POSITIVE,
        1.0,
        -1.0,
        1.5,
        3.0,
        1.1,
        -7.5,
        2.25,
        1e-308,
        1e308,
        f64::MAX,
        f64::MIN,
        f64::INFINITY,
        f64::NEG_INFINITY,
        f64::NAN,
    ];
    for &a in edges {
        for &b in edges {
            assert!(
                agree(a, b),
                "edge sweep: fmod({a:?}, {b:?}) = {:?} but exact algorithm gives {:?}",
                a % b,
                lean_frem_exact_alg(a, b)
            );
        }
    }

    // Deterministic xorshift64* over raw bit patterns (hits NaNs, infs,
    // subnormals, and wild magnitude ratios).
    let mut state: u64 = 0x9E37_79B9_7F4A_7C15;
    let mut next = || {
        state ^= state << 13;
        state ^= state >> 7;
        state ^= state << 17;
        state
    };
    for i in 0..2_000_000 {
        let a = f64::from_bits(next());
        let b = f64::from_bits(next());
        assert!(
            agree(a, b),
            "fuzz #{i}: fmod(0x{:016x}, 0x{:016x}) = 0x{:016x} but exact algorithm gives 0x{:016x}",
            a.to_bits(),
            b.to_bits(),
            (a % b).to_bits(),
            lean_frem_exact_alg(a, b).to_bits()
        );
    }
}

#[test]
fn fp_to_si_in_range_truncates() {
    // 42.9 -> i32 truncates toward zero to 42 (in range, defined).
    let (m, f) = build_nullary(vec![Ty::I32], |fb| {
        let x = fb.fconst(Ty::F64, 42.9);
        vec![fb.cast(CastOp::FPToSI, Ty::F64, Ty::I32, x)]
    });
    assert_eq!(run_signed(&m, f), Ok(42));
}

#[test]
fn fp_to_si_nan_is_ub() {
    let (m, f) = build_nullary(vec![Ty::I32], |fb| {
        let x = fb.fconst(Ty::F64, f64::NAN);
        vec![fb.cast(CastOp::FPToSI, Ty::F64, Ty::I32, x)]
    });
    assert_eq!(
        run_signed(&m, f),
        Err(InterpretErrorCode::UndefinedBehavior)
    );
}

#[test]
fn fp_to_si_out_of_range_is_ub() {
    // 1e30 is far beyond i32::MAX -> UB (NOT saturated).
    let (m, f) = build_nullary(vec![Ty::I32], |fb| {
        let x = fb.fconst(Ty::F64, 1e30);
        vec![fb.cast(CastOp::FPToSI, Ty::F64, Ty::I32, x)]
    });
    assert_eq!(
        run_signed(&m, f),
        Err(InterpretErrorCode::UndefinedBehavior)
    );
}

#[test]
fn fp_to_ui_negative_is_ub() {
    // A negative float into an unsigned int is out of range -> UB.
    let (m, f) = build_nullary(vec![Ty::U32], |fb| {
        let x = fb.fconst(Ty::F64, -1.0);
        vec![fb.cast(CastOp::FPToUI, Ty::F64, Ty::U32, x)]
    });
    assert_eq!(
        run_signed(&m, f),
        Err(InterpretErrorCode::UndefinedBehavior)
    );
}

// ---------------------------------------------------------------------------
// WS2.23: per-width float semantics and float memory images, cross-engine.
//
// `F32` is the IEEE binary32 operation (docs/ub-numerics-policy.md §2): the
// interpreter runs it in `f32`; the Lean model computes in binary64 and rounds
// ONCE to binary32 (`roundToFormat`, lean/trust_ir-semantics/TrustIr/
// Semantics/FloatFormat.lean). The table below is the Rust half of ONE shared
// table; the Lean half is the `f32_table_*` theorems in
// lean/trust_ir-semantics/TrustIr/Semantics/FloatFixtures.lean, and
// `f32_cross_engine_table_matches_lean_fixtures` checks the two agree row by
// row (same name, same expected bits, no row on one side only).
// ---------------------------------------------------------------------------

/// One row's operation. Operands are bit patterns, so nothing is parsed.
#[derive(Clone, Debug)]
enum F32Row {
    /// `BinOp op F32` over two binary32 operands.
    Bin(BinOp, u32, u32),
    /// `Cast FPTrunc F64 -> F32` of a binary64 operand.
    Trunc(u64),
    /// `Cast UIToFP src -> F32` of an unsigned integer.
    UiToFp(Ty, i128),
    /// `Cast SIToFP src -> F32` of a signed integer.
    SiToFp(Ty, i128),
}

/// (row name == Lean `f32_table_<name>`, operation, expected binary32 bits).
const F32_CROSS_ENGINE_TABLE: &[(&str, F32Row, u32)] = &[
    (
        "fadd_0_1_0_2",
        F32Row::Bin(BinOp::FAdd, 0x3dcc_cccd, 0x3e4c_cccd),
        0x3e99_999a,
    ),
    (
        "fsub_one_minus_half_ulp",
        F32Row::Bin(BinOp::FSub, 0x3f80_0000, 0x3380_0000),
        0x3f7f_ffff,
    ),
    (
        "fmul_0_1_squared",
        F32Row::Bin(BinOp::FMul, 0x3dcc_cccd, 0x3dcc_cccd),
        0x3c23_d70b,
    ),
    (
        "fdiv_one_third",
        F32Row::Bin(BinOp::FDiv, 0x3f80_0000, 0x4040_0000),
        0x3eaa_aaab,
    ),
    (
        "frem_5_25_by_2",
        F32Row::Bin(BinOp::FRem, 0x40a8_0000, 0x4000_0000),
        0x3fa0_0000,
    ),
    (
        "fmul_overflow_to_inf",
        F32Row::Bin(BinOp::FMul, 0x7f7f_ffff, 0x4000_0000),
        0x7f80_0000,
    ),
    (
        "fmul_to_subnormal",
        F32Row::Bin(BinOp::FMul, 0x0080_0000, 0x3f00_0000),
        0x0040_0000,
    ),
    (
        "fdiv_half_least_subnormal_ties_to_zero",
        F32Row::Bin(BinOp::FDiv, 0x0000_0001, 0x4000_0000),
        0x0000_0000,
    ),
    (
        "fdiv_three_halves_least_subnormal_ties_even",
        F32Row::Bin(BinOp::FDiv, 0x0000_0003, 0x4000_0000),
        0x0000_0002,
    ),
    (
        "fadd_2p24_plus_one",
        F32Row::Bin(BinOp::FAdd, 0x4b80_0000, 0x3f80_0000),
        0x4b80_0000,
    ),
    (
        "fptrunc_third",
        F32Row::Trunc(0x3fd5_5555_5555_5555),
        0x3eaa_aaab,
    ),
    // (2 - 2^-24)·2^127, the RNE overflow threshold: a tie that rounds to +inf.
    (
        "fptrunc_overflow_threshold_tie",
        F32Row::Trunc(0x47ef_ffff_f000_0000),
        0x7f80_0000,
    ),
    (
        "fptrunc_below_overflow_threshold",
        F32Row::Trunc(0x47ef_ffff_efff_ffff),
        0x7f7f_ffff,
    ),
    // 2^-150 and 3·2^-150: halfway cases below the least subnormal, ties to even.
    (
        "fptrunc_half_least_subnormal",
        F32Row::Trunc(0x3690_0000_0000_0000),
        0x0000_0000,
    ),
    (
        "fptrunc_three_halves_least_subnormal",
        F32Row::Trunc(0x36a8_0000_0000_0000),
        0x0000_0002,
    ),
    // 1 + 2^-24 ties to even (1.0); one sticky bit further rounds up — a
    // truncating rounder gets the second one wrong.
    (
        "fptrunc_one_plus_half_ulp_ties_even",
        F32Row::Trunc(0x3ff0_0000_1000_0000),
        0x3f80_0000,
    ),
    (
        "fptrunc_one_plus_half_ulp_sticky",
        F32Row::Trunc(0x3ff0_0000_1000_0004),
        0x3f80_0001,
    ),
    (
        "fptrunc_negative_underflow_keeps_sign",
        F32Row::Trunc(0xb690_0000_0000_0000),
        0x8000_0000,
    ),
    (
        "fptrunc_neg_zero",
        F32Row::Trunc(0x8000_0000_0000_0000),
        0x8000_0000,
    ),
    (
        "fptrunc_neg_inf",
        F32Row::Trunc(0xfff0_0000_0000_0000),
        0xff80_0000,
    ),
    // 2^60 + 2^36 + 1 rounds UP to 2^60 + 2^37; through an f64 intermediate
    // it lands on the halfway point and ties to even 2^60 (double rounding).
    (
        "uitofp_u64_no_double_rounding",
        F32Row::UiToFp(Ty::U64, 1_152_921_573_326_323_713),
        0x5d80_0001,
    ),
    (
        "sitofp_i64_no_double_rounding",
        F32Row::SiToFp(Ty::I64, -1_152_921_573_326_323_713),
        0xdd80_0001,
    ),
    (
        "uitofp_u32_max",
        F32Row::UiToFp(Ty::U32, 4_294_967_295),
        0x4f80_0000,
    ),
];

fn run_f32_bits(module: &Module, fid: FuncId) -> u32 {
    let bits = run_f64_bits(module, fid);
    u32::try_from(bits).expect("an F32 return carries 32 bits")
}

fn f32_row_bits(row: &F32Row) -> u32 {
    let (m, f) = build_nullary(vec![Ty::F32], |fb| match row {
        &F32Row::Bin(op, lhs, rhs) => {
            let a = fb.fconst(Ty::F32, f64::from(f32::from_bits(lhs)));
            let b = fb.fconst(Ty::F32, f64::from(f32::from_bits(rhs)));
            vec![fb.binop(op, Ty::F32, a, b)]
        }
        &F32Row::Trunc(bits) => {
            let x = fb.fconst(Ty::F64, f64::from_bits(bits));
            vec![fb.cast(CastOp::FPTrunc, Ty::F64, Ty::F32, x)]
        }
        F32Row::UiToFp(src, value) => {
            let x = fb.iconst(src.clone(), *value);
            vec![fb.cast(CastOp::UIToFP, src.clone(), Ty::F32, x)]
        }
        F32Row::SiToFp(src, value) => {
            let x = fb.iconst(src.clone(), *value);
            vec![fb.cast(CastOp::SIToFP, src.clone(), Ty::F32, x)]
        }
    });
    run_f32_bits(&m, f)
}

fn float_fixtures_lean_source() -> String {
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../lean/trust_ir-semantics/TrustIr/Semantics/FloatFixtures.lean");
    std::fs::read_to_string(&path)
        .unwrap_or_else(|e| panic!("read Lean float fixtures {}: {e}", path.display()))
}

#[test]
fn f32_cross_engine_table_interpreter_bits() {
    for (name, row, expected) in F32_CROSS_ENGINE_TABLE {
        let got = f32_row_bits(row);
        let expected = *expected;
        assert_eq!(
            got, expected,
            "{name}: interpreter gave {got:#010x}, the shared table says {expected:#010x}"
        );
    }
}

#[test]
fn f32_cross_engine_table_matches_lean_fixtures() {
    let lean = float_fixtures_lean_source();
    for (name, _, expected) in F32_CROSS_ENGINE_TABLE {
        let theorem = format!("theorem f32_table_{name} :");
        let at = lean
            .find(&theorem)
            .unwrap_or_else(|| panic!("{name}: Lean half `{theorem}` is missing"));
        let expected_str = format!("\"ok:f32:{expected:#010x}\"");
        let next_theorem = lean[at + theorem.len()..]
            .find("theorem ")
            .map_or(lean.len(), |i| at + theorem.len() + i);
        assert!(
            lean[at..next_theorem].contains(&expected_str),
            "{name}: Lean half does not assert {expected_str}"
        );
    }
    // No row on the Lean side only.
    let lean_rows = lean.matches("theorem f32_table_").count();
    assert_eq!(
        lean_rows,
        F32_CROSS_ENGINE_TABLE.len(),
        "the Lean f32_table_* rows and F32_CROSS_ENGINE_TABLE differ in number"
    );
}

/// Mutation control for the table: the rows above are not satisfiable by a
/// truncating rounder or by rounding through an f64 intermediate.
#[test]
fn f32_cross_engine_table_discriminates_rounding_mutants() {
    // A truncating (round-toward-zero) f64 -> f32.
    let truncate = |x: f64| -> u32 {
        let r = x as f32;
        if f64::from(r).abs() > x.abs() {
            f32::from_bits(r.to_bits() - 1).to_bits()
        } else {
            r.to_bits()
        }
    };
    let sticky = f64::from_bits(0x3ff0_0000_1000_0004);
    assert_ne!(
        truncate(sticky),
        0x3f80_0001,
        "the sticky row must catch truncation"
    );
    // Double rounding through f64.
    let via_f64 = (1_152_921_573_326_323_713_u64 as f64) as f32;
    assert_ne!(
        via_f64.to_bits(),
        0x5d80_0001,
        "the u64 row must catch double rounding"
    );
    // An encoder that ignores the width (the F64 pattern's top half).
    assert_ne!((1.5f64.to_bits() >> 32) as u32, 1.5f32.to_bits());
}

/// `review/lean-float-memory-placeholder`: a float that goes through memory
/// comes back bit-exact at its own width (the Lean half:
/// `review_lean_float_memory_placeholder_*` in FloatFixtures.lean).
#[test]
fn review_lean_float_memory_placeholder_roundtrips() {
    // store f64 1.5; load -> 1.5
    let (m, f) = build_nullary(vec![Ty::F64], |fb| {
        let p = fb.alloca(Ty::F64);
        let x = fb.fconst(Ty::F64, 1.5);
        fb.store(Ty::F64, p, x);
        vec![fb.load(Ty::F64, p)]
    });
    assert_eq!(run_f64_bits(&m, f), 0x3ff8_0000_0000_0000);
    // store f32 0.1f32; load -> 0x3dcccccd
    let (m, f) = build_nullary(vec![Ty::F32], |fb| {
        let p = fb.alloca(Ty::F32);
        let x = fb.fconst(Ty::F32, f64::from(0.1f32));
        fb.store(Ty::F32, p, x);
        vec![fb.load(Ty::F32, p)]
    });
    assert_eq!(run_f32_bits(&m, f), 0x3dcc_cccd);
    // The F32 image is four bytes of the binary32 pattern: reread as i32.
    let (m, f) = build_nullary(vec![Ty::I32], |fb| {
        let p = fb.alloca(Ty::F32);
        let x = fb.fconst(Ty::F32, 1.5);
        fb.store(Ty::F32, p, x);
        vec![fb.load(Ty::I32, p)]
    });
    assert_eq!(run_signed(&m, f), Ok(0x3fc0_0000));
    // Decode side: the integer-written bits of 1.5 load as F64 1.5.
    let (m, f) = build_nullary(vec![Ty::F64], |fb| {
        let p = fb.alloca(Ty::I64);
        let x = fb.iconst(Ty::I64, 0x3ff8_0000_0000_0000);
        fb.store(Ty::I64, p, x);
        vec![fb.load(Ty::F64, p)]
    });
    assert_eq!(run_f64_bits(&m, f), 0x3ff8_0000_0000_0000);
}

/// `trust-ir-self-declared/lean-semantic-depth-ledger`, float row: the proof
/// program's `fn avg(a: f32, b: f32) -> f32 { (a + b) / 2.0 }` at
/// `a = 16777216, b = 1` is 8388608 in f32 (8388608.5 at f64). The Lean half
/// is `lean_semantic_depth_ledger_float_avg_f32`.
#[test]
fn lean_semantic_depth_ledger_float_row() {
    let (m, f) = build_nullary(vec![Ty::F32], |fb| {
        let a = fb.fconst(Ty::F32, 16_777_216.0);
        let b = fb.fconst(Ty::F32, 1.0);
        let sum = fb.binop(BinOp::FAdd, Ty::F32, a, b);
        let two = fb.fconst(Ty::F32, 2.0);
        vec![fb.binop(BinOp::FDiv, Ty::F32, sum, two)]
    });
    assert_eq!(run_f32_bits(&m, f), 8_388_608.0f32.to_bits());
    // A 128-bit source rounds once at F64 too: 2^100 + 2^47 + 1 -> 2^100 + 2^48
    // (the Lean half: lean_semantic_depth_ledger_float_uitofp_f64_u128_rounds_once).
    let (m, f) = build_nullary(vec![Ty::F64], |fb| {
        let x = fb.iconst(Ty::U128, (1_i128 << 100) + (1_i128 << 47) + 1);
        vec![fb.cast(CastOp::UIToFP, Ty::U128, Ty::F64, x)]
    });
    assert_eq!(run_f64_bits(&m, f), 0x4630_0000_0000_0001);
}

// ---------------------------------------------------------------------------
// WS2.23 review: adversarial rows. Each pins the interpreter's (bit-faithful)
// answer that the Lean model used to contradict; the Lean halves are the
// `ws2_23_review_*` theorems in FloatFixtures.lean.
// ---------------------------------------------------------------------------

/// (1) A NaN's stored image is observable at an integer type. The interpreter
/// keeps `FloatBits`, so a bitcast-made signalling NaN reloads as its own
/// pattern 0x7f800001; the Lean model cannot see a NaN's payload, so a
/// canonical-NaN image would have answered 0x7fc00000. Lean refuses the store
/// (`ws2_23_review_snan_store_reload_refused`).
#[test]
fn ws2_23_review_snan_store_reload_keeps_payload() {
    let (m, f) = build_nullary(vec![Ty::I32], |fb| {
        let p = fb.alloca(Ty::F32);
        let bits = fb.iconst(Ty::I32, 0x7f80_0001);
        let x = fb.cast(CastOp::Bitcast, Ty::I32, Ty::F32, bits);
        fb.store(Ty::F32, p, x);
        vec![fb.load(Ty::I32, p)]
    });
    assert_eq!(run_signed(&m, f), Ok(0x7f80_0001));
}

/// (2) A tuple constant's F32 field is the literal rounded to binary32
/// (the Lean half: `ws2_23_review_tuple_const_*`).
#[test]
fn ws2_23_review_tuple_const_f32_field_rounds() {
    use trust_ir::constant::Constant;
    let (m, f) = build_nullary(vec![Ty::F32, Ty::F64], |fb| {
        let t = fb.const_value(
            Ty::Tuple(vec![Ty::F32, Ty::F64]),
            Constant::Aggregate(vec![Constant::Float(0.1), Constant::Float(0.1)]),
        );
        let a = fb.extract_field(Ty::F32, t, 0);
        let b = fb.extract_field(Ty::F64, t, 1);
        vec![a, b]
    });
    let outcome = Interpreter::with_module(&m)
        .execute_func(f, [])
        .expect("execution succeeds");
    let bits: Vec<u64> = outcome
        .returns
        .iter()
        .map(|v| match v.kind {
            InterpretValueKind::FloatBits(bits) => bits,
            ref other => panic!("expected float return, got {other:?}"),
        })
        .collect();
    assert_eq!(
        bits,
        vec![u64::from(0.1f32.to_bits()), 0.1f64.to_bits()],
        "the F32 field is 0x3dcccccd, the F64 field binary64 0.1"
    );
}

/// (3) `cmpxchg` at F32 compares bit patterns: a matching expected value
/// succeeds and the desired value is written (the Lean half:
/// `ws2_23_review_cmpxchg_f32_*`; the Lean model used to report failure for
/// every float).
#[test]
fn ws2_23_review_cmpxchg_f32_success_writes_desired() {
    use trust_ir::inst::Ordering;
    let (m, f) = build_nullary(vec![Ty::Bool, Ty::F32], |fb| {
        let p = fb.alloca(Ty::F32);
        let x = fb.fconst(Ty::F32, 1.5);
        fb.store(Ty::F32, p, x);
        let d = fb.fconst(Ty::F32, 2.0);
        let (_old, ok) = fb.cmpxchg(Ty::F32, p, x, d, Ordering::SeqCst, Ordering::SeqCst);
        let now = fb.load(Ty::F32, p);
        vec![ok, now]
    });
    let outcome = Interpreter::with_module(&m)
        .execute_func(f, [])
        .expect("execution succeeds");
    assert!(matches!(
        outcome.returns[0].kind,
        InterpretValueKind::Bool(true)
    ));
    assert!(matches!(
        outcome.returns[1].kind,
        InterpretValueKind::FloatBits(bits) if bits == u64::from(2.0f32.to_bits())
    ));
}

/// Bitwise: a stored `+0.0` does not match an expected `-0.0`.
#[test]
fn ws2_23_review_cmpxchg_f32_signed_zero_differs() {
    use trust_ir::inst::Ordering;
    let (m, f) = build_nullary(vec![Ty::Bool], |fb| {
        let p = fb.alloca(Ty::F32);
        let z = fb.fconst(Ty::F32, 0.0);
        fb.store(Ty::F32, p, z);
        let nz = fb.fconst(Ty::F32, -0.0);
        let (_old, ok) = fb.cmpxchg(Ty::F32, p, nz, nz, Ordering::SeqCst, Ordering::SeqCst);
        vec![ok]
    });
    assert!(!run_bool(&m, f));
}

/// Every review row has its Lean half, so neither side can be dropped alone.
#[test]
fn ws2_23_review_rows_have_lean_halves() {
    let lean = float_fixtures_lean_source();
    for row in [
        "ws2_23_review_snan_store_reload_refused",
        "ws2_23_review_fneg_nan_store_refused",
        "ws2_23_review_tuple_const_f32_field_rounds",
        "ws2_23_review_tuple_const_extract_f32",
        "ws2_23_review_vector_const_f32_lanes_round",
        "ws2_23_review_struct_const_inexact_float_refused",
        "ws2_23_review_struct_const_exact_float_admitted",
        "ws2_23_review_cmpxchg_f32_success",
        "ws2_23_review_cmpxchg_f32_writes_desired",
        "ws2_23_review_cmpxchg_f32_signed_zero_differs",
        "ws2_23_review_cmpxchg_f32_nan_refused",
    ] {
        assert!(
            lean.contains(&format!("theorem {row} :")),
            "Lean half `{row}` is missing from FloatFixtures.lean"
        );
    }
}
