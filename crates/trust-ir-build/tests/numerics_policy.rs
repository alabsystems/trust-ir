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
    (mb.build(), fid)
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
