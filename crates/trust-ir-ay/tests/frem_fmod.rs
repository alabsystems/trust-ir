// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0
//
// TRUST-IR-AY-FREM-1: `BinOp::FRem` is C `fmod` / LLVM `frem` / Rust `%` -- the
// TRUNCATING remainder with the dividend's sign (docs/ub-numerics-policy.md
// §2, interpreter `lhs % rhs`, Lean `floatFRem`). SMT-LIB `fp.rem` is the IEEE
// round-to-nearest remainder, a different function: `fp.rem(5, 3) = -1` while
// `5.0 % 3.0 = 2.0`. Lowering `FRem` straight to `fp.rem` let a VC over a
// remainder PROVE the false `5 % 3 < 0` and REFUTE the true `5 % 3 == 2` (and
// `x >= 0 => x % 3 >= 0`).
//
// Every concrete case below is cross-checked against the reference
// interpreter (`trust_ir::interpret`), bit for bit, so the adapter is held to
// the semantics of record rather than to a second hand-written expectation.
// The symbolic cases are kept at f32/f16: an f64 symbolic `fp.rem` + `fp.add`
// exceeds ay's default memory ceiling (scout20 `fix1`/`fix2` memout).

#![allow(clippy::disallowed_methods)] // a test drives ay directly; a panic here is a test failure (r11 item 5, crates/trust-ir-ay/clippy.toml)

use ay::{Solver, Sort, Term};
use trust_ir::Module;
use trust_ir::inst::{BinOp, CastOp, FCmpOp};
use trust_ir::interpret::{InterpretValueKind, Interpreter, f16_bits_to_f64};
use trust_ir::proof::{ObligationKind, ProofObligation, ProofStatus};
use trust_ir::ty::Ty;
use trust_ir::value::{FuncId, ProofId};
use trust_ir_ay::{
    VcObligationOutcome, VcSource, VcVerdict, apply_vc_outcomes, create_fp_solver, encode_binop,
    verify_function,
};
use trust_ir_build::{ModuleBuilder, validate_module};

// ============================================================================
// Formats and the interpreter oracle
// ============================================================================

#[derive(Clone, Copy, Debug)]
enum Fmt {
    F16,
    F32,
    F64,
}

impl Fmt {
    fn ty(self) -> Ty {
        match self {
            Fmt::F16 => Ty::F16,
            Fmt::F32 => Ty::F32,
            Fmt::F64 => Ty::F64,
        }
    }

    /// `(eb, sb)` of the SMT-LIB FloatingPoint sort `trust_ir_ay::ty_to_sort`
    /// maps this type to.
    fn eb_sb(self) -> (u32, u32) {
        match self {
            Fmt::F16 => (5, 11),
            Fmt::F32 => (8, 24),
            Fmt::F64 => (11, 53),
        }
    }

    fn mask(self) -> u64 {
        match self {
            Fmt::F16 => 0xFFFF,
            Fmt::F32 => 0xFFFF_FFFF,
            Fmt::F64 => u64::MAX,
        }
    }

    /// The value of a bit pattern of this format, widened exactly to f64.
    fn value(self, bits: u64) -> f64 {
        match self {
            Fmt::F16 => f16_bits_to_f64(bits as u16),
            Fmt::F32 => f64::from(f32::from_bits(bits as u32)),
            Fmt::F64 => f64::from_bits(bits),
        }
    }
}

/// The reference interpreter's `FRem` on operand BIT PATTERNS of `fmt`,
/// returning the result's bit pattern. Every operand used here is exactly
/// representable in `fmt`, so the `Constant::Float(f64)` carrier is exact.
fn interp_frem_bits(fmt: Fmt, x_bits: u64, y_bits: u64) -> u64 {
    let ty = fmt.ty();
    let mut mb = ModuleBuilder::new("frem_oracle");
    let ft = mb.add_func_type(vec![], vec![ty.clone()]);
    let fid = {
        let mut fb = mb.function("frem", ft);
        let entry = fb.create_block();
        fb.switch_to_block(entry);
        let a = fb.fconst(ty.clone(), fmt.value(x_bits));
        let b = fb.fconst(ty.clone(), fmt.value(y_bits));
        let r = fb.binop(BinOp::FRem, ty, a, b);
        fb.ret(vec![r]);
        fb.build()
    };
    let module = mb.build().expect("ModuleBuilder::build: test fixture");
    let outcome = Interpreter::with_module(&module)
        .execute_func(fid, [])
        .expect("the interpreter executes FRem");
    match outcome.returns[0].kind {
        InterpretValueKind::FloatBits(bits) => bits & fmt.mask(),
        ref other => panic!("expected a float return, got {other:?}"),
    }
}

// ============================================================================
// Solver helpers
// ============================================================================

#[derive(Debug, PartialEq, Eq)]
enum Verdict {
    Unsat,
    Sat,
    Unknown,
}

fn check(solver: &mut Solver) -> Verdict {
    let result = solver.try_check_sat().expect("check-sat runs");
    if result.is_unsat() {
        Verdict::Unsat
    } else if result.is_sat() {
        Verdict::Sat
    } else {
        Verdict::Unknown
    }
}

fn fp_const(solver: &mut Solver, fmt: Fmt, bits: u64) -> Term {
    let (eb, sb) = fmt.eb_sb();
    solver
        .try_fp_const_from_bits(bits, eb, sb)
        .expect("an in-envelope FP constant")
}

/// Is `goal(frem(x, y))` VALID for the adapter's encoding of `FRem` over the
/// constant operands `x_bits`, `y_bits`? Asserts the negation and returns the
/// verdict: `Unsat` means valid.
fn frem_goal_verdict(
    fmt: Fmt,
    x_bits: u64,
    y_bits: u64,
    goal: impl FnOnce(&mut Solver, Term) -> Term,
) -> Verdict {
    let mut solver = create_fp_solver().unwrap();
    let x = fp_const(&mut solver, fmt, x_bits);
    let y = fp_const(&mut solver, fmt, y_bits);
    let r = encode_binop(&mut solver, BinOp::FRem, x, y).expect("FRem encodes");
    let g = goal(&mut solver, r);
    let negated = solver.try_not(g).unwrap();
    solver.try_assert_term(negated).unwrap();
    check(&mut solver)
}

/// Does the adapter's `frem(x, y)` equal the bit pattern `expected_bits`
/// (SMT `=`: exact, so `-0.0` and `+0.0` differ), or, for a NaN expectation,
/// is it NaN (SMT-LIB has one NaN; the NaN payload is not pinned by the
/// numerics policy either)?
fn frem_is(fmt: Fmt, x_bits: u64, y_bits: u64, expected_bits: u64) -> Verdict {
    let expected_is_nan = fmt.value(expected_bits).is_nan();
    frem_goal_verdict(fmt, x_bits, y_bits, |solver, r| {
        if expected_is_nan {
            solver.try_fp_is_nan(r).unwrap()
        } else {
            let e = fp_const(solver, fmt, expected_bits);
            solver.try_eq(r, e).unwrap()
        }
    })
}

/// The interpreter's result for `x % y`, after checking it against the
/// hand-stated expectation, and the adapter's verdict that its encoding
/// equals exactly that result.
fn assert_matches_interpreter(fmt: Fmt, x_bits: u64, y_bits: u64, stated: Option<u64>) {
    let oracle = interp_frem_bits(fmt, x_bits, y_bits);
    if let Some(stated) = stated {
        assert_eq!(
            oracle,
            stated,
            "{fmt:?} {} % {}: the interpreter (semantics of record) disagrees with the stated \
             fmod value",
            fmt.value(x_bits),
            fmt.value(y_bits)
        );
    }
    assert_eq!(
        frem_is(fmt, x_bits, y_bits, oracle),
        Verdict::Unsat,
        "{fmt:?} {} % {}: the adapter's FRem is not provably the interpreter's {} ({oracle:#x})",
        fmt.value(x_bits),
        fmt.value(y_bits),
        fmt.value(oracle)
    );
}

fn f64b(v: f64) -> u64 {
    v.to_bits()
}

fn f32b(v: f32) -> u64 {
    u64::from(v.to_bits())
}

// ============================================================================
// (a) the scout's witness: 5 % 3
// ============================================================================

/// `5.0 % 3.0 == 2.0` must be PROVED and `5.0 % 3.0 < 0.0` must NOT be. Under
/// the IEEE-remainder lowering `fp.rem(5, 3) = -1`, so the first was refuted
/// and the false second one proved.
#[test]
fn frem_f64_5_by_3_is_2_and_not_negative() {
    assert_eq!(interp_frem_bits(Fmt::F64, f64b(5.0), f64b(3.0)), f64b(2.0));
    assert_eq!(
        frem_goal_verdict(Fmt::F64, f64b(5.0), f64b(3.0), |s, r| {
            let two = fp_const(s, Fmt::F64, f64b(2.0));
            s.try_fp_eq(r, two).unwrap()
        }),
        Verdict::Unsat,
        "5.0 % 3.0 == 2.0 must be valid"
    );
    assert_eq!(
        frem_goal_verdict(Fmt::F64, f64b(5.0), f64b(3.0), |s, r| {
            let zero = fp_const(s, Fmt::F64, f64b(0.0));
            s.try_fp_lt(r, zero).unwrap()
        }),
        Verdict::Sat,
        "5.0 % 3.0 < 0.0 is false and must not be proved"
    );
}

// ============================================================================
// (b) sign, tie and signed-zero cases, each cross-checked against the interpreter
// ============================================================================

/// The cases where `fp.rem` and `fmod` differ (`-5 % 3`, the tie `3 % 2`,
/// `5.25 % 2`, a negative divisor) and the one where they agree only because
/// the zero result keeps the dividend's sign (`-6 % 3 == -0.0`), at f64.
#[test]
fn frem_f64_sign_tie_and_signed_zero_cases() {
    let cases: [(f64, f64, f64); 6] = [
        (-5.0, 3.0, -2.0), // fp.rem: +1
        (3.0, 2.0, 1.0),   // tie 1.5 rounds to even 2 -> fp.rem: -1
        (5.25, 2.0, 1.25), // fp.rem: -0.75 (the conformance `frem_5_25_by_2` row)
        (5.0, -3.0, 2.0),  // divisor sign is irrelevant -> fp.rem: -1
        (-6.0, 3.0, -0.0), // exact multiple: zero with the DIVIDEND's sign
        (6.0, -3.0, 0.0),  // ... and +0.0 for a positive dividend
    ];
    for (x, y, expected) in cases {
        assert_matches_interpreter(Fmt::F64, f64b(x), f64b(y), Some(f64b(expected)));
    }
}

/// The same characteristic cases at f32 and f16, plus the IEEE special
/// operands (NaN, infinities, zero divisor, signed-zero dividends, subnormals,
/// a wide exponent gap), each held bit-exact to the interpreter. The special
/// cases already agreed between `fp.rem` and `fmod`; they are here so the
/// correction never fires where it must not.
#[test]
fn frem_matches_interpreter_bit_exact_table() {
    let f32_cases: [(f32, f32); 22] = [
        (5.0, 3.0),
        (-5.0, 3.0),
        (5.0, -3.0),
        (-5.0, -3.0),
        (3.0, 2.0),
        (-3.0, 2.0),
        (5.25, 2.0),
        (-6.0, 3.0),
        (7.5, 2.5),
        (1.0, 3.0),
        (-1.0, 3.0),
        (0.0, 3.0),
        (-0.0, 3.0),
        (5.0, f32::INFINITY),
        (-5.0, f32::NEG_INFINITY),
        (f32::INFINITY, 3.0),
        (5.0, 0.0),
        (5.0, -0.0),
        (f32::NAN, 3.0),
        (5.0, f32::NAN),
        (f32::MAX, 3.0),
        (f32::MAX, f32::from_bits(1)), // largest over the least subnormal
    ];
    for (x, y) in f32_cases {
        assert_matches_interpreter(Fmt::F32, f32b(x), f32b(y), None);
    }
    // Subnormal operands at f32. The second pair takes the correction
    // (-7q % 2q: fp.rem is +1q, fmod is -1q), and the add stays exact.
    for (x_bits, y_bits) in [(0x0000_0007u64, 0x0000_0003u64), (0x8000_0007, 0x0000_0002)] {
        assert_matches_interpreter(Fmt::F32, x_bits, y_bits, None);
    }

    // f16 (binary16 bit patterns): 5 % 3, -5 % 3, 3 % 2, 5.25 % 2, -6 % 3,
    // max % 3, a subnormal pair on which the correction fires, and max over
    // the least subnormal.
    let f16_cases: [(u64, u64); 8] = [
        (0x4500, 0x4200), // 5 % 3
        (0xC500, 0x4200), // -5 % 3
        (0x4200, 0x4000), // 3 % 2
        (0x4540, 0x4000), // 5.25 % 2
        (0xC600, 0x4200), // -6 % 3
        (0x7BFF, 0x4200), // 65504 % 3
        (0x0007, 0x0002), // 7q % 2q: fp.rem is -1q (tie 3.5 -> 4), fmod is +1q
        (0x7BFF, 0x0001), // max % least subnormal
    ];
    for (x_bits, y_bits) in f16_cases {
        assert_matches_interpreter(Fmt::F16, x_bits, y_bits, None);
    }

    // f64: the policy doc's wide-gap example and a huge negative dividend.
    // Each concrete f64 query took ay 9-14 s on a loaded machine (2026-10-06),
    // so the special operands are covered at f32/f16 above, where the logic
    // is the same.
    let f64_cases: [(f64, f64); 2] = [
        (1e308, 1e-308), // 3.498445546245627e-309, a subnormal (ub-numerics-policy §2)
        (-1e308, 3.0),   // fp.rem: +1 -> fmod: -2
    ];
    for (x, y) in f64_cases {
        assert_matches_interpreter(Fmt::F64, f64b(x), f64b(y), None);
    }
}

// ============================================================================
// (c) symbolic properties of the truncating remainder
// ============================================================================

/// For every finite f32 `x >= 0`, `x % 3.0 >= 0.0`. The IEEE remainder
/// refutes this (scout20 `r5`: SAT); `fmod` keeps the dividend's sign.
#[test]
fn frem_f32_nonnegative_dividend_gives_nonnegative_result() {
    let mut solver = create_fp_solver().unwrap();
    let x = solver.declare_const("x", Sort::FloatingPoint(8, 24));
    let three = fp_const(&mut solver, Fmt::F32, f32b(3.0));
    let zero = fp_const(&mut solver, Fmt::F32, f32b(0.0));
    let r = encode_binop(&mut solver, BinOp::FRem, x, three).unwrap();

    let nonneg = solver.try_fp_ge(x, zero).unwrap();
    solver.try_assert_term(nonneg).unwrap();
    let inf = solver.try_fp_is_infinite(x).unwrap();
    let finite = solver.try_not(inf).unwrap();
    solver.try_assert_term(finite).unwrap();
    let goal = solver.try_fp_ge(r, zero).unwrap();
    let negated = solver.try_not(goal).unwrap();
    solver.try_assert_term(negated).unwrap();
    assert_eq!(check(&mut solver), Verdict::Unsat);
}

/// For every finite f16 `x`, `x % -3.0` is not NaN, has the DIVIDEND's sign
/// (zero results included), and `|x % -3| < 3` and `|x % -3| <= |x|`. The
/// IEEE remainder violates the sign clause (`5 rem -3 = -1`). The divisor is
/// concrete: with both operands symbolic ay answers `unknown` after several
/// minutes, and an unknown proves nothing either way.
#[test]
fn frem_f16_symbolic_dividend_sign_and_magnitude() {
    let mut solver = create_fp_solver().unwrap();
    let x = solver.declare_const("x", Sort::FloatingPoint(5, 11));
    let y = fp_const(&mut solver, Fmt::F16, 0xC200); // -3.0
    let r = encode_binop(&mut solver, BinOp::FRem, x, y).unwrap();

    let assume_not = |solver: &mut Solver, t: Term| {
        let n = solver.try_not(t).unwrap();
        solver.try_assert_term(n).unwrap();
    };
    let x_nan = solver.try_fp_is_nan(x).unwrap();
    assume_not(&mut solver, x_nan);
    let x_inf = solver.try_fp_is_infinite(x).unwrap();
    assume_not(&mut solver, x_inf);

    let r_nan = solver.try_fp_is_nan(r).unwrap();
    let r_not_nan = solver.try_not(r_nan).unwrap();
    let r_neg = solver.try_fp_is_negative(r).unwrap();
    let x_neg = solver.try_fp_is_negative(x).unwrap();
    let same_sign = solver.try_eq(r_neg, x_neg).unwrap();
    let r_abs = solver.try_fp_abs(r).unwrap();
    let y_abs = solver.try_fp_abs(y).unwrap();
    let x_abs = solver.try_fp_abs(x).unwrap();
    let below_y = solver.try_fp_lt(r_abs, y_abs).unwrap();
    let within_x = solver.try_fp_le(r_abs, x_abs).unwrap();
    let a = solver.try_and(r_not_nan, same_sign).unwrap();
    let b = solver.try_and(below_y, within_x).unwrap();
    let goal = solver.try_and(a, b).unwrap();
    assume_not(&mut solver, goal);
    assert_eq!(check(&mut solver), Verdict::Unsat);
}

// ============================================================================
// (d) the whole-function VC and apply_vc_outcomes
// ============================================================================

/// `fn frem_check() { assert((5.0 % 3.0) <cmp> k) }`, the float operands
/// produced by exact `sitofp` casts of `i64` constants (the whole-function VC
/// refuses `Constant::Float` by name, so a literal `fconst` would never reach
/// the `FRem` encoding), with one site-less Pending postcondition row scoped
/// to the function.
fn build_frem_assert_module(cmp: FCmpOp, k: i128) -> (Module, FuncId, ProofId) {
    let mut mb = ModuleBuilder::new("frem_vc");
    let ft = mb.add_func_type(vec![], vec![]);
    let mut fb = mb.function("frem_check", ft);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    let five = fb.iconst(Ty::I64, 5);
    let three = fb.iconst(Ty::I64, 3);
    let kk = fb.iconst(Ty::I64, k);
    let x = fb.cast(CastOp::SIToFP, Ty::I64, Ty::F64, five);
    let y = fb.cast(CastOp::SIToFP, Ty::I64, Ty::F64, three);
    let e = fb.cast(CastOp::SIToFP, Ty::I64, Ty::F64, kk);
    let r = fb.binop(BinOp::FRem, Ty::F64, x, y);
    let ok = fb.fcmp(cmp, Ty::F64, r, e);
    fb.assert(ok);
    fb.ret(vec![]);
    let func = fb.build();
    let mut module = mb.build().expect("ModuleBuilder::build: test fixture");
    let oid = ProofId::new(0);
    module.proof_obligations.push(
        ProofObligation::new(
            oid,
            ObligationKind::Postcondition,
            ProofStatus::Pending,
            "the remainder check holds",
        )
        .with_function(func),
    );
    assert!(validate_module(&module).is_empty(), "fixture validates");
    (module, func, oid)
}

/// Does the reference interpreter run the fixture's assert to completion?
fn interpreter_assert_holds(module: &Module, func: FuncId) -> bool {
    Interpreter::with_module(module)
        .execute_func(func, [])
        .is_ok()
}

/// TRUE assert `5.0 % 3.0 == 2.0`: the interpreter passes it, so the VC must
/// never refute it, and `apply_vc_outcomes` must leave the obligation
/// `Pending`. Under the IEEE-remainder lowering the VC refuted it (measured
/// 2026-10-06: `Refuted { counterexample: Model([]) }`), and
/// `apply_vc_outcomes` records such a refutation as `Failed` (the false-assert
/// test below shows that on the same fixture): a false refutation recorded in
/// the module.
///
/// The verdict is `Proved` or `Unknown`, never `Refuted`. Today it is
/// `Unknown`, because the VC solver runs with `set_produce_proofs(true)` and
/// in that mode the pinned ay answers `unknown` on any query through
/// `fp.rem`. That includes the bare `fp.rem(5, 3) == -1`, which it proves
/// UNSAT with proofs off (measured 2026-10-06). An unknown is fail-closed:
/// it mints no status.
#[test]
fn vc_true_frem_assert_is_never_refuted_and_never_fails_the_obligation() {
    let (mut module, func, oid) = build_frem_assert_module(FCmpOp::OEq, 2);
    assert!(
        interpreter_assert_holds(&module, func),
        "the interpreter runs `assert(5.0 % 3.0 == 2.0)` to completion"
    );

    let vc = verify_function(&module, func).unwrap();
    assert!(
        vc.whole_function_fallback.is_none(),
        "whole-function VC, not the sited fallback: {:?}",
        vc.whole_function_fallback
    );
    assert_eq!(vc.conditions.len(), 1);
    assert_eq!(vc.conditions[0].source, VcSource::Assert);
    assert!(
        matches!(
            vc.conditions[0].verdict,
            VcVerdict::Proved | VcVerdict::Unknown { .. }
        ),
        "`5.0 % 3.0 == 2.0` must never be refuted, got {:?}",
        vc.conditions[0].verdict
    );
    assert_eq!(vc.refuted().count(), 0);
    assert!(
        !matches!(vc.obligations[0].1, VcObligationOutcome::ProvedByVc),
        "a site-less row is never backed: {:?}",
        vc.obligations[0].1
    );

    let transitions = apply_vc_outcomes(&mut module, &vc).unwrap();
    assert!(transitions.is_empty(), "{transitions:?}");
    let row = module
        .proof_obligations
        .iter()
        .find(|o| o.id == oid)
        .unwrap();
    assert_eq!(row.status, ProofStatus::Pending);
}

/// FALSE assert `5.0 % 3.0 < 0.0`: the interpreter traps on it, the VC must
/// refute it (never prove it), and `apply_vc_outcomes` records `Failed`.
/// Under the IEEE-remainder lowering the bare encoding PROVED it (see
/// `frem_f64_5_by_3_is_2_and_not_negative`). Through `verify_function`, whose
/// solver produces proofs, the pinned ay answered `Unknown` instead (measured
/// 2026-10-06), so on the old encoding this test failed on `Unknown`, not on a
/// proof.
#[test]
fn vc_false_frem_assert_is_refuted_never_proved() {
    let (mut module, func, oid) = build_frem_assert_module(FCmpOp::OLt, 0);
    assert!(
        !interpreter_assert_holds(&module, func),
        "the interpreter traps on `assert(5.0 % 3.0 < 0.0)`"
    );

    let vc = verify_function(&module, func).unwrap();
    assert!(vc.whole_function_fallback.is_none());
    assert_eq!(vc.conditions.len(), 1);
    assert!(
        matches!(vc.conditions[0].verdict, VcVerdict::Refuted { .. }),
        "`5.0 % 3.0 < 0.0` must be refuted, got {:?}",
        vc.conditions[0].verdict
    );
    assert!(!vc.all_proved());

    let transitions = apply_vc_outcomes(&mut module, &vc).unwrap();
    assert_eq!(transitions, vec![(oid, ProofStatus::Failed)]);
}
