-- Copyright 2026 Andrew Yates
-- Author: Andrew Yates <andrewyates.name@gmail.com>
-- Licensed under the Apache License, Version 2.0
--
-- Phase 5 ay bridge: reflection layer connecting Lean proofs to ay SMT
-- automated proofs via a shared expression language.
--
-- Reference: designs/2026-04-16-trust_ir-semantics-lean-architecture.md, Section 6 Phase 5
-- Reference: de Moura & Bjorner, "Z3: An Efficient SMT Solver", TACAS 2008
-- Reference: Ebner et al., "A Metaprogramming Framework for Formal Verification",
--            Proc. ACM Program. Lang. (ICFP), 2017

import TrustIr.Semantics.Eval

namespace TrustIr

/-!
# ay Bridge (Phase 5)

This module defines the reflection layer that bridges Lean-checked proofs
with ay (SMT solver) automated proofs.

## Architecture

The bridge has three layers:

1. **TrustIrExpr** -- an inductive type mirroring ay SMT-LIB expressions,
   restricted to the bitvector and boolean theories used by TrustIr.

2. **Encoding** -- functions that translate TrustIr instruction operands
   into TrustIrExpr, so ay can reason about instruction behavior.

3. **Reflection** -- an interpretation function from TrustIrExpr back to
   Lean Prop, plus a soundness axiom: if ay reports UNSAT, the
   corresponding Lean Prop holds.

## Trust model

The ay solver is an EXTERNAL ORACLE. We do NOT verify ay's internals.
Instead, we trust a single axiom (ay_sound): if ay says UNSAT for a
formula, that formula is indeed unsatisfiable. This is the standard
"proof-producing solver" trust model used by Isabelle/HOL's smt method
and Coq's SMTCoq.

In production, ay can optionally produce proof certificates that are
independently checked. The axiom here is the minimal trust assumption
needed to USE ay results in Lean proofs.

## Intended usage by TrustCg (framework — awaiting instantiation)

This module is a proof *framework*: the theorems below are proved, but
`ay_check` is an uninstantiated `opaque` (no `@[extern]`/`@[implemented_by]`
binding or certificate importer — see "Future Work"). The SMT-LIB serializer
emits requests at an explicitly supplied width. Until the hook is instantiated,
no `ay_check width e = .unsat` fact can be produced inside
Lean, so nothing is cross-verified through *this* bridge yet. (The Rust
`trust-ir-ay` adapter performs solver-backed checks on a parallel, Lean-
disconnected path; it does not instantiate `ay_check`.)

When instantiated, TrustCg would verify optimization passes by:
1. Encoding the original and optimized instruction as `TrustIrExpr`,
2. asserting their inequality and sending it to ay,
3. concluding equivalence if ay returns UNSAT,
4. and lifting that to a Lean proof via the `ay_sound_unsat` axiom.
-/

-- =================================================================
-- SMT expression type
-- =================================================================

/-- SMT expression type mirroring ay bitvector and boolean theories.
    This is the shared language between Lean and ay. -/
inductive TrustIrExpr where
  -- Bitvector constants and operations
  | bvConst  : (width : Nat) -> Int -> TrustIrExpr
  | bvAdd    : TrustIrExpr -> TrustIrExpr -> TrustIrExpr
  | bvSub    : TrustIrExpr -> TrustIrExpr -> TrustIrExpr
  | bvMul    : TrustIrExpr -> TrustIrExpr -> TrustIrExpr
  | bvUDiv   : TrustIrExpr -> TrustIrExpr -> TrustIrExpr
  | bvSDiv   : TrustIrExpr -> TrustIrExpr -> TrustIrExpr
  | bvURem   : TrustIrExpr -> TrustIrExpr -> TrustIrExpr
  | bvSRem   : TrustIrExpr -> TrustIrExpr -> TrustIrExpr
  | bvAnd    : TrustIrExpr -> TrustIrExpr -> TrustIrExpr
  | bvOr     : TrustIrExpr -> TrustIrExpr -> TrustIrExpr
  | bvXor    : TrustIrExpr -> TrustIrExpr -> TrustIrExpr
  | bvNeg    : TrustIrExpr -> TrustIrExpr
  | bvNot    : TrustIrExpr -> TrustIrExpr
  | bvShl    : TrustIrExpr -> TrustIrExpr -> TrustIrExpr
  | bvLShr   : TrustIrExpr -> TrustIrExpr -> TrustIrExpr
  | bvAShr   : TrustIrExpr -> TrustIrExpr -> TrustIrExpr
  -- WS3.20 rotates (SMT-LIB `rotate_left`/`rotate_right` with a TERM amount,
  -- which the adapter spells as `bvshl`/`bvlshr`/`bvor` over `amount bvurem
  -- width`): the amount is reduced modulo the width, so both are total.
  | bvRotL   : TrustIrExpr -> TrustIrExpr -> TrustIrExpr
  | bvRotR   : TrustIrExpr -> TrustIrExpr -> TrustIrExpr
  -- Boolean operations
  | boolConst : Bool -> TrustIrExpr
  | boolNot   : TrustIrExpr -> TrustIrExpr
  | boolAnd   : TrustIrExpr -> TrustIrExpr -> TrustIrExpr
  | boolOr    : TrustIrExpr -> TrustIrExpr -> TrustIrExpr
  | boolImpl  : TrustIrExpr -> TrustIrExpr -> TrustIrExpr
  -- Comparisons (bitvector -> bool)
  | eq       : TrustIrExpr -> TrustIrExpr -> TrustIrExpr
  | bvUlt    : TrustIrExpr -> TrustIrExpr -> TrustIrExpr
  | bvUle    : TrustIrExpr -> TrustIrExpr -> TrustIrExpr
  | bvSlt    : TrustIrExpr -> TrustIrExpr -> TrustIrExpr
  | bvSle    : TrustIrExpr -> TrustIrExpr -> TrustIrExpr
  -- Control
  | ite      : TrustIrExpr -> TrustIrExpr -> TrustIrExpr -> TrustIrExpr
  -- Variables (for universally quantified formulas)
  | var      : String -> Nat -> TrustIrExpr
  deriving Repr

-- =================================================================
-- Denotational semantics for TrustIrExpr
-- =================================================================

/-- Environment: maps variable names to integer values. -/
def SMTEnv := String -> Int

/-- Default environment: all variables are 0. -/
def SMTEnv.default : SMTEnv := fun _ => 0

/-- Truncate an integer to width bits (unsigned modular arithmetic). -/
private def truncBV (val : Int) (width : Nat) : Int :=
  let modulus := (2 : Int) ^ width
  ((val % modulus) + modulus) % modulus

/-- Interpret a width-bit bitvector as a two's-complement SIGNED integer.
    SMT-LIB `bvslt`/`bvsle`/`bvsdiv`/`bvsrem`/`bvashr` are signed operations;
    evaluating them on the raw unsigned residue (as the old code did, making
    them textually identical to their unsigned counterparts) is unsound. -/
private def toSignedBV (val : Int) (width : Nat) : Int :=
  let u := truncBV val width
  let half := (2 : Int) ^ (width - 1)
  if u ≥ half then u - (2 : Int) ^ width else u

private theorem truncBV_eq_truncateUnsigned (val : Int) (width : Nat) :
    truncBV val width = truncateUnsigned val width := by
  simp [truncBV, truncateUnsigned, Int.add_emod]

private theorem toSignedBV_eq_toSigned (val : Int) (width : Nat) :
    toSignedBV val width = toSigned val width := by
  simp only [toSignedBV, toSigned, truncBV_eq_truncateUnsigned, truncateUnsigned]

/-- Evaluate a TrustIrExpr to an Int given an environment and a bitvector width.
    Bitvector operations use modular arithmetic at the specified width.
    The width parameter allows cross-target evaluation (e.g., 32-bit for
    i32 operations, 64-bit for i64). Defaults to 64 for backward
    compatibility.
    Boolean operations map true -> 1, false -> 0. -/
def TrustIrExpr.evalAt (env : SMTEnv) (w : Nat) : TrustIrExpr -> Int
  | .bvConst width val  => truncBV val width
  | .bvAdd e1 e2        => truncBV (e1.evalAt env w + e2.evalAt env w) w
  | .bvSub e1 e2        => truncBV (e1.evalAt env w - e2.evalAt env w) w
  | .bvMul e1 e2        => truncBV (e1.evalAt env w * e2.evalAt env w) w
  | .bvUDiv e1 e2       =>
    let d := e2.evalAt env w
    if d == 0 then truncBV (-1) w else truncBV (e1.evalAt env w / d) w
  | .bvSDiv e1 e2       =>
    let d := toSignedBV (e2.evalAt env w) w
    -- SMT-LIB `bvsdiv` rounds the quotient toward zero: the pinned T-rounding adapter,
    -- not the Euclidean `/` operator. `trustIrIntTDiv (-7) 2 = -3` matches bvsdiv;
    -- ediv would give -4.
    let n := toSignedBV (e1.evalAt env w) w
    if d == 0 then truncBV (if n < 0 then 1 else -1) w
    else truncBV (trustIrIntTDiv n d) w
  | .bvURem e1 e2       =>
    let d := e2.evalAt env w
    if d == 0 then truncBV (e1.evalAt env w) w
    else truncBV (e1.evalAt env w % d) w
  | .bvSRem e1 e2       =>
    let d := toSignedBV (e2.evalAt env w) w
    -- SMT-LIB `bvsrem` takes the sign of the dividend: the pinned T-rounding adapter,
    -- not the Euclidean `%` operator. `trustIrIntTMod (-7) 3 = -1` matches bvsrem;
    -- emod would give 2.
    if d == 0 then truncBV (e1.evalAt env w) w
    else truncBV (trustIrIntTMod (toSignedBV (e1.evalAt env w) w) d) w
  | .bvAnd e1 e2        => Int.land (e1.evalAt env w) (e2.evalAt env w)
  | .bvOr e1 e2         => Int.lor (e1.evalAt env w) (e2.evalAt env w)
  | .bvXor e1 e2        => Int.xor (e1.evalAt env w) (e2.evalAt env w)
  | .bvNeg e             => truncBV (-(e.evalAt env w)) w
  | .bvNot e             => Int.xor (e.evalAt env w) ((2 : Int) ^ w - 1)
  -- A shift at or beyond the width has a determined result. Test the amount
  -- BEFORE constructing its power: a 64-bit amount can otherwise request an
  -- integer with 2^64 bits just to discard it modulo 2^64.
  | .bvShl e1 e2        =>
    let amount := (e2.evalAt env w).toNat
    if amount < w then truncBV ((e1.evalAt env w) * ((2 : Int) ^ amount)) w
    else 0
  | .bvLShr e1 e2       =>
    let amount := (e2.evalAt env w).toNat
    if amount < w then truncBV ((e1.evalAt env w) / ((2 : Int) ^ amount)) w
    else 0
  | .bvAShr e1 e2       =>
    let amount := (e2.evalAt env w).toNat
    let signed := toSignedBV (e1.evalAt env w) w
    if amount < w then truncBV (Int.fdiv signed ((2 : Int) ^ amount)) w
    else if signed < 0 then truncBV (-1) w else 0
  -- The same total definitions `semIntBinOp .RotL/.RotR` use (Arith.lean).
  | .bvRotL e1 e2       => Int.ofNat (rotlWidth (e1.evalAt env w).toNat w (e2.evalAt env w).toNat)
  | .bvRotR e1 e2       => Int.ofNat (rotrWidth (e1.evalAt env w).toNat w (e2.evalAt env w).toNat)
  | .boolConst b         => if b then 1 else 0
  | .boolNot e           => if e.evalAt env w == 0 then 1 else 0
  | .boolAnd e1 e2      => if e1.evalAt env w != 0 && e2.evalAt env w != 0 then 1 else 0
  | .boolOr e1 e2       => if e1.evalAt env w != 0 || e2.evalAt env w != 0 then 1 else 0
  | .boolImpl e1 e2     => if e1.evalAt env w == 0 || e2.evalAt env w != 0 then 1 else 0
  | .eq e1 e2            => if e1.evalAt env w == e2.evalAt env w then 1 else 0
  | .bvUlt e1 e2        => if e1.evalAt env w < e2.evalAt env w then 1 else 0
  | .bvUle e1 e2        => if e1.evalAt env w <= e2.evalAt env w then 1 else 0
  | .bvSlt e1 e2        => if toSignedBV (e1.evalAt env w) w < toSignedBV (e2.evalAt env w) w then 1 else 0
  | .bvSle e1 e2        => if toSignedBV (e1.evalAt env w) w ≤ toSignedBV (e2.evalAt env w) w then 1 else 0
  | .ite c t e           => if c.evalAt env w != 0 then t.evalAt env w else e.evalAt env w
  | .var name width      => truncBV (env name) width

/-- An arbitrary integer environment denotes a value in the variable's
    declared unsigned bitvector range, independently of the ambient width. -/
theorem variable_encoding_range (env : SMTEnv) (ambient width : Nat) (name : String) :
    0 ≤ TrustIrExpr.evalAt env ambient (.var name width) ∧
    TrustIrExpr.evalAt env ambient (.var name width) < (2 : Int) ^ width := by
  have positive : 0 < (2 : Int) ^ width := by
    have castPower : (2 : Int) ^ width = ((2 ^ width : Nat) : Int) :=
      (Int.natCast_pow 2 width).symm
    rw [castPower]
    trustIrCompilerProof { exact Int.ofNat_pos.mpr (Nat.two_pow_pos width) } { exact Int.natCast_pos.mpr (Nat.two_pow_pos width) }
  have nonzero : (2 : Int) ^ width ≠ 0 := by
    intro h
    rw [h] at positive
    exact (Int.lt_irrefl 0) positive
  exact ⟨Int.emod_nonneg _ nonzero, Int.emod_lt_of_pos _ positive⟩

/-- Expose the actual signed division evaluator through the shared signed
representation and residue operations, including both total-operation branches. -/
theorem bvSDiv_evalAt_semantics (env : SMTEnv) (width : Nat) (left right : TrustIrExpr) :
    (.bvSDiv left right : TrustIrExpr).evalAt env width =
      truncateUnsigned (if toSigned (right.evalAt env width) width == 0 then
        (if toSigned (left.evalAt env width) width < 0 then 1 else -1)
      else trustIrIntTDiv (toSigned (left.evalAt env width) width)
        (toSigned (right.evalAt env width) width)) width := by
  simp only [TrustIrExpr.evalAt, toSignedBV_eq_toSigned, truncBV_eq_truncateUnsigned]
  split <;> simp_all only [if_pos, if_neg]

/-- Expose the actual signed remainder evaluator without discarding divisor zero. -/
theorem bvSRem_evalAt_semantics (env : SMTEnv) (width : Nat) (left right : TrustIrExpr) :
    (.bvSRem left right : TrustIrExpr).evalAt env width =
      truncateUnsigned (if toSigned (right.evalAt env width) width == 0 then left.evalAt env width
      else trustIrIntTMod (toSigned (left.evalAt env width) width)
        (toSigned (right.evalAt env width) width)) width := by
  simp only [TrustIrExpr.evalAt, toSignedBV_eq_toSigned, truncBV_eq_truncateUnsigned]
  split <;> simp_all only [if_pos, if_neg]

/-- Expose the existing guarded bvShl evaluator through the shared residue operation. -/
theorem bvShl_evalAt_semantics (env : SMTEnv) (width : Nat) (left right : TrustIrExpr) :
    (.bvShl left right : TrustIrExpr).evalAt env width =
      truncateUnsigned (if (right.evalAt env width).toNat < width then
        left.evalAt env width * (2 : Int) ^ (right.evalAt env width).toNat else 0) width := by
  simp only [TrustIrExpr.evalAt, truncBV_eq_truncateUnsigned]
  split <;> simp_all only [if_pos, if_neg, truncateUnsigned, Int.zero_emod]

/-- Expose the existing guarded bvLShr evaluator through the shared residue operation. -/
theorem bvLShr_evalAt_semantics (env : SMTEnv) (width : Nat) (left right : TrustIrExpr) :
    (.bvLShr left right : TrustIrExpr).evalAt env width =
      truncateUnsigned (if (right.evalAt env width).toNat < width then
        left.evalAt env width / (2 : Int) ^ (right.evalAt env width).toNat else 0) width := by
  simp only [TrustIrExpr.evalAt, truncBV_eq_truncateUnsigned]
  split <;> simp_all only [if_pos, if_neg, truncateUnsigned, Int.zero_emod]

/-- Expose the existing guarded arithmetic shift, including signed-fill saturation. -/
theorem bvAShr_evalAt_semantics (env : SMTEnv) (width : Nat) (left right : TrustIrExpr) :
    (.bvAShr left right : TrustIrExpr).evalAt env width =
      truncateUnsigned (if (right.evalAt env width).toNat < width then
        Int.fdiv (toSigned (left.evalAt env width) width) ((2 : Int) ^ (right.evalAt env width).toNat)
      else if toSigned (left.evalAt env width) width < 0 then -1 else 0) width := by
  simp only [TrustIrExpr.evalAt, toSignedBV_eq_toSigned, truncBV_eq_truncateUnsigned]
  by_cases small : (right.evalAt env width).toNat < width
  · simp only [small, if_true]
  · by_cases negative : toSigned (left.evalAt env width) width < 0 <;>
      simp only [small, negative, if_false, if_true, truncateUnsigned, Int.zero_emod]

-- SMT-LIB bitvector operations are total even where the corresponding IR
-- instruction has a definedness precondition. These reductions check the
-- zero-divisor cases independently of any solver or native_decide.
example : TrustIrExpr.evalAt SMTEnv.default 8
    (.bvUDiv (.bvConst 8 7) (.bvConst 8 0)) = 255 := by decide
example : TrustIrExpr.evalAt SMTEnv.default 8
    (.bvSDiv (.bvConst 8 7) (.bvConst 8 0)) = 255 := by decide
example : TrustIrExpr.evalAt SMTEnv.default 8
    (.bvSDiv (.bvConst 8 (-7)) (.bvConst 8 0)) = 1 := by decide
example : TrustIrExpr.evalAt SMTEnv.default 8
    (.bvURem (.bvConst 8 7) (.bvConst 8 0)) = 7 := by decide
example : TrustIrExpr.evalAt SMTEnv.default 8
    (.bvSRem (.bvConst 8 (-7)) (.bvConst 8 0)) = 249 := by decide
-- Signed division still truncates toward zero and wraps MIN / -1.
example : TrustIrExpr.evalAt SMTEnv.default 8
    (.bvSDiv (.bvConst 8 (-7)) (.bvConst 8 2)) = 253 := by decide
example : TrustIrExpr.evalAt SMTEnv.default 8
    (.bvSDiv (.bvConst 8 (-128)) (.bvConst 8 (-1))) = 128 := by decide
example : TrustIrExpr.evalAt SMTEnv.default 8
    (.bvSRem (.bvConst 8 (-7)) (.bvConst 8 3)) = 255 := by decide
-- Variables carry their declared width even when the ambient operation width
-- differs. Unbounded environment integers cannot falsify unsigned order.
example : TrustIrExpr.evalAt (fun _ => -1) 64 (.var "x" 8) = 255 := by decide
example : TrustIrExpr.evalAt (fun _ => 257) 64 (.var "x" 8) = 1 := by decide
example : TrustIrExpr.evalAt (fun _ => -1) 8
    (.bvUlt (.var "x" 8) (.bvConst 8 0)) = 0 := by decide

-- Oversized shifts are total and do not construct a power of the shift
-- amount. The all-ones 64-bit amount exercises the resource failure directly.
example : TrustIrExpr.evalAt SMTEnv.default 64
    (.bvShl (.bvConst 64 1) (.bvConst 64 (-1))) = 0 := by decide
example : TrustIrExpr.evalAt SMTEnv.default 64
    (.bvLShr (.bvConst 64 (-1)) (.bvConst 64 (-1))) = 0 := by decide
example : TrustIrExpr.evalAt SMTEnv.default 64
    (.bvAShr (.bvConst 64 (-2)) (.bvConst 64 (-1))) = 18446744073709551615 := by decide
example : TrustIrExpr.evalAt SMTEnv.default 8
    (.bvAShr (.bvConst 8 127) (.bvConst 8 8)) = 0 := by decide
example : TrustIrExpr.evalAt SMTEnv.default 8
    (.bvAShr (.bvConst 8 (-2)) (.bvConst 8 8)) = 255 := by decide
example : TrustIrExpr.evalAt SMTEnv.default 8
    (.bvShl (.bvConst 8 1) (.bvConst 8 7)) = 128 := by decide
example : TrustIrExpr.evalAt SMTEnv.default 8
    (.bvLShr (.bvConst 8 128) (.bvConst 8 7)) = 1 := by decide
example : TrustIrExpr.evalAt SMTEnv.default 8
    (.bvAShr (.bvConst 8 (-128)) (.bvConst 8 7)) = 255 := by decide

/-- Backward-compatible eval: defaults to 64-bit width. -/
def TrustIrExpr.eval (env : SMTEnv) (expr : TrustIrExpr) : Int :=
  expr.evalAt env 64

-- =================================================================
-- Encoding TrustIr operations as SMT expressions
-- =================================================================

/-- Encode the integer/Bool SMT fragment. Float operations have no bit-vector
    encoding here; callers must retain and check the successful result. -/
def encodeBinOp (op : BinOp) (lhs rhs : TrustIrExpr) : Option TrustIrExpr :=
  match op with
  | .Add   => some (.bvAdd lhs rhs)
  | .Sub   => some (.bvSub lhs rhs)
  | .Mul   => some (.bvMul lhs rhs)
  | .UDiv  => some (.bvUDiv lhs rhs)
  | .SDiv  => some (.bvSDiv lhs rhs)
  | .URem  => some (.bvURem lhs rhs)
  | .SRem  => some (.bvSRem lhs rhs)
  | .FAdd | .FSub | .FMul | .FDiv | .FRem | .FMin | .FMax | .FCopySign => none
  | .And   => some (.bvAnd lhs rhs)
  | .Or    => some (.bvOr lhs rhs)
  | .Xor   => some (.bvXor lhs rhs)
  | .Shl   => some (.bvShl lhs rhs)
  | .LShr  => some (.bvLShr lhs rhs)
  | .AShr  => some (.bvAShr lhs rhs)
  -- Bool connectives. On the 0/1 carrier the bitwise BV ops agree pointwise with
  -- the logical ones, so this encoding is exact for well-formed Bool operands --
  -- and the SOLVER side, unlike the Clean prelude's opaque `Int.lor`, reasons
  -- about `bvAnd`/`bvOr`/`bvXor` natively.
  | .BAnd  => some (.bvAnd lhs rhs)
  | .BOr   => some (.bvOr lhs rhs)
  | .BXor  => some (.bvXor lhs rhs)
  -- WS3.20 rotates: exact (the adapter's `encode_rotate` and `semIntBinOp`
  -- state the same modulo-width definition).
  | .RotL  => some (.bvRotL lhs rhs)
  | .RotR  => some (.bvRotR lhs rhs)

/-- Decode an encoded integer result under the IR's definedness policy.
    SMT arithmetic is total; an SMT result does not discharge these guards.
    Bitwise results enter the same residue representation as the IR. -/
def decodeIntBinOpEncoding (op : BinOp) (width : Nat) (lhs rhs result : Int) :
    Except SemError Int :=
  match op with
  | .UDiv => if rhs == 0 then .error (.ub "unsigned division by zero") else .ok result
  | .URem => if rhs == 0 then .error (.ub "unsigned remainder by zero") else .ok result
  | .SDiv | .SRem =>
    if rhs == 0 then
      .error (.ub (if op == .SDiv then "signed division by zero" else "signed remainder by zero"))
    else if toSigned lhs width == -((2 : Int) ^ (width - 1)) && toSigned rhs width == -1 then
      .error (.ub (if op == .SDiv then "signed division overflow (INT_MIN / -1)"
        else "signed remainder overflow (INT_MIN % -1)"))
    else .ok result
  | .Shl | .LShr | .AShr =>
    if rhs ≥ (width : Int) then .error (.ub "shift amount out of range") else .ok result
  | .And | .Or | .Xor => .ok (truncateUnsigned result width)
  | .FAdd | .FSub | .FMul | .FDiv | .FRem | .FMin | .FMax | .FCopySign =>
    .error (.typeError "float operation on integer operands")
  | _ => .ok result

private theorem truncBV_of_residue (width : Nat) (v : Int)
    (nonnegative : 0 ≤ v) (bound : v < (2 : Int) ^ width) : truncBV v width = v := by
  rw [truncBV_eq_truncateUnsigned]
  exact Int.emod_eq_of_lt nonnegative bound

private theorem signed_nonzero_of_residue (width : Nat) (v : Int)
    (nonnegative : 0 ≤ v) (bound : v < (2 : Int) ^ width) (nonzero : v ≠ 0) :
    toSigned v width ≠ 0 := by
  dsimp only [toSigned]
  rw [Int.emod_eq_of_lt nonnegative bound]
  split <;> omega

/-- Complete IR outcome for every successfully encoded integer operation.
    Operand bounds are representation facts. Only Boolean opcodes additionally
    require the actual 0/1 Bool carrier. No premise assumes definedness or a
    result: all IR errors are retained by the decoder. -/
theorem int_binop_encoding_outcome (op : BinOp) (width : Nat) (lhs rhs : Int)
    (leftNonnegative : 0 ≤ lhs) (leftBound : lhs < (2 : Int) ^ width)
    (rightNonnegative : 0 ≤ rhs) (rightBound : rhs < (2 : Int) ^ width)
    (boolOperands : op = .BAnd ∨ op = .BOr ∨ op = .BXor →
      (lhs = 0 ∨ lhs = 1) ∧ (rhs = 0 ∨ rhs = 1))
    (encoded : TrustIrExpr)
    (encoding : encodeBinOp op (.bvConst width lhs) (.bvConst width rhs) = some encoded)
    (env : SMTEnv) :
    semIntBinOp op width lhs rhs =
      decodeIntBinOpEncoding op width lhs rhs (encoded.evalAt env width) := by
  have left := truncBV_of_residue width lhs leftNonnegative leftBound
  have right := truncBV_of_residue width rhs rightNonnegative rightBound
  have rightNat : (rhs.toNat : Int) = rhs := Int.toNat_of_nonneg rightNonnegative
  cases op <;> simp [encodeBinOp] at encoding
  all_goals subst encoded
  all_goals simp only [semIntBinOp, decodeIntBinOpEncoding, TrustIrExpr.evalAt,
    left, right, toSignedBV_eq_toSigned, truncBV_eq_truncateUnsigned]
  all_goals try simp only [truncateUnsigned, Int.add_emod, Int.emod_emod, Int.emod_self,
    Int.add_zero]
  all_goals try rfl
  case UDiv => by_cases zero : rhs = 0 <;> simp [zero]
  case URem => by_cases zero : rhs = 0 <;> simp [zero]
  case SDiv =>
    by_cases zero : rhs = 0
    · simp [zero]
    · have signed := signed_nonzero_of_residue width rhs rightNonnegative rightBound zero
      simp [zero, signed]
  case SRem =>
    by_cases zero : rhs = 0
    · simp [zero]
    · have signed := signed_nonzero_of_residue width rhs rightNonnegative rightBound zero
      simp [zero, signed]
  case Shl =>
    by_cases large : rhs ≥ (width : Int)
    · simp [large]
    · have small : rhs.toNat < width := by omega
      simp [large, small]
  case LShr =>
    by_cases large : rhs ≥ (width : Int)
    · simp [large]
    · have small : rhs.toNat < width := by omega
      simp [large, small]
  case AShr =>
    by_cases large : rhs ≥ (width : Int)
    · simp [large]
    · have small : rhs.toNat < width := by omega
      simp [large, small]
  case BAnd =>
    obtain ⟨l, r⟩ := boolOperands (Or.inl rfl)
    rcases l with rfl | rfl <;> rcases r with rfl | rfl <;> rfl
  case BOr =>
    obtain ⟨l, r⟩ := boolOperands (Or.inr (Or.inl rfl))
    rcases l with rfl | rfl <;> rcases r with rfl | rfl <;> rfl
  case BXor =>
    obtain ⟨l, r⟩ := boolOperands (Or.inr (Or.inr rfl))
    rcases l with rfl | rfl <;> rcases r with rfl | rfl <;> rfl
  case RotL => simp [Int.emod_eq_of_lt leftNonnegative leftBound,
    Int.emod_eq_of_lt rightNonnegative rightBound]
  case RotR => simp [Int.emod_eq_of_lt leftNonnegative leftBound,
    Int.emod_eq_of_lt rightNonnegative rightBound]

/-- The actual integer value consumer preserves the decoded error or binds
    the exact encoded result at the original width. The type parameter is
    retained as the consumer uses it; this law confers no type admission. -/
theorem int_binop_values_encoding_outcome (op : BinOp) (ty : Ty) (width : Nat)
    (lhs rhs : Int)
    (leftNonnegative : 0 ≤ lhs) (leftBound : lhs < (2 : Int) ^ width)
    (rightNonnegative : 0 ≤ rhs) (rightBound : rhs < (2 : Int) ^ width)
    (boolOperands : op = .BAnd ∨ op = .BOr ∨ op = .BXor →
      (lhs = 0 ∨ lhs = 1) ∧ (rhs = 0 ∨ rhs = 1))
    (encoded : TrustIrExpr)
    (encoding : encodeBinOp op (.bvConst width lhs) (.bvConst width rhs) = some encoded)
    (env : SMTEnv) :
    semBinOpValues op ty (.int width lhs) (.int width rhs) =
      (do let result ← decodeIntBinOpEncoding op width lhs rhs (encoded.evalAt env width)
          pure (.int width result)) := by
  have outcome := int_binop_encoding_outcome op width lhs rhs leftNonnegative leftBound
    rightNonnegative rightBound boolOperands encoded encoding env
  cases ty <;> simp [semBinOpValues, outcome]

/-- Encode a TrustIr ICmpOp as a TrustIrExpr combinator. -/
def encodeICmp (op : ICmpOp) (lhs rhs : TrustIrExpr) : TrustIrExpr :=
  match op with
  | .Eq  => .eq lhs rhs
  | .Ne  => .boolNot (.eq lhs rhs)
  | .Ult => .bvUlt lhs rhs
  | .Ule => .bvUle lhs rhs
  | .Ugt => .bvUlt rhs lhs
  | .Uge => .bvUle rhs lhs
  | .Slt => .bvSlt lhs rhs
  | .Sle => .bvSle lhs rhs
  | .Sgt => .bvSlt rhs lhs
  | .Sge => .bvSle rhs lhs

/-- Every encoded comparison agrees with the actual integer predicate at the
    ambient width. The operands are the actual evaluated expressions, so this
    law does not assume that an unrelated pair of integers is represented.
    Signed predicates normalize exactly as the instruction semantics does. -/
theorem icmp_encoding_correct_at (op : ICmpOp) (env : SMTEnv) (width : Nat)
    (lhs rhs : TrustIrExpr) :
    (encodeICmp op lhs rhs).evalAt env width =
      if semICmp op width (lhs.evalAt env width) (rhs.evalAt env width) then 1 else 0 := by
  cases op <;> simp [encodeICmp, TrustIrExpr.evalAt, semICmp,
    toSignedBV_eq_toSigned]

/-- Constants are interpreted using the same residue representation as actual
    integer values, at their declared width rather than the legacy width 64. -/
theorem icmp_constant_encoding_correct (op : ICmpOp) (width : Nat) (lhs rhs : Int)
    (env : SMTEnv) :
    (encodeICmp op (.bvConst width lhs) (.bvConst width rhs)).evalAt env width =
      if semICmp op width (truncateUnsigned lhs width) (truncateUnsigned rhs width)
      then 1 else 0 := by
  rw [icmp_encoding_correct_at]
  simp only [TrustIrExpr.evalAt, truncBV_eq_truncateUnsigned]

/-- The integer-vector consumer uses the same encoded predicate for each
    actual lane. Both input lane lists have the same construction and width. -/
theorem vector_icmp_encoding_correct (op : ICmpOp) (width : Nat)
    (inputs : List (Int × Int)) (env : SMTEnv) :
    semVectorICmp op width
      (inputs.map (fun pair => Value.intAt width pair.1))
      (inputs.map (fun pair => Value.intAt width pair.2)) =
    .ok (inputs.map (fun pair => .bool
      ((encodeICmp op (.bvConst width pair.1) (.bvConst width pair.2)).evalAt env width != 0))) := by
  induction inputs with
  | nil => rfl
  | cons pair rest ih =>
    simp only [List.map_cons, semVectorICmp]
    have read (v : Int) : icmpIntValue width (Value.intAt width v) =
        .ok (truncateUnsigned v width) := by
      trustIrCompilerProof { simp [icmpIntValue, Value.intAt] } {
        simp only [icmpIntValue, Value.intAt]
        have reflexive : (width == width) = true := by
          change decide (width = width) = true
          exact decide_eq_true rfl
        rw [reflexive]
        rfl
      }
    rw [read, read]
    change (do
      let tail ← semVectorICmp op width
        (rest.map (fun (pair : Int × Int) => Value.intAt width pair.1))
        (rest.map (fun (pair : Int × Int) => Value.intAt width pair.2))
      pure (Value.bool (semICmp op width (truncateUnsigned pair.1 width)
        (truncateUnsigned pair.2 width)) :: tail) : Except SemError (List Value)) = _
    rw [ih]
    simp only [Except.bind, pure, Except.pure]
    trustIrCompilerProof { congr 2 } {
      apply congrArg (fun answer : Bool => (Except.ok (Value.bool answer ::
        rest.map (fun pair => Value.bool
          ((encodeICmp op (.bvConst width pair.1) (.bvConst width pair.2)).evalAt env width != 0))) :
          Except SemError (List Value)))
    }
    rw [icmp_constant_encoding_correct]
    cases semICmp op width (truncateUnsigned pair.1 width) (truncateUnsigned pair.2 width) <;> rfl

/-- Bind the encoding to the actual scalar value consumer, including its static
    integer type and target layout. Width and integer premises describe the
    selected type; neither premise assumes the comparison's answer. -/
theorem scalar_icmp_values_encoding_correct (op : ICmpOp) (ty : Ty)
    (model : ByteModel) (width : Nat) (integer : ty.isInteger = true)
    (bits : ty.bitWidthFor model = some width)
    (lhs rhs : Int) (env : SMTEnv) :
    semICmpValues op ty (Value.intAt width lhs) (Value.intAt width rhs) model =
      .ok (.bool ((encodeICmp op (.bvConst width lhs) (.bvConst width rhs)).evalAt env width != 0)) := by
  have encoded := icmp_constant_encoding_correct op width lhs rhs env
  cases ty <;> simp_all [Ty.isInteger, semICmpValues, icmpIntValue, Value.intAt,
    bind, Except.bind, pure, Except.pure]
  all_goals cases semICmp op width (truncateUnsigned lhs width) (truncateUnsigned rhs width) <;> rfl

/-- Actual Bool comparison uses signed width one, including the interpretation
    of true as -1 for signed predicates. -/
theorem bool_icmp_values_encoding_correct (op : ICmpOp) (lhs rhs : Bool)
    (model : ByteModel) (env : SMTEnv) :
    semICmpValues op .Bool (.bool lhs) (.bool rhs) model =
      .ok (.bool ((encodeICmp op (.bvConst 1 (if lhs then 1 else 0))
        (.bvConst 1 (if rhs then 1 else 0))).evalAt env 1 != 0)) := by
  rw [icmp_constant_encoding_correct]
  cases lhs <;> cases rhs <;>
    simp [semICmpValues, icmpBoolValue, semBoolICmp, truncateUnsigned,
      bind, Except.bind, pure, Except.pure]
  all_goals cases semICmp op 1 _ _ <;> rfl

/-- The complete vector value consumer, including the actual lane-count and
    admitted-element gates, returns precisely the encoded lane predicates. -/
theorem vector_icmp_values_encoding_correct (op : ICmpOp) (elemTy : Ty)
    (width : Nat) (laneWidth : elemTy.icmpIntLaneWidth? = some width)
    (inputs : List (Int × Int)) (nonempty : inputs.length ≠ 0)
    (model : ByteModel) (env : SMTEnv) :
    semICmpValues op (.Vector inputs.length elemTy)
      (.vector (inputs.map (fun pair => Value.intAt width pair.1)))
      (.vector (inputs.map (fun pair => Value.intAt width pair.2))) model =
    .ok (.vector (inputs.map (fun pair => .bool
      ((encodeICmp op (.bvConst width pair.1) (.bvConst width pair.2)).evalAt env width != 0)))) := by
  cases elemTy <;> simp_all [Ty.icmpIntLaneWidth?, semICmpValues,
    vector_icmp_encoding_correct op width inputs env,
    bind, Except.bind, pure, Except.pure]

-- =================================================================
-- ay oracle interface
-- =================================================================

/-- Result of a ay satisfiability check. -/
inductive AYResult where
  | sat     : AYResult
  | unsat   : AYResult
  | unknown : AYResult
  deriving DecidableEq, Repr

/-- Opaque ay check function. This represents the external call to ay.
    It is intended to be instantiated via FFI or process invocation; it is
    NOT bound today (no `@[extern]`/`@[implemented_by]`), so it is an
    uninstantiated framework hook — no `ay_check width e = .unsat` fact can be
    produced inside Lean until that binding and the checked certificate
    importer land. The width is mandatory and is the ambient operation width
    used by the expression evaluator and SMT-LIB serializer. -/
instance : Inhabited AYResult := Inhabited.mk .unknown

opaque ay_check : (width : Nat) -> TrustIrExpr -> AYResult

-- =================================================================
-- Reflection: TrustIrExpr to Lean Prop
-- =================================================================

/-- Interpret a TrustIrExpr as a Lean Prop.
    A formula is "true" if it evaluates to nonzero for all environments. -/
def TrustIrExpr.toProp (expr : TrustIrExpr) (width : Nat) : Prop :=
  forall env : SMTEnv, expr.evalAt env width != 0

/-- A formula is valid if it holds for all environments. -/
def formula_valid (width : Nat) (expr : TrustIrExpr) : Prop :=
  TrustIrExpr.toProp expr width

/-- A formula is unsatisfiable if no environment makes it true. -/
def formula_unsat (width : Nat) (expr : TrustIrExpr) : Prop :=
  forall env : SMTEnv, expr.evalAt env width = 0

-- =================================================================
-- Soundness axiom
-- =================================================================

/-- The ay soundness axiom: if ay reports UNSAT for a formula,
    then the formula is indeed unsatisfiable (no environment satisfies it).

    This is the sole declared project axiom for the ay bridge. The request's
    operation width is part of the premise and conclusion. Hook binding,
    certificate import and serializer soundness remain separate obligations.

    Trust justification:
    - ay is a mature, extensively tested SMT solver
    - ay supports proof certificate generation for independent checking
    - In production, we can validate ay's certificates with an independent
      checker (reducing trust to the checker, not ay itself) -/
axiom ay_sound_unsat :
  forall (width : Nat) (expr : TrustIrExpr),
    ay_check width expr = .unsat -> formula_unsat width expr

/-- Contrapositive of soundness: if a formula IS satisfiable (some env
    makes it nonzero), then ay does NOT report UNSAT.
    This follows logically from ay_sound_unsat. -/
theorem ay_sound_contrapositive (width : Nat) (expr : TrustIrExpr)
    (hSat : exists (env : SMTEnv), expr.evalAt env width ≠ 0) :
    ay_check width expr ≠ .unsat := by
  intro hUnsat
  have hAllZero := ay_sound_unsat width expr hUnsat
  match hSat with
  | ⟨env, hNonzero⟩ => exact absurd (hAllZero env) hNonzero

-- =================================================================
-- Verification of instruction equivalence via ay
-- =================================================================

/-- Two TrustIrExpr are equivalent if they evaluate to the same value
    in every environment. -/
def expr_equiv (width : Nat) (e1 e2 : TrustIrExpr) : Prop :=
  forall env : SMTEnv, e1.evalAt env width = e2.evalAt env width

/-- To check expr_equiv via ay, we check UNSAT of (e1 != e2).
    If ay says UNSAT for (e1 xor e2) -- i.e., they can never differ --
    then e1 and e2 are equivalent. -/
def expr_diff (e1 e2 : TrustIrExpr) : TrustIrExpr :=
  .boolNot (.eq e1 e2)

/-- ay-verified expression equivalence: if ay says the expressions
    can never differ, they are equivalent. -/
theorem ay_expr_equiv (width : Nat) (e1 e2 : TrustIrExpr)
    (hUnsat : ay_check width (expr_diff e1 e2) = .unsat) :
    expr_equiv width e1 e2 := by
  trustIrCompilerProof {
    have hAllZero := ay_sound_unsat width (expr_diff e1 e2) hUnsat
    intro env
    have hZero := hAllZero env
    simp only [expr_diff, TrustIrExpr.evalAt, formula_unsat] at hZero
    by_cases h : TrustIrExpr.evalAt env width e1 = TrustIrExpr.evalAt env width e2
    · exact h
    · -- A difference would make the asserted disequality true at this width.
      exfalso
      simp [TrustIrExpr.evalAt, h] at hZero
  } {
    have hAllZero := ay_sound_unsat width (expr_diff e1 e2) hUnsat
    intro env
    have hZero := hAllZero env
    change (if ((if e1.evalAt env width == e2.evalAt env width then (1 : Int) else 0) == 0)
      then (1 : Int) else 0) = 0 at hZero
    cases same : e1.evalAt env width == e2.evalAt env width with
    | true => exact eq_of_beq same
    | false =>
      rw [same] at hZero
      change (1 : Int) = 0 at hZero
      cases hZero
  }

-- =================================================================
-- Verified constant folding via ay
-- =================================================================

/-- ay-verified constant fold: if ay confirms that a BinOp on two
    constants equals a known result, the fold is sound.

    Usage by TrustCg:
    1. Observe BinOp op (Const w a) (Const w b) in the IR
    2. Compute candidate result r
    3. Ask ay: is (encodeBinOp op (bvConst w a) (bvConst w b)) == (bvConst w r)?
    4. If ay says UNSAT for the negation, apply this theorem -/
theorem ay_constant_fold (op : BinOp) (width : Nat)
    (lhsVal rhsVal result : Int) (encoded : TrustIrExpr)
    (hEncoded : encodeBinOp op (.bvConst width lhsVal) (.bvConst width rhsVal) = some encoded)
    (hAY : ay_check width (expr_diff encoded (.bvConst width result)) = .unsat) :
    ∃ expression, encodeBinOp op (.bvConst width lhsVal) (.bvConst width rhsVal) = some expression ∧
      expr_equiv width expression (.bvConst width result) :=
  ⟨encoded, hEncoded, ay_expr_equiv width _ _ hAY⟩

/-- Width is semantic input: the same encoded byte addition wraps at width
    eight and differs from zero at width 64. An oracle result at one width
    therefore cannot establish a fold at the other width. -/
theorem byte_add_width_distinguishes :
    let difference := expr_diff (.bvAdd (.bvConst 8 255) (.bvConst 8 1)) (.bvConst 8 0)
    difference.evalAt SMTEnv.default 8 = 0 ∧ difference.evalAt SMTEnv.default 64 = 1 := by
  decide

/-- AY equivalence at the operation's width preserves the full IR outcome.
    A total SMT fold does not remove undefinedness errors from the decoder. -/
theorem ay_constant_fold_outcome (op : BinOp) (width : Nat) (lhs rhs result : Int)
    (leftNonnegative : 0 ≤ lhs) (leftBound : lhs < (2 : Int) ^ width)
    (rightNonnegative : 0 ≤ rhs) (rightBound : rhs < (2 : Int) ^ width)
    (boolOperands : op = .BAnd ∨ op = .BOr ∨ op = .BXor →
      (lhs = 0 ∨ lhs = 1) ∧ (rhs = 0 ∨ rhs = 1))
    (encoded : TrustIrExpr)
    (encoding : encodeBinOp op (.bvConst width lhs) (.bvConst width rhs) = some encoded)
    (hAY : ay_check width (expr_diff encoded (.bvConst width result)) = .unsat) :
    semIntBinOp op width lhs rhs =
      decodeIntBinOpEncoding op width lhs rhs (truncateUnsigned result width) := by
  have equivalent := ay_expr_equiv width encoded (.bvConst width result) hAY SMTEnv.default
  have outcome := int_binop_encoding_outcome op width lhs rhs leftNonnegative leftBound
    rightNonnegative rightBound boolOperands encoded encoding SMTEnv.default
  rw [equivalent] at outcome
  simpa only [TrustIrExpr.evalAt, truncBV_eq_truncateUnsigned] using outcome

/-- Floating-point min/max cannot acquire an SMT fold through this integer encoder. -/
theorem minmax_encoding_refused (lhs rhs : TrustIrExpr) :
    encodeBinOp .FMin lhs rhs = none ∧ encodeBinOp .FMax lhs rhs = none := by
  constructor <;> rfl

-- =================================================================
-- Bridge from SMT equivalence to TrustIr inst_equiv
-- =================================================================

/-- Two instructions are TrustIr-equivalent if they produce the same
    result on every machine state. (Same definition as in
    TransformCorrectness.lean, repeated here for self-containedness.) -/
def ay_inst_equiv (i1 i2 : Inst) : Prop :=
  forall s, Sem.run (stepInst i1) s = Sem.run (stepInst i2) s

/-- Decode the SMT result in the original state into the complete instruction
    outcome. Sharing this decoder between two encodings preserves result lanes,
    errors and the final machine state, not just a scalar return value. -/
abbrev InstructionDecoder :=
  MachineState -> Int -> Except SemError (InstrResult × MachineState)

/-- Preserve an encoded value error or perform the actual fresh SSA binding.
    The original state supplies both the result identifier and all retained
    memory, permissions, globals, exceptions and execution-choice state. -/
def bindEncodedValue (state : MachineState) (outcome : Except SemError Value) :
    Except SemError (InstrResult × MachineState) := do
  let value ← outcome
  let (id, final) := state.bindValue value
  pure (.value (some id), final)

/-- Complete stateful outcome of an actually encoded integer instruction.
    The lookup premises identify its real operands. Representation premises
    retain their existing meaning; neither definedness nor the final result
    is assumed. All target models and all remaining machine fields are covered. -/
theorem int_binop_step_encoding_outcome (op : BinOp) (ty : Ty) (width : Nat)
    (leftId rightId : ValueId) (state : MachineState) (model : ByteModel)
    (lhs rhs : Int)
    (leftLookup : state.lookupValue leftId = some (.int width lhs))
    (rightLookup : state.lookupValue rightId = some (.int width rhs))
    (leftNonnegative : 0 ≤ lhs) (leftBound : lhs < (2 : Int) ^ width)
    (rightNonnegative : 0 ≤ rhs) (rightBound : rhs < (2 : Int) ^ width)
    (boolOperands : op = .BAnd ∨ op = .BOr ∨ op = .BXor →
      (lhs = 0 ∨ lhs = 1) ∧ (rhs = 0 ∨ rhs = 1))
    (encoded : TrustIrExpr)
    (encoding : encodeBinOp op (.bvConst width lhs) (.bvConst width rhs) = some encoded)
    (env : SMTEnv) :
    Sem.run (stepInst (.BinOp op ty leftId rightId) model) state =
      bindEncodedValue state (do
        let result ← decodeIntBinOpEncoding op width lhs rhs (encoded.evalAt env width)
        pure (.int width result)) := by
  have notMinMax : op.isMinMax = false := by
    cases op <;> simp_all [BinOp.isMinMax, encodeBinOp]
  have outcome := int_binop_values_encoding_outcome op ty width lhs rhs
    leftNonnegative leftBound rightNonnegative rightBound boolOperands encoded encoding env
  cases decoded : decodeIntBinOpEncoding op width lhs rhs (encoded.evalAt env width) <;>
    simp [stepInst, semBinOp, notMinMax, semBinOpDeterministic,
    Sem.lookupValue, leftLookup, rightLookup, Sem.rejectPartial,
    outcome, decoded, Sem.run, Sem.getState, Sem.setState, Sem.bindFresh,
    StateT.run, StateT.bind, StateT.get, StateT.set, StateT.pure, StateT.lift,
    bindEncodedValue, bind, pure, throw, throwThe, MonadExceptOf.throw, Except.bind, Except.pure]

/-- The contextual evaluator uses the same integer instruction path. Its
    original byte model is retained; the typed Bool override is separate. -/
theorem int_binop_context_encoding_outcome (op : BinOp) (ty : Ty) (width : Nat)
    (integer : ty.isInteger = true) (ctx : EvalContext)
    (leftId rightId : ValueId) (state : MachineState) (lhs rhs : Int)
    (leftLookup : state.lookupValue leftId = some (.int width lhs))
    (rightLookup : state.lookupValue rightId = some (.int width rhs))
    (leftNonnegative : 0 ≤ lhs) (leftBound : lhs < (2 : Int) ^ width)
    (rightNonnegative : 0 ≤ rhs) (rightBound : rhs < (2 : Int) ^ width)
    (boolOperands : op = .BAnd ∨ op = .BOr ∨ op = .BXor →
      (lhs = 0 ∨ lhs = 1) ∧ (rhs = 0 ∨ rhs = 1))
    (encoded : TrustIrExpr)
    (encoding : encodeBinOp op (.bvConst width lhs) (.bvConst width rhs) = some encoded)
    (env : SMTEnv) :
    Sem.run (stepInstWithContext ctx (.BinOp op ty leftId rightId)) state =
      bindEncodedValue state (do
        let result ← decodeIntBinOpEncoding op width lhs rhs (encoded.evalAt env width)
        pure (.int width result)) := by
  have bare := int_binop_step_encoding_outcome op ty width leftId rightId state ctx.byteModel
    lhs rhs leftLookup rightLookup leftNonnegative leftBound rightNonnegative rightBound
    boolOperands encoded encoding env
  cases ty <;> simp_all [Ty.isInteger, stepInstWithContext]

/-- Width-bound AY evidence reaches the actual contextual instruction's
    complete error or final state, under the real operand lookup premises. -/
theorem ay_constant_fold_context_outcome (op : BinOp) (ty : Ty) (width : Nat)
    (integer : ty.isInteger = true) (ctx : EvalContext)
    (leftId rightId : ValueId) (state : MachineState) (lhs rhs result : Int)
    (leftLookup : state.lookupValue leftId = some (.int width lhs))
    (rightLookup : state.lookupValue rightId = some (.int width rhs))
    (leftNonnegative : 0 ≤ lhs) (leftBound : lhs < (2 : Int) ^ width)
    (rightNonnegative : 0 ≤ rhs) (rightBound : rhs < (2 : Int) ^ width)
    (boolOperands : op = .BAnd ∨ op = .BOr ∨ op = .BXor →
      (lhs = 0 ∨ lhs = 1) ∧ (rhs = 0 ∨ rhs = 1))
    (encoded : TrustIrExpr)
    (encoding : encodeBinOp op (.bvConst width lhs) (.bvConst width rhs) = some encoded)
    (hAY : ay_check width (expr_diff encoded (.bvConst width result)) = .unsat) :
    Sem.run (stepInstWithContext ctx (.BinOp op ty leftId rightId)) state =
      bindEncodedValue state (do
        let folded ← decodeIntBinOpEncoding op width lhs rhs (truncateUnsigned result width)
        pure (.int width folded)) := by
  have equivalent := ay_expr_equiv width encoded (.bvConst width result) hAY SMTEnv.default
  have outcome := int_binop_context_encoding_outcome op ty width integer ctx leftId rightId
    state lhs rhs leftLookup rightLookup leftNonnegative leftBound rightNonnegative rightBound
    boolOperands encoded encoding SMTEnv.default
  rw [equivalent] at outcome
  simpa only [TrustIrExpr.evalAt, truncBV_eq_truncateUnsigned] using outcome

/-- All ten scalar integer predicates reach actual stateful execution, with
    the target's original width selection and the actual fresh result binding. -/
theorem scalar_icmp_step_encoding_outcome (op : ICmpOp) (ty : Ty) (width : Nat)
    (integer : ty.isInteger = true) (model : ByteModel)
    (bits : ty.bitWidthFor model = some width)
    (leftId rightId : ValueId) (state : MachineState) (lhs rhs : Int)
    (leftLookup : state.lookupValue leftId = some (Value.intAt width lhs))
    (rightLookup : state.lookupValue rightId = some (Value.intAt width rhs))
    (env : SMTEnv) :
    Sem.run (stepInst (.ICmp op ty leftId rightId) model) state =
      bindEncodedValue state (.ok (.bool
        ((encodeICmp op (.bvConst width lhs) (.bvConst width rhs)).evalAt env width != 0))) := by
  have outcome := scalar_icmp_values_encoding_correct op ty model width integer bits lhs rhs env
  simp only [Value.intAt] at outcome
  simp [stepInst, semICmpInst, Sem.lookupValue, leftLookup, rightLookup, Sem.rejectPartial,
    outcome, Value.intAt, Sem.run, Sem.getState, Sem.setState, Sem.bindFresh,
    StateT.run, StateT.bind, StateT.get, StateT.set, StateT.pure,
    bindEncodedValue, bind, pure, Except.bind, Except.pure]

/-- Typed Bool instructions admit only the six logical spellings. An encoded
    arithmetic result cannot erase the actual Bool opcode refusal. -/
def decodeBoolBinOpEncoding (op : BinOp) (result : Int) : Except SemError Value :=
  match op with
  | .And | .BAnd | .Or | .BOr | .Xor | .BXor => .ok (.bool (result != 0))
  | _ => .error (.typeError "boolean binary operation requires a boolean operator")

theorem bool_binop_values_encoding_outcome (op : BinOp) (lhs rhs : Bool)
    (encoded : TrustIrExpr)
    (encoding : encodeBinOp op (.bvConst 1 (if lhs then 1 else 0))
      (.bvConst 1 (if rhs then 1 else 0)) = some encoded) (env : SMTEnv) :
    semBoolBinOpValues op (.bool lhs) (.bool rhs) =
      decodeBoolBinOpEncoding op (encoded.evalAt env 1) := by
  cases op <;> simp [encodeBinOp] at encoding
  all_goals subst encoded
  all_goals cases lhs <;> cases rhs <;> rfl

/-- The actual contextual Bool override preserves its typed opcode refusal
    or binds the exact encoded Boolean result in the original state. -/
theorem bool_binop_context_encoding_outcome (op : BinOp) (ctx : EvalContext)
    (leftId rightId : ValueId) (state : MachineState) (lhs rhs : Bool)
    (leftLookup : state.lookupValue leftId = some (.bool lhs))
    (rightLookup : state.lookupValue rightId = some (.bool rhs))
    (encoded : TrustIrExpr)
    (encoding : encodeBinOp op (.bvConst 1 (if lhs then 1 else 0))
      (.bvConst 1 (if rhs then 1 else 0)) = some encoded) (env : SMTEnv) :
    Sem.run (stepInstWithContext ctx (.BinOp op .Bool leftId rightId)) state =
      bindEncodedValue state (decodeBoolBinOpEncoding op (encoded.evalAt env 1)) := by
  have outcome := bool_binop_values_encoding_outcome op lhs rhs encoded encoding env
  cases decoded : decodeBoolBinOpEncoding op (encoded.evalAt env 1) <;>
    simp [stepInstWithContext, semBoolBinOpInst, Sem.lookupValue, leftLookup, rightLookup,
      outcome, decoded, Sem.run, Sem.getState, Sem.setState, Sem.bindFresh,
      StateT.run, StateT.bind, StateT.get, StateT.set, StateT.pure, StateT.lift,
      bindEncodedValue, bind, pure, throw, throwThe, MonadExceptOf.throw, Except.bind, Except.pure]

/-- Scalar comparison uses the same target-dependent path in the actual
    contextual evaluator. -/
theorem scalar_icmp_context_encoding_outcome (op : ICmpOp) (ty : Ty) (width : Nat)
    (integer : ty.isInteger = true) (ctx : EvalContext)
    (bits : ty.bitWidthFor ctx.byteModel = some width)
    (leftId rightId : ValueId) (state : MachineState) (lhs rhs : Int)
    (leftLookup : state.lookupValue leftId = some (Value.intAt width lhs))
    (rightLookup : state.lookupValue rightId = some (Value.intAt width rhs))
    (env : SMTEnv) :
    Sem.run (stepInstWithContext ctx (.ICmp op ty leftId rightId)) state =
      bindEncodedValue state (.ok (.bool
        ((encodeICmp op (.bvConst width lhs) (.bvConst width rhs)).evalAt env width != 0))) := by
  exact scalar_icmp_step_encoding_outcome op ty width integer ctx.byteModel bits
    leftId rightId state lhs rhs leftLookup rightLookup env

/-- Actual Bool comparison, including signed one-bit ordering, retains the
    original contextual state and actual fresh result identifier. -/
theorem bool_icmp_context_encoding_outcome (op : ICmpOp) (ctx : EvalContext)
    (leftId rightId : ValueId) (state : MachineState) (lhs rhs : Bool)
    (leftLookup : state.lookupValue leftId = some (.bool lhs))
    (rightLookup : state.lookupValue rightId = some (.bool rhs))
    (env : SMTEnv) :
    Sem.run (stepInstWithContext ctx (.ICmp op .Bool leftId rightId)) state =
      bindEncodedValue state (.ok (.bool
        ((encodeICmp op (.bvConst 1 (if lhs then 1 else 0))
          (.bvConst 1 (if rhs then 1 else 0))).evalAt env 1 != 0))) := by
  have outcome := bool_icmp_values_encoding_correct op lhs rhs ctx.byteModel env
  simp [stepInstWithContext, stepInst, semICmpInst, Sem.lookupValue,
    leftLookup, rightLookup, Sem.rejectPartial, outcome,
    Sem.run, Sem.getState, Sem.setState, Sem.bindFresh,
    StateT.run, StateT.bind, StateT.get, StateT.set, StateT.pure,
    bindEncodedValue, bind, pure, Except.bind, Except.pure]

/-- Every admitted integer-vector comparison reaches the actual contextual
    instruction, preserving the complete vector, fresh binding and final state. -/
theorem vector_icmp_context_encoding_outcome (op : ICmpOp) (elemTy : Ty)
    (width : Nat) (laneWidth : elemTy.icmpIntLaneWidth? = some width)
    (inputs : List (Int × Int)) (nonempty : inputs.length ≠ 0)
    (ctx : EvalContext) (leftId rightId : ValueId) (state : MachineState)
    (leftLookup : state.lookupValue leftId =
      some (.vector (inputs.map (fun pair => Value.intAt width pair.1))))
    (rightLookup : state.lookupValue rightId =
      some (.vector (inputs.map (fun pair => Value.intAt width pair.2))))
    (env : SMTEnv) :
    Sem.run (stepInstWithContext ctx (.ICmp op (.Vector inputs.length elemTy) leftId rightId)) state =
      bindEncodedValue state (.ok (.vector (inputs.map (fun pair => .bool
        ((encodeICmp op (.bvConst width pair.1) (.bvConst width pair.2)).evalAt env width != 0))))) := by
  have outcome := vector_icmp_values_encoding_correct op elemTy width laneWidth
    inputs nonempty ctx.byteModel env
  simp [stepInstWithContext, stepInst, semICmpInst, Sem.lookupValue,
    leftLookup, rightLookup, Sem.rejectPartial, outcome,
    Sem.run, Sem.getState, Sem.setState, Sem.bindFresh,
    StateT.run, StateT.bind, StateT.get, StateT.set, StateT.pure,
    bindEncodedValue, bind, pure, Except.bind, Except.pure]

/-- An instruction's encoding is faithful when evaluating and decoding it
    reproduces that instruction's actual monadic behavior on every state.

    Each instruction proves this relation independently against the SAME
    decoder. The previous universal premise quantified over arbitrary unrelated
    instructions and encodings; instantiating it with its own encoding would
    require every instruction to have identical behavior. -/
def encoding_determines_behavior (width : Nat) (inst : Inst) (encode : TrustIrExpr)
    (stateToEnv : MachineState -> SMTEnv) (decode : InstructionDecoder) : Prop :=
  forall s, Sem.run (stepInst inst) s = decode s (encode.evalAt (stateToEnv s) width)

/-- Equivalent SMT expressions imply equivalent instructions when both actual
    instruction executions are faithfully decoded through the same relation.
    Neither faithfulness premise is supplied by the solver. -/
theorem ay_equiv_implies_inst_equiv (width : Nat) (i1 i2 : Inst)
    (encode1 encode2 : TrustIrExpr)
    (stateToEnv : MachineState -> SMTEnv)
    (decode : InstructionDecoder)
    (hEquiv : expr_equiv width encode1 encode2)
    (hFaithful1 : encoding_determines_behavior width i1 encode1 stateToEnv decode)
    (hFaithful2 : encoding_determines_behavior width i2 encode2 stateToEnv decode)
    : ay_inst_equiv i1 i2 := by
  intro s
  calc
    Sem.run (stepInst i1) s = decode s (encode1.evalAt (stateToEnv s) width) := hFaithful1 s
    _ = decode s (encode2.evalAt (stateToEnv s) width) := congrArg (decode s) (hEquiv (stateToEnv s))
    _ = Sem.run (stepInst i2) s := (hFaithful2 s).symm

/-- A concrete inhabitant: Unreachable preserves the state and returns Stuck.
    No oracle, axiom or instruction-equivalence premise constructs this fact. -/
theorem unreachable_encoding_faithful (width : Nat) (encode : TrustIrExpr)
    (stateToEnv : MachineState -> SMTEnv) :
    encoding_determines_behavior width .Unreachable encode stateToEnv
      (fun s _ => .ok (.terminator .Stuck, s)) := by
  intro s
  rfl

/-- A decoder that reports an error cannot faithfully encode Unreachable.
    Equal scalar encodings cannot erase the instruction's outcome. -/
theorem unreachable_error_decoder_refused (width : Nat) (encode : TrustIrExpr)
    (stateToEnv : MachineState -> SMTEnv) (error : SemError) :
    ¬ encoding_determines_behavior width .Unreachable encode stateToEnv
      (fun _ _ => .error error) := by
  intro h
  have bad := h MachineState.empty
  change (Except.ok (.terminator .Stuck, MachineState.empty) :
    Except SemError (InstrResult × MachineState)) = Except.error error at bad
  cases bad

-- =================================================================
-- Concrete encoding correctness lemmas
-- =================================================================

/-- Addition encoding is correct: the SMT encoding of Add matches
    the TrustIr semIntBinOp .Add semantics (both are modular addition). -/
theorem add_encoding_correct (width : Nat) (a b : Int) (encoded : TrustIrExpr)
    (encoding : encodeBinOp .Add (.bvConst width a) (.bvConst width b) = some encoded) :
    TrustIrExpr.eval SMTEnv.default encoded =
    truncBV (truncBV a width + truncBV b width) 64 := by
  simp only [encodeBinOp, Option.some.injEq] at encoding
  subst encoded
  simp [TrustIrExpr.eval, TrustIrExpr.evalAt]

/-- Width-parameterized addition encoding correctness. -/
theorem add_encoding_correct_at (w width : Nat) (a b : Int) (encoded : TrustIrExpr)
    (encoding : encodeBinOp .Add (.bvConst width a) (.bvConst width b) = some encoded) :
    TrustIrExpr.evalAt SMTEnv.default w encoded =
    truncBV (truncBV a width + truncBV b width) w := by
  simp only [encodeBinOp, Option.some.injEq] at encoding
  subst encoded
  simp [TrustIrExpr.evalAt]

/-- Boolean constant encoding: true encodes to 1, false to 0. -/
theorem bool_const_encoding (b : Bool) :
    TrustIrExpr.eval SMTEnv.default (.boolConst b) = if b then 1 else 0 := by
  simp [TrustIrExpr.eval, TrustIrExpr.evalAt]

/-- Equality encoding reflexivity: eq e e always evaluates to 1 (true). -/
theorem eq_refl_encoding (e : TrustIrExpr) (env : SMTEnv) :
    TrustIrExpr.eval env (.eq e e) = 1 := by
  simp [TrustIrExpr.eval, TrustIrExpr.evalAt]

-- =================================================================
-- Future work
-- =================================================================

/-
## Planned extensions

1. **Proof certificate validation:**
   Instead of the ay_sound_unsat axiom, parse ay's proof certificates
   and verify them in Lean. This eliminates trust in ay entirely.
   Reference: Barbosa et al., "Flexible Proof Production in an
   Industrial-Strength SMT Solver", CADE 2023.

2. **Floating-point theory:**
   Extend TrustIrExpr with IEEE 754 floating-point operations (FP theory
   in SMT-LIB). The current integer encoder refuses float operations.

3. **Memory theory:**
   Extend TrustIrExpr with array theory for reasoning about memory
   operations. This enables ay-verified alias analysis.

4. **Quantifier support:**
   Add forall/exists to TrustIrExpr for universally quantified properties
   (e.g., "for all inputs, this optimization is correct").

5. **Incremental solving:**
   Support ay's incremental mode (push/pop) for verifying multiple
   related properties efficiently.

## Instantiating `ay_check` — the precise FFI boundary (audit #86)

`ay_check` is the single uninstantiated hook. Closing it has exactly three
parts, the first two of which are in-repo and the third of which is ay-side:

1. **Serializer (implemented for the current BV/Bool language).**
   `TrustIrExpr.toSMTLib` in `Proofs/AYSMTLib.lean` emits QF_BV scripts with
   checked sorts, positive homogeneous widths and encoded variable names.
   `Tests/AYSMTLib.lean` generates the independent evaluator/oracle corpus.
   Requests now carry a typed target term. `AYTargetCorrect.lean` proves
   whole-language native target value/truth and unsatisfiability correspondence,
   while a fixed-token grammar derivation binds the emitted text to that term.
   This does not bind `ay_check`, import certificates or implement a general
   SMT-LIB parser. IEEE FP vocabulary and mixed-width
   expressions are not represented by this serializer's admitted language.

2. **Certificate path (in-repo, ALREADY MODELLED).** The Rust side already owns
   the request/evidence serializer this bridge would feed:
   `trust_ir::request::NativeVerificationRequest::stable_digest()` and
   `NativeVerificationBundle::stable_digest()` produce the deterministic,
   versioned dispatch identity; `ProofEvidence::SmtProof(..)` /
   `ProofCertificateRef` are the certificate slots an ay UNSAT result lands in;
   `ProofObligation::status = Discharged`/`Certified` is the post-check state.
   That path is real today (the `trust-ir-ay` adapter exercises a parallel
   solver-backed version of it). What is missing is the *link*: a checked
   importer that turns an ay proof certificate into a `ProofEvidence` whose
   acceptance discharges the Lean `ay_sound_unsat` premise (replacing the axiom
   with a kernel-checked certificate per "Planned extension 1").

3. **FFI / process invocation (ay-side, OUT OF THIS REPO).** Binding `ay_check`
   via `@[extern]` or a process call requires the ay solver itself, which lives
   in the `ay` repo and is consumed only through the non-default
   `trust-ir-ay` adapter. This repo cannot instantiate it; doing so is the
   cross-repo step gated on (1) and (2).
-/

-- These semantic connections use no solver axiom or native evaluator.

#trustIrAxiomsExact TrustIr.icmp_encoding_correct_at == [propext, Quot.sound]

#trustIrAxiomsExact TrustIr.icmp_constant_encoding_correct == [propext, Quot.sound]

#trustIrAxiomsExact TrustIr.vector_icmp_encoding_correct == [propext, Quot.sound]

#trustIrAxiomsExact TrustIr.scalar_icmp_values_encoding_correct == [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.bool_icmp_values_encoding_correct == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.vector_icmp_values_encoding_correct == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

-- Complete integer outcomes retain the IR guards without solver authority.

#trustIrAxiomsExact TrustIr.int_binop_encoding_outcome == [propext, Quot.sound, Classical.choice]

#trustIrAxiomsExact TrustIr.int_binop_values_encoding_outcome == [propext, Quot.sound, Classical.choice]

-- Stateful encoding laws retain actual lookup and fresh binding.

#trustIrAxiomsExact TrustIr.int_binop_step_encoding_outcome == [propext, Quot.sound, Classical.choice]

#trustIrAxiomsExact TrustIr.int_binop_context_encoding_outcome == [propext, Classical.choice, Quot.sound]

#trustIrAxiomsExact TrustIr.scalar_icmp_step_encoding_outcome == [propext, Classical.choice, Quot.sound]

#trustIrAxiomsExact TrustIr.bool_binop_values_encoding_outcome == [propext]

#trustIrAxiomsExact TrustIr.bool_binop_context_encoding_outcome == [propext, Classical.choice, Quot.sound]

#trustIrAxiomsExact TrustIr.scalar_icmp_context_encoding_outcome == [propext, Classical.choice, Quot.sound]

#trustIrAxiomsExact TrustIr.bool_icmp_context_encoding_outcome == [propext, Classical.choice, Quot.sound]

#trustIrAxiomsExact TrustIr.vector_icmp_context_encoding_outcome == [propext, Classical.choice, Quot.sound]

-- Width is explicit throughout the oracle-to-instruction contract.

#trustIrAxiomsExact TrustIr.ay_sound_contrapositive == [propext, TrustIr.ay_sound_unsat]

#trustIrAxiomsExact TrustIr.ay_expr_equiv == [propext, TrustIr.ay_sound_unsat, Quot.sound]

#trustIrAxiomsExact TrustIr.ay_constant_fold == [propext, TrustIr.ay_sound_unsat, Quot.sound]

#trustIrAxiomsExact TrustIr.byte_add_width_distinguishes == [propext]

#trustIrAxiomsExact TrustIr.ay_constant_fold_outcome == [propext, TrustIr.ay_sound_unsat, Quot.sound, Classical.choice]

#trustIrAxiomsExact TrustIr.ay_constant_fold_context_outcome == [propext, Classical.choice, Quot.sound, TrustIr.ay_sound_unsat]

#trustIrAxiomsExact TrustIr.ay_equiv_implies_inst_equiv == [propext, Quot.sound, Classical.choice]

end TrustIr

-- Core signed evaluator exposure: exact axiom guards.

#trustIrAxiomsPinned TrustIr.bvSDiv_evalAt_semantics == [propext, Classical.choice, Quot.sound] modern [propext]

#trustIrAxiomsPinned TrustIr.bvSRem_evalAt_semantics == [propext, Classical.choice, Quot.sound] modern [propext]

-- Core shift evaluator exposure: exact axiom guards.

#trustIrAxiomsPinned TrustIr.bvShl_evalAt_semantics == [propext, Classical.choice, Quot.sound] modern [propext]

#trustIrAxiomsPinned TrustIr.bvLShr_evalAt_semantics == [propext, Classical.choice, Quot.sound] modern [propext]

#trustIrAxiomsExact TrustIr.bvAShr_evalAt_semantics == [propext]
