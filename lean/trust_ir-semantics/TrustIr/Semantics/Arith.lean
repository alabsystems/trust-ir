-- Copyright 2026 Andrew Yates
-- Author: Andrew Yates <andrewyates.name@gmail.com>
-- Licensed under the Apache License, Version 2.0
--
-- Arithmetic semantics: BinOp, UnOp, OverflowOp.
-- Phase 1 of the formalization roadmap.
--
-- Reference: designs/2026-04-16-trust_ir-semantics-lean-architecture.md, Section 6 Phase 1
--
-- Design note: Integer arithmetic uses wrapping (modular) semantics.
-- TrustIr integers do not trap on overflow — overflow checking is done
-- via separate OverflowOp instructions that return (result, flag) pairs.
-- This matches LLVM IR semantics.

import TrustIr.BinOp
import TrustIr.Semantics.Monad
import TrustIr.Semantics.FloatFormat
import TrustIr.Semantics.IntRepresentation

namespace TrustIr

/-!
# Arithmetic Semantics

## Integer Arithmetic

All integer operations use wrapping (modular) semantics at the
specified bit width. This mirrors LLVM IR: `add` wraps, `add.overflow`
returns a flag.

For Lean 4, we use `Int` with explicit modular reduction via `truncate`.

## Floating-Point Arithmetic

Floating-point operations are axiomatized in Phase 1. Full IEEE 754
semantics (rounding modes, NaN propagation, subnormals) is future work.
This follows the Aeneas approach.

## Division and Remainder

Division by zero is UB (undefined behavior), matching LLVM IR semantics.
The semantic function returns `SemError.ub` in this case.
-/

-- =================================================================
-- WS3.20 (F-057) bit intrinsics: total functions on the `width`-bit residue
-- =================================================================

/-- Count leading zero bits of `value` viewed as a `width`-bit unsigned
    integer (bits above `width` are ignored). TOTAL: `ctlzWidth 0 w = w` —
    the ONE spelling the format has (no `is_zero_poison` operand). Recursion
    peels the TOP bit: at width `w + 1` the top bit is bit `w`. Mirrors the
    reference interpreter (`eval_int_unop`, `UnOp::CtLz`). -/
def ctlzWidth (value : Nat) : Nat → Nat
  | 0 => 0
  | w + 1 => if (value / 2 ^ w) % 2 == 1 then 0 else 1 + ctlzWidth value w

/-- Count trailing zero bits of the `width`-bit residue of `value`. TOTAL:
    `cttzWidth 0 w = w`. Recursion peels the BOTTOM bit. -/
def cttzWidth (value : Nat) : Nat → Nat
  | 0 => 0
  | w + 1 => if value % 2 == 1 then 0 else 1 + cttzWidth (value / 2) w

/-- Reverse the low `width` bits of `value`: bit `i` moves to bit
    `width - 1 - i`. Recursion moves the bottom bit to the top of the
    remaining width. -/
def bitReverseWidth (value : Nat) : Nat → Nat
  | 0 => 0
  | w + 1 => (value % 2) * 2 ^ w + bitReverseWidth (value / 2) w

/-- Reverse the order of the low `n` BYTES of `value` (`bswapWidth` derives
    `n` from the width; every TrustIr integer width is a whole number of
    bytes, and at one byte this is the identity). -/
def bswapBytes (value : Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => (value % 256) * 256 ^ n + bswapBytes (value / 256) n

/-- Byte swap of the `width`-bit residue of `value` (Rust `swap_bytes`,
    LLVM `bswap`). -/
def bswapWidth (value width : Nat) : Nat :=
  bswapBytes value (width / 8)

/-- Rotate the `width`-bit residue of `value` LEFT by `amount` positions.
    TOTAL: the amount is reduced modulo the width (Rust `rotate_left`, LLVM
    `fshl(x, x, n)`), so there is no out-of-range UB, unlike `Shl`. The two
    halves `(value <<< n) mod 2^w` and `value >>> (w - n)` occupy disjoint
    bit ranges, so their sum is their bitwise or. -/
def rotlWidth (value width amount : Nat) : Nat :=
  let n := amount % width
  (value * 2 ^ n) % 2 ^ width + value / 2 ^ (width - n)

/-- Rotate the `width`-bit residue of `value` RIGHT by `amount` positions
    (Rust `rotate_right`, LLVM `fshr(x, x, n)`); the mirror of `rotlWidth`. -/
def rotrWidth (value width amount : Nat) : Nat :=
  let n := amount % width
  value / 2 ^ n + (value * 2 ^ (width - n)) % 2 ^ width

/-- Evaluate a binary operation on integer values.
    Returns the result value or an error.

    Matches Rust `trust_ir::BinOp` integer variants:
    Add, Sub, Mul, UDiv, SDiv, URem, SRem, And, Or, Xor, Shl, LShr, AShr,
    and the WS3.20 rotates RotL, RotR (total: amount modulo width). -/
def semIntBinOp (op : BinOp) (width : Nat) (lhs rhs : Int) : Except SemError Int :=
  let modulus := (2 : Int) ^ width
  let wrap (v : Int) : Int := ((v % modulus) + modulus) % modulus
  match op with
  | .Add  => .ok (wrap (lhs + rhs))
  | .Sub  => .ok (wrap (lhs - rhs))
  | .Mul  => .ok (wrap (lhs * rhs))
  | .UDiv =>
    if rhs == 0 then .error (.ub "unsigned division by zero")
    else .ok (wrap (lhs / rhs))
  | .SDiv =>
    if rhs == 0 then .error (.ub "signed division by zero")
    else
      let sl := toSigned lhs width
      let sr := toSigned rhs width
      -- INT_MIN / -1 overflows the signed range: UNDEFINED (matches Rust/LLVM
      -- `sdiv`; discharged by NoOverflow). See docs/ub-numerics-policy.md §1.
      if sl == -((2 : Int) ^ (width - 1)) && sr == -1 then
        .error (.ub "signed division overflow (INT_MIN / -1)")
      -- Truncating (round-toward-zero) division: `Int.div` (the T-rounding
      -- function in Lean core), NOT the `/` operator which resolves to Euclidean
      -- `Int.ediv`. `Int.div (-7) 2 = -3`, matching Rust i128 `/` and LLVM
      -- `sdiv`; `Int.ediv` would give -4 (floor), diverging from the ratified
      -- policy. See docs/ub-numerics-policy.md §1.
      else .ok (wrap (trustIrIntTDiv sl sr))
  | .URem =>
    if rhs == 0 then .error (.ub "unsigned remainder by zero")
    else .ok (wrap (lhs % rhs))
  | .SRem =>
    if rhs == 0 then .error (.ub "signed remainder by zero")
    else
      let sl := toSigned lhs width
      let sr := toSigned rhs width
      -- INT_MIN % -1: the implied division overflows, so this is UNDEFINED too
      -- (matches Rust/LLVM `srem`).
      if sl == -((2 : Int) ^ (width - 1)) && sr == -1 then
        .error (.ub "signed remainder overflow (INT_MIN % -1)")
      -- Truncating remainder (sign of the dividend): `Int.mod` (the T-rounding
      -- function in Lean core), NOT the `%` operator which resolves to Euclidean
      -- `Int.emod`. `Int.mod (-7) 3 = -1`, matching Rust i128 `%` and LLVM
      -- `srem`; `Int.emod` would give 2 (non-negative), diverging from the
      -- ratified policy. See docs/ub-numerics-policy.md §1.
      else .ok (wrap (trustIrIntTMod sl sr))
  | .And  => .ok (wrap (Int.land lhs rhs))
  | .Or   => .ok (wrap (Int.lor lhs rhs))
  | .Xor  => .ok (wrap (Int.xor lhs rhs))
  -- Boolean connectives on the Int 0/1 carrier. TOTAL and computable: no UB
  -- guard, no `wrap` (the result is already the canonical 0 or 1), and -- unlike
  -- `Int.land`/`Int.lor` above -- fully decidable, so a downstream obligation
  -- stated over these reduces instead of resting on an opaque symbol. Any
  -- nonzero operand counts as true, which matches the `bool` ABI (0/1) while
  -- staying total on operands outside it.
  | .BAnd => .ok (if (lhs != 0) && (rhs != 0) then 1 else 0)
  | .BOr  => .ok (if (lhs != 0) || (rhs != 0) then 1 else 0)
  | .BXor => .ok (if Bool.xor (lhs != 0) (rhs != 0) then 1 else 0)
  -- Shifts: a shift amount >= bit width is UNDEFINED (poison), matching the
  -- Rust reference interpreter and LLVM `shl`/`lshr`/`ashr`. The frontend must
  -- discharge the `ShiftInRange` obligation; the amount is NOT masked. See
  -- docs/ub-numerics-policy.md §1.
  | .Shl  =>
    if rhs ≥ (width : Int) then .error (.ub "shift amount out of range")
    else .ok (wrap (lhs * (2 ^ rhs.toNat)))
  | .LShr =>
    if rhs ≥ (width : Int) then .error (.ub "shift amount out of range")
    else .ok (wrap (lhs / (2 ^ rhs.toNat)))
  | .AShr =>
    if rhs ≥ (width : Int) then .error (.ub "shift amount out of range")
    else
      let sl := toSigned lhs width
      -- Arithmetic shift right = floor division by 2^n (`Int.fdiv`), matching
      -- Rust's i128 `>>` on the signed value, which rounds toward negative
      -- infinity (fdiv(-1, 2) = -1). The divisor 2^n is always positive, so
      -- this is stated explicitly as floor rather than sharing the SDiv path.
      .ok (wrap (Int.fdiv sl (2 ^ rhs.toNat)))
  -- WS3.20 rotates: TOTAL on the unsigned residues; the amount is reduced
  -- modulo the width inside `rotlWidth`/`rotrWidth`, so — unlike the shifts
  -- above — no `ShiftInRange` obligation exists for them. Mirrors
  -- `rotate_at_width` in the reference interpreter.
  | .RotL => .ok (Int.ofNat (rotlWidth (wrap lhs).toNat width (wrap rhs).toNat))
  | .RotR => .ok (Int.ofNat (rotrWidth (wrap lhs).toNat width (wrap rhs).toNat))
  -- Float operations are handled separately
  | .FAdd | .FSub | .FMul | .FDiv | .FRem | .FMin | .FMax | .FCopySign =>
    .error (.typeError "float operation on integer operands")

/-- Exact C `fmod` / LLVM `frem` / Rust `%` on binary64: truncating remainder
    (quotient rounded toward zero, result has the dividend's sign), computed
    EXACTLY via integer arithmetic on the `frExp` decomposition rather than in
    rounded float arithmetic. The former rounded formula
    `lhs - trunc(lhs/rhs)*rhs` was NOT bit-identical to libm `fmod`: it lost
    the dividend's `-0.0` sign (`-6.0 % 3.0`), returned `NaN` for
    `finite % inf`, and overflowed to `±inf`/collapsed to `0` on
    extreme-magnitude operands (`1e308 % 1e-308`, `1e308 % 3.0`).

    `fmod` is exactly specified by IEEE 754 / C: for finite `x`, `y ≠ 0` the
    true remainder `x - trunc(x/y)·y` is always exactly representable in the
    operand format, so this integer computation is bit-identical to the Rust
    reference interpreter's `%` (libm fmod). Special cases (C fmod contract):
    `fmod(NaN, y) = NaN`, `fmod(x, NaN) = NaN`, `fmod(±inf, y) = NaN`,
    `fmod(x, ±0) = NaN`, `fmod(x, ±inf) = x` (finite x), `fmod(±0, y) = ±0`,
    and a zero remainder keeps the dividend's sign (`-6.0 % 3.0 = -0.0`).

    Exactness: `|x| = mx·2^(ex-53)`, `|y| = my·2^(ey-53)` with
    `mx, my ∈ [2^52, 2^53)` from `frExp` normalization (subnormals included);
    `|x| ≥ |y|` forces `ex ≥ ey`, so both are integer multiples of `2^(ey-53)`
    and the remainder is `r·2^(ey-53)` with `r = (mx <<< (ex-ey)) % my < 2^53`
    computed in exact `Nat` arithmetic. `Float.ofNat` is exact below `2^53`
    and `Float.scaleB` (C scalbn) is exact on representable results.
    Cross-validated bit-for-bit against libm fmod on 2·10^6 pseudo-random f64
    bit patterns plus structured edge cases on the Rust side
    (crates/trust-ir-build/tests/numerics_policy.rs) and locked by the
    `frem_*_stable` fixtures in Semantics/ExecutableFixtures.lean.
    See docs/ub-numerics-policy.md §2. -/
def floatFRem (x y : Float) : Float :=
  if x.isNaN then x
  else if y.isNaN then y
  else if x.isInf || y == 0.0 then (0.0 : Float) / 0.0  -- NaN
  else if y.isInf || x == 0.0 then x
  else
    let ax := x.abs
    let ay := y.abs
    if ax < ay then x  -- |x| < |y|: the remainder is x itself, exactly
    else
      let (fx, ex) := ax.frExp
      let (fy, ey) := ay.frExp
      let mx := (fx.scaleB 53).toUInt64.toNat
      let my := (fy.scaleB 53).toUInt64.toNat
      let r := (mx <<< (ex - ey).toNat) % my
      let mag := (Float.ofNat r).scaleB (ey - 53)
      if x < 0.0 then -mag else mag

/-- Evaluate a binary operation on binary64 float values (Lean's `Float`).
    The TYPED entry point is `semFloatBinOpAt`, which checks the operands
    against the static float type and rounds the result to it.

    Matches Rust `trust_ir::BinOp` float variants: FAdd, FSub, FMul, FDiv, FRem -/
def semFloatBinOp (op : BinOp) (lhs rhs : Float) : Except SemError Float :=
  match op with
  | .FAdd => .ok (lhs + rhs)
  | .FSub => .ok (lhs - rhs)
  | .FMul => .ok (lhs * rhs)
  | .FDiv => .ok (lhs / rhs)
  | .FRem =>
    -- C `fmod` / LLVM `frem`: truncating remainder (quotient rounded toward
    -- zero), NOT the round-to-nearest IEEE remainder. Computed exactly (see
    -- floatFRem), bit-identical to the Rust reference interpreter (`%` on
    -- f64). See docs/ub-numerics-policy.md §2.
    .ok (floatFRem lhs rhs)
  | .FCopySign =>
    -- WS3.20: IEEE copySign — the magnitude of `lhs` with the sign of `rhs`.
    -- Exact (no rounding), so `roundFloatAt` is the identity on an
    -- inhabitant. The sign of a NaN `rhs` is NOT observable in Lean 4.8.0
    -- (no `Float.toBits`; see FloatFormat.lean), so that case REFUSES rather
    -- than guessing a sign the reference interpreter reads from the bits.
    -- `floatSignBit` distinguishes `-0.0`.
    if rhs.isNaN then
      .error (.unsupported .float "copysign from a NaN sign is unobservable (no Float.toBits in Lean 4.8.0)")
    else if floatSignBit rhs then .ok (-lhs.abs) else .ok lhs.abs
  | .FMin | .FMax =>
    .error (.unsupported .float "min/max requires explicit choice execution (semBinOp)")
  | _ => .error (.typeError "integer operation on float operands")

/-- A float `BinOp` at its static type `ty` (docs/ub-numerics-policy.md §2:
    the operation is the IEEE operation AT THAT PRECISION). Both operands must
    inhabit `ty` (`checkFloatAt`), the operation runs in binary64
    (`semFloatBinOp`), and the result is rounded to `ty` exactly once
    (`roundFloatAt`). For `F64` the rounding is the identity. For `F32`,
    binary64-then-one-rounding is exact for `+ - * /` because 53 ≥ 2·24 + 2,
    and `FRem` is exact before rounding. A width the model does not round
    refuses (`unsupported.float`) instead of answering at binary64. -/
def semFloatBinOpAt (op : BinOp) (ty : Ty) (lhs rhs : Float) :
    Except SemError Float := do
  checkFloatAt ty lhs
  checkFloatAt ty rhs
  let wide ← semFloatBinOp op lhs rhs
  roundFloatAt ty wide

/-- THE integer lane rule of the bounded executable vector subset: an integer
    lane type, with the lane count and lane width of its 128-bit vector. The
    other three shape checks (`executableIntVectorWidth?`,
    `executableVectorPayloadMatches`, and `Aggregate.lean`'s
    `executableVectorLanePayloadMatches` / `executableVectorLaneValueMatches`)
    are read from it, so the set is stated once.

    A lane value carries no signedness (the operation does: `semICmp`'s
    predicate, `SDiv` / `UDiv`), so the signed and the unsigned type of one
    width are one shape, exactly as the x86-64 vector-compare cells are keyed
    by lane width and count alone. These are the fixed-width integer lanes the
    validator admits (`<n x isize>`, `<n x usize>` and 128-bit lanes are not
    vector types there). Until 2026-09-30 every check listed only the signed
    types, so each unsigned-lane cell (`<16 x u8>` … `<2 x u64>`), which the
    validator and the interpreter accept, was `unsupported vector_shape` here
    (1580 of 3160 runs of
    `vector_icmp_cells_agree_across_engines_and_with_the_statement`). -/
def Ty.executableIntLane? : Ty → Option (Nat × Nat)
  | .I8 | .U8 => some (16, 8)
  | .I16 | .U16 => some (8, 16)
  | .I32 | .U32 => some (4, 32)
  | .I64 | .U64 => some (2, 64)
  | _ => none

/-- Bounded executable integer-vector subset: `(lanes, width)` of a vector
    type whose lane type and count are `Ty.executableIntLane?`'s. -/
def Ty.executableIntVectorWidth? : Ty → Option (Nat × Nat)
  | .Vector n elemTy =>
    match elemTy.executableIntLane? with
    | some (lanes, width) => if n == lanes then some (lanes, width) else none
    | none => none
  | _ => none

/-- Bounded executable bool-vector subset used by vector select. -/
def Ty.executableBoolVectorLanes? : Ty → Option Nat
  | .Vector 16 .Bool => some 16
  | .Vector 8 .Bool => some 8
  | .Vector 4 .Bool => some 4
  | .Vector 2 .Bool => some 2
  | _ => none

/-- All vector shapes enabled by the first executable vector semantics path. -/
def Ty.executableVectorLanes? (ty : Ty) : Option Nat :=
  match ty.executableIntVectorWidth? with
  | some (lanes, _) => some lanes
  | none => ty.executableBoolVectorLanes?

def Value.isIntWidth (width : Nat) : Value → Bool
  | .int w _ => w == width
  | _ => false

def Value.isBool : Value → Bool
  | .bool _ => true
  | _ => false

/-- Runtime payload check for the bounded executable vector subset: the
    integer shapes of `Ty.executableIntVectorWidth?` and the bool masks of
    `Ty.executableBoolVectorLanes?`. -/
def Ty.executableVectorPayloadMatches (ty : Ty) (lanes : List Value) : _root_.Bool :=
  match ty.executableIntVectorWidth? with
  | some (n, width) => lanes.length == n && lanes.all (Value.isIntWidth width)
  | none =>
    match ty.executableBoolVectorLanes? with
    | some n => lanes.length == n && lanes.all Value.isBool
    | none => false

/-- Lane-wise integer BinOp over supported vector payloads. -/
def semVectorIntBinOp (op : BinOp) (width : Nat)
    : List Value → List Value → Except SemError (List Value)
  | [], [] => .ok []
  | .int w1 l :: lhsRest, .int w2 r :: rhsRest =>
    if w1 != width || w2 != width then
      .error (.typeError "Vector BinOp: lane integer width mismatch")
    else do
      let lane ← semIntBinOp op width l r
      let rest ← semVectorIntBinOp op width lhsRest rhsRest
      pure (.int width lane :: rest)
  | [], _ :: _ => .error (.typeError "Vector BinOp: mismatched lane counts")
  | _ :: _, [] => .error (.typeError "Vector BinOp: mismatched lane counts")
  | _ :: _, _ :: _ => .error (.typeError "Vector BinOp: non-integer lane")

/-- Count one bits in the low `width` bits of `value`. -/
def popCountWidth (value width : Nat) : Nat :=
  (List.range width).foldl
    (fun acc i => acc + ((value / ((2 : Nat) ^ i)) % 2))
    0

/-- Evaluate a unary operation on an integer value.
    Matches Rust `trust_ir::UnOp`: Neg, Not, CtPop -/
def semIntUnOp (op : UnOp) (width : Nat) (operand : Int) : Except SemError Int :=
  let modulus := (2 : Int) ^ width
  let wrap (v : Int) : Int := ((v % modulus) + modulus) % modulus
  match op with
  | .Neg  => .ok (wrap (-operand))
  | .Not  =>
    -- Bitwise NOT: flip all bits = (2^width - 1) XOR operand
    let mask := modulus - 1
    .ok (wrap (Int.xor mask operand))
  | .CtPop =>
    .ok (Int.ofNat (popCountWidth (wrap operand).toNat width))
  -- WS3.20 bit intrinsics: total on the unsigned residue (`ctlz 0 = cttz 0 =
  -- width`). Each mirrors the reference interpreter's `eval_int_unop` arm.
  | .CtLz => .ok (Int.ofNat (ctlzWidth (wrap operand).toNat width))
  | .CtTz => .ok (Int.ofNat (cttzWidth (wrap operand).toNat width))
  | .BSwap => .ok (Int.ofNat (bswapWidth (wrap operand).toNat width))
  | .BitReverse => .ok (Int.ofNat (bitReverseWidth (wrap operand).toNat width))
  | .FNeg => .error (.typeError "float negation on integer operand")
  | .FAbs => .error (.typeError "float absolute value on integer operand")
  | .FSqrt | .FFloor | .FCeil | .FTrunc =>
    .error (.typeError "float unary operation on integer operand")

/-- Evaluate a unary operation on a float value.
    Matches the modeled floating-point Rust `trust_ir::UnOp` operators -/
def semFloatUnOp (op : UnOp) (operand : Float) : Except SemError Float :=
  match op with
  | .FNeg => .ok (-operand)
  | .FAbs => .ok operand.abs
  | .FSqrt => .ok operand.sqrt
  | .FFloor => .ok operand.floor
  | .FCeil => .ok operand.ceil
  -- Preserve signed zero and NaNs without passing through an integer carrier.
  | .FTrunc => .ok (if operand < 0 then operand.ceil else operand.floor)
  | _     => .error (.typeError "integer unary op on float operand")

/-- A float `UnOp` at its static type `ty`: the operand must inhabit `ty`
    and the result is rounded to `ty` exactly once (`FNeg` and `FAbs` are exact, so the
    rounding is the identity on an inhabitant). Floor, ceil and trunc return
    representable integral values. Square root uses binary64 then the common
    width rounder; binary64 has more than twice binary32 precision (53 ≥
    2·24 + 2), so a binary32 square-root midpoint cannot induce double rounding.
    See the WS2.23 precision argument in the completion roadmap. -/
def semFloatUnOpAt (op : UnOp) (ty : Ty) (operand : Float) :
    Except SemError Float := do
  checkFloatAt ty operand
  let wide ← semFloatUnOp op operand
  roundFloatAt ty wide

/-- Integer lane widths admitted by the validator, without a backend lane
    count. The older `executable*` predicates remain backend classifiers. -/
def Ty.semanticIntLaneWidth? (ty : Ty) : Option Nat :=
  ty.executableIntLane?.map Prod.snd

def Ty.semanticVectorLane (ty : Ty) : _root_.Bool :=
  match ty with
  | .Bool => true
  | _ => ty.isFloat || ty.semanticIntLaneWidth?.isSome

/-- Check a vector's static shape and exact runtime census. Recursion in the
    operations below follows the actual payload; no extra fuel is imposed. -/
def checkVectorShape (count : Nat) (elemTy : Ty) (lanes : List Value) :
    Except SemError Unit := do
  if count == 0 then
    throw (.unsupported .vectorShape "zero-lane vectors are not executable")
  if !elemTy.semanticVectorLane then
    throw (.unsupported .vectorType "vector lane type is not admitted")
  if lanes.length != count then
    throw (.typeError "vector lane census does not match its declared type")

/-- Transport may retain poison; arithmetic and insertion inspect their
    operands. Float membership uses the existing typed precision boundary. -/
def checkVectorLaneType (elemTy : Ty) (allowPoison : Bool) (value : Value) :
    Except SemError Unit := do
  if value.isPoison || value.isUninit then
    if allowPoison then return ()
    else throw (.ub "vector operation: use of an uninitialized lane")
  match elemTy, value with
  | .Bool, .bool _ => pure ()
  | .F16, .float f | .F32, .float f | .F64, .float f => checkFloatAt elemTy f
  | _, .int width _ =>
    match elemTy.semanticIntLaneWidth? with
    | some expected =>
      if width == expected then pure ()
      else throw (.typeError "vector integer lane width does not match its declared type")
    | none => throw (.typeError "vector lane does not inhabit its declared type")
  | _, _ => throw (.typeError "vector lane does not inhabit its declared type")

def checkVectorLanes (elemTy : Ty) (allowPoison : Bool) : List Value → Except SemError Unit
  | [] => .ok ()
  | lane :: rest => do
    checkVectorLaneType elemTy allowPoison lane
    checkVectorLanes elemTy allowPoison rest

trustIrDenseMatch
/-- The six boolean connectives admitted for scalar and vector Bool. -/
def semBoolBinOp (op : BinOp) (lhs rhs : Bool) : Except SemError Bool :=
  match op with
  | .And | .BAnd => .ok (lhs && rhs)
  | .Or | .BOr => .ok (lhs || rhs)
  | .Xor | .BXor => .ok (Bool.xor lhs rhs)
  | _ => .error (.typeError "boolean binary operation requires a boolean operator")

#trustIrAxiomsExact TrustIr.semBoolBinOp == []

trustIrDenseMatch
/-- The typed Bool value boundary. Both operands are inspected, even when a
    mathematical connective could short-circuit. Integer carriers are refused. -/
def semBoolBinOpValues (op : BinOp) (lhs rhs : Value) : Except SemError Value := do
  if lhs.isPoison || lhs.isUninit || rhs.isPoison || rhs.isUninit then
    throw (.ub "Bool BinOp: use of an uninitialized operand")
  match lhs, rhs with
  | .bool left, .bool right => return .bool (← semBoolBinOp op left right)
  | _, _ => throw (.typeError "Bool BinOp: expected boolean operands")

#trustIrAxiomsExact TrustIr.semBoolBinOpValues == []

def semVectorBinOpLane (op : BinOp) (elemTy : Ty) (lhs rhs : Value) :
    Except SemError Value := do
  checkVectorLaneType elemTy false lhs
  checkVectorLaneType elemTy false rhs
  match lhs, rhs with
  | .bool l, .bool r => return .bool (← semBoolBinOp op l r)
  | .int width l, .int _ r =>
    match op with
    | .BAnd | .BOr | .BXor =>
      throw (.typeError "boolean vector operator requires Bool lanes")
    | _ => return .int width (← semIntBinOp op width l r)
  | .float l, .float r => return .float (← semFloatBinOpAt op elemTy l r)
  | _, _ => throw (.typeError "vector binary operands have different lane types")

def semVectorBinOp (op : BinOp) (elemTy : Ty) :
    List Value → List Value → Except SemError (List Value)
  | [], [] => .ok []
  | lhs :: left, rhs :: right => do
    let first ← semVectorBinOpLane op elemTy lhs rhs
    let rest ← semVectorBinOp op elemTy left right
    pure (first :: rest)
  | _, _ => .error (.typeError "vector binary operands have different lane counts")

def semVectorUnOpLane (op : UnOp) (elemTy : Ty) (value : Value) :
    Except SemError Value := do
  checkVectorLaneType elemTy false value
  match value with
  | .bool b =>
    match op with
    | .Not => pure (.bool (!b))
    | _ => throw (.typeError "vector Bool unary operation must be Not")
  | .int width raw => return .int width (← semIntUnOp op width raw)
  | .float f => return .float (← semFloatUnOpAt op elemTy f)
  | _ => throw (.typeError "vector unary operand has the wrong lane type")

def semVectorUnOp (op : UnOp) (elemTy : Ty) : List Value → Except SemError (List Value)
  | [] => .ok []
  | lane :: lanes => do
    let first ← semVectorUnOpLane op elemTy lane
    let rest ← semVectorUnOp op elemTy lanes
    pure (first :: rest)

/-- Checked vector execution and the unchanged legacy scalar operand paths. -/
def semBinOpValues (op : BinOp) (ty : Ty) (lhsVal rhsVal : Value) : Except SemError Value := do
  match ty, lhsVal, rhsVal with
  | .Bool, .bool lhs, .bool rhs => return .bool (← semBoolBinOp op lhs rhs)
  | .Vector count elemTy, .vector lhs, .vector rhs =>
    checkVectorShape count elemTy lhs
    checkVectorShape count elemTy rhs
    return .vector (← semVectorBinOp op elemTy lhs rhs)
  | _, .int w1 l, .int w2 r =>
    if w1 != w2 then throw (.typeError "BinOp: mismatched integer widths")
    else return .int w1 (← semIntBinOp op w1 l r)
  | _, .float l, .float r => return .float (← semFloatBinOpAt op ty l r)
  | _, _, _ => throw (.typeError s!"BinOp: incompatible operand types for {repr op}")

def semUnOpValue (op : UnOp) (ty : Ty) (operand : Value) : Except SemError Value := do
  match ty, operand with
  | .Vector count elemTy, .vector lanes =>
    checkVectorShape count elemTy lanes
    return .vector (← semVectorUnOp op elemTy lanes)
  | _, .int width raw => return .int width (← semIntUnOp op width raw)
  | _, .float f => return .float (← semFloatUnOpAt op ty f)
  | _, _ => throw (.typeError s!"UnOp: invalid operand type for {repr op}")

/-- Evaluate an overflow-checked operation.
    Returns (result, overflow_flag).
    Matches Rust `trust_ir::OverflowOp`: AddOverflow, SubOverflow, MulOverflow -/
def semOverflowOp (op : OverflowOp) (width : Nat) (signed : Bool) (lhs rhs : Int)
    : Except SemError (Int × Bool) :=
  let modulus := (2 : Int) ^ width
  let half := (2 : Int) ^ (width - 1)
  let wrap (v : Int) : Int := ((v % modulus) + modulus) % modulus
  -- The overflow flag is computed against the OPERAND SIGNEDNESS (`signed`),
  -- not always-signed: signed ops overflow when the exact result leaves
  -- [-2^(w-1), 2^(w-1)); unsigned ops when it leaves [0, 2^w). The wrapped
  -- value is identical either way (two's complement). See
  -- docs/ub-numerics-policy.md §1.
  if signed then
    let checkSigned (exact : Int) : (Int × Bool) :=
      (wrap exact, exact ≥ half || exact < -half)
    let sl := toSigned lhs width
    let sr := toSigned rhs width
    match op with
    | .AddOverflow => .ok (checkSigned (sl + sr))
    | .SubOverflow => .ok (checkSigned (sl - sr))
    | .MulOverflow => .ok (checkSigned (sl * sr))
  else
    -- lhs, rhs are already the unsigned residues in [0, 2^w).
    let checkUnsigned (exact : Int) : (Int × Bool) :=
      (wrap exact, exact ≥ modulus || exact < 0)
    match op with
    | .AddOverflow => .ok (checkUnsigned (lhs + rhs))
    | .SubOverflow => .ok (checkUnsigned (lhs - rhs))
    | .MulOverflow => .ok (checkUnsigned (lhs * rhs))

/-- The complete permitted operand choices of a typed min/max. A two-element
    list is the opposite-signed-zero case. NaN payloads retain the existing
    unobservable-payload boundary; a non-NaN operand is returned unchanged. -/
def floatMinMaxCandidates (op : BinOp) (ty : Ty) (lhs rhs : Float) :
    Except SemError (List Float) := do
  if !op.isMinMax then
    throw (.typeError "expected FMin or FMax")
  checkFloatAt ty lhs
  checkFloatAt ty rhs
  if lhs.isNaN then pure [rhs]
  else if rhs.isNaN then pure [lhs]
  else if lhs == 0.0 && rhs == 0.0 && floatSignBit lhs != floatSignBit rhs then
    pure [lhs, rhs]
  else match op with
    | .FMin => pure [if lhs < rhs then lhs else rhs]
    | .FMax => pure [if lhs > rhs then lhs else rhs]
    | _ => throw (.typeError "expected FMin or FMax")

/-- Select one permitted result using the explicit dynamic choice input.
    Only opposite signed zeros consume a choice; every other case is fixed. -/
def semFloatMinMaxAt (op : BinOp) (ty : Ty) (lhs rhs : Float) : Sem Float := do
  let candidates ← match floatMinMaxCandidates op ty lhs rhs with
    | .ok candidates => pure candidates
    | .error error => throw error
  match candidates with
  | [value] => pure value
  | [left, right] =>
    let chooseLeft ← Sem.nextFloatZeroChoice
    pure (if chooseLeft then left else right)
  | _ => Sem.throwTypeError "invalid min/max candidate shape"

def semFloatMinMaxScalarValue (op : BinOp) (ty : Ty) (lhs rhs : Value) : Sem Value := do
  Sem.rejectPartial lhs "BinOp"
  Sem.rejectPartial rhs "BinOp"
  if !ty.isFloat then Sem.throwTypeError "min/max requires a float type"
  match lhs, rhs with
  | .float left, .float right =>
    pure (.float (← semFloatMinMaxAt op ty left right))
  | _, _ => Sem.throwTypeError "min/max requires float operands"

/-- Left-to-right lane execution, with independent choices for repeated lanes. -/
def semFloatMinMaxLanes (op : BinOp) (ty : Ty) :
    List Value → List Value → Sem (List Value)
  | [], [] => pure []
  | left :: lefts, right :: rights => do
    let value ← semFloatMinMaxScalarValue op ty left right
    let values ← semFloatMinMaxLanes op ty lefts rights
    pure (value :: values)
  | _, _ => Sem.throwTypeError "min/max vector lane counts differ"

def semFloatMinMaxValues (op : BinOp) (ty : Ty) (lhs rhs : Value) : Sem Value := do
  Sem.rejectPartial lhs "BinOp"
  Sem.rejectPartial rhs "BinOp"
  match ty with
  | .Vector count elemTy =>
    if count == 0 then
      Sem.throwUnsupported .vectorShape "zero-lane min/max vector"
    if !elemTy.isFloat then Sem.throwTypeError "min/max requires float vector lanes"
    match lhs, rhs with
    | .vector left, .vector right =>
      if left.length != count || right.length != count then
        Sem.throwTypeError "min/max vector lane count does not match type"
      pure (.vector (← semFloatMinMaxLanes op elemTy left right))
    | _, _ => Sem.throwTypeError "min/max requires vector operands"
  | _ => semFloatMinMaxScalarValue op ty lhs rhs

def semFloatMinMax (op : BinOp) (ty : Ty) (lhsId rhsId : ValueId) : Sem ValueId := do
  let lhs ← Sem.lookupValue lhsId
  let rhs ← Sem.lookupValue rhsId
  Sem.bindFresh (← semFloatMinMaxValues op ty lhs rhs)

/-- Single-result operation implementation. Min/max uses the explicit-choice
    implementation selected by `semBinOp`. -/
def semBinOpDeterministic (op : BinOp) (ty : Ty) (lhsId rhsId : ValueId) : Sem ValueId := do
  let lhsVal ← Sem.lookupValue lhsId
  let rhsVal ← Sem.lookupValue rhsId
  -- Arithmetic inspects both operands: consuming a poison value is UB.
  Sem.rejectPartial lhsVal "BinOp"
  Sem.rejectPartial rhsVal "BinOp"
  match semBinOpValues op ty lhsVal rhsVal with
  | .ok result => Sem.bindFresh result
  | .error error => throw error

/-- Contextual typed Bool execution. The bare arithmetic wrapper above keeps
    its historical integer-carrier proof contracts; actual module evaluation
    selects this check for a statically Bool instruction. -/
def semBoolBinOpInst (op : BinOp) (lhsId rhsId : ValueId) : Sem ValueId := do
  let lhs ← Sem.lookupValue lhsId
  let rhs ← Sem.lookupValue rhsId
  match semBoolBinOpValues op lhs rhs with
  | .ok result => Sem.bindFresh result
  | .error error => throw error

/-- Execute a binary operation, including all permitted min/max zero choices. -/
def semBinOp (op : BinOp) (ty : Ty) (lhsId rhsId : ValueId) : Sem ValueId :=
  if op.isMinMax then semFloatMinMax op ty lhsId rhsId
  else semBinOpDeterministic op ty lhsId rhsId

/-- Evaluate a UnOp instruction in the semantic monad. -/
def semUnOp (op : UnOp) (ty : Ty) (operandId : ValueId) : Sem ValueId := do
  let operand ← Sem.lookupValue operandId
  Sem.rejectPartial operand "UnOp"
  match semUnOpValue op ty operand with
  | .ok result => Sem.bindFresh result
  | .error error => throw error

/-- Evaluate an OverflowOp instruction in the semantic monad.
    Binds TWO fresh SSA values, in order: the wrapped result (`int`), then the
    overflow flag (`bool`), and returns their ids `(result, overflowed)`.
    This is the Rust two-result shape (`InstrNode.results = [%v, %o]`,
    interpret.rs `bind_results(.., [result, flag])`); there is no packed
    aggregate form (WS2.24). -/
def semOverflow (op : OverflowOp) (ty : Ty) (lhsId rhsId : ValueId) :
    Sem (ValueId × ValueId) := do
  let lhsVal ← Sem.lookupValue lhsId
  let rhsVal ← Sem.lookupValue rhsId
  Sem.rejectPartial lhsVal "OverflowOp"
  Sem.rejectPartial rhsVal "OverflowOp"
  match lhsVal, rhsVal with
  | .int w1 l, .int w2 r =>
    if w1 != w2 then Sem.throwTypeError "OverflowOp: mismatched integer widths"
    else match semOverflowOp op w1 ty.isSigned l r with
      | .ok (result, flag) => Sem.bindFreshPair (.int w1 result) (.bool flag)
      | .error e => throw e
  | _, _ => Sem.throwTypeError s!"OverflowOp: non-integer operands for {repr op}"

end TrustIr
