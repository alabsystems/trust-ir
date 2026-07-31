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

/-- Truncate an integer to `width` bits using modular arithmetic.
    For width w, the result is in [0, 2^w). -/
def truncateUnsigned (val : Int) (width : Nat) : Int :=
  val % (2 ^ width)

/-- Interpret an unsigned integer as signed (two's complement).
    For width w: values >= 2^(w-1) are negative. -/
def toSigned (val : Int) (width : Nat) : Int :=
  let half := (2 : Int) ^ (width - 1)
  let modulus := (2 : Int) ^ width
  let uval := val % modulus
  if uval >= half then uval - modulus else uval

/-- Evaluate a binary operation on integer values.
    Returns the result value or an error.

    Matches Rust `trust_ir::BinOp` integer variants:
    Add, Sub, Mul, UDiv, SDiv, URem, SRem, And, Or, Xor, Shl, LShr, AShr -/
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
      else .ok (wrap (Int.div sl sr))
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
      else .ok (wrap (Int.mod sl sr))
  | .And  => .ok (wrap (Int.land lhs rhs))
  | .Or   => .ok (wrap (Int.lor lhs rhs))
  | .Xor  => .ok (wrap (Int.xor lhs rhs))
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
  -- Float operations are handled separately
  | .FAdd | .FSub | .FMul | .FDiv | .FRem =>
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

/-- Evaluate a binary operation on float values.
    Axiomatized for Phase 1: uses Lean's built-in Float operations.

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
  | _ => .error (.typeError "integer operation on float operands")

/-- Bounded executable integer-vector subset for the first vector semantics path. -/
def Ty.executableIntVectorWidth? : Ty → Option (Nat × Nat)
  | .Vector 16 .I8 => some (16, 8)
  | .Vector 8 .I16 => some (8, 16)
  | .Vector 4 .I32 => some (4, 32)
  | .Vector 2 .I64 => some (2, 64)
  | _ => none

/-- Bounded executable bool-vector subset used by vector select and icmp. -/
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

/-- Runtime payload check for the bounded executable vector subset. -/
def Ty.executableVectorPayloadMatches (ty : Ty) (lanes : List Value) : _root_.Bool :=
  match ty with
  | .Vector 16 .I8 => lanes.length == 16 && lanes.all (Value.isIntWidth 8)
  | .Vector 8 .I16 => lanes.length == 8 && lanes.all (Value.isIntWidth 16)
  | .Vector 4 .I32 => lanes.length == 4 && lanes.all (Value.isIntWidth 32)
  | .Vector 2 .I64 => lanes.length == 2 && lanes.all (Value.isIntWidth 64)
  | .Vector 16 .Bool => lanes.length == 16 && lanes.all Value.isBool
  | .Vector 8 .Bool => lanes.length == 8 && lanes.all Value.isBool
  | .Vector 4 .Bool => lanes.length == 4 && lanes.all Value.isBool
  | .Vector 2 .Bool => lanes.length == 2 && lanes.all Value.isBool
  | _ => false

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
  | .FNeg => .error (.typeError "float negation on integer operand")

/-- Evaluate a unary operation on a float value.
    Matches Rust `trust_ir::UnOp`: FNeg -/
def semFloatUnOp (op : UnOp) (operand : Float) : Except SemError Float :=
  match op with
  | .FNeg => .ok (-operand)
  | _     => .error (.typeError "integer unary op on float operand")

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

/-- Evaluate a BinOp instruction in the semantic monad.
    Dispatches to integer or float semantics based on operand types. -/
def semBinOp (op : BinOp) (ty : Ty) (lhsId rhsId : ValueId) : Sem ValueId := do
  let lhsVal ← Sem.lookupValue lhsId
  let rhsVal ← Sem.lookupValue rhsId
  -- Arithmetic inspects both operands: consuming a poison value is UB.
  Sem.rejectPartial lhsVal "BinOp"
  Sem.rejectPartial rhsVal "BinOp"
  match ty, lhsVal, rhsVal with
  | ty, .vector lhs, .vector rhs =>
    match ty.executableIntVectorWidth? with
    | some (lanes, width) =>
      if lhs.length != lanes || rhs.length != lanes then
        Sem.throwTypeError "Vector BinOp: lane count does not match type"
      else
        match semVectorIntBinOp op width lhs rhs with
        | .ok result => Sem.bindFresh (.vector result)
        | .error e   => throw e
    | none =>
      Sem.throwUnsupported .vectorType
        s!"Vector BinOp: unsupported vector type {repr ty}"
  | _, .int w1 l, .int w2 r =>
    if w1 != w2 then Sem.throwTypeError "BinOp: mismatched integer widths"
    else match semIntBinOp op w1 l r with
      | .ok result => Sem.bindFresh (.int w1 result)
      | .error e   => throw e
  | _, .float l, .float r =>
    match semFloatBinOp op l r with
    | .ok result => Sem.bindFresh (.float result)
    | .error e   => throw e
  | _, _, _ => Sem.throwTypeError s!"BinOp: incompatible operand types for {repr op}"

/-- Evaluate a UnOp instruction in the semantic monad. -/
def semUnOp (op : UnOp) (_ty : Ty) (operandId : ValueId) : Sem ValueId := do
  let operand ← Sem.lookupValue operandId
  Sem.rejectPartial operand "UnOp"
  match operand with
  | .int w v =>
    match semIntUnOp op w v with
    | .ok result => Sem.bindFresh (.int w result)
    | .error e   => throw e
  | .float v =>
    match semFloatUnOp op v with
    | .ok result => Sem.bindFresh (.float result)
    | .error e   => throw e
  | _ => Sem.throwTypeError s!"UnOp: invalid operand type for {repr op}"

/-- Evaluate an OverflowOp instruction in the semantic monad.
    Binds a pair: (result : int, overflowed : bool). -/
def semOverflow (op : OverflowOp) (ty : Ty) (lhsId rhsId : ValueId) : Sem ValueId := do
  let lhsVal ← Sem.lookupValue lhsId
  let rhsVal ← Sem.lookupValue rhsId
  Sem.rejectPartial lhsVal "OverflowOp"
  Sem.rejectPartial rhsVal "OverflowOp"
  match lhsVal, rhsVal with
  | .int w1 l, .int w2 r =>
    if w1 != w2 then Sem.throwTypeError "OverflowOp: mismatched integer widths"
    else match semOverflowOp op w1 ty.isSigned l r with
      | .ok (result, flag) =>
        -- Return as aggregate: (result, overflow_flag)
        Sem.bindFresh (.aggregate [.int w1 result, .bool flag])
      | .error e => throw e
  | _, _ => Sem.throwTypeError s!"OverflowOp: non-integer operands for {repr op}"

end TrustIr
