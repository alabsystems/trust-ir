-- Copyright 2026 Andrew Yates
-- Author: Andrew Yates <andrewyates.name@gmail.com>
-- Licensed under the Apache License, Version 2.0
--
-- Comparison semantics: ICmp, FCmp.
-- Phase 1 of the formalization roadmap.

import TrustIr.CmpOp
import TrustIr.Semantics.Arith

namespace TrustIr

/-!
# Comparison Semantics

## Integer Comparisons (ICmpOp)

Signedness is in the operation, not the type:
- Eq/Ne: sign-independent for two's complement
- Ult/Ule/Ugt/Uge: unsigned (interpret as natural numbers)
- Slt/Sle/Sgt/Sge: signed (two's complement)

## Floating-Point Comparisons (FCmpOp)

IEEE 754 ordered vs unordered semantics:
- Ordered (O-prefix): false if either operand is NaN
- Unordered (U-prefix): true if either operand is NaN
Axiomatized in Phase 1; NaN semantics via Lean's Float.isNaN.
-/

/-- Evaluate an integer comparison. Returns Bool. -/
def semICmp (op : ICmpOp) (width : Nat) (lhs rhs : Int) : Bool :=
  match op with
  | .Eq  => lhs == rhs
  | .Ne  => lhs != rhs
  | .Ult => lhs < rhs          -- unsigned: values already in [0, 2^w)
  | .Ule => lhs <= rhs
  | .Ugt => lhs > rhs
  | .Uge => lhs >= rhs
  | .Slt => toSigned lhs width < toSigned rhs width
  | .Sle => toSigned lhs width <= toSigned rhs width
  | .Sgt => toSigned lhs width > toSigned rhs width
  | .Sge => toSigned lhs width >= toSigned rhs width

/-- Lane-wise integer comparison over supported vector payloads. -/
def semVectorICmp (op : ICmpOp) (width : Nat)
    : List Value → List Value → Except SemError (List Value)
  | [], [] => .ok []
  | .int w1 l :: lhsRest, .int w2 r :: rhsRest =>
    if w1 != width || w2 != width then
      .error (.typeError "Vector ICmp: lane integer width mismatch")
    else do
      let rest ← semVectorICmp op width lhsRest rhsRest
      pure (.bool (semICmp op width l r) :: rest)
  | [], _ :: _ => .error (.typeError "Vector ICmp: mismatched lane counts")
  | _ :: _, [] => .error (.typeError "Vector ICmp: mismatched lane counts")
  | _ :: _, _ :: _ => .error (.typeError "Vector ICmp: non-integer lane")

/-- Evaluate a floating-point comparison.
    Axiomatized: uses Lean's Float comparison + NaN checks. -/
def semFCmp (op : FCmpOp) (lhs rhs : Float) : Bool :=
  let isNaN := lhs.isNaN || rhs.isNaN
  match op with
  -- Ordered: false if either is NaN
  | .OEq => !isNaN && lhs == rhs
  | .ONe => !isNaN && lhs != rhs
  | .OLt => !isNaN && lhs < rhs
  | .OLe => !isNaN && lhs <= rhs
  | .OGt => !isNaN && lhs > rhs
  | .OGe => !isNaN && lhs >= rhs
  -- Unordered: true if either is NaN
  | .UEq => isNaN || lhs == rhs
  | .UNe => isNaN || lhs != rhs
  | .ULt => isNaN || lhs < rhs
  | .ULe => isNaN || lhs <= rhs
  | .UGt => isNaN || lhs > rhs
  | .UGe => isNaN || lhs >= rhs

/-- Evaluate an ICmp instruction in the semantic monad. -/
def semICmpInst (op : ICmpOp) (ty : Ty) (lhsId rhsId : ValueId) : Sem ValueId := do
  let lhsVal ← Sem.lookupValue lhsId
  let rhsVal ← Sem.lookupValue rhsId
  -- Comparison inspects both operands: consuming a poison value is UB.
  Sem.rejectPartial lhsVal "ICmp"
  Sem.rejectPartial rhsVal "ICmp"
  match ty, lhsVal, rhsVal with
  | ty, .vector lhs, .vector rhs =>
    match ty.executableIntVectorWidth? with
    | some (lanes, width) =>
      if lhs.length != lanes || rhs.length != lanes then
        Sem.throwTypeError "Vector ICmp: lane count does not match type"
      else
        match semVectorICmp op width lhs rhs with
        | .ok result => Sem.bindFresh (.vector result)
        | .error e   => throw e
    | none =>
      Sem.throwUnsupported .vectorType
        s!"Vector ICmp: unsupported vector type {repr ty}"
  | _, .int w1 l, .int w2 r =>
    if w1 != w2 then Sem.throwTypeError "ICmp: mismatched integer widths"
    else Sem.bindFresh (.bool (semICmp op w1 l r))
  | _, _, _ => Sem.throwTypeError s!"ICmp: non-integer operands for {repr op}"

/-- Evaluate an FCmp instruction in the semantic monad. -/
def semFCmpInst (op : FCmpOp) (_ty : Ty) (lhsId rhsId : ValueId) : Sem ValueId := do
  let lhsVal ← Sem.lookupValue lhsId
  let rhsVal ← Sem.lookupValue rhsId
  Sem.rejectPartial lhsVal "FCmp"
  Sem.rejectPartial rhsVal "FCmp"
  match lhsVal, rhsVal with
  | .float l, .float r =>
    Sem.bindFresh (.bool (semFCmp op l r))
  | _, _ => Sem.throwTypeError s!"FCmp: non-float operands for {repr op}"

end TrustIr
