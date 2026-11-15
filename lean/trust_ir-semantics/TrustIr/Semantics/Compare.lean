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

/-- Bool is a one-bit integer for every comparison predicate. Its signed
    value is `-1` for true and `0` for false. -/
def semBoolICmp (op : ICmpOp) (lhs rhs : Bool) : Bool :=
  semICmp op 1 (if lhs then 1 else 0) (if rhs then 1 else 0)

/-- All ten Bool predicates, including signed one-bit ordering. -/
theorem semBoolICmp_truth_table (op : ICmpOp) (lhs rhs : Bool) :
    semBoolICmp op lhs rhs = (match op with
      | .Eq => lhs == rhs | .Ne => lhs != rhs
      | .Ult => !lhs && rhs | .Ule => !lhs || rhs
      | .Ugt => lhs && !rhs | .Uge => lhs || !rhs
      | .Slt => lhs && !rhs | .Sle => lhs || !rhs
      | .Sgt => !lhs && rhs | .Sge => !lhs || rhs) := by
  cases op <;> cases lhs <;> cases rhs <;> decide

/-- Inspect one integer lane, checking the declared width before comparison. -/
def icmpIntValue (width : Nat) : Value → Except SemError Int
  | .partial _ | .undef _ | .uninit =>
    .error (.ub "ICmp: use of an uninitialized integer value")
  | .int actual raw =>
    if actual == width then .ok raw
    else .error (.typeError "ICmp: integer width does not match type")
  | _ => .error (.typeError "ICmp: expected an integer operand")

/-- Inspect one Bool lane; integer payloads are not Bool values. -/
def icmpBoolValue : Value → Except SemError Bool
  | .partial _ | .undef _ | .uninit =>
    .error (.ub "ICmp: use of an uninitialized bool value")
  | .bool value => .ok value
  | _ => .error (.typeError "ICmp: expected a bool operand")

/-- Lane-wise integer comparison. Recursion follows the actual lane list;
    the instruction checks its census against the declared vector type. -/
def semVectorICmp (op : ICmpOp) (width : Nat)
    : List Value → List Value → Except SemError (List Value)
  | [], [] => .ok []
  | lhs :: lhsRest, rhs :: rhsRest => do
    let l ← icmpIntValue width lhs
    let r ← icmpIntValue width rhs
    let rest ← semVectorICmp op width lhsRest rhsRest
    pure (.bool (semICmp op width l r) :: rest)
  | [], _ :: _ => .error (.typeError "Vector ICmp: mismatched lane counts")
  | _ :: _, [] => .error (.typeError "Vector ICmp: mismatched lane counts")

/-- Bool-vector comparison uses the same one-bit rule as scalar Bool. -/
def semVectorBoolICmp (op : ICmpOp)
    : List Value → List Value → Except SemError (List Value)
  | [], [] => .ok []
  | lhs :: lhsRest, rhs :: rhsRest => do
    let l ← icmpBoolValue lhs
    let r ← icmpBoolValue rhs
    let rest ← semVectorBoolICmp op lhsRest rhsRest
    pure (.bool (semBoolICmp op l r) :: rest)
  | [], _ :: _ => .error (.typeError "Vector ICmp: mismatched lane counts")
  | _ :: _, [] => .error (.typeError "Vector ICmp: mismatched lane counts")

/-- Integer lanes admitted by the vector validator, independent of backend
    register shapes. Other vector operations retain their own shape checks. -/
def Ty.icmpIntLaneWidth? : Ty → Option Nat
  | .I8 | .U8 => some 8
  | .I16 | .U16 => some 16
  | .I32 | .U32 => some 32
  | .I64 | .U64 => some 64
  | _ => none

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

/-- Pointer comparison exposes the numeric address without dereferencing it.
    Provenance is retained in the operand and grants no extra comparison bits;
    malformed addresses cannot wrap into the selected target's address space. -/
def pointerComparisonAddress (model : ByteModel) : Value → Except SemError Int
  | .nullPtr => .ok 0
  | .ptr address _ =>
    if address < model.addressLimit then .ok (Int.ofNat address)
    else .error (.ub "ICmp: pointer address exceeds the target width")
  | _ => .error (.typeError "ICmp: expected a pointer operand")

/-- Checked value-level comparison. Every positive validator-admitted integer
    or Bool vector census is traversed structurally, without a backend shape
    restriction. No other vector operation is enabled by this rule. -/
def semICmpValues (op : ICmpOp) (ty : Ty) (lhsVal rhsVal : Value)
    (model : ByteModel := .le64) : Except SemError Value := do
  match ty with
  | .Ptr =>
    let lhs ← pointerComparisonAddress model lhsVal
    let rhs ← pointerComparisonAddress model rhsVal
    pure (.bool (semICmp op model.pointerBits lhs rhs))
  | .Bool =>
    let lhs ← icmpBoolValue lhsVal
    let rhs ← icmpBoolValue rhsVal
    pure (.bool (semBoolICmp op lhs rhs))
  | .Vector lanes elemTy =>
    if lanes == 0 then
      .error (.unsupported .vectorType "Vector ICmp: zero-lane vectors are not executable")
    else
      match lhsVal, rhsVal with
      | .vector lhs, .vector rhs =>
        if lhs.length != lanes || rhs.length != lanes then
          .error (.typeError "Vector ICmp: lane count does not match type")
        else
          match elemTy with
          | .Bool => return .vector (← semVectorBoolICmp op lhs rhs)
          | _ =>
            match elemTy.icmpIntLaneWidth? with
            | some width => return .vector (← semVectorICmp op width lhs rhs)
            | none => .error (.unsupported .vectorType
                s!"Vector ICmp: unsupported lane type {repr elemTy}")
      | _, _ => .error (.typeError "Vector ICmp: expected vector operands")
  | _ =>
    if ty.isInteger then
      match ty.bitWidthFor model with
      | some width =>
        let lhs ← icmpIntValue width lhsVal
        let rhs ← icmpIntValue width rhsVal
        pure (.bool (semICmp op width lhs rhs))
      | none => .error (.typeError "ICmp: integer type has no bit width")
    else .error (.typeError s!"ICmp: unsupported operand type {repr ty}")

/-- Compare operands after both root poison guards. Lane poison is checked
    when structural vector traversal inspects that lane. -/
def semICmpInst (op : ICmpOp) (ty : Ty) (lhsId rhsId : ValueId)
    (model : ByteModel := .le64) : Sem ValueId := do
  let lhsVal ← Sem.lookupValue lhsId
  let rhsVal ← Sem.lookupValue rhsId
  -- Comparison inspects both operands: consuming a poison value is UB.
  Sem.rejectPartial lhsVal "ICmp"
  Sem.rejectPartial rhsVal "ICmp"
  match semICmpValues op ty lhsVal rhsVal model with
  | .ok result => Sem.bindFresh result
  | .error error => throw error

/-- Evaluate an FCmp instruction in the semantic monad. The comparison itself
    is exact at every width, but both operands must inhabit the static float
    type `ty` (`checkFloatAt`), so a value the model cannot vouch for at that
    width is refused rather than compared at binary64. -/
def semVectorFCmp (op : FCmpOp) (elemTy : Ty) :
    List Value → List Value → Except SemError (List Value)
  | [], [] => .ok []
  | lhs :: left, rhs :: right => do
    checkVectorLaneType elemTy false lhs
    checkVectorLaneType elemTy false rhs
    let first ← match lhs, rhs with
      | .float l, .float r => pure (.bool (semFCmp op l r))
      | _, _ => throw (.typeError "Vector FCmp: expected float lanes")
    let rest ← semVectorFCmp op elemTy left right
    pure (first :: rest)
  | _, _ => .error (.typeError "Vector FCmp: mismatched lane counts")

def semFCmpValues (op : FCmpOp) (ty : Ty) (lhsVal rhsVal : Value) :
    Except SemError Value := do
  match ty, lhsVal, rhsVal with
  | .Vector count elemTy, .vector lhs, .vector rhs =>
    checkVectorShape count elemTy lhs
    checkVectorShape count elemTy rhs
    if !elemTy.isFloat then throw (.typeError "Vector FCmp: lane type is not float")
    return .vector (← semVectorFCmp op elemTy lhs rhs)
  | _, .float l, .float r =>
    checkFloatAt ty l
    checkFloatAt ty r
    pure (.bool (semFCmp op l r))
  | _, _, _ => throw (.typeError s!"FCmp: non-float operands for {repr op}")

def semFCmpInst (op : FCmpOp) (ty : Ty) (lhsId rhsId : ValueId) : Sem ValueId := do
  let lhsVal ← Sem.lookupValue lhsId
  let rhsVal ← Sem.lookupValue rhsId
  Sem.rejectPartial lhsVal "FCmp"
  Sem.rejectPartial rhsVal "FCmp"
  match semFCmpValues op ty lhsVal rhsVal with
  | .ok result => Sem.bindFresh result
  | .error error => throw error

end TrustIr
