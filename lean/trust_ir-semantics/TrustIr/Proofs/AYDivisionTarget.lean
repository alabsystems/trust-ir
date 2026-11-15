-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0
import TrustIr.Proofs.AYUnsignedDivision

namespace TrustIr.AYGateCNF
open TrustIrExpr

def DivisionCode.quotientWord {width : Nat} (code : DivisionCode width)
    (size : code.quotient.length = width) : WordCode width :=
  ⟨code.remainder.gates, fun i => code.quotient.get ⟨i.val, by rw [size]; exact i.isLt⟩⟩

theorem division_tabulate_get (wires : List Nat) (width : Nat) (size : wires.length = width) :
    tabulate (fun i : Fin width => wires.get ⟨i.val, by rw [size]; exact i.isLt⟩) = wires := by
  apply List.ext_get (by rw [tabulate_length, size])
  intro n left right
  have bound : n < width := by simpa only [tabulate_length] using left
  rw [tabulate_get _ ⟨n, bound⟩]

theorem DivisionCode.quotientWord_check {width : Nat} (code : DivisionCode width)
    (size : code.quotient.length = width) (next : Nat) (checked : code.check next = true) :
    (code.quotientWord size).check next = true := by
  obtain ⟨wordCheck, quotientBound⟩ := (DivisionCode.check_iff _ _).mp checked
  apply (WordCode.check_iff _ _).mpr
  refine ⟨((WordCode.check_iff _ _).mp wordCheck).1, ?_⟩
  intro i
  apply quotientBound
  trustIrCompilerProof { exact List.get_mem _ _ _ } { exact List.get_mem _ _ }

theorem DivisionCode.quotientWord_toNat {width : Nat} (code : DivisionCode width)
    (size : code.quotient.length = width) (env : Assignment) :
    ((code.quotientWord size).value env).toNat = (code.value env).1 := by
  rw [WordCode.value, wordValue_toNat, DivisionCode.quotientWord, division_tabulate_get _ _ size]
  rfl

inductive UnsignedDivisionOp where
  | quotient | remainder
  deriving Repr, DecidableEq

def UnsignedDivisionOp.target (op : UnsignedDivisionOp) (width : Nat) : SMTBinary (.bv width) (.bv width) :=
  match op with
  | .quotient => .bvUDiv width
  | .remainder => .bvURem width

def UnsignedDivisionOp.eval {width : Nat} (op : UnsignedDivisionOp) (left right : BitVec width) : BitVec width :=
  match op with
  | .quotient => BitVec.smtUDiv left right
  | .remainder => BitVec.umod left right

def WordCode.unsignedDivision {width : Nat} (op : UnsignedDivisionOp)
    (dividend divisor : Fin width → Nat) (next : Nat) : WordCode width :=
  let code := DivisionCode.unsigned dividend divisor next
  match op with
  | .quotient => code.quotientWord (DivisionCode.unsigned_quotient_length _ _ _)
  | .remainder => code.remainder

theorem WordCode.unsignedDivision_check {width : Nat} (op : UnsignedDivisionOp)
    (dividend divisor : Fin width → Nat) (next : Nat)
    (dividendBound : ∀ i, dividend i < next) (divisorBound : ∀ i, divisor i < next) :
    (WordCode.unsignedDivision op dividend divisor next).check next = true := by
  have checked := DivisionCode.unsigned_check dividend divisor next dividendBound divisorBound
  cases op with
  | quotient => exact DivisionCode.quotientWord_check _ (DivisionCode.unsigned_quotient_length _ _ _) _ checked
  | remainder => exact ((DivisionCode.check_iff _ _).mp checked).1

theorem unsignedDivision_eval_toNat {width : Nat} (left right : BitVec width) :
    ((UnsignedDivisionOp.quotient.eval left right).toNat, (UnsignedDivisionOp.remainder.eval left right).toNat) =
      if right.toNat = 0 then (2^width-1,left.toNat) else (left.toNat/right.toNat,left.toNat%right.toNat) := by
  have zero : right = 0 ↔ right.toNat = 0 := by
    constructor
    · intro same; rw [same]; rfl
    · intro same; apply BitVec.eq_of_toNat_eq; simpa using same
  by_cases empty : right.toNat = 0
  · simp [UnsignedDivisionOp.eval, BitVec.smtUDiv, zero.mpr empty, BitVec.umod, empty]
  · have notZero : right ≠ BitVec.ofNat width 0 := by
      intro same
      apply empty
      rw [same]
      simp
    simp [UnsignedDivisionOp.eval, BitVec.smtUDiv, notZero, BitVec.udiv, BitVec.umod, empty]

theorem WordCode.unsignedDivision_value {width : Nat} (op : UnsignedDivisionOp)
    (dividend divisor : Fin width → Nat) (next : Nat)
    (dividendBound : ∀ i, dividend i < next) (divisorBound : ∀ i, divisor i < next) (env : Assignment) :
    (WordCode.unsignedDivision op dividend divisor next).value env =
      op.eval (wordValue dividend env) (wordValue divisor env) := by
  have actual := DivisionCode.unsigned_value dividend divisor next dividendBound divisorBound env
  have native := unsignedDivision_eval_toNat (wordValue dividend env) (wordValue divisor env)
  have same : (DivisionCode.unsigned dividend divisor next).value env =
      ((UnsignedDivisionOp.quotient.eval (wordValue dividend env) (wordValue divisor env)).toNat,
       (UnsignedDivisionOp.remainder.eval (wordValue dividend env) (wordValue divisor env)).toNat) := actual.trans native.symm
  apply BitVec.eq_of_toNat_eq
  cases op with
  | quotient =>
    rw [WordCode.unsignedDivision, DivisionCode.quotientWord_toNat]
    exact congrArg Prod.fst same
  | remainder => exact congrArg Prod.snd same

theorem WordCode.unsignedDivision_target {width : Nat} (op : UnsignedDivisionOp)
    (dividend divisor : Fin width → Nat) (next : Nat)
    (dividendBound : ∀ i, dividend i < next) (divisorBound : ∀ i, divisor i < next)
    (env : Assignment) (left right : SMTTerm (.bv width)) (target : SMTEnv)
    (leftValue : wordValue dividend env = left.eval target) (rightValue : wordValue divisor env = right.eval target) :
    (WordCode.unsignedDivision op dividend divisor next).value env =
      (SMTTerm.binary (op.target width) left right).eval target := by
  rw [WordCode.unsignedDivision_value _ _ _ _ dividendBound divisorBound, leftValue, rightValue]
  cases op <;> rfl

theorem WordCode.unsignedDivision_gates {width : Nat} (op : UnsignedDivisionOp)
    (dividend divisor : Fin width → Nat) (next : Nat) :
    (WordCode.unsignedDivision op dividend divisor next).gates =
      (DivisionCode.unsigned dividend divisor next).remainder.gates := by cases op <;> rfl

theorem WordCode.unsignedDivision_length {width : Nat} (op : UnsignedDivisionOp)
    (dividend divisor : Fin width → Nat) (next : Nat) :
    (WordCode.unsignedDivision op dividend divisor next).gates.length = width+width*(6*width+10) := by
  rw [WordCode.unsignedDivision_gates, DivisionCode.unsigned_gate_count]

def WordCode.composeUnsignedDivision {width : Nat} (op : UnsignedDivisionOp) (next : Nat)
    (left right : WordCode width) : WordCode width :=
  let both := WordCode.append left right
  WordCode.append both (WordCode.unsignedDivision op left.bits right.bits (next+both.gates.length))

theorem WordCode.composeUnsignedDivision_check {width : Nat} (op : UnsignedDivisionOp) (next : Nat)
    (left right : WordCode width) (leftCheck : left.check next = true)
    (rightCheck : right.check (next+left.gates.length) = true) :
    (WordCode.composeUnsignedDivision op next left right).check next = true := by
  obtain ⟨leftBounds, rightBounds⟩ := WordCode.append_operand_bounds next left right leftCheck rightCheck
  exact WordCode.append_check _ _ _ (WordCode.append_check _ _ _ leftCheck rightCheck)
    (WordCode.unsignedDivision_check _ _ _ _ leftBounds rightBounds)

theorem WordCode.composeUnsignedDivision_value {width : Nat} (op : UnsignedDivisionOp) (next : Nat)
    (left right : WordCode width) (leftCheck : left.check next = true)
    (rightCheck : right.check (next+left.gates.length) = true) (env : Assignment) :
    (WordCode.composeUnsignedDivision op next left right).value env =
      op.eval (left.value env) (right.value (run left.gates env)) := by
  obtain ⟨leftBounds, rightBounds⟩ := WordCode.append_operand_bounds next left right leftCheck rightCheck
  have rightValid := ((WordCode.check_iff _ _).mp rightCheck).1
  have leftValue : wordValue left.bits (run (WordCode.append left right).gates env) = left.value env := by
    apply wordValue_congr
    intro i
    exact rightValid.append_preserves (next := next) (first := left.gates) env (left.bits i)
      (((WordCode.check_iff _ _).mp leftCheck).2 i)
  have rightValue : wordValue right.bits (run (WordCode.append left right).gates env) =
      right.value (run left.gates env) := by rw [WordCode.append, run_append]; rfl
  rw [WordCode.composeUnsignedDivision, WordCode.append_value,
    WordCode.unsignedDivision_value _ _ _ _ leftBounds rightBounds, leftValue, rightValue]

theorem WordCode.composeUnsignedDivision_target {width : Nat} (op : UnsignedDivisionOp) (next : Nat)
    (left right : WordCode width) (leftCheck : left.check next = true)
    (rightCheck : right.check (next+left.gates.length) = true) (env : Assignment)
    (leftTerm rightTerm : SMTTerm (.bv width)) (target : SMTEnv)
    (leftValue : left.value env = leftTerm.eval target)
    (rightValue : right.value (run left.gates env) = rightTerm.eval target) :
    (WordCode.composeUnsignedDivision op next left right).value env =
      (SMTTerm.binary (op.target width) leftTerm rightTerm).eval target := by
  rw [WordCode.composeUnsignedDivision_value _ _ _ _ leftCheck rightCheck, leftValue, rightValue]
  cases op <;> rfl

def WordCode.checkedUnsignedDivision {width : Nat} (op : UnsignedDivisionOp)
    (dividend divisor : Fin width → Nat) (next : Nat) (env : Assignment) : Option (BitVec width) :=
  if divisionInputsCheck dividend divisor next then
    (WordCode.unsignedDivision op dividend divisor next).checkedEval next env
  else none

theorem WordCode.checkedUnsignedDivision_eq_some {width : Nat} (op : UnsignedDivisionOp)
    (dividend divisor : Fin width → Nat) (next : Nat) (env : Assignment) (result : BitVec width) :
    WordCode.checkedUnsignedDivision op dividend divisor next env = some result ↔
      (∀ i, dividend i < next) ∧ (∀ i, divisor i < next) ∧
        (WordCode.unsignedDivision op dividend divisor next).value env = result := by
  by_cases checked : divisionInputsCheck dividend divisor next = true
  · obtain ⟨dividendBound, divisorBound⟩ := (divisionInputsCheck_iff _ _ _).mp checked
    simp [WordCode.checkedUnsignedDivision, checked, WordCode.checkedEval_eq_some,
      WordCode.unsignedDivision_check _ _ _ _ dividendBound divisorBound, dividendBound, divisorBound]
  · have bad : ¬ ((∀ i, dividend i < next) ∧ (∀ i, divisor i < next)) :=
      fun bounds => checked ((divisionInputsCheck_iff _ _ _).mpr bounds)
    trustIrCompilerProof {
      simp only [WordCode.checkedUnsignedDivision, checked, Bool.false_eq_true, if_false, Option.noConfusion, false_iff]
    } {
      simp only [WordCode.checkedUnsignedDivision, checked, Bool.false_eq_true, if_false, reduceCtorEq, false_iff]
    }
    intro valid
    exact bad ⟨valid.1, valid.2.1⟩

theorem WordCode.checkedUnsignedDivision_target {width : Nat} (op : UnsignedDivisionOp)
    (dividend divisor : Fin width → Nat) (next : Nat)
    (dividendBound : ∀ i, dividend i < next) (divisorBound : ∀ i, divisor i < next)
    (env : Assignment) (left right : SMTTerm (.bv width)) (target : SMTEnv)
    (leftValue : wordValue dividend env = left.eval target) (rightValue : wordValue divisor env = right.eval target) :
    WordCode.checkedUnsignedDivision op dividend divisor next env =
      some ((SMTTerm.binary (op.target width) left right).eval target) := by
  exact (WordCode.checkedUnsignedDivision_eq_some _ _ _ _ _ _).mpr
    ⟨dividendBound, divisorBound, WordCode.unsignedDivision_target _ _ _ _ dividendBound divisorBound env
      left right target leftValue rightValue⟩

end TrustIr.AYGateCNF

#trustIrAxiomsExact TrustIr.AYGateCNF.division_tabulate_get == [propext, Classical.choice, Quot.sound]

#trustIrAxiomsExact TrustIr.AYGateCNF.DivisionCode.quotientWord_check == [propext, Quot.sound, Classical.choice]

#trustIrAxiomsExact TrustIr.AYGateCNF.DivisionCode.quotientWord_toNat == [propext, Classical.choice, Quot.sound]

#trustIrAxiomsExact TrustIr.AYGateCNF.WordCode.unsignedDivision_check == [propext, Classical.choice, Quot.sound]

#trustIrAxiomsExact TrustIr.AYGateCNF.unsignedDivision_eval_toNat == [propext]

#trustIrAxiomsExact TrustIr.AYGateCNF.WordCode.unsignedDivision_value == [propext, Classical.choice, Quot.sound]

#trustIrAxiomsExact TrustIr.AYGateCNF.WordCode.unsignedDivision_target == [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AYGateCNF.WordCode.unsignedDivision_gates == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.AYGateCNF.WordCode.unsignedDivision_length == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsExact TrustIr.AYGateCNF.WordCode.composeUnsignedDivision_check == [propext, Classical.choice, Quot.sound]

#trustIrAxiomsExact TrustIr.AYGateCNF.WordCode.composeUnsignedDivision_value == [propext, Classical.choice, Quot.sound]

#trustIrAxiomsExact TrustIr.AYGateCNF.WordCode.composeUnsignedDivision_target == [propext, Classical.choice, Quot.sound]

#trustIrAxiomsExact TrustIr.AYGateCNF.WordCode.checkedUnsignedDivision_eq_some == [propext, Classical.choice, Quot.sound]

#trustIrAxiomsExact TrustIr.AYGateCNF.WordCode.checkedUnsignedDivision_target == [propext, Classical.choice, Quot.sound]
