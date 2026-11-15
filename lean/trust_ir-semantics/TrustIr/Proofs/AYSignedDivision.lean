-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0
import TrustIr.Proofs.AYDivisionTarget

namespace TrustIr.AYGateCNF
open TrustIrExpr

/-- Negate the actual word conditionally, preserving its original inputs
through one negation program and selecting with the original condition. -/
def WordCode.negateIf {width : Nat} (bit : Nat) (input : Fin width → Nat) (next : Nat) : WordCode width :=
  let negative := WordCode.neg input next
  WordCode.append negative (WordCode.ite bit negative.bits input (next+negative.gates.length))

theorem WordCode.negateIf_check {width : Nat} (bit : Nat) (input : Fin width → Nat) (next : Nat)
    (bound : ∀ i, input i < next) (bitBound : bit < next) :
    (WordCode.negateIf bit input next).check next = true := by
  have checked := WordCode.neg_check input next bound
  apply WordCode.append_check _ _ _ checked
  apply WordCode.ite_check
  · omega
  · exact ((WordCode.check_iff _ _).mp checked).2
  · intro i; have before := bound i; omega

theorem WordCode.negateIf_value {width : Nat} (bit : Nat) (input : Fin width → Nat) (next : Nat)
    (bound : ∀ i, input i < next) (bitBound : bit < next) (env : Assignment) :
    (WordCode.negateIf bit input next).value env = if env bit then -(wordValue input env) else wordValue input env := by
  have checked := WordCode.neg_check input next bound
  have valid := ((WordCode.check_iff _ _).mp checked).1
  have later : ∀ i, input i < next+(WordCode.neg input next).gates.length := by
    intro i; have before := bound i; omega
  have same : wordValue input (run (WordCode.neg input next).gates env) = wordValue input env := by
    apply wordValue_congr
    intro i; exact (valid.run_correct env).1 _ (bound i)
  rw [WordCode.negateIf, WordCode.append_value,
    WordCode.ite_value _ _ _ _ (by omega) ((WordCode.check_iff _ _).mp checked).2 later,
    (valid.run_correct env).1 _ bitBound, same]
  change (if env bit then (WordCode.neg input next).value env else _) = _
  rw [WordCode.neg_value _ _ bound]

inductive SignedDivisionOp where
  | quotient | remainder
  deriving Repr, DecidableEq

def SignedDivisionOp.unsigned : SignedDivisionOp → UnsignedDivisionOp
  | .quotient => .quotient | .remainder => .remainder

def SignedDivisionOp.eval {width : Nat} (op : SignedDivisionOp) (left right : BitVec width) : BitVec width :=
  match op with
  | .quotient => BitVec.smtSDiv left right
  | .remainder => BitVec.srem left right

def SignedDivisionOp.target (op : SignedDivisionOp) (width : Nat) : SMTBinary (.bv width) (.bv width) :=
  match op with
  | .quotient => .bvSDiv width | .remainder => .bvSRem width

def Code.divisionSign (op : SignedDivisionOp) (left right next : Nat) : Code :=
  match op with
  | .quotient => ⟨[.xor2 next left right],next⟩
  | .remainder => Code.wire left

theorem Code.divisionSign_check (op : SignedDivisionOp) (left right next : Nat)
    (leftBound : left < next) (rightBound : right < next) :
    (Code.divisionSign op left right next).check next = true := by
  cases op with
  | quotient =>
    apply (Code.check_iff _ _).mpr
    refine ⟨Valid.cons rfl (by simpa [Gate.inputs] using And.intro leftBound rightBound) (.nil _), ?_⟩
    simp [Code.divisionSign]
  | remainder => exact (Code.wire_check _ _).mpr leftBound

theorem Code.divisionSign_eval (op : SignedDivisionOp) (left right next : Nat) (env : Assignment) :
    (Code.divisionSign op left right next).eval env =
      match op with | .quotient => xor (env left) (env right) | .remainder => env left := by
  cases op with
  | quotient => simp [Code.divisionSign, Code.eval, run, Gate.apply, Gate.eval, Gate.output]
  | remainder => rfl

theorem signedDivision_normalized {width : Nat} (op : SignedDivisionOp) (left right : BitVec width) :
    let magnitude := op.unsigned.eval (if left.msb then -left else left) (if right.msb then -right else right)
    let negative := match op with | .quotient => xor left.msb right.msb | .remainder => left.msb
    (if negative then -magnitude else magnitude) = op.eval left right := by
  cases op <;> cases hl : left.msb <;> cases hr : right.msb <;>
    simp [SignedDivisionOp.unsigned, SignedDivisionOp.eval, UnsignedDivisionOp.eval, BitVec.smtSDiv, BitVec.srem, hl, hr]

def WordCode.signedMagnitude {width : Nat} (op : SignedDivisionOp) (left right : Fin width → Nat)
    (leftSign rightSign next : Nat) : WordCode width :=
  let lhs := WordCode.negateIf leftSign left next
  let rhs := WordCode.negateIf rightSign right (next+lhs.gates.length)
  WordCode.composeUnsignedDivision op.unsigned next lhs rhs

theorem WordCode.signedMagnitude_check {width : Nat} (op : SignedDivisionOp) (left right : Fin width → Nat)
    (leftSign rightSign next : Nat) (leftBound : ∀ i, left i < next) (rightBound : ∀ i, right i < next)
    (leftSignBound : leftSign < next) (rightSignBound : rightSign < next) :
    (WordCode.signedMagnitude op left right leftSign rightSign next).check next = true := by
  apply WordCode.composeUnsignedDivision_check
  · exact WordCode.negateIf_check _ _ _ leftBound leftSignBound
  · apply WordCode.negateIf_check
    · intro i; have before := rightBound i; omega
    · omega

theorem WordCode.signedMagnitude_value {width : Nat} (op : SignedDivisionOp) (left right : Fin width → Nat)
    (leftSign rightSign next : Nat) (leftBound : ∀ i, left i < next) (rightBound : ∀ i, right i < next)
    (leftSignBound : leftSign < next) (rightSignBound : rightSign < next) (env : Assignment) :
    (WordCode.signedMagnitude op left right leftSign rightSign next).value env =
      op.unsigned.eval (if env leftSign then -(wordValue left env) else wordValue left env)
        (if env rightSign then -(wordValue right env) else wordValue right env) := by
  have lhsCheck := WordCode.negateIf_check leftSign left next leftBound leftSignBound
  have later : ∀ i, right i < next+(WordCode.negateIf leftSign left next).gates.length := by
    intro i; have before := rightBound i; omega
  have signLater : rightSign < next+(WordCode.negateIf leftSign left next).gates.length := by omega
  have rhsCheck := WordCode.negateIf_check rightSign right _ later signLater
  have valid := ((WordCode.check_iff _ _).mp lhsCheck).1
  have rightSame : wordValue right (run (WordCode.negateIf leftSign left next).gates env) = wordValue right env := by
    apply wordValue_congr
    intro i; exact (valid.run_correct env).1 _ (rightBound i)
  rw [WordCode.signedMagnitude, WordCode.composeUnsignedDivision_value _ _ _ _ lhsCheck rhsCheck,
    WordCode.negateIf_value _ _ _ leftBound leftSignBound,
    WordCode.negateIf_value _ _ _ later signLater, rightSame,
    (valid.run_correct env).1 _ rightSignBound]

def WordCode.signedDivision {width : Nat} (op : SignedDivisionOp) (left right : Fin width → Nat)
    (next : Nat) : WordCode width :=
  if positive : 0 < width then
    let sign : Fin width := ⟨width-1, by omega⟩
    let condition := Code.divisionSign op (left sign) (right sign) next
    let magnitude := WordCode.signedMagnitude op left right (left sign) (right sign) (next+condition.gates.length)
    let prior := condition.appendWord magnitude
    WordCode.append prior (WordCode.negateIf condition.output prior.bits (next+prior.gates.length))
  else ⟨[],left⟩

theorem WordCode.signedDivision_check {width : Nat} (op : SignedDivisionOp) (left right : Fin width → Nat)
    (next : Nat) (leftBound : ∀ i, left i < next) (rightBound : ∀ i, right i < next) :
    (WordCode.signedDivision op left right next).check next = true := by
  unfold WordCode.signedDivision
  split
  · rename_i positive
    let sign : Fin width := ⟨width-1, by omega⟩
    have condition := Code.divisionSign_check op (left sign) (right sign) next (leftBound sign) (rightBound sign)
    have laterLeft : ∀ i, left i < next+(Code.divisionSign op (left sign) (right sign) next).gates.length := by
      intro i; have before := leftBound i; omega
    have laterRight : ∀ i, right i < next+(Code.divisionSign op (left sign) (right sign) next).gates.length := by
      intro i; have before := rightBound i; omega
    have mag := WordCode.signedMagnitude_check op left right (left sign) (right sign) _
      laterLeft laterRight (laterLeft sign) (laterRight sign)
    have prior := Code.appendWord_check _ _ _ condition mag
    apply WordCode.append_check _ _ _ prior
    apply WordCode.negateIf_check
    · exact ((WordCode.check_iff _ _).mp prior).2
    · have bound := ((Code.check_iff _ _).mp condition).2
      apply Nat.lt_of_lt_of_le bound
      simp only [Code.appendWord, List.length_append]
      change next+(Code.divisionSign op (left sign) (right sign) next).gates.length ≤ _
      simp only [← Nat.add_assoc]
      exact Nat.le_add_right _ _
  · apply (WordCode.check_iff _ _).mpr
    exact ⟨.nil next, by simpa using leftBound⟩

theorem WordCode.signedDivision_value {width : Nat} (op : SignedDivisionOp) (left right : Fin width → Nat)
    (next : Nat) (leftBound : ∀ i, left i < next) (rightBound : ∀ i, right i < next) (env : Assignment) :
    (WordCode.signedDivision op left right next).value env = op.eval (wordValue left env) (wordValue right env) := by
  by_cases positive : 0 < width
  · let sign : Fin width := ⟨width-1, by omega⟩
    let condition := Code.divisionSign op (left sign) (right sign) next
    let start := next+condition.gates.length
    let magnitude := WordCode.signedMagnitude op left right (left sign) (right sign) start
    let prior := condition.appendWord magnitude
    have checked := Code.divisionSign_check op (left sign) (right sign) next (leftBound sign) (rightBound sign)
    obtain ⟨conditionValid, conditionBound⟩ := (Code.check_iff _ _).mp checked
    have laterLeft : ∀ i, left i < start := by intro i; have before := leftBound i; dsimp [start]; omega
    have laterRight : ∀ i, right i < start := by intro i; have before := rightBound i; dsimp [start]; omega
    have magCheck := WordCode.signedMagnitude_check op left right (left sign) (right sign) start
      laterLeft laterRight (laterLeft sign) (laterRight sign)
    have priorCheck := Code.appendWord_check condition magnitude next checked magCheck
    have finalSignBound : condition.output < next+prior.gates.length := by
      dsimp [prior, Code.appendWord]
      rw [List.length_append]
      apply Nat.lt_of_lt_of_le conditionBound
      change next+condition.gates.length ≤ next+(condition.gates.length+magnitude.gates.length)
      omega
    have conditionSame : run prior.gates env condition.output = condition.eval env := by
      rw [show prior.gates = condition.gates ++ magnitude.gates from rfl, run_append]
      exact ((((WordCode.check_iff _ _).mp magCheck).1).run_correct _).1 _ conditionBound
    have originalSame : ∀ id, id < next → run condition.gates env id = env id := (conditionValid.run_correct env).1
    have leftSame : wordValue left (run condition.gates env) = wordValue left env :=
      wordValue_congr _ _ _ (fun i => originalSame _ (leftBound i))
    have rightSame : wordValue right (run condition.gates env) = wordValue right env :=
      wordValue_congr _ _ _ (fun i => originalSame _ (rightBound i))
    have magnitudeValue : prior.value env =
        op.unsigned.eval (if env (left sign) then -(wordValue left env) else wordValue left env)
          (if env (right sign) then -(wordValue right env) else wordValue right env) := by
      rw [Code.appendWord_value, WordCode.signedMagnitude_value _ _ _ _ _ _ laterLeft laterRight
        (laterLeft sign) (laterRight sign), leftSame, rightSame,
        originalSame _ (leftBound sign), originalSame _ (rightBound sign)]
    have leftSign : env (left sign) = (wordValue left env).msb := by
      rw [trustIrWidthLemma BitVec.msb_eq_getLsb_last BitVec.msb_eq_getLsbD_last]
      exact (wordValue_bit left env sign).symm
    have rightSign : env (right sign) = (wordValue right env).msb := by
      rw [trustIrWidthLemma BitVec.msb_eq_getLsb_last BitVec.msb_eq_getLsbD_last]
      exact (wordValue_bit right env sign).symm
    rw [WordCode.signedDivision, dif_pos positive]
    change (WordCode.append prior (WordCode.negateIf condition.output prior.bits (next+prior.gates.length))).value env = _
    rw [WordCode.append_value, WordCode.negateIf_value _ _ _ ((WordCode.check_iff _ _).mp priorCheck).2 finalSignBound,
      conditionSame]
    change (if condition.eval env then -(prior.value env) else prior.value env) = _
    rw [magnitudeValue, Code.divisionSign_eval, leftSign, rightSign]
    exact signedDivision_normalized op _ _
  · have empty : width = 0 := by omega
    subst width
    apply trustIrWordExt
    intro i
    exact Fin.elim0 i

theorem WordCode.signedDivision_target {width : Nat} (op : SignedDivisionOp) (left right : Fin width → Nat)
    (next : Nat) (leftBound : ∀ i, left i < next) (rightBound : ∀ i, right i < next)
    (env : Assignment) (leftTerm rightTerm : SMTTerm (.bv width)) (target : SMTEnv)
    (leftValue : wordValue left env = leftTerm.eval target) (rightValue : wordValue right env = rightTerm.eval target) :
    (WordCode.signedDivision op left right next).value env =
      (SMTTerm.binary (op.target width) leftTerm rightTerm).eval target := by
  rw [WordCode.signedDivision_value _ _ _ _ leftBound rightBound, leftValue, rightValue]
  cases op <;> rfl

def WordCode.composeSignedDivision {width : Nat} (op : SignedDivisionOp) (next : Nat)
    (left right : WordCode width) : WordCode width :=
  let both := WordCode.append left right
  WordCode.append both (WordCode.signedDivision op left.bits right.bits (next+both.gates.length))

theorem WordCode.composeSignedDivision_check {width : Nat} (op : SignedDivisionOp) (next : Nat)
    (left right : WordCode width) (leftCheck : left.check next = true)
    (rightCheck : right.check (next+left.gates.length) = true) :
    (WordCode.composeSignedDivision op next left right).check next = true := by
  obtain ⟨leftBounds, rightBounds⟩ := WordCode.append_operand_bounds next left right leftCheck rightCheck
  exact WordCode.append_check _ _ _ (WordCode.append_check _ _ _ leftCheck rightCheck)
    (WordCode.signedDivision_check _ _ _ _ leftBounds rightBounds)

theorem WordCode.composeSignedDivision_value {width : Nat} (op : SignedDivisionOp) (next : Nat)
    (left right : WordCode width) (leftCheck : left.check next = true)
    (rightCheck : right.check (next+left.gates.length) = true) (env : Assignment) :
    (WordCode.composeSignedDivision op next left right).value env =
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
  rw [WordCode.composeSignedDivision, WordCode.append_value,
    WordCode.signedDivision_value _ _ _ _ leftBounds rightBounds, leftValue, rightValue]

theorem WordCode.composeSignedDivision_target {width : Nat} (op : SignedDivisionOp) (next : Nat)
    (left right : WordCode width) (leftCheck : left.check next = true)
    (rightCheck : right.check (next+left.gates.length) = true) (env : Assignment)
    (leftTerm rightTerm : SMTTerm (.bv width)) (target : SMTEnv)
    (leftValue : left.value env = leftTerm.eval target)
    (rightValue : right.value (run left.gates env) = rightTerm.eval target) :
    (WordCode.composeSignedDivision op next left right).value env =
      (SMTTerm.binary (op.target width) leftTerm rightTerm).eval target := by
  rw [WordCode.composeSignedDivision_value _ _ _ _ leftCheck rightCheck, leftValue, rightValue]
  cases op <;> rfl

def WordCode.checkedSignedDivision {width : Nat} (op : SignedDivisionOp)
    (dividend divisor : Fin width → Nat) (next : Nat) (env : Assignment) : Option (BitVec width) :=
  if divisionInputsCheck dividend divisor next then
    (WordCode.signedDivision op dividend divisor next).checkedEval next env
  else none

theorem WordCode.checkedSignedDivision_eq_some {width : Nat} (op : SignedDivisionOp)
    (dividend divisor : Fin width → Nat) (next : Nat) (env : Assignment) (result : BitVec width) :
    WordCode.checkedSignedDivision op dividend divisor next env = some result ↔
      (∀ i, dividend i < next) ∧ (∀ i, divisor i < next) ∧
        (WordCode.signedDivision op dividend divisor next).value env = result := by
  by_cases checked : divisionInputsCheck dividend divisor next = true
  · obtain ⟨dividendBound, divisorBound⟩ := (divisionInputsCheck_iff _ _ _).mp checked
    simp [WordCode.checkedSignedDivision, checked, WordCode.checkedEval_eq_some,
      WordCode.signedDivision_check _ _ _ _ dividendBound divisorBound, dividendBound, divisorBound]
  · have bad : ¬ ((∀ i, dividend i < next) ∧ (∀ i, divisor i < next)) :=
      fun bounds => checked ((divisionInputsCheck_iff _ _ _).mpr bounds)
    trustIrCompilerProof {
      simp only [WordCode.checkedSignedDivision, checked, Bool.false_eq_true, if_false, Option.noConfusion, false_iff]
    } {
      simp only [WordCode.checkedSignedDivision, checked, Bool.false_eq_true, if_false, reduceCtorEq, false_iff]
    }
    intro valid
    exact bad ⟨valid.1, valid.2.1⟩

theorem WordCode.checkedSignedDivision_target {width : Nat} (op : SignedDivisionOp)
    (dividend divisor : Fin width → Nat) (next : Nat)
    (dividendBound : ∀ i, dividend i < next) (divisorBound : ∀ i, divisor i < next)
    (env : Assignment) (left right : SMTTerm (.bv width)) (target : SMTEnv)
    (leftValue : wordValue dividend env = left.eval target) (rightValue : wordValue divisor env = right.eval target) :
    WordCode.checkedSignedDivision op dividend divisor next env =
      some ((SMTTerm.binary (op.target width) left right).eval target) := by
  exact (WordCode.checkedSignedDivision_eq_some _ _ _ _ _ _).mpr
    ⟨dividendBound, divisorBound, WordCode.signedDivision_target _ _ _ _ dividendBound divisorBound env
      left right target leftValue rightValue⟩

theorem WordCode.neg_length {width : Nat} (input : Fin width → Nat) (next : Nat) :
    (WordCode.neg input next).gates.length = 4*width+1 := by
  simp only [WordCode.neg, WordCode.append, List.length_append, WordCode.constant, tabulate_length,
    WordCode.sub_length]
  omega

theorem WordCode.negateIf_length {width : Nat} (bit : Nat) (input : Fin width → Nat) (next : Nat) :
    (WordCode.negateIf bit input next).gates.length = 7*width+2 := by
  simp only [WordCode.negateIf, WordCode.append, List.length_append, WordCode.neg_length, WordCode.ite_length]
  omega

theorem WordCode.signedMagnitude_length {width : Nat} (op : SignedDivisionOp) (left right : Fin width → Nat)
    (leftSign rightSign next : Nat) :
    (WordCode.signedMagnitude op left right leftSign rightSign next).gates.length =
      2*(7*width+2)+width+width*(6*width+10) := by
  simp only [WordCode.signedMagnitude, WordCode.composeUnsignedDivision, WordCode.append, List.length_append,
    WordCode.unsignedDivision_length, WordCode.negateIf_length]
  omega

theorem Code.divisionSign_length (op : SignedDivisionOp) (left right next : Nat) :
    (Code.divisionSign op left right next).gates.length = if op = .quotient then 1 else 0 := by
  cases op <;> rfl

theorem WordCode.signedDivision_length {width : Nat} (op : SignedDivisionOp) (left right : Fin width → Nat)
    (next : Nat) :
    (WordCode.signedDivision op left right next).gates.length =
      if width = 0 then 0 else 3*(7*width+2)+width+width*(6*width+10)+(if op = .quotient then 1 else 0) := by
  unfold WordCode.signedDivision
  split
  · rename_i positive
    rw [if_neg (show width ≠ 0 by omega)]
    simp only [WordCode.append, Code.appendWord, List.length_append, WordCode.negateIf_length,
      WordCode.signedMagnitude_length, Code.divisionSign_length]
    omega
  · rename_i empty
    rw [if_pos (show width = 0 by omega)]
    rfl

end TrustIr.AYGateCNF

#trustIrAxiomsExact TrustIr.AYGateCNF.WordCode.negateIf_check == [propext, Classical.choice, Quot.sound]

#trustIrAxiomsExact TrustIr.AYGateCNF.WordCode.negateIf_value == [propext, Classical.choice, Quot.sound]

#trustIrAxiomsExact TrustIr.AYGateCNF.Code.divisionSign_check == [propext, Quot.sound]

#trustIrAxiomsExact TrustIr.AYGateCNF.Code.divisionSign_eval == [Quot.sound, propext]

#trustIrAxiomsExact TrustIr.AYGateCNF.signedDivision_normalized == [propext]

#trustIrAxiomsExact TrustIr.AYGateCNF.WordCode.signedMagnitude_check == [propext, Classical.choice, Quot.sound]

#trustIrAxiomsExact TrustIr.AYGateCNF.WordCode.signedMagnitude_value == [propext, Classical.choice, Quot.sound]

#trustIrAxiomsExact TrustIr.AYGateCNF.WordCode.signedDivision_check == [propext, Classical.choice, Quot.sound]

#trustIrAxiomsExact TrustIr.AYGateCNF.WordCode.signedDivision_value == [propext, Classical.choice, Quot.sound]

#trustIrAxiomsExact TrustIr.AYGateCNF.WordCode.signedDivision_target == [propext, Classical.choice, Quot.sound]

#trustIrAxiomsExact TrustIr.AYGateCNF.WordCode.composeSignedDivision_check == [propext, Classical.choice, Quot.sound]

#trustIrAxiomsExact TrustIr.AYGateCNF.WordCode.composeSignedDivision_value == [propext, Classical.choice, Quot.sound]

#trustIrAxiomsExact TrustIr.AYGateCNF.WordCode.composeSignedDivision_target == [propext, Classical.choice, Quot.sound]

#trustIrAxiomsExact TrustIr.AYGateCNF.WordCode.checkedSignedDivision_eq_some == [propext, Classical.choice, Quot.sound]

#trustIrAxiomsExact TrustIr.AYGateCNF.WordCode.checkedSignedDivision_target == [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AYGateCNF.WordCode.neg_length == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.AYGateCNF.WordCode.negateIf_length == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.AYGateCNF.WordCode.signedMagnitude_length == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

/-- info: 'TrustIr.AYGateCNF.Code.divisionSign_length' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.AYGateCNF.Code.divisionSign_length

#trustIrAxiomsPinned TrustIr.AYGateCNF.WordCode.signedDivision_length == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]
