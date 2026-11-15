-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0
import TrustIr.Proofs.AYWordAdd

macro "trustIrWordSubAdd" : term => do
  if Lean.versionString == "4.8.0" then `(BitVec.sub_toAdd)
  else if Lean.versionString == "4.30.0-rc2" then `(BitVec.sub_eq_add_neg)
  else Lean.Macro.throwError "unsupported compiler for native word subtraction"

namespace TrustIr.AYGateCNF

/-- Two's complement uses native modular arithmetic, including width zero. -/
theorem word_not_add_one {width : Nat} (word : BitVec width) :
    ~~~word + BitVec.ofNat width 1 = -word := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, BitVec.toNat_not, BitVec.toNat_ofNat, Nat.add_mod_mod,
    BitVec.toNat_neg]
  congr 1
  have bound := word.isLt
  omega

/-- Subtraction complements the actual right wires and starts one ripple with
a true carry. It does not construct an intermediate arithmetic negation. -/
def WordCode.sub {width : Nat} (left right : Fin width → Nat) (next : Nat) : WordCode width :=
  let inverted := WordCode.bitNot right next
  WordCode.append inverted (WordCode.addCarry true left inverted.bits (next + inverted.gates.length))

theorem WordCode.sub_check {width : Nat} (left right : Fin width → Nat) (next : Nat)
    (leftBound : ∀ i, left i < next) (rightBound : ∀ i, right i < next) :
    (WordCode.sub left right next).check next = true := by
  have inverted := WordCode.bitNot_check right next rightBound
  apply WordCode.append_check _ _ next inverted
  apply WordCode.addCarry_check
  · intro i; have bound := leftBound i; omega
  · exact ((WordCode.check_iff _ _).mp inverted).2

theorem WordCode.sub_value {width : Nat} (left right : Fin width → Nat) (next : Nat)
    (leftBound : ∀ i, left i < next) (rightBound : ∀ i, right i < next) (env : Assignment) :
    (WordCode.sub left right next).value env = wordValue left env - wordValue right env := by
  have checked := WordCode.bitNot_check right next rightBound
  obtain ⟨valid, bounds⟩ := (WordCode.check_iff _ _).mp checked
  have leftLater : ∀ i, left i < next + (WordCode.bitNot right next).gates.length := by
    intro i; have bound := leftBound i; omega
  have leftSame : wordValue left (run (WordCode.bitNot right next).gates env) = wordValue left env := by
    apply wordValue_congr
    intro i
    exact (valid.run_correct env).1 (left i) (leftBound i)
  rw [WordCode.sub, WordCode.append_value, WordCode.addCarry_value _ _ _ _ leftLater bounds,
    leftSame]
  change wordValue left env + (WordCode.bitNot right next).value env + BitVec.ofNat width 1 = _
  rw [WordCode.bitNot_value right next rightBound, BitVec.add_assoc, word_not_add_one,
    trustIrWordSubAdd]

/-- Negation subtracts the input from an allocated zero word. -/
def WordCode.neg {width : Nat} (input : Fin width → Nat) (next : Nat) : WordCode width :=
  let zero := WordCode.constant (BitVec.ofNat width 0) next
  WordCode.append zero (WordCode.sub zero.bits input (next + zero.gates.length))

theorem WordCode.neg_check {width : Nat} (input : Fin width → Nat) (next : Nat)
    (bound : ∀ i, input i < next) : (WordCode.neg input next).check next = true := by
  have checked := WordCode.constant_check (BitVec.ofNat width 0) next
  apply WordCode.append_check _ _ next checked
  apply WordCode.sub_check
  · exact ((WordCode.check_iff _ _).mp checked).2
  · intro i; have before := bound i; omega

theorem WordCode.neg_value {width : Nat} (input : Fin width → Nat) (next : Nat)
    (bound : ∀ i, input i < next) (env : Assignment) :
    (WordCode.neg input next).value env = -(wordValue input env) := by
  have checked := WordCode.constant_check (BitVec.ofNat width 0) next
  obtain ⟨valid, bounds⟩ := (WordCode.check_iff _ _).mp checked
  have inputLater : ∀ i, input i < next + (WordCode.constant (BitVec.ofNat width 0) next).gates.length := by
    intro i; have before := bound i; omega
  have inputSame : wordValue input (run (WordCode.constant (BitVec.ofNat width 0) next).gates env) =
      wordValue input env := by
    apply wordValue_congr
    intro i
    exact (valid.run_correct env).1 (input i) (bound i)
  rw [WordCode.neg, WordCode.append_value, WordCode.sub_value _ _ _ bounds inputLater, inputSame]
  change (WordCode.constant (BitVec.ofNat width 0) next).value env - wordValue input env = _
  rw [WordCode.constant_value, trustIrWordSubAdd, BitVec.zero_add]

def WordCode.composeNeg {width : Nat} (next : Nat) (child : WordCode width) : WordCode width :=
  WordCode.append child (WordCode.neg child.bits (next + child.gates.length))

theorem WordCode.composeNeg_check {width : Nat} (next : Nat) (child : WordCode width)
    (checked : child.check next = true) : (WordCode.composeNeg next child).check next = true := by
  apply WordCode.append_check child _ next checked
  exact WordCode.neg_check _ _ ((child.check_iff next).mp checked).2

theorem WordCode.composeNeg_value {width : Nat} (next : Nat) (child : WordCode width)
    (checked : child.check next = true) (env : Assignment) :
    (WordCode.composeNeg next child).value env = -(child.value env) := by
  rw [WordCode.composeNeg, WordCode.append_value,
    WordCode.neg_value _ _ ((child.check_iff next).mp checked).2]
  rfl

def WordCode.composeSub {width : Nat} (next : Nat) (left right : WordCode width) : WordCode width :=
  let both := WordCode.append left right
  WordCode.append both (WordCode.sub left.bits right.bits (next + both.gates.length))

theorem WordCode.composeSub_check {width : Nat} (next : Nat) (left right : WordCode width)
    (leftCheck : left.check next = true)
    (rightCheck : right.check (next + left.gates.length) = true) :
    (WordCode.composeSub next left right).check next = true := by
  obtain ⟨leftBounds, rightBounds⟩ := WordCode.append_operand_bounds next left right leftCheck rightCheck
  apply WordCode.append_check _ _ next (WordCode.append_check left right next leftCheck rightCheck)
  exact WordCode.sub_check _ _ _ leftBounds rightBounds

theorem WordCode.composeSub_value {width : Nat} (next : Nat) (left right : WordCode width)
    (leftCheck : left.check next = true)
    (rightCheck : right.check (next + left.gates.length) = true) (env : Assignment) :
    (WordCode.composeSub next left right).value env = left.value env - right.value (run left.gates env) := by
  obtain ⟨leftBounds, rightBounds⟩ := WordCode.append_operand_bounds next left right leftCheck rightCheck
  have rightValid := ((right.check_iff _).mp rightCheck).1
  have leftValue : wordValue left.bits (run (WordCode.append left right).gates env) = left.value env := by
    apply wordValue_congr
    intro i
    exact rightValid.append_preserves (next := next) (first := left.gates) env (left.bits i)
      (((left.check_iff next).mp leftCheck).2 i)
  have rightValue : wordValue right.bits (run (WordCode.append left right).gates env) =
      right.value (run left.gates env) := by rw [WordCode.append, run_append]; rfl
  rw [WordCode.composeSub, WordCode.append_value, WordCode.sub_value _ _ _ leftBounds rightBounds,
    leftValue, rightValue]

theorem WordCode.sub_target {width : Nat} (left right : Fin width → Nat) (next : Nat)
    (leftBound : ∀ i, left i < next) (rightBound : ∀ i, right i < next) (env : Assignment)
    (leftTerm rightTerm : TrustIrExpr.SMTTerm (.bv width)) (target : SMTEnv)
    (leftValue : wordValue left env = leftTerm.eval target)
    (rightValue : wordValue right env = rightTerm.eval target) :
    (WordCode.sub left right next).value env =
      (TrustIrExpr.SMTTerm.binary (.bvSub width) leftTerm rightTerm).eval target := by
  rw [WordCode.sub_value left right next leftBound rightBound env, leftValue, rightValue]
  rfl

theorem WordCode.neg_target {width : Nat} (input : Fin width → Nat) (next : Nat)
    (bound : ∀ i, input i < next) (env : Assignment)
    (term : TrustIrExpr.SMTTerm (.bv width)) (target : SMTEnv)
    (same : wordValue input env = term.eval target) :
    (WordCode.neg input next).value env = (TrustIrExpr.SMTTerm.unary (.bvNeg width) term).eval target := by
  rw [WordCode.neg_value input next bound env, same]
  rfl

theorem WordCode.composeSub_target {width : Nat} (next : Nat) (left right : WordCode width)
    (leftCheck : left.check next = true)
    (rightCheck : right.check (next + left.gates.length) = true) (env : Assignment)
    (leftTerm rightTerm : TrustIrExpr.SMTTerm (.bv width)) (target : SMTEnv)
    (leftValue : left.value env = leftTerm.eval target)
    (rightValue : right.value (run left.gates env) = rightTerm.eval target) :
    (WordCode.composeSub next left right).value env =
      (TrustIrExpr.SMTTerm.binary (.bvSub width) leftTerm rightTerm).eval target := by
  rw [WordCode.composeSub_value next left right leftCheck rightCheck env, leftValue, rightValue]
  rfl

theorem WordCode.composeNeg_target {width : Nat} (next : Nat) (child : WordCode width)
    (checked : child.check next = true) (env : Assignment)
    (term : TrustIrExpr.SMTTerm (.bv width)) (target : SMTEnv)
    (same : child.value env = term.eval target) :
    (WordCode.composeNeg next child).value env =
      (TrustIrExpr.SMTTerm.unary (.bvNeg width) term).eval target := by
  rw [WordCode.composeNeg_value next child checked env, same]
  rfl

/-- An asserted result bit has a CNF model exactly when the actual decoded
word has that bit set. Both directions construct or identify gate execution. -/
theorem WordCode.asserted_bit_iff {width : Nat} (code : WordCode width) (next : Nat)
    (checked : code.check next = true) (env : Assignment) (i : Fin width) :
    (∃ model : Assignment, (∀ id, id < next → model id = env id) ∧
      CNF.eval model (assertOutput code.gates (code.bits i)) = true) ↔
        (trustIrWordBit (code.value env)) i.val = true := by
  obtain ⟨valid, bounds⟩ := (code.check_iff next).mp checked
  simpa only [WordCode.value, wordValue_bit] using valid.asserted_iff env (code.bits i) (bounds i)

end TrustIr.AYGateCNF

#trustIrAxiomsExact TrustIr.AYGateCNF.word_not_add_one == [propext, Quot.sound, Classical.choice]

#trustIrAxiomsExact TrustIr.AYGateCNF.WordCode.sub_check == [propext, Classical.choice, Quot.sound]

#trustIrAxiomsExact TrustIr.AYGateCNF.WordCode.sub_value == [propext, Classical.choice, Quot.sound]

#trustIrAxiomsExact TrustIr.AYGateCNF.WordCode.sub_target == [propext, Classical.choice, Quot.sound]

#trustIrAxiomsExact TrustIr.AYGateCNF.WordCode.neg_check == [propext, Classical.choice, Quot.sound]

#trustIrAxiomsExact TrustIr.AYGateCNF.WordCode.neg_value == [propext, Classical.choice, Quot.sound]

#trustIrAxiomsExact TrustIr.AYGateCNF.WordCode.neg_target == [propext, Classical.choice, Quot.sound]

#trustIrAxiomsExact TrustIr.AYGateCNF.WordCode.composeSub_check == [propext, Classical.choice, Quot.sound]

#trustIrAxiomsExact TrustIr.AYGateCNF.WordCode.composeSub_value == [propext, Classical.choice, Quot.sound]

#trustIrAxiomsExact TrustIr.AYGateCNF.WordCode.composeSub_target == [propext, Classical.choice, Quot.sound]

#trustIrAxiomsExact TrustIr.AYGateCNF.WordCode.composeNeg_check == [propext, Classical.choice, Quot.sound]

#trustIrAxiomsExact TrustIr.AYGateCNF.WordCode.composeNeg_value == [propext, Classical.choice, Quot.sound]

#trustIrAxiomsExact TrustIr.AYGateCNF.WordCode.composeNeg_target == [propext, Classical.choice, Quot.sound]

#trustIrAxiomsExact TrustIr.AYGateCNF.WordCode.asserted_bit_iff == [propext, Classical.choice, Quot.sound]
