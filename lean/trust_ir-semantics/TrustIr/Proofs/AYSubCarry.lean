-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0
import TrustIr.Proofs.AYWordSub

namespace TrustIr.AYGateCNF

theorem WordCode.castWidth_gates {a b : Nat} (same : a = b) (code : WordCode a) :
    (code.castWidth same).gates = code.gates := by cases same; rfl

/-- The subtraction's actual outgoing carry. It shares every emitted gate
with WordCode.sub: complement right, then one ripple with a true carry. -/
def Code.subNoBorrow {width : Nat} (left right : Fin width → Nat) (next : Nat) : Code :=
  let inverted := WordCode.bitNot right next
  inverted.appendBool (Code.addCarryOut true left inverted.bits (next + inverted.gates.length))

theorem Code.subNoBorrow_gates {width : Nat} (left right : Fin width → Nat) (next : Nat) :
    (Code.subNoBorrow left right next).gates = (WordCode.sub left right next).gates := by
  simp only [Code.subNoBorrow, WordCode.appendBool, Code.addCarryOut, Code.append, Code.constant,
    Adder.carryCode, WordCode.sub, WordCode.append, WordCode.addCarry, WordCode.ripple,
    WordCode.castWidth_gates, Adder.code]
  rfl

theorem Code.subNoBorrow_check {width : Nat} (left right : Fin width → Nat) (next : Nat)
    (leftBound : ∀ i, left i < next) (rightBound : ∀ i, right i < next) :
    (Code.subNoBorrow left right next).check next = true := by
  have inverted := WordCode.bitNot_check right next rightBound
  apply WordCode.appendBool_check _ _ _ inverted
  apply Code.addCarryOut_check
  · intro i; have before := leftBound i; omega
  · exact ((WordCode.check_iff _ _).mp inverted).2

theorem Code.subNoBorrow_numeric {width : Nat} (left right : Fin width → Nat) (next : Nat)
    (leftBound : ∀ i, left i < next) (rightBound : ∀ i, right i < next) (env : Assignment) :
    (wordValue left env).toNat + (2^width - 1 - (wordValue right env).toNat) + 1 =
      ((WordCode.sub left right next).value env).toNat +
        2^width * ((Code.subNoBorrow left right next).eval env).toNat := by
  let inverted := WordCode.bitNot right next
  have checked := WordCode.bitNot_check right next rightBound
  have leftLater : ∀ i, left i < next + inverted.gates.length := by
    intro i; have before := leftBound i; omega
  have numeric := Code.addCarryOut_numeric true left inverted.bits (next + inverted.gates.length)
    leftLater ((WordCode.check_iff _ _).mp checked).2 (run inverted.gates env)
  have leftSame : wordValue left (run inverted.gates env) = wordValue left env := by
    apply wordValue_congr
    intro i
    exact (((WordCode.check_iff _ _).mp checked).1.run_correct env).1 _ (leftBound i)
  have rightValue : wordValue inverted.bits (run inverted.gates env) = ~~~(wordValue right env) :=
    WordCode.bitNot_value right next rightBound env
  have sumValue : (WordCode.addCarry true left inverted.bits (next+inverted.gates.length)).value
      (run inverted.gates env) = (WordCode.sub left right next).value env := by
    rw [WordCode.sub, WordCode.append_value]
  have carryValue : (Code.addCarryOut true left inverted.bits (next+inverted.gates.length)).eval
      (run inverted.gates env) = (Code.subNoBorrow left right next).eval env := by
    rw [Code.subNoBorrow, WordCode.appendBool_eval]
  rw [leftSame, rightValue, sumValue, carryValue] at numeric
  simpa only [BitVec.toNat_not, Bool.toNat_true] using numeric

theorem Code.subNoBorrow_eval {width : Nat} (left right : Fin width → Nat) (next : Nat)
    (leftBound : ∀ i, left i < next) (rightBound : ∀ i, right i < next) (env : Assignment) :
    (Code.subNoBorrow left right next).eval env =
      decide ((wordValue right env).toNat ≤ (wordValue left env).toNat) := by
  have numeric := Code.subNoBorrow_numeric left right next leftBound rightBound env
  have sumBound := ((WordCode.sub left right next).value env).isLt
  have rightSize := (wordValue right env).isLt
  cases carry : (Code.subNoBorrow left right next).eval env with
  | false =>
    rw [carry] at numeric
    simp only [Bool.toNat_false, Nat.mul_zero, Nat.add_zero] at numeric
    have less : (wordValue left env).toNat < (wordValue right env).toNat := by omega
    simp [show ¬ (wordValue right env).toNat ≤ (wordValue left env).toNat by omega]
  | true =>
    rw [carry] at numeric
    simp only [Bool.toNat_true, Nat.mul_one] at numeric
    have enough : (wordValue right env).toNat ≤ (wordValue left env).toNat := by omega
    simp [enough]

theorem buildAdder_carry_position (inputs : List (Nat × Nat)) (carry : Nat) :
    (buildAdder inputs (carry+1) carry).outputCarry = carry + 2*inputs.length := by
  induction inputs generalizing carry with
  | nil => simp [buildAdder, Adder.outputCarry, Adder.nil]
  | cons pair rest ih =>
    change (buildAdder rest (carry+1+2) (carry+1+1)).outputCarry = _
    rw [show carry+1+2 = (carry+1+1)+1 by omega, ih]
    simp only [List.length_cons]
    omega

theorem buildAdder_gate_count (inputs : List (Nat × Nat)) (next carry : Nat) :
    (buildAdder inputs next carry).gates.length = 2*inputs.length := by
  induction inputs generalizing next carry with
  | nil => rfl
  | cons pair rest ih =>
    change ((buildAdder rest (next+2) (next+1)).gates.length + 2) = _
    rw [ih]
    simp [Nat.mul_add]

theorem Code.subNoBorrow_output {width : Nat} (left right : Fin width → Nat) (next : Nat) :
    (Code.subNoBorrow left right next).output = next + 3*width := by
  simp only [Code.subNoBorrow, WordCode.appendBool, Code.addCarryOut, Code.append, Adder.carryCode,
    wordAdder, buildAdder_carry_position, tabulate_length, WordCode.bitNot]
  omega

theorem WordCode.sub_length {width : Nat} (left right : Fin width → Nat) (next : Nat) :
    (WordCode.sub left right next).gates.length = 3*width+1 := by
  rw [← Code.subNoBorrow_gates]
  simp only [Code.subNoBorrow, WordCode.appendBool, Code.addCarryOut, Code.append, Code.constant,
    Adder.carryCode, List.length_append, wordAdder, buildAdder_gate_count, tabulate_length,
    WordCode.bitNot, List.length_cons, List.length_nil, Nat.add_zero]
  omega

end TrustIr.AYGateCNF
