-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0
import TrustIr.Proofs.AYWordSub

namespace TrustIr.AYGateCNF

/-- Native modular Horner arithmetic for one recorded multiplier bit. -/
theorem word_mul_horner {width : Nat} (x : BitVec width) (rest : Nat) (bit : Bool) :
    x * BitVec.ofNat width rest + x * BitVec.ofNat width rest +
      (if bit then x else BitVec.ofNat width 0) =
    x * BitVec.ofNat width (bit.toNat + 2 * rest) := by
  apply BitVec.eq_of_toNat_eq
  cases bit <;> simp [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat,
    Nat.add_mod, Nat.mul_mod, Nat.mod_mod, Nat.mul_add, Nat.mul_two, Nat.two_mul, Nat.add_assoc]
  all_goals simp only [Nat.mod_mod]
  all_goals simp only [← Nat.mul_mod, ← Nat.add_mod]
  all_goals (congr 1 <;> simp only [Nat.mul_add, Nat.mul_one] <;> omega)

/-- Doubling is wire movement with one allocated zero, not another adder. -/
def WordCode.shiftOne {width : Nat} (input : Fin width → Nat) (next : Nat) : WordCode width :=
  ⟨[.constFalse next], fun i => if i.val = 0 then next else input ⟨i.val - 1, by omega⟩⟩

theorem WordCode.shiftOne_check {width : Nat} (input : Fin width → Nat) (next : Nat)
    (bound : ∀ i, input i < next) : (WordCode.shiftOne input next).check next = true := by
  apply (WordCode.check_iff _ _).mpr
  constructor
  · exact Valid.cons rfl (by simp [Gate.inputs]) (.nil _)
  · intro i
    change (if i.val = 0 then next else input ⟨i.val - 1, by omega⟩) < next + 1
    split
    · omega
    · have before := bound ⟨i.val - 1, by omega⟩; omega

theorem WordCode.shiftOne_value {width : Nat} (input : Fin width → Nat) (next : Nat)
    (bound : ∀ i, input i < next) (env : Assignment) :
    (WordCode.shiftOne input next).value env = wordValue input env + wordValue input env := by
  have doubled : (wordValue input env <<< 1) = wordValue input env + wordValue input env := by
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.mul_two]
  rw [← doubled]
  apply trustIrWordExt
  intro i
  change (trustIrWordBit (wordValue (WordCode.shiftOne input next).bits (run [.constFalse next] env))) i.val = _
  rw [wordValue_bit]
  trustIrCompilerProof { rw [BitVec.getLsb_shiftLeft] } { rw [BitVec.getLsbD_shiftLeft] }
  by_cases zero : i.val = 0
  · simp [WordCode.shiftOne, zero, run, Gate.apply, Gate.output, Gate.eval]
  · have predBound : i.val - 1 < width := by omega
    have before := bound ⟨i.val - 1, predBound⟩
    have notFresh : input ⟨i.val - 1, predBound⟩ ≠ next := Nat.ne_of_lt before
    simp [WordCode.shiftOne, zero, i.isLt, show ¬ i.val < 1 by omega, run, Gate.apply,
      Gate.output, wordValue_bit, notFresh]
    exact (wordValue_bit input env ⟨i.val - 1, predBound⟩).symm

/-- Share an accumulated word, double it by rewiring, AND a partial row, then add.
All operands predate the row; no already allocated child program is duplicated. -/
def WordCode.mulStep {width : Nat} (left : Fin width → Nat) (bit : Nat)
    (acc : Fin width → Nat) (next : Nat) : WordCode width :=
  let doubled := WordCode.shiftOne acc next
  WordCode.composeAdd next doubled
    (WordCode.bitwise .band left (fun _ => bit) (next + doubled.gates.length))

theorem WordCode.mulStep_check {width : Nat} (left : Fin width → Nat) (bit : Nat)
    (acc : Fin width → Nat) (next : Nat) (leftBound : ∀ i, left i < next)
    (bitBound : bit < next) (accBound : ∀ i, acc i < next) :
    (WordCode.mulStep left bit acc next).check next = true := by
  apply WordCode.composeAdd_check _ _ _ (WordCode.shiftOne_check acc next accBound)
  apply WordCode.bitwise_check
  · intro i; have before := leftBound i; omega
  · intro _i; omega

theorem WordCode.mulStep_value {width : Nat} (left : Fin width → Nat) (bit : Nat)
    (acc : Fin width → Nat) (next : Nat) (leftBound : ∀ i, left i < next)
    (bitBound : bit < next) (accBound : ∀ i, acc i < next) (env : Assignment) :
    (WordCode.mulStep left bit acc next).value env =
      wordValue acc env + wordValue acc env +
        (if env bit then wordValue left env else BitVec.ofNat width 0) := by
  have checked := WordCode.shiftOne_check acc next accBound
  have valid := ((WordCode.check_iff _ _).mp checked).1
  have leftLater : ∀ i, left i < next + (WordCode.shiftOne acc next).gates.length := by
    intro i; have before := leftBound i; omega
  have bitLater : bit < next + (WordCode.shiftOne acc next).gates.length := by omega
  have masked := WordCode.bitwise_check .band left (fun _ => bit) _ leftLater (fun _ => bitLater)
  have leftSame : wordValue left (run (WordCode.shiftOne acc next).gates env) = wordValue left env := by
    apply wordValue_congr
    intro i
    exact (valid.run_correct env).1 (left i) (leftBound i)
  have bitSame := (valid.run_correct env).1 bit bitBound
  rw [WordCode.mulStep, WordCode.composeAdd_value _ _ _ checked masked,
    WordCode.shiftOne_value _ _ accBound, WordCode.mask_value _ _ _ leftLater bitLater,
    leftSame, bitSame]

/-- Core list folding keeps this builder total without new partial workers.
Higher multiplier bits are emitted first; each lower bit shares their result. -/
def WordCode.mulRows {width : Nat} (left : Fin width → Nat) (right : List Nat) (next : Nat) : WordCode width :=
  right.foldr (fun bit rest next =>
    let prior := rest next
    WordCode.append prior (WordCode.mulStep left bit prior.bits (next + prior.gates.length)))
    (fun next => WordCode.constant (BitVec.ofNat width 0) next) next

theorem WordCode.mulRows_check {width : Nat} (left : Fin width → Nat) (right : List Nat) (next : Nat)
    (leftBound : ∀ i, left i < next) (rightBound : ∀ bit ∈ right, bit < next) :
    (WordCode.mulRows left right next).check next = true := by
  induction right generalizing next with
  | nil => exact WordCode.constant_check _ _
  | cons bit rest ih =>
    have checked := ih next leftBound (fun id member => rightBound id (List.Mem.tail _ member))
    have bitBefore := rightBound bit (List.Mem.head _)
    have leftLater : ∀ i, left i < next + (WordCode.mulRows left rest next).gates.length := by
      intro i; have before := leftBound i; omega
    have bitLater : bit < next + (WordCode.mulRows left rest next).gates.length := by omega
    exact WordCode.append_check _ _ next checked
      (WordCode.mulStep_check left bit (WordCode.mulRows left rest next).bits _ leftLater bitLater
        ((WordCode.check_iff _ _).mp checked).2)

theorem WordCode.mulRows_value {width : Nat} (left : Fin width → Nat) (right : List Nat) (next : Nat)
    (leftBound : ∀ i, left i < next) (rightBound : ∀ bit ∈ right, bit < next) (env : Assignment) :
    (WordCode.mulRows left right next).value env = wordValue left env * BitVec.ofNat width (wireNumber right env) := by
  induction right generalizing next env with
  | nil =>
    rw [show WordCode.mulRows left [] next = WordCode.constant (BitVec.ofNat width 0) next from rfl,
      WordCode.constant_value]
    apply BitVec.eq_of_toNat_eq
    simp [wireNumber]
  | cons bit rest ih =>
    have restBound := fun id member => rightBound id (List.Mem.tail bit member)
    have checked := WordCode.mulRows_check left rest next leftBound restBound
    obtain ⟨valid, bounds⟩ := (WordCode.check_iff _ _).mp checked
    have bitBefore := rightBound bit (List.Mem.head _)
    have leftLater : ∀ i, left i < next + (WordCode.mulRows left rest next).gates.length := by
      intro i; have before := leftBound i; omega
    have bitLater : bit < next + (WordCode.mulRows left rest next).gates.length := by omega
    have leftSame : wordValue left (run (WordCode.mulRows left rest next).gates env) = wordValue left env := by
      apply wordValue_congr
      intro i
      exact (valid.run_correct env).1 (left i) (leftBound i)
    have bitSame := (valid.run_correct env).1 bit bitBefore
    change (WordCode.append (WordCode.mulRows left rest next)
      (WordCode.mulStep left bit (WordCode.mulRows left rest next).bits
        (next + (WordCode.mulRows left rest next).gates.length))).value env = _
    rw [WordCode.append_value, WordCode.mulStep_value _ _ _ _ leftLater bitLater bounds,
      leftSame, bitSame]
    change (WordCode.mulRows left rest next).value env + (WordCode.mulRows left rest next).value env + _ = _
    rw [ih next leftBound restBound env]
    exact word_mul_horner _ _ _

/-- Full-width multiplication reads the recorded little-endian right wires. -/
def WordCode.mul {width : Nat} (left right : Fin width → Nat) (next : Nat) : WordCode width :=
  WordCode.mulRows left (tabulate right) next

theorem WordCode.mul_check {width : Nat} (left right : Fin width → Nat) (next : Nat)
    (leftBound : ∀ i, left i < next) (rightBound : ∀ i, right i < next) :
    (WordCode.mul left right next).check next = true := by
  apply WordCode.mulRows_check _ _ _ leftBound
  intro bit member
  obtain ⟨i, same⟩ := tabulate_cases right bit member
  rw [← same]
  exact rightBound i

theorem WordCode.mul_value {width : Nat} (left right : Fin width → Nat) (next : Nat)
    (leftBound : ∀ i, left i < next) (rightBound : ∀ i, right i < next) (env : Assignment) :
    (WordCode.mul left right next).value env = wordValue left env * wordValue right env := by
  have bounds : ∀ bit ∈ tabulate right, bit < next := by
    intro bit member
    obtain ⟨i, same⟩ := tabulate_cases right bit member
    rw [← same]
    exact rightBound i
  rw [WordCode.mul, WordCode.mulRows_value _ _ _ leftBound bounds, ← wordValue_toNat]
  congr 1
  apply BitVec.eq_of_toNat_eq
  simp [Nat.mod_eq_of_lt (wordValue right env).isLt]

def WordCode.composeMul {width : Nat} (next : Nat) (left right : WordCode width) : WordCode width :=
  let both := WordCode.append left right
  WordCode.append both (WordCode.mul left.bits right.bits (next + both.gates.length))

theorem WordCode.composeMul_check {width : Nat} (next : Nat) (left right : WordCode width)
    (leftCheck : left.check next = true)
    (rightCheck : right.check (next + left.gates.length) = true) :
    (WordCode.composeMul next left right).check next = true := by
  obtain ⟨leftBounds, rightBounds⟩ := WordCode.append_operand_bounds next left right leftCheck rightCheck
  apply WordCode.append_check _ _ next (WordCode.append_check left right next leftCheck rightCheck)
  exact WordCode.mul_check _ _ _ leftBounds rightBounds

theorem WordCode.composeMul_value {width : Nat} (next : Nat) (left right : WordCode width)
    (leftCheck : left.check next = true)
    (rightCheck : right.check (next + left.gates.length) = true) (env : Assignment) :
    (WordCode.composeMul next left right).value env = left.value env * right.value (run left.gates env) := by
  obtain ⟨leftBounds, rightBounds⟩ := WordCode.append_operand_bounds next left right leftCheck rightCheck
  have rightValid := ((right.check_iff _).mp rightCheck).1
  have leftValue : wordValue left.bits (run (WordCode.append left right).gates env) = left.value env := by
    apply wordValue_congr
    intro i
    exact rightValid.append_preserves (next := next) (first := left.gates) env (left.bits i)
      (((left.check_iff next).mp leftCheck).2 i)
  have rightValue : wordValue right.bits (run (WordCode.append left right).gates env) =
      right.value (run left.gates env) := by rw [WordCode.append, run_append]; rfl
  rw [WordCode.composeMul, WordCode.append_value, WordCode.mul_value _ _ _ leftBounds rightBounds,
    leftValue, rightValue]

theorem WordCode.mul_target {width : Nat} (left right : Fin width → Nat) (next : Nat)
    (leftBound : ∀ i, left i < next) (rightBound : ∀ i, right i < next) (env : Assignment)
    (leftTerm rightTerm : TrustIrExpr.SMTTerm (.bv width)) (target : SMTEnv)
    (leftValue : wordValue left env = leftTerm.eval target)
    (rightValue : wordValue right env = rightTerm.eval target) :
    (WordCode.mul left right next).value env =
      (TrustIrExpr.SMTTerm.binary (.bvMul width) leftTerm rightTerm).eval target := by
  rw [WordCode.mul_value left right next leftBound rightBound env, leftValue, rightValue]
  rfl

theorem WordCode.composeMul_target {width : Nat} (next : Nat) (left right : WordCode width)
    (leftCheck : left.check next = true)
    (rightCheck : right.check (next + left.gates.length) = true) (env : Assignment)
    (leftTerm rightTerm : TrustIrExpr.SMTTerm (.bv width)) (target : SMTEnv)
    (leftValue : left.value env = leftTerm.eval target)
    (rightValue : right.value (run left.gates env) = rightTerm.eval target) :
    (WordCode.composeMul next left right).value env =
      (TrustIrExpr.SMTTerm.binary (.bvMul width) leftTerm rightTerm).eval target := by
  rw [WordCode.composeMul_value next left right leftCheck rightCheck env, leftValue, rightValue]
  rfl

end TrustIr.AYGateCNF

#trustIrAxiomsPinned TrustIr.AYGateCNF.word_mul_horner == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsExact TrustIr.AYGateCNF.WordCode.shiftOne_check == [propext, Classical.choice, Quot.sound]

#trustIrAxiomsExact TrustIr.AYGateCNF.WordCode.shiftOne_value == [propext, Classical.choice, Quot.sound]

#trustIrAxiomsExact TrustIr.AYGateCNF.WordCode.mulStep_check == [propext, Classical.choice, Quot.sound]

#trustIrAxiomsExact TrustIr.AYGateCNF.WordCode.mulStep_value == [propext, Classical.choice, Quot.sound]



#trustIrAxiomsExact TrustIr.AYGateCNF.WordCode.mulRows_check == [propext, Classical.choice, Quot.sound]

#trustIrAxiomsExact TrustIr.AYGateCNF.WordCode.mulRows_value == [propext, Classical.choice, Quot.sound]

#trustIrAxiomsExact TrustIr.AYGateCNF.WordCode.mul_check == [propext, Classical.choice, Quot.sound]

#trustIrAxiomsExact TrustIr.AYGateCNF.WordCode.mul_value == [propext, Classical.choice, Quot.sound]

#trustIrAxiomsExact TrustIr.AYGateCNF.WordCode.composeMul_check == [propext, Classical.choice, Quot.sound]

#trustIrAxiomsExact TrustIr.AYGateCNF.WordCode.composeMul_value == [propext, Classical.choice, Quot.sound]

#trustIrAxiomsExact TrustIr.AYGateCNF.WordCode.mul_target == [propext, Classical.choice, Quot.sound]

#trustIrAxiomsExact TrustIr.AYGateCNF.WordCode.composeMul_target == [propext, Classical.choice, Quot.sound]
