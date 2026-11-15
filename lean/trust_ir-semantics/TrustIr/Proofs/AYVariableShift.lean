-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0
import TrustIr.Proofs.AYWordShift
import TrustIr.Proofs.AYWordIte

namespace TrustIr.AYGateCNF
open TrustIrExpr

theorem ShiftDirection.eval_zero {width : Nat} (direction : ShiftDirection) (word : BitVec width) :
    direction.eval 0 word = word := by
  cases direction <;> apply trustIrWordExt <;> intro i <;>
    simp [ShiftDirection.eval, i.isLt]

theorem ShiftDirection.eval_add {width : Nat} (direction : ShiftDirection) (a b : Nat) (word : BitVec width) :
    direction.eval b (direction.eval a word) = direction.eval (a + b) word := by
  cases direction with
  | right =>
    apply trustIrWordExt
    intro i
    simp [ShiftDirection.eval, Nat.add_assoc]
  | left =>
    apply trustIrWordExt
    intro i
    trustIrCompilerProof {
      simp only [ShiftDirection.eval, BitVec.getLsb_shiftLeft]
    } {
      simp only [ShiftDirection.eval, BitVec.getLsbD_shiftLeft]
    }
    by_cases small : i.val < b
    · simp [small, show i.val < a + b by omega]
    · by_cases smaller : i.val - b < a
      · simp [small, smaller, show i.val < a + b by omega]
      · simp [small, smaller, i.isLt, show i.val - b < width by omega,
          show ¬ i.val < a + b by omega, show i.val - b - a = i.val - (a + b) by omega]

/-- One amount bit selects between the actual routed stage and unchanged wires. -/
def WordCode.shiftStep {width : Nat} (direction : ShiftDirection) (distance bit : Nat)
    (input : Fin width → Nat) (next : Nat) : WordCode width :=
  let shifted := WordCode.shiftStage direction distance input next
  WordCode.append shifted (WordCode.ite bit shifted.bits input (next + shifted.gates.length))

theorem WordCode.shiftStep_check {width : Nat} (direction : ShiftDirection) (distance bit : Nat)
    (input : Fin width → Nat) (next : Nat) (bound : ∀ i, input i < next) (bitBound : bit < next) :
    (WordCode.shiftStep direction distance bit input next).check next = true := by
  have checked := WordCode.shiftStage_check direction distance input next bound
  apply WordCode.append_check _ _ _ checked
  apply WordCode.ite_check
  · omega
  · exact ((WordCode.check_iff _ _).mp checked).2
  · intro i; have before := bound i; omega

theorem WordCode.shiftStep_value {width : Nat} (direction : ShiftDirection) (distance bit : Nat)
    (input : Fin width → Nat) (next : Nat) (bound : ∀ i, input i < next) (bitBound : bit < next)
    (env : Assignment) :
    (WordCode.shiftStep direction distance bit input next).value env =
      direction.eval (if env bit then distance else 0) (wordValue input env) := by
  have checked := WordCode.shiftStage_check direction distance input next bound
  obtain ⟨valid, bounds⟩ := (WordCode.check_iff _ _).mp checked
  have bitLater : bit < next + (WordCode.shiftStage direction distance input next).gates.length := by omega
  have inputLater : ∀ i, input i < next + (WordCode.shiftStage direction distance input next).gates.length := by
    intro i; have before := bound i; omega
  have same : wordValue input (run (WordCode.shiftStage direction distance input next).gates env) = wordValue input env := by
    apply wordValue_congr
    intro i
    exact (valid.run_correct env).1 _ (bound i)
  rw [WordCode.shiftStep, WordCode.append_value,
    WordCode.ite_value _ _ _ _ bitLater bounds inputLater, same, (valid.run_correct env).1 bit bitBound]
  change (if env bit then (WordCode.shiftStage direction distance input next).value env else _) = _
  rw [WordCode.shiftStage_value _ _ _ _ bound]
  cases env bit <;> simp [ShiftDirection.eval_zero]

/-- All amount bits participate, including high bits which force a zero result.
The total core fold emits high amount bits first and shares every prior word. -/
def WordCode.shiftRows {width : Nat} (direction : ShiftDirection) (amount : List Nat)
    (distance : Nat) (input : Fin width → Nat) (next : Nat) : WordCode width :=
  amount.foldr (fun bit rest distance next =>
    let prior := rest (2 * distance) next
    WordCode.append prior (WordCode.shiftStep direction distance bit prior.bits (next + prior.gates.length)))
    (fun _ _ => ⟨[], input⟩) distance next

theorem WordCode.shiftRows_check {width : Nat} (direction : ShiftDirection) (amount : List Nat)
    (distance : Nat) (input : Fin width → Nat) (next : Nat)
    (bound : ∀ i, input i < next) (amountBound : ∀ bit ∈ amount, bit < next) :
    (WordCode.shiftRows direction amount distance input next).check next = true := by
  induction amount generalizing distance next with
  | nil => exact (WordCode.check_iff _ _).mpr ⟨.nil next, by simpa using bound⟩
  | cons bit rest ih =>
    have checked := ih (2 * distance) next bound (fun id member => amountBound id (List.Mem.tail _ member))
    have bitBefore := amountBound bit (List.Mem.head _)
    apply WordCode.append_check _ _ _ checked
    apply WordCode.shiftStep_check _ _ _ _ _ ((WordCode.check_iff _ _).mp checked).2
    omega

theorem WordCode.shiftRows_value {width : Nat} (direction : ShiftDirection) (amount : List Nat)
    (distance : Nat) (input : Fin width → Nat) (next : Nat)
    (bound : ∀ i, input i < next) (amountBound : ∀ bit ∈ amount, bit < next) (env : Assignment) :
    (WordCode.shiftRows direction amount distance input next).value env =
      direction.eval (distance * wireNumber amount env) (wordValue input env) := by
  induction amount generalizing distance next env with
  | nil =>
    change wordValue input env = direction.eval (distance * 0) (wordValue input env)
    simp [ShiftDirection.eval_zero]
  | cons bit rest ih =>
    have restBound := fun id member => amountBound id (List.Mem.tail bit member)
    have checked := WordCode.shiftRows_check direction rest (2 * distance) input next bound restBound
    obtain ⟨valid, bounds⟩ := (WordCode.check_iff _ _).mp checked
    have bitBefore := amountBound bit (List.Mem.head _)
    have bitLater : bit < next + (WordCode.shiftRows direction rest (2 * distance) input next).gates.length := by omega
    have bitSame := (valid.run_correct env).1 bit bitBefore
    change (WordCode.append (WordCode.shiftRows direction rest (2 * distance) input next)
      (WordCode.shiftStep direction distance bit (WordCode.shiftRows direction rest (2 * distance) input next).bits
        (next + (WordCode.shiftRows direction rest (2 * distance) input next).gates.length))).value env = _
    rw [WordCode.append_value, WordCode.shiftStep_value _ _ _ _ _ bounds bitLater, bitSame]
    change direction.eval (if env bit then distance else 0)
      ((WordCode.shiftRows direction rest (2 * distance) input next).value env) = _
    rw [ih (2 * distance) next bound restBound, ShiftDirection.eval_add]
    congr 1
    simp only [wireNumber, List.foldr]
    cases env bit <;> simp [Nat.mul_add, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm, Nat.add_comm]

/-- Full unmasked logical shifts over the actual little-endian amount wires. -/
def WordCode.shift {width : Nat} (direction : ShiftDirection) (input amount : Fin width → Nat)
    (next : Nat) : WordCode width := WordCode.shiftRows direction (tabulate amount) 1 input next

theorem WordCode.shift_check {width : Nat} (direction : ShiftDirection) (input amount : Fin width → Nat)
    (next : Nat) (bound : ∀ i, input i < next) (amountBound : ∀ i, amount i < next) :
    (WordCode.shift direction input amount next).check next = true := by
  apply WordCode.shiftRows_check _ _ _ _ _ bound
  intro bit member
  obtain ⟨i, same⟩ := tabulate_cases amount bit member
  rw [← same]
  exact amountBound i

theorem WordCode.shift_value {width : Nat} (direction : ShiftDirection) (input amount : Fin width → Nat)
    (next : Nat) (bound : ∀ i, input i < next) (amountBound : ∀ i, amount i < next) (env : Assignment) :
    (WordCode.shift direction input amount next).value env =
      direction.eval (wordValue amount env).toNat (wordValue input env) := by
  have bounds : ∀ bit ∈ tabulate amount, bit < next := by
    intro bit member
    obtain ⟨i, same⟩ := tabulate_cases amount bit member
    rw [← same]
    exact amountBound i
  rw [WordCode.shift, WordCode.shiftRows_value _ _ _ _ _ bound bounds, ← wordValue_toNat, Nat.one_mul]

def WordCode.composeShift {width : Nat} (direction : ShiftDirection) (next : Nat) (left right : WordCode width) : WordCode width :=
  let both := WordCode.append left right
  WordCode.append both (WordCode.shift direction left.bits right.bits (next + both.gates.length))

theorem WordCode.composeShift_check {width : Nat} (direction : ShiftDirection) (next : Nat) (left right : WordCode width)
    (leftCheck : left.check next = true)
    (rightCheck : right.check (next + left.gates.length) = true) :
    (WordCode.composeShift direction next left right).check next = true := by
  obtain ⟨leftBounds, rightBounds⟩ := WordCode.append_operand_bounds next left right leftCheck rightCheck
  apply WordCode.append_check _ _ next (WordCode.append_check left right next leftCheck rightCheck)
  exact WordCode.shift_check direction _ _ _ leftBounds rightBounds

theorem WordCode.composeShift_value {width : Nat} (direction : ShiftDirection) (next : Nat) (left right : WordCode width)
    (leftCheck : left.check next = true)
    (rightCheck : right.check (next + left.gates.length) = true) (env : Assignment) :
    (WordCode.composeShift direction next left right).value env = direction.eval (right.value (run left.gates env)).toNat (left.value env) := by
  obtain ⟨leftBounds, rightBounds⟩ := WordCode.append_operand_bounds next left right leftCheck rightCheck
  have rightValid := ((right.check_iff _).mp rightCheck).1
  have leftValue : wordValue left.bits (run (WordCode.append left right).gates env) = left.value env := by
    apply wordValue_congr
    intro i
    exact rightValid.append_preserves (next := next) (first := left.gates) env (left.bits i)
      (((left.check_iff next).mp leftCheck).2 i)
  have rightValue : wordValue right.bits (run (WordCode.append left right).gates env) =
      right.value (run left.gates env) := by rw [WordCode.append, run_append]; rfl
  rw [WordCode.composeShift, WordCode.append_value, WordCode.shift_value direction _ _ _ leftBounds rightBounds,
    leftValue, rightValue]


theorem WordCode.shift_target {width : Nat} (direction : ShiftDirection) (input amount : Fin width → Nat)
    (next : Nat) (bound : ∀ i, input i < next) (amountBound : ∀ i, amount i < next) (env : Assignment)
    (wordTerm amountTerm : SMTTerm (.bv width)) (target : SMTEnv)
    (wordValueEq : wordValue input env = wordTerm.eval target)
    (amountValueEq : wordValue amount env = amountTerm.eval target) :
    (WordCode.shift direction input amount next).value env =
      (SMTTerm.binary (direction.target width) wordTerm amountTerm).eval target := by
  rw [WordCode.shift_value _ _ _ _ bound amountBound, wordValueEq, amountValueEq]
  exact (direction.target_eval _ _).symm

theorem WordCode.composeShift_target {width : Nat} (direction : ShiftDirection) (next : Nat)
    (word amount : WordCode width) (wordCheck : word.check next = true)
    (amountCheck : amount.check (next + word.gates.length) = true) (env : Assignment)
    (wordTerm amountTerm : SMTTerm (.bv width)) (target : SMTEnv)
    (wordValueEq : word.value env = wordTerm.eval target)
    (amountValueEq : amount.value (run word.gates env) = amountTerm.eval target) :
    (WordCode.composeShift direction next word amount).value env =
      (SMTTerm.binary (direction.target width) wordTerm amountTerm).eval target := by
  rw [WordCode.composeShift_value _ _ _ _ wordCheck amountCheck, wordValueEq, amountValueEq]
  exact (direction.target_eval _ _).symm

theorem WordCode.shiftStep_length {width : Nat} (direction : ShiftDirection) (distance bit : Nat)
    (input : Fin width → Nat) (next : Nat) :
    (WordCode.shiftStep direction distance bit input next).gates.length = 3 * width + 2 := by
  simp only [WordCode.shiftStep, WordCode.append, List.length_append, WordCode.shiftStage_length,
    WordCode.ite_length]
  omega

theorem WordCode.shiftRows_length {width : Nat} (direction : ShiftDirection) (amount : List Nat)
    (distance : Nat) (input : Fin width → Nat) (next : Nat) :
    (WordCode.shiftRows direction amount distance input next).gates.length = amount.length * (3 * width + 2) := by
  induction amount generalizing distance next with
  | nil => simp [WordCode.shiftRows]
  | cons bit rest ih =>
    change ((WordCode.shiftRows direction rest (2 * distance) input next).gates ++ _).length = _
    rw [List.length_append, WordCode.shiftStep_length, ih]
    simp [Nat.add_mul, Nat.add_comm]

theorem WordCode.shift_length {width : Nat} (direction : ShiftDirection) (input amount : Fin width → Nat)
    (next : Nat) : (WordCode.shift direction input amount next).gates.length = width * (3 * width + 2) := by
  rw [WordCode.shift, WordCode.shiftRows_length, tabulate_length]

end TrustIr.AYGateCNF

#trustIrAxiomsPinned TrustIr.AYGateCNF.ShiftDirection.eval_zero == [propext, Quot.sound, Classical.choice] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.AYGateCNF.ShiftDirection.eval_add == [propext, Quot.sound, Classical.choice] modern [propext, Quot.sound]

#trustIrAxiomsExact TrustIr.AYGateCNF.WordCode.shiftStep_check == [propext, Quot.sound, Classical.choice]

#trustIrAxiomsExact TrustIr.AYGateCNF.WordCode.shiftStep_value == [propext, Classical.choice, Quot.sound]

#trustIrAxiomsExact TrustIr.AYGateCNF.WordCode.shiftRows_check == [propext, Quot.sound, Classical.choice]

#trustIrAxiomsExact TrustIr.AYGateCNF.WordCode.shiftRows_value == [propext, Classical.choice, Quot.sound]

#trustIrAxiomsExact TrustIr.AYGateCNF.WordCode.shift_check == [propext, Quot.sound, Classical.choice]

#trustIrAxiomsExact TrustIr.AYGateCNF.WordCode.shift_value == [propext, Classical.choice, Quot.sound]

#trustIrAxiomsExact TrustIr.AYGateCNF.WordCode.composeShift_check == [propext, Quot.sound, Classical.choice]

#trustIrAxiomsExact TrustIr.AYGateCNF.WordCode.composeShift_value == [propext, Classical.choice, Quot.sound]

#trustIrAxiomsExact TrustIr.AYGateCNF.WordCode.shift_target == [propext, Classical.choice, Quot.sound]

#trustIrAxiomsExact TrustIr.AYGateCNF.WordCode.composeShift_target == [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AYGateCNF.WordCode.shiftStep_length == [propext, Quot.sound, Classical.choice] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.AYGateCNF.WordCode.shiftRows_length == [propext, Quot.sound, Classical.choice] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.AYGateCNF.WordCode.shift_length == [propext, Quot.sound, Classical.choice] modern [propext, Quot.sound]
