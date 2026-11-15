-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0
import TrustIr.Proofs.AYWordWires

namespace TrustIr.AYGateCNF
open TrustIrExpr

/-- Constant-distance logical shift stages. Both directions share one fresh
zero wire, including distances at least the width. No shift-distance masking. -/
inductive ShiftDirection where
  | left | right
  deriving Repr, DecidableEq

def ShiftDirection.source (direction : ShiftDirection) (distance index width : Nat) : Option (Fin width) :=
  match direction with
  | .left => if h : distance ≤ index ∧ index - distance < width then some ⟨index - distance, h.2⟩ else none
  | .right => if h : distance + index < width then some ⟨distance + index, h⟩ else none

def ShiftDirection.eval {width : Nat} (direction : ShiftDirection) (distance : Nat) (word : BitVec width) :
    BitVec width :=
  match direction with
  | .left => word <<< distance
  | .right => word >>> distance

def WordCode.shiftStage {width : Nat} (direction : ShiftDirection) (distance : Nat)
    (input : Fin width → Nat) (next : Nat) : WordCode width :=
  ⟨[.constFalse next], fun i => match direction.source distance i.val width with
    | some source => input source
    | none => next⟩

theorem WordCode.shiftStage_length {width : Nat} (direction : ShiftDirection) (distance : Nat)
    (input : Fin width → Nat) (next : Nat) :
    (WordCode.shiftStage direction distance input next).gates.length = 1 := rfl

theorem WordCode.shiftStage_check {width : Nat} (direction : ShiftDirection) (distance : Nat)
    (input : Fin width → Nat) (next : Nat) (bound : ∀ i, input i < next) :
    (WordCode.shiftStage direction distance input next).check next = true := by
  apply (WordCode.check_iff _ _).mpr
  refine ⟨Valid.cons rfl (by simp [Gate.inputs]) (.nil _), ?_⟩
  intro i
  change (match direction.source distance i.val width with
    | some source => input source | none => next) < next + 1
  split
  · rename_i source _
    have before := bound source; omega
  · omega

theorem WordCode.shiftStage_value {width : Nat} (direction : ShiftDirection) (distance : Nat)
    (input : Fin width → Nat) (next : Nat) (bound : ∀ i, input i < next) (env : Assignment) :
    (WordCode.shiftStage direction distance input next).value env = direction.eval distance (wordValue input env) := by
  trustIrCompilerProof {
    have valid := ((WordCode.check_iff _ _).mp (WordCode.shiftStage_check direction distance input next bound)).1
    have frame : ∀ i, run [.constFalse next] env (input i) = env (input i) :=
      fun i => (valid.run_correct env).1 _ (bound i)
    have zero : run [.constFalse next] env next = false := by simp [run, Gate.apply, Gate.eval, Gate.output]
    apply BitVec.eq_of_getLsb_eq
    intro i
    change (wordValue _ (run [.constFalse next] env)).getLsb i.val = _
    rw [wordValue_bit]
    cases direction with
    | left =>
      simp only [WordCode.shiftStage, ShiftDirection.source, ShiftDirection.eval, BitVec.getLsb_shiftLeft]
      by_cases h : distance ≤ i.val
      · have small : i.val - distance < width := by omega
        simp only [show (distance ≤ i.val ∧ i.val - distance < width) from ⟨h, small⟩,
          dite_true, frame, i.isLt, decide_True, show ¬ i.val < distance by omega,
          decide_False, Bool.not_false, Bool.true_and]
        exact (wordValue_bit input env ⟨i.val - distance, small⟩).symm
      · simp [h, zero, show ¬ (distance ≤ i.val ∧ i.val - distance < width) by omega,
          show i.val < distance by omega]
    | right =>
      simp only [WordCode.shiftStage, ShiftDirection.source, ShiftDirection.eval, BitVec.getLsb_ushiftRight]
      by_cases h : distance + i.val < width
      · simp only [dif_pos h, frame]
        exact (wordValue_bit input env ⟨distance + i.val, h⟩).symm
      · simp [h, zero, BitVec.getLsb_ge, show width ≤ distance + i.val by omega]
  } {
    have valid := ((WordCode.check_iff _ _).mp (WordCode.shiftStage_check direction distance input next bound)).1
    have frame : ∀ i, run [.constFalse next] env (input i) = env (input i) :=
      fun i => (valid.run_correct env).1 _ (bound i)
    have zero : run [.constFalse next] env next = false := by simp [run, Gate.apply, Gate.eval, Gate.output]
    apply trustIrWordExt
    intro i
    change (wordValue _ (run [.constFalse next] env)).getLsbD i.val = _
    rw [wordValue_bit]
    cases direction with
    | left =>
      simp only [WordCode.shiftStage, ShiftDirection.source, ShiftDirection.eval, BitVec.getLsbD_shiftLeft]
      by_cases h : distance ≤ i.val
      · have small : i.val - distance < width := by omega
        simp only [dif_pos (show distance ≤ i.val ∧ i.val - distance < width from ⟨h, small⟩), frame]
        simpa [i.isLt, show ¬ i.val < distance by omega] using
          (wordValue_bit input env ⟨i.val - distance, small⟩).symm
      · simp [h, zero, show ¬ (distance ≤ i.val ∧ i.val - distance < width) by omega,
          show i.val < distance by omega]
    | right =>
      simp only [WordCode.shiftStage, ShiftDirection.source, ShiftDirection.eval, BitVec.getLsbD_ushiftRight]
      by_cases h : distance + i.val < width
      · simp only [dif_pos h, frame]
        exact (wordValue_bit input env ⟨distance + i.val, h⟩).symm
      · simp [h, zero, BitVec.getLsbD_of_ge, show width ≤ distance + i.val by omega]
  }

def ShiftDirection.target (direction : ShiftDirection) (width : Nat) : SMTBinary (.bv width) (.bv width) :=
  match direction with
  | .left => .bvShl width
  | .right => .bvLShr width

theorem ShiftDirection.target_eval {width : Nat} (direction : ShiftDirection) (word amount : BitVec width) :
    (direction.target width).eval word amount = direction.eval amount.toNat word := by
  trustIrCompilerProof {
    cases direction with
    | right => rfl
    | left =>
      change (if amount.toNat < width then word <<< amount else 0) = word <<< amount.toNat
      split
      · rfl
      · rename_i outside
        apply BitVec.eq_of_getLsb_eq
        intro i
        simp [BitVec.getLsb_shiftLeft, show i.val < amount.toNat by omega]
  } {
    cases direction with
    | right => rfl
    | left =>
      change (if amount.toNat < width then word <<< amount else 0) = word <<< amount.toNat
      split
      · rfl
      · rename_i outside
        apply trustIrWordExt
        intro i
        simp [BitVec.getLsbD_shiftLeft, show i.val < amount.toNat by omega]
  }

theorem WordCode.shiftStage_target {width : Nat} (direction : ShiftDirection) (distance : Nat)
    (input : Fin width → Nat) (next : Nat) (bound : ∀ i, input i < next) (env : Assignment)
    (word amount : SMTTerm (.bv width)) (target : SMTEnv)
    (inputValue : wordValue input env = word.eval target)
    (amountValue : distance = (amount.eval target).toNat) :
    (WordCode.shiftStage direction distance input next).value env =
      (SMTTerm.binary (direction.target width) word amount).eval target := by
  rw [WordCode.shiftStage_value direction distance input next bound env, inputValue, amountValue]
  exact (direction.target_eval _ _).symm

/-- Preserve a checked child's actual graph and result vector before routing. -/
def WordCode.composeShiftStage {width : Nat} (direction : ShiftDirection) (distance next : Nat)
    (child : WordCode width) : WordCode width :=
  WordCode.append child (WordCode.shiftStage direction distance child.bits (next + child.gates.length))

theorem WordCode.composeShiftStage_check {width : Nat} (direction : ShiftDirection) (distance next : Nat)
    (child : WordCode width) (checked : child.check next = true) :
    (WordCode.composeShiftStage direction distance next child).check next = true := by
  apply WordCode.append_check _ _ _ checked
  exact WordCode.shiftStage_check _ _ _ _ ((child.check_iff next).mp checked).2

theorem WordCode.composeShiftStage_value {width : Nat} (direction : ShiftDirection) (distance next : Nat)
    (child : WordCode width) (checked : child.check next = true) (env : Assignment) :
    (WordCode.composeShiftStage direction distance next child).value env = direction.eval distance (child.value env) := by
  rw [WordCode.composeShiftStage, WordCode.append_value,
    WordCode.shiftStage_value _ _ _ _ ((child.check_iff next).mp checked).2]
  rfl

theorem WordCode.composeShiftStage_target {width : Nat} (direction : ShiftDirection) (distance next : Nat)
    (child : WordCode width) (checked : child.check next = true) (env : Assignment)
    (word amount : SMTTerm (.bv width)) (target : SMTEnv)
    (inputValue : child.value env = word.eval target)
    (amountValue : distance = (amount.eval target).toNat) :
    (WordCode.composeShiftStage direction distance next child).value env =
      (SMTTerm.binary (direction.target width) word amount).eval target := by
  rw [WordCode.composeShiftStage_value _ _ _ _ checked, inputValue, amountValue]
  exact (direction.target_eval _ _).symm

end TrustIr.AYGateCNF

#trustIrAxiomsExact TrustIr.AYGateCNF.WordCode.shiftStage_length == []

#trustIrAxiomsExact TrustIr.AYGateCNF.WordCode.shiftStage_check == [propext, Quot.sound, Classical.choice]

#trustIrAxiomsExact TrustIr.AYGateCNF.WordCode.shiftStage_value == [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AYGateCNF.ShiftDirection.target_eval == [propext, Quot.sound, Classical.choice] modern [propext, Quot.sound]

#trustIrAxiomsExact TrustIr.AYGateCNF.WordCode.shiftStage_target == [propext, Classical.choice, Quot.sound]

#trustIrAxiomsExact TrustIr.AYGateCNF.WordCode.composeShiftStage_check == [propext, Quot.sound, Classical.choice]

#trustIrAxiomsExact TrustIr.AYGateCNF.WordCode.composeShiftStage_value == [propext, Classical.choice, Quot.sound]

#trustIrAxiomsExact TrustIr.AYGateCNF.WordCode.composeShiftStage_target == [propext, Classical.choice, Quot.sound]
