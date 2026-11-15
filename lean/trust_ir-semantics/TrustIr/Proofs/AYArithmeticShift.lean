-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0
import TrustIr.Proofs.AYVariableShift
import TrustIr.Proofs.AYWordSignedValue

namespace TrustIr.AYGateCNF
open TrustIrExpr

theorem word_sshiftRight {width : Nat} (word : BitVec width) (distance : Nat) :
    BitVec.sshiftRight word distance =
      if word.msb then ~~~(~~~word >>> distance) else word >>> distance := by
  cases width with
  | zero => exact Subsingleton.elim _ _
  | succ width =>
    have valid := word.isLt
    by_cases sign : word.msb = true
    · have high := BitVec.toNat_ge_of_msb_true sign
      simp only [Nat.add_sub_cancel] at high
      have negative : ¬ 2 * word.toNat < 2^(width+1) := by omega
      have original : word.toInt = Int.negSucc (2^(width+1) - 1 - word.toNat) := by
        simp only [BitVec.toInt, if_neg negative, Int.negSucc_eq]
        omega
      have small : 2^(width+1) - 1 - word.toNat < 2^(width+1) := by omega
      have shifted : (2^(width+1) - 1 - word.toNat) >>> distance < 2^(width+1) := by
        rw [Nat.shiftRight_eq_div_pow]
        exact Nat.lt_of_le_of_lt (Nat.div_le_self _ _) small
      simp only [sign, Bool.true_eq, ite_true, BitVec.sshiftRight, original, Int.shiftRight]
      change BitVec.ofInt (width+1) (Int.negSucc ((2^(width+1)-1-word.toNat) >>> distance)) = _
      rw [word_ofInt_negSucc _ _ shifted]
      congr 1
      apply BitVec.eq_of_toNat_eq
      simp [Nat.mod_eq_of_lt shifted]
    · have low : word.toNat < 2^width := by
        simp [BitVec.msb_eq_decide] at sign
        exact sign
      have positive : 2 * word.toNat < 2^(width+1) := by omega
      have original : word.toInt = Int.ofNat word.toNat := by simp [BitVec.toInt, positive]
      simp only [show word.msb = false by cases h : word.msb <;> simp_all,
        Bool.false_eq_true, ite_false, BitVec.sshiftRight, original, Int.shiftRight]
      change BitVec.ofInt (width+1) (Int.ofNat (word.toNat >>> distance)) = _
      rw [word_ofInt_nat]
      apply BitVec.eq_of_toNat_eq
      have shifted : word.toNat >>> distance < 2^(width+1) := by
        rw [Nat.shiftRight_eq_div_pow]
        exact Nat.lt_of_le_of_lt (Nat.div_le_self _ _) valid
      simp [Nat.mod_eq_of_lt shifted]

theorem word_xor_mask {width : Nat} (word : BitVec width) (sign : Nat) (env : Assignment) :
    word ^^^ wordValue (fun _ => sign) env = if env sign then ~~~word else word := by
  trustIrCompilerProof {
    apply BitVec.eq_of_getLsb_eq
    intro i
    cases h : env sign <;> simp [BitVec.getLsb_xor, wordValue_bit, h, i.isLt]
  } {
    apply trustIrWordExt
    intro i
    rw [BitVec.getLsbD_xor, wordValue_bit]
    cases h : env sign <;> simp [h, BitVec.getLsbD_not, i.isLt]
  }

/-- Complement before and after the logical shift, controlled by the same
original sign wire. The amount and sign are shared, never re-emitted. -/
def WordCode.signedShift {width : Nat} (input amount : Fin width → Nat) (sign next : Nat) : WordCode width :=
  let inverted := WordCode.bitwise .bxor input (fun _ => sign) next
  let shifted := WordCode.shift .right inverted.bits amount (next + inverted.gates.length)
  let prior := WordCode.append inverted shifted
  WordCode.append prior (WordCode.bitwise .bxor shifted.bits (fun _ => sign) (next + prior.gates.length))

theorem WordCode.signedShift_check {width : Nat} (input amount : Fin width → Nat) (sign next : Nat)
    (inputBound : ∀ i, input i < next) (amountBound : ∀ i, amount i < next) (signBound : sign < next) :
    (WordCode.signedShift input amount sign next).check next = true := by
  have inverted := WordCode.bitwise_check .bxor input (fun _ => sign) next inputBound (fun _ => signBound)
  have amountLater : ∀ i, amount i < next + (WordCode.bitwise .bxor input (fun _ => sign) next).gates.length := by
    intro i; have before := amountBound i; omega
  have shifted := WordCode.shift_check .right _ amount _ ((WordCode.check_iff _ _).mp inverted).2 amountLater
  have prior := WordCode.append_check _ _ _ inverted shifted
  apply WordCode.append_check _ _ _ prior
  apply WordCode.bitwise_check
  · simpa [WordCode.append, Nat.add_assoc] using ((WordCode.check_iff _ _).mp shifted).2
  · intro _; omega

theorem WordCode.signedShift_value {width : Nat} (input amount : Fin width → Nat) (sign next : Nat)
    (inputBound : ∀ i, input i < next) (amountBound : ∀ i, amount i < next) (signBound : sign < next)
    (env : Assignment) :
    (WordCode.signedShift input amount sign next).value env =
      if env sign then ~~~(~~~(wordValue input env) >>> (wordValue amount env).toNat)
      else wordValue input env >>> (wordValue amount env).toNat := by
  let inverted := WordCode.bitwise .bxor input (fun _ => sign) next
  let shifted := WordCode.shift .right inverted.bits amount (next + inverted.gates.length)
  let prior := WordCode.append inverted shifted
  have invertedCheck := WordCode.bitwise_check .bxor input (fun _ => sign) next inputBound (fun _ => signBound)
  have amountLater : ∀ i, amount i < next + inverted.gates.length := by
    intro i; have before := amountBound i; omega
  have shiftedCheck := WordCode.shift_check .right _ amount _ ((WordCode.check_iff _ _).mp invertedCheck).2 amountLater
  have priorCheck := WordCode.append_check _ _ _ invertedCheck shiftedCheck
  have shiftedBound : ∀ i, shifted.bits i < next + prior.gates.length := by
    simpa [prior, WordCode.append, Nat.add_assoc] using ((WordCode.check_iff _ _).mp shiftedCheck).2
  have signLater : sign < next + prior.gates.length := by omega
  have signSame := (((WordCode.check_iff _ _).mp priorCheck).1.run_correct env).1 sign signBound
  have amountSame : wordValue amount (run inverted.gates env) = wordValue amount env := by
    apply wordValue_congr
    intro i
    exact (((WordCode.check_iff _ _).mp invertedCheck).1.run_correct env).1 _ (amountBound i)
  have before : inverted.value env = if env sign then ~~~(wordValue input env) else wordValue input env := by
    rw [WordCode.bitwise_value .bxor input (fun _ => sign) next inputBound (fun _ => signBound)]
    exact word_xor_mask _ _ _
  have middle : prior.value env =
      (if env sign then ~~~(wordValue input env) else wordValue input env) >>> (wordValue amount env).toNat := by
    rw [WordCode.append_value, WordCode.shift_value .right _ _ _ ((WordCode.check_iff _ _).mp invertedCheck).2 amountLater,
      amountSame]
    change inverted.value env >>> _ = _
    rw [before]
  change (WordCode.append prior (WordCode.bitwise .bxor shifted.bits (fun _ => sign) (next + prior.gates.length))).value env = _
  rw [WordCode.append_value, WordCode.bitwise_value .bxor _ _ _ shiftedBound (fun _ => signLater)]
  simp only [BitwiseOp.eval]
  rw [word_xor_mask, signSame]
  change (if env sign then ~~~(prior.value env) else prior.value env) = _
  rw [middle]
  cases env sign <;> rfl

/-- Arithmetic right shift binds sign to the actual input MSB. Empty words have
no sign bit and need no graph. Every amount bit is retained by the logical core. -/
def WordCode.ashr {width : Nat} (input amount : Fin width → Nat) (next : Nat) : WordCode width :=
  match width, input, amount with
  | 0, input, _ => ⟨[], input⟩
  | width+1, input, amount => WordCode.signedShift input amount (input ⟨width, by omega⟩) next

theorem WordCode.ashr_check {width : Nat} (input amount : Fin width → Nat) (next : Nat)
    (inputBound : ∀ i, input i < next) (amountBound : ∀ i, amount i < next) :
    (WordCode.ashr input amount next).check next = true := by
  cases width with
  | zero => exact (WordCode.check_iff _ _).mpr ⟨.nil next, fun i => i.elim0⟩
  | succ width => exact WordCode.signedShift_check _ _ _ _ inputBound amountBound (inputBound _)

theorem WordCode.ashr_value {width : Nat} (input amount : Fin width → Nat) (next : Nat)
    (inputBound : ∀ i, input i < next) (amountBound : ∀ i, amount i < next) (env : Assignment) :
    (WordCode.ashr input amount next).value env =
      BitVec.sshiftRight (wordValue input env) (wordValue amount env).toNat := by
  cases width with
  | zero => exact Subsingleton.elim _ _
  | succ width =>
    have signValue : env (input ⟨width, by omega⟩) = (wordValue input env).msb := by
      trustIrCompilerProof { rw [BitVec.msb_eq_getLsb_last] } {
        rw [BitVec.msb_eq_getLsbD_last]
      }
      simpa using (wordValue_bit input env ⟨width, by omega⟩).symm
    rw [WordCode.ashr, WordCode.signedShift_value _ _ _ _ inputBound amountBound (inputBound _), signValue,
      word_sshiftRight]

theorem WordCode.signedShift_length {width : Nat} (input amount : Fin width → Nat) (sign next : Nat) :
    (WordCode.signedShift input amount sign next).gates.length = width * (3 * width + 2) + 2 * width := by
  simp only [WordCode.signedShift, WordCode.append, List.length_append, WordCode.shift_length,
    WordCode.bitwise, tabulate_length]
  omega

theorem WordCode.ashr_length {width : Nat} (input amount : Fin width → Nat) (next : Nat) :
    (WordCode.ashr input amount next).gates.length = width * (3 * width + 2) + 2 * width := by
  cases width with
  | zero => rfl
  | succ width => exact WordCode.signedShift_length _ _ _ _

def WordCode.composeAShr {width : Nat} (next : Nat) (left right : WordCode width) : WordCode width :=
  let both := WordCode.append left right
  WordCode.append both (WordCode.ashr left.bits right.bits (next + both.gates.length))

theorem WordCode.composeAShr_check {width : Nat} (next : Nat) (left right : WordCode width)
    (leftCheck : left.check next = true)
    (rightCheck : right.check (next + left.gates.length) = true) :
    (WordCode.composeAShr next left right).check next = true := by
  obtain ⟨leftBounds, rightBounds⟩ := WordCode.append_operand_bounds next left right leftCheck rightCheck
  apply WordCode.append_check _ _ next (WordCode.append_check left right next leftCheck rightCheck)
  exact WordCode.ashr_check _ _ _ leftBounds rightBounds

theorem WordCode.composeAShr_value {width : Nat} (next : Nat) (left right : WordCode width)
    (leftCheck : left.check next = true)
    (rightCheck : right.check (next + left.gates.length) = true) (env : Assignment) :
    (WordCode.composeAShr next left right).value env = BitVec.sshiftRight (left.value env) (right.value (run left.gates env)).toNat := by
  obtain ⟨leftBounds, rightBounds⟩ := WordCode.append_operand_bounds next left right leftCheck rightCheck
  have rightValid := ((right.check_iff _).mp rightCheck).1
  have leftValue : wordValue left.bits (run (WordCode.append left right).gates env) = left.value env := by
    apply wordValue_congr
    intro i
    exact rightValid.append_preserves (next := next) (first := left.gates) env (left.bits i)
      (((left.check_iff next).mp leftCheck).2 i)
  have rightValue : wordValue right.bits (run (WordCode.append left right).gates env) =
      right.value (run left.gates env) := by rw [WordCode.append, run_append]; rfl
  rw [WordCode.composeAShr, WordCode.append_value, WordCode.ashr_value _ _ _ leftBounds rightBounds,
    leftValue, rightValue]


theorem WordCode.ashr_target {width : Nat} (input amount : Fin width → Nat)
    (next : Nat) (bound : ∀ i, input i < next) (amountBound : ∀ i, amount i < next) (env : Assignment)
    (wordTerm amountTerm : SMTTerm (.bv width)) (target : SMTEnv)
    (wordValueEq : wordValue input env = wordTerm.eval target)
    (amountValueEq : wordValue amount env = amountTerm.eval target) :
    (WordCode.ashr input amount next).value env =
      (SMTTerm.binary (.bvAShr width) wordTerm amountTerm).eval target := by
  rw [WordCode.ashr_value _ _ _ bound amountBound, wordValueEq, amountValueEq]
  rfl

theorem WordCode.composeAShr_target {width : Nat} (next : Nat)
    (word amount : WordCode width) (wordCheck : word.check next = true)
    (amountCheck : amount.check (next + word.gates.length) = true) (env : Assignment)
    (wordTerm amountTerm : SMTTerm (.bv width)) (target : SMTEnv)
    (wordValueEq : word.value env = wordTerm.eval target)
    (amountValueEq : amount.value (run word.gates env) = amountTerm.eval target) :
    (WordCode.composeAShr next word amount).value env =
      (SMTTerm.binary (.bvAShr width) wordTerm amountTerm).eval target := by
  rw [WordCode.composeAShr_value _ _ _ wordCheck amountCheck, wordValueEq, amountValueEq]
  rfl

end TrustIr.AYGateCNF





#trustIrAxiomsExact TrustIr.AYGateCNF.word_sshiftRight == [propext, Quot.sound, Classical.choice]

#trustIrAxiomsExact TrustIr.AYGateCNF.word_xor_mask == [propext, Classical.choice, Quot.sound]

#trustIrAxiomsExact TrustIr.AYGateCNF.WordCode.signedShift_check == [propext, Quot.sound, Classical.choice]

#trustIrAxiomsExact TrustIr.AYGateCNF.WordCode.signedShift_value == [propext, Classical.choice, Quot.sound]

#trustIrAxiomsExact TrustIr.AYGateCNF.WordCode.ashr_check == [propext, Classical.choice, Quot.sound]

#trustIrAxiomsExact TrustIr.AYGateCNF.WordCode.ashr_value == [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AYGateCNF.WordCode.signedShift_length == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.AYGateCNF.WordCode.ashr_length == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsExact TrustIr.AYGateCNF.WordCode.composeAShr_check == [propext, Classical.choice, Quot.sound]

#trustIrAxiomsExact TrustIr.AYGateCNF.WordCode.composeAShr_value == [propext, Classical.choice, Quot.sound]

#trustIrAxiomsExact TrustIr.AYGateCNF.WordCode.ashr_target == [propext, Classical.choice, Quot.sound]

#trustIrAxiomsExact TrustIr.AYGateCNF.WordCode.composeAShr_target == [propext, Classical.choice, Quot.sound]
