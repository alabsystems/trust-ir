-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0
import TrustIr.Proofs.AYRestoringStep

namespace TrustIr.AYGateCNF

/-- Numeric conservation for the actual shared subtraction and quotient flag. -/
theorem WordCode.restoringStep_numeric {width : Nat} (divisor remainder : Fin width → Nat) (bit next : Nat)
    (divisorBound : ∀ i, divisor i < next) (remainderBound : ∀ i, remainder i < next) (bitBound : bit < next)
    (env : Assignment) :
    ((WordCode.restoringStep divisor remainder bit next).value env).toNat +
      (wordValue divisor env).toNat * ((Code.restoringFlag divisor remainder bit next).eval env).toNat =
        2*(wordValue remainder env).toNat + (env bit).toNat := by
  let extended := WordCode.resize (width+1) divisor next
  let trial := WordCode.concat remainder (fun _ : Fin 1 => bit)
  have checked := WordCode.resize_check (width+1) divisor next divisorBound
  have trialCheck := WordCode.concat_check remainder (fun _ : Fin 1 => bit) next remainderBound (fun _ => bitBound)
  have before : ∀ i, trial.bits i < next := ((WordCode.check_iff _ _).mp trialCheck).2
  have later : ∀ i, trial.bits i < next+extended.gates.length := by
    intro i; have bound := before i; omega
  have same : wordValue trial.bits (run extended.gates env) = wordValue trial.bits env := by
    apply wordValue_congr
    intro i
    exact (((WordCode.check_iff _ _).mp checked).1.run_correct env).1 _ (before i)
  have numeric := WordCode.subtractIfGe_numeric trial.bits extended.bits (next+extended.gates.length)
    later ((WordCode.check_iff _ _).mp checked).2 (run extended.gates env)
  rw [same] at numeric
  have divisorValue : wordValue extended.bits (run extended.gates env) =
      (wordValue divisor env).zeroExtend (width+1) := WordCode.resize_value _ _ _ divisorBound env
  rw [divisorValue, word_widen_toNat] at numeric
  have trialValue : wordValue trial.bits env = (wordValue remainder env).concat (env bit) := by
    have value := WordCode.concat_value remainder (fun _ : Fin 1 => bit) env
    rw [word_single_bit] at value
    exact value
  rw [trialValue, BitVec.toNat_concat] at numeric
  rw [WordCode.restoringStep, WordCode.append_value, Code.restoringFlag, WordCode.appendBool_eval]
  simpa only [Nat.mul_comm] using numeric

/-- A nonzero divisor and the incoming strict remainder bound are precisely
the invariant needed to make one conditional subtraction restore the bound. -/
theorem WordCode.restoringStep_remainder_lt {width : Nat} (divisor remainder : Fin width → Nat) (bit next : Nat)
    (divisorBound : ∀ i, divisor i < next) (remainderBound : ∀ i, remainder i < next) (bitBound : bit < next)
    (env : Assignment) (small : (wordValue remainder env).toNat < (wordValue divisor env).toNat) :
    ((WordCode.restoringStep divisor remainder bit next).value env).toNat < (wordValue divisor env).toNat := by
  have numeric := WordCode.restoringStep_numeric divisor remainder bit next divisorBound remainderBound bitBound env
  rw [Code.restoringFlag_eval _ _ _ _ divisorBound remainderBound bitBound] at numeric
  have bitSize : (env bit).toNat ≤ 1 := by cases env bit <;> decide
  by_cases enough : (wordValue divisor env).toNat ≤ 2*(wordValue remainder env).toNat + (env bit).toNat
  · simp only [enough, trustIrWidthLemma decide_True decide_true, Bool.toNat_true, Nat.mul_one] at numeric
    omega
  · simp only [enough, trustIrWidthLemma decide_False decide_false, Bool.toNat_false, Nat.mul_zero, Nat.add_zero] at numeric
    omega

/-- Appending one source bit updates the quotient using the actual emitted
flag, and the emitted wide remainder is the unique Euclidean remainder. -/
theorem WordCode.restoringStep_div_mod {width : Nat} (divisor remainder : Fin width → Nat) (bit next : Nat)
    (divisorBound : ∀ i, divisor i < next) (remainderBound : ∀ i, remainder i < next) (bitBound : bit < next)
    (env : Assignment) (dividendPrefix quotient : Nat)
    (decomposition : dividendPrefix = (wordValue divisor env).toNat * quotient + (wordValue remainder env).toNat)
    (small : (wordValue remainder env).toNat < (wordValue divisor env).toNat) :
    (2*dividendPrefix+(env bit).toNat) / (wordValue divisor env).toNat =
        2*quotient+((Code.restoringFlag divisor remainder bit next).eval env).toNat ∧
      (2*dividendPrefix+(env bit).toNat) % (wordValue divisor env).toNat =
        ((WordCode.restoringStep divisor remainder bit next).value env).toNat := by
  let d := (wordValue divisor env).toNat
  let r := ((WordCode.restoringStep divisor remainder bit next).value env).toNat
  let q := 2*quotient+((Code.restoringFlag divisor remainder bit next).eval env).toNat
  let n := 2*dividendPrefix+(env bit).toNat
  have numeric := WordCode.restoringStep_numeric divisor remainder bit next divisorBound remainderBound bitBound env
  have bound : r < d := WordCode.restoringStep_remainder_lt divisor remainder bit next
    divisorBound remainderBound bitBound env small
  have conserved : n = d*q+r := by
    dsimp [n, d, q, r]
    rw [decomposition]
    simp only [Nat.mul_add, Nat.mul_assoc, Nat.mul_left_comm _ 2]
    omega
  have divValue : n/d=q := by
    apply Nat.div_eq_of_lt_le
    · rw [conserved, Nat.mul_comm q d]; omega
    · rw [conserved, Nat.succ_mul, Nat.mul_comm q d]; omega
  have modValue : n%d=r := by
    have identity := Nat.mod_add_div n d
    rw [divValue] at identity
    omega
  exact ⟨divValue, modValue⟩

/-- Zero divisors still conserve the full wide trial and take the quotient
branch; this is the stage behavior required for an all-ones zero-divisor quotient. -/
theorem WordCode.restoringStep_zero {width : Nat} (divisor remainder : Fin width → Nat) (bit next : Nat)
    (divisorBound : ∀ i, divisor i < next) (remainderBound : ∀ i, remainder i < next) (bitBound : bit < next)
    (env : Assignment) (zero : (wordValue divisor env).toNat = 0) :
    ((WordCode.restoringStep divisor remainder bit next).value env).toNat =
        2*(wordValue remainder env).toNat+(env bit).toNat ∧
      (Code.restoringFlag divisor remainder bit next).eval env = true := by
  have numeric := WordCode.restoringStep_numeric divisor remainder bit next divisorBound remainderBound bitBound env
  rw [zero, Nat.zero_mul, Nat.add_zero] at numeric
  refine ⟨numeric, ?_⟩
  rw [Code.restoringFlag_eval _ _ _ _ divisorBound remainderBound bitBound, zero]
  simp

end TrustIr.AYGateCNF

#trustIrAxiomsExact TrustIr.AYGateCNF.WordCode.restoringStep_numeric == [propext, Classical.choice, Quot.sound]

#trustIrAxiomsExact TrustIr.AYGateCNF.WordCode.restoringStep_remainder_lt == [propext, Classical.choice, Quot.sound]

#trustIrAxiomsExact TrustIr.AYGateCNF.WordCode.restoringStep_div_mod == [propext, Classical.choice, Quot.sound]

#trustIrAxiomsExact TrustIr.AYGateCNF.WordCode.restoringStep_zero == [propext, Classical.choice, Quot.sound]
