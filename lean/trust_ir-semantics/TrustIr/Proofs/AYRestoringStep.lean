-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0
import TrustIr.Proofs.AYSubCarry
import TrustIr.Proofs.AYWordIte
import TrustIr.Proofs.AYWordWidths

namespace TrustIr.AYGateCNF

/-- One subtraction graph supplies both its difference and the selector's
actual no-borrow wire. No comparison or child graph is emitted a second time. -/
def WordCode.subtractIfGe {width : Nat} (left right : Fin width → Nat) (next : Nat) : WordCode width :=
  let difference := WordCode.sub left right next
  WordCode.append difference (WordCode.ite (Code.subNoBorrow left right next).output difference.bits left
    (next + difference.gates.length))

private theorem subtraction_bounds {width : Nat} (left right : Fin width → Nat) (next : Nat)
    (leftBound : ∀ i, left i < next) (rightBound : ∀ i, right i < next) :
    (Code.subNoBorrow left right next).output < next + (WordCode.sub left right next).gates.length := by
  have bound := ((Code.check_iff _ _).mp (Code.subNoBorrow_check left right next leftBound rightBound)).2
  rwa [Code.subNoBorrow_gates] at bound

theorem WordCode.subtractIfGe_check {width : Nat} (left right : Fin width → Nat) (next : Nat)
    (leftBound : ∀ i, left i < next) (rightBound : ∀ i, right i < next) :
    (WordCode.subtractIfGe left right next).check next = true := by
  have checked := WordCode.sub_check left right next leftBound rightBound
  apply WordCode.append_check _ _ _ checked
  apply WordCode.ite_check _ _ _ _ (subtraction_bounds _ _ _ leftBound rightBound)
    ((WordCode.check_iff _ _).mp checked).2
  intro i; have before := leftBound i; omega

theorem WordCode.subtractIfGe_value {width : Nat} (left right : Fin width → Nat) (next : Nat)
    (leftBound : ∀ i, left i < next) (rightBound : ∀ i, right i < next) (env : Assignment) :
    (WordCode.subtractIfGe left right next).value env =
      if (wordValue right env).toNat ≤ (wordValue left env).toNat
      then wordValue left env - wordValue right env else wordValue left env := by
  have checked := WordCode.sub_check left right next leftBound rightBound
  have leftLater : ∀ i, left i < next + (WordCode.sub left right next).gates.length := by
    intro i; have before := leftBound i; omega
  have leftSame : wordValue left (run (WordCode.sub left right next).gates env) = wordValue left env := by
    apply wordValue_congr
    intro i
    exact (((WordCode.check_iff _ _).mp checked).1.run_correct env).1 _ (leftBound i)
  have decision : run (WordCode.sub left right next).gates env (Code.subNoBorrow left right next).output =
      decide ((wordValue right env).toNat ≤ (wordValue left env).toNat) := by
    rw [← Code.subNoBorrow_gates]
    exact Code.subNoBorrow_eval _ _ _ leftBound rightBound env
  rw [WordCode.subtractIfGe, WordCode.append_value,
    WordCode.ite_value _ _ _ _ (subtraction_bounds _ _ _ leftBound rightBound)
      ((WordCode.check_iff _ _).mp checked).2 leftLater, decision, leftSame]
  change (if decide _ then (WordCode.sub left right next).value env else _) = _
  rw [WordCode.sub_value _ _ _ leftBound rightBound]
  simp

/-- The decision is observed from the same complete graph as its word result. -/
def Code.subtractIfGeFlag {width : Nat} (left right : Fin width → Nat) (next : Nat) : Code :=
  ⟨(WordCode.subtractIfGe left right next).gates, (Code.subNoBorrow left right next).output⟩

theorem Code.subtractIfGeFlag_check {width : Nat} (left right : Fin width → Nat) (next : Nat)
    (leftBound : ∀ i, left i < next) (rightBound : ∀ i, right i < next) :
    (Code.subtractIfGeFlag left right next).check next = true := by
  have checked := WordCode.subtractIfGe_check left right next leftBound rightBound
  apply (Code.check_iff _ _).mpr
  refine ⟨((WordCode.check_iff _ _).mp checked).1, ?_⟩
  have before := subtraction_bounds left right next leftBound rightBound
  simp only [Code.subtractIfGeFlag, WordCode.subtractIfGe, WordCode.append, List.length_append]
  omega

theorem Code.subtractIfGeFlag_eval {width : Nat} (left right : Fin width → Nat) (next : Nat)
    (leftBound : ∀ i, left i < next) (rightBound : ∀ i, right i < next) (env : Assignment) :
    (Code.subtractIfGeFlag left right next).eval env =
      decide ((wordValue right env).toNat ≤ (wordValue left env).toNat) := by
  have difference := WordCode.sub_check left right next leftBound rightBound
  have tail := WordCode.ite_check (Code.subNoBorrow left right next).output
    (WordCode.sub left right next).bits left _ (subtraction_bounds _ _ _ leftBound rightBound)
    ((WordCode.check_iff _ _).mp difference).2
    (fun i => Nat.lt_of_lt_of_le (leftBound i) (Nat.le_add_right _ _))
  change run ((WordCode.sub left right next).gates ++ _) env (Code.subNoBorrow left right next).output = _
  rw [run_append, (((WordCode.check_iff _ _).mp tail).1.run_correct
    (run (WordCode.sub left right next).gates env)).1 _ (subtraction_bounds _ _ _ leftBound rightBound)]
  rw [← Code.subNoBorrow_gates]
  exact Code.subNoBorrow_eval _ _ _ leftBound rightBound env

theorem WordCode.subtractIfGe_length {width : Nat} (left right : Fin width → Nat) (next : Nat) :
    (WordCode.subtractIfGe left right next).gates.length = 6*width+2 := by
  simp only [WordCode.subtractIfGe, WordCode.append, List.length_append, WordCode.sub_length,
    WordCode.ite_length]
  omega

theorem WordCode.subtractIfGe_numeric {width : Nat} (left right : Fin width → Nat) (next : Nat)
    (leftBound : ∀ i, left i < next) (rightBound : ∀ i, right i < next) (env : Assignment) :
    ((WordCode.subtractIfGe left right next).value env).toNat +
      (wordValue right env).toNat * ((Code.subtractIfGeFlag left right next).eval env).toNat =
        (wordValue left env).toNat := by
  have numeric := Code.subNoBorrow_numeric left right next leftBound rightBound env
  have rightSize := (wordValue right env).isLt
  rw [Code.subtractIfGeFlag_eval _ _ _ leftBound rightBound,
    WordCode.subtractIfGe_value _ _ _ leftBound rightBound]
  by_cases enough : (wordValue right env).toNat ≤ (wordValue left env).toNat
  · have carry : (Code.subNoBorrow left right next).eval env = true := by
      rw [Code.subNoBorrow_eval _ _ _ leftBound rightBound]; simp [enough]
    rw [carry] at numeric
    simp only [Bool.toNat_true, Nat.mul_one] at numeric
    simp only [if_pos enough, enough, ite_true, trustIrWidthLemma decide_True decide_true, Bool.toNat_true, Nat.mul_one]
    rw [← WordCode.sub_value _ _ _ leftBound rightBound]
    change ((WordCode.sub left right next).value env).toNat + (wordValue right env).toNat = (wordValue left env).toNat
    omega
  · simp [enough]

theorem word_single_bit (bit : Nat) (env : Assignment) :
    wordValue (fun _ : Fin 1 => bit) env = BitVec.ofBool (env bit) := by
  apply trustIrWordExt
  intro i
  have zero : i.val = 0 := by omega
  rw [wordValue_bit]
  cases h : env bit
  all_goals trustIrCompilerProof {
    simp [BitVec.ofBool, BitVec.getLsb, zero, h]
  } {
    simp [BitVec.ofBool, BitVec.getLsbD, zero, h]
  }

theorem word_widen_toNat {width : Nat} (word : BitVec width) :
    (word.zeroExtend (width+1)).toNat = word.toNat := by
  rw [trustIrWidthLemma BitVec.toNat_zeroExtend BitVec.toNat_setWidth, Nat.mod_eq_of_lt]
  exact Nat.lt_of_lt_of_le word.isLt (Nat.pow_le_pow_right (by decide) (by omega))

/-- One restoring division stage keeps the trial remainder at width+1, so its
shifted-out high bit is never lost before comparison/subtraction. -/
def WordCode.restoringStep {width : Nat} (divisor remainder : Fin width → Nat) (bit next : Nat) : WordCode (width+1) :=
  let extended := WordCode.resize (width+1) divisor next
  let trial := WordCode.concat remainder (fun _ : Fin 1 => bit)
  WordCode.append extended (WordCode.subtractIfGe trial.bits extended.bits (next+extended.gates.length))

def Code.restoringFlag {width : Nat} (divisor remainder : Fin width → Nat) (bit next : Nat) : Code :=
  let extended := WordCode.resize (width+1) divisor next
  let trial := WordCode.concat remainder (fun _ : Fin 1 => bit)
  extended.appendBool (Code.subtractIfGeFlag trial.bits extended.bits (next+extended.gates.length))

theorem Code.restoringFlag_gates {width : Nat} (divisor remainder : Fin width → Nat) (bit next : Nat) :
    (Code.restoringFlag divisor remainder bit next).gates = (WordCode.restoringStep divisor remainder bit next).gates := rfl

private theorem trial_bounds {width : Nat} (remainder : Fin width → Nat) (bit next : Nat)
    (bound : ∀ i, remainder i < next) (bitBound : bit < next) :
    ∀ i, (WordCode.concat remainder (fun _ : Fin 1 => bit)).bits i < next := by
  have checked := WordCode.concat_check remainder (fun _ : Fin 1 => bit) next bound (fun _ => bitBound)
  simpa [WordCode.concat] using ((WordCode.check_iff _ _).mp checked).2

private theorem trial_value {width : Nat} (remainder : Fin width → Nat) (bit : Nat) (env : Assignment) :
    wordValue (WordCode.concat remainder (fun _ : Fin 1 => bit)).bits env =
      (wordValue remainder env).concat (env bit) := by
  have value := WordCode.concat_value remainder (fun _ : Fin 1 => bit) env
  rw [word_single_bit] at value
  exact value

theorem WordCode.restoringStep_check {width : Nat} (divisor remainder : Fin width → Nat) (bit next : Nat)
    (divisorBound : ∀ i, divisor i < next) (remainderBound : ∀ i, remainder i < next) (bitBound : bit < next) :
    (WordCode.restoringStep divisor remainder bit next).check next = true := by
  have checked := WordCode.resize_check (width+1) divisor next divisorBound
  apply WordCode.append_check _ _ _ checked
  apply WordCode.subtractIfGe_check
  · intro i; have before := trial_bounds remainder bit next remainderBound bitBound i; omega
  · exact ((WordCode.check_iff _ _).mp checked).2

theorem Code.restoringFlag_check {width : Nat} (divisor remainder : Fin width → Nat) (bit next : Nat)
    (divisorBound : ∀ i, divisor i < next) (remainderBound : ∀ i, remainder i < next) (bitBound : bit < next) :
    (Code.restoringFlag divisor remainder bit next).check next = true := by
  have checked := WordCode.resize_check (width+1) divisor next divisorBound
  apply WordCode.appendBool_check _ _ _ checked
  apply Code.subtractIfGeFlag_check
  · intro i; have before := trial_bounds remainder bit next remainderBound bitBound i; omega
  · exact ((WordCode.check_iff _ _).mp checked).2

theorem WordCode.restoringStep_value {width : Nat} (divisor remainder : Fin width → Nat) (bit next : Nat)
    (divisorBound : ∀ i, divisor i < next) (remainderBound : ∀ i, remainder i < next) (bitBound : bit < next)
    (env : Assignment) :
    (WordCode.restoringStep divisor remainder bit next).value env =
      let trial := (wordValue remainder env).concat (env bit)
      let extended := (wordValue divisor env).zeroExtend (width+1)
      if extended.toNat ≤ trial.toNat then trial - extended else trial := by
  have checked := WordCode.resize_check (width+1) divisor next divisorBound
  have before := trial_bounds remainder bit next remainderBound bitBound
  have later : ∀ i, (WordCode.concat remainder (fun _ : Fin 1 => bit)).bits i <
      next + (WordCode.resize (width+1) divisor next).gates.length := by
    intro i; have bound := before i; omega
  have same : wordValue (WordCode.concat remainder (fun _ : Fin 1 => bit)).bits
      (run (WordCode.resize (width+1) divisor next).gates env) = (wordValue remainder env).concat (env bit) := by
    rw [← trial_value remainder bit env]
    apply wordValue_congr
    intro i
    exact (((WordCode.check_iff _ _).mp checked).1.run_correct env).1 _ (before i)
  rw [WordCode.restoringStep, WordCode.append_value,
    WordCode.subtractIfGe_value _ _ _ later ((WordCode.check_iff _ _).mp checked).2, same]
  have extended : wordValue (WordCode.resize (width+1) divisor next).bits
      (run (WordCode.resize (width+1) divisor next).gates env) = (wordValue divisor env).zeroExtend (width+1) :=
    WordCode.resize_value _ _ _ divisorBound env
  rw [extended]

theorem Code.restoringFlag_eval {width : Nat} (divisor remainder : Fin width → Nat) (bit next : Nat)
    (divisorBound : ∀ i, divisor i < next) (remainderBound : ∀ i, remainder i < next) (bitBound : bit < next)
    (env : Assignment) :
    (Code.restoringFlag divisor remainder bit next).eval env =
      decide ((wordValue divisor env).toNat ≤ 2*(wordValue remainder env).toNat + (env bit).toNat) := by
  have checked := WordCode.resize_check (width+1) divisor next divisorBound
  have before := trial_bounds remainder bit next remainderBound bitBound
  have later : ∀ i, (WordCode.concat remainder (fun _ : Fin 1 => bit)).bits i <
      next + (WordCode.resize (width+1) divisor next).gates.length := by intro i; have bound := before i; omega
  have same : wordValue (WordCode.concat remainder (fun _ : Fin 1 => bit)).bits
      (run (WordCode.resize (width+1) divisor next).gates env) = (wordValue remainder env).concat (env bit) := by
    rw [← trial_value remainder bit env]
    apply wordValue_congr
    intro i
    exact (((WordCode.check_iff _ _).mp checked).1.run_correct env).1 _ (before i)
  rw [Code.restoringFlag, WordCode.appendBool_eval,
    Code.subtractIfGeFlag_eval _ _ _ later ((WordCode.check_iff _ _).mp checked).2, same]
  change decide (((WordCode.resize (width+1) divisor next).value env).toNat ≤ _) = _
  rw [WordCode.resize_value _ _ _ divisorBound, word_widen_toNat, BitVec.toNat_concat]
  simp only [Nat.mul_comm]

theorem WordCode.restoringStep_length {width : Nat} (divisor remainder : Fin width → Nat) (bit next : Nat) :
    (WordCode.restoringStep divisor remainder bit next).gates.length = 6*width+9 := by
  simp only [WordCode.restoringStep, WordCode.append, List.length_append, WordCode.subtractIfGe_length,
    WordCode.resize, WordCode.route, List.length_cons, List.length_nil]
  omega

end TrustIr.AYGateCNF
