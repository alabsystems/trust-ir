-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0
import TrustIr.Proofs.AYDivisionLoop

namespace TrustIr.AYGateCNF

def divisionInputsCheck {width : Nat} (dividend divisor : Fin width → Nat) (next : Nat) : Bool :=
  (tabulate dividend).all (fun id => decide (id < next)) &&
    (tabulate divisor).all (fun id => decide (id < next))

theorem divisionInputsCheck_iff {width : Nat} (dividend divisor : Fin width → Nat) (next : Nat) :
    divisionInputsCheck dividend divisor next = true ↔
      (∀ i, dividend i < next) ∧ (∀ i, divisor i < next) := by
  have bounds (input : Fin width → Nat) :
      (tabulate input).all (fun id => decide (id < next)) = true ↔ ∀ i, input i < next := by
    constructor
    · intro checked i
      have all : ∀ id ∈ tabulate input, id < next := by simpa using checked
      exact all _ (tabulate_mem input i)
    · intro bound
      have all : ∀ id ∈ tabulate input, id < next := by
        intro id member
        obtain ⟨i, same⟩ := tabulate_cases input id member
        rw [← same]
        exact bound i
      simpa using all
  simp only [divisionInputsCheck, Bool.and_eq_true, bounds]

/-- Check original operand references before allocating the zero remainder or
any round. A reference to a future internal gate is not an original input. -/
def DivisionCode.unsignedCheckedEval {width : Nat} (dividend divisor : Fin width → Nat) (next : Nat)
    (env : Assignment) : Option (Nat × Nat) :=
  if divisionInputsCheck dividend divisor next then
    (DivisionCode.unsigned dividend divisor next).checkedEval next env
  else none

theorem DivisionCode.unsignedCheckedEval_eq_some {width : Nat} (dividend divisor : Fin width → Nat) (next : Nat)
    (env : Assignment) (result : Nat × Nat) :
    DivisionCode.unsignedCheckedEval dividend divisor next env = some result ↔
      (∀ i, dividend i < next) ∧ (∀ i, divisor i < next) ∧
        (DivisionCode.unsigned dividend divisor next).value env = result := by
  by_cases checked : divisionInputsCheck dividend divisor next = true
  · obtain ⟨dividendBound, divisorBound⟩ := (divisionInputsCheck_iff _ _ _).mp checked
    simp [DivisionCode.unsignedCheckedEval, checked, DivisionCode.checkedEval_eq_some,
      DivisionCode.unsigned_check _ _ _ dividendBound divisorBound, dividendBound, divisorBound]
  · have bad : ¬ ((∀ i, dividend i < next) ∧ (∀ i, divisor i < next)) :=
      fun bounds => checked ((divisionInputsCheck_iff _ _ _).mpr bounds)
    trustIrCompilerProof {
      simp only [DivisionCode.unsignedCheckedEval, checked, Bool.false_eq_true, if_false, Option.noConfusion,
        false_iff]
    } {
      simp only [DivisionCode.unsignedCheckedEval, checked, Bool.false_eq_true, if_false, reduceCtorEq,
        false_iff]
    }
    intro valid
    exact bad ⟨valid.1, valid.2.1⟩

theorem DivisionCode.unsignedCheckedEval_result {width : Nat} (dividend divisor : Fin width → Nat) (next : Nat)
    (dividendBound : ∀ i, dividend i < next) (divisorBound : ∀ i, divisor i < next) (env : Assignment) :
    DivisionCode.unsignedCheckedEval dividend divisor next env = some
      (if (wordValue divisor env).toNat = 0 then (2^width-1, (wordValue dividend env).toNat)
      else ((wordValue dividend env).toNat / (wordValue divisor env).toNat,
        (wordValue dividend env).toNat % (wordValue divisor env).toNat)) := by
  exact (DivisionCode.unsignedCheckedEval_eq_some _ _ _ _ _).mpr
    ⟨dividendBound, divisorBound, DivisionCode.unsigned_value _ _ _ dividendBound divisorBound env⟩

end TrustIr.AYGateCNF

#trustIrAxiomsExact TrustIr.AYGateCNF.divisionInputsCheck_iff == [propext, Quot.sound, Classical.choice]

#trustIrAxiomsExact TrustIr.AYGateCNF.DivisionCode.unsignedCheckedEval_eq_some == [propext, Classical.choice, Quot.sound]

#trustIrAxiomsExact TrustIr.AYGateCNF.DivisionCode.unsignedCheckedEval_result == [propext, Classical.choice, Quot.sound]
