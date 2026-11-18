-- Copyright 2026 Andrew Yates
-- Licensed under the Apache License, Version 2.0
import SemR
import TrustIr.Proofs.UnsignedDivisionWp

/-! Agreement of the two existing unsigned-division operator definitions.

This relates their actual computations for every canonical unsigned operand
and arbitrary postcondition. It introduces no evaluator, source refinement,
whole-body equivalence or proof authority for a compiler obligation.
-/

namespace SemR.CanonicalUnsignedDivision

private theorem int_range (width value : Nat) (bound : value < 2 ^ width) :
    0 ≤ (value : Int) ∧ (value : Int) < (2 : Int) ^ width := by
  constructor
  · exact Int.natCast_nonneg _
  · have cast := Int.ofNat_lt.mpr bound
    simpa only [Int.natCast_pow] using cast

/-- Nonzero division has the same full quotient, without a result-width
correction, in both existing operator semantics. -/
theorem value (width left right : Nat)
    (leftRange : left < 2 ^ width) (rightRange : right < 2 ^ width)
    (nonzero : right ≠ 0) :
    SemR.intBin .udiv width left right = .ok (left / right) ∧
    TrustIr.semIntBinOp .UDiv width (left : Int) (right : Int) =
      .ok ((left / right : Nat) : Int) := by
  constructor
  · simp [SemR.intBin, nonzero]
  · have nonzeroInt : (right : Int) ≠ 0 := Int.ofNat_ne_zero.mpr nonzero
    have computed := TrustIr.UnsignedDivisionWp.value width left right
      (int_range width left leftRange) (int_range width right rightRange) nonzeroInt
    simpa only [Int.natCast_ediv] using computed

/-- Both operators reject zero with the actual same UB reason. -/
theorem zero (width left : Nat) :
    SemR.intBin .udiv width left 0 = .ub "unsigned division by zero" ∧
    TrustIr.semIntBinOp .UDiv width (left : Int) 0 =
      .error (.ub "unsigned division by zero") := by
  exact ⟨by simp [SemR.intBin], TrustIr.UnsignedDivisionWp.zero width left⟩

/-- Success and an arbitrary continuation agree. In particular, discarding
the quotient does not erase the division-definedness obligation. -/
theorem wp_iff (width left right : Nat)
    (leftRange : left < 2 ^ width) (rightRange : right < 2 ^ width)
    (post : Int → Prop) :
    (∃ returned, SemR.intBin .udiv width left right = .ok returned ∧
      post (returned : Int)) ↔
    (∃ returned, TrustIr.semIntBinOp .UDiv width (left : Int) (right : Int) =
      .ok returned ∧ post returned) := by
  by_cases nonzero : right = 0
  · subst right
    simp [SemR.intBin, TrustIr.semIntBinOp]
  · obtain ⟨source, target⟩ := value width left right leftRange rightRange nonzero
    rw [source, target]
    simp

/-- Both models require a nonzero divisor even for a discarded result. -/
theorem dead_result_iff (width left right : Nat)
    (leftRange : left < 2 ^ width) (rightRange : right < 2 ^ width) :
    (∃ returned, SemR.intBin .udiv width left right = .ok returned) ↔ right ≠ 0 := by
  have agreement := wp_iff width left right leftRange rightRange (fun _ => True)
  have defined := TrustIr.UnsignedDivisionWp.dead_result_wp_iff width left right
    (int_range width left leftRange) (int_range width right rightRange)
  simp only [and_true] at agreement
  simpa only [Int.ofNat_ne_zero] using agreement.trans defined

end SemR.CanonicalUnsignedDivision
