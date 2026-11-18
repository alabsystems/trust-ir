-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0
import SemR
import TrustIr.Proofs.UnsignedRemainderWp

/-! Agreement of the existing unsigned-remainder operators for every canonical
unsigned operand and arbitrary continuation. No evaluator, decoder, whole-body
refinement or compiler proof authority is introduced. -/

namespace SemR.CanonicalUnsignedRemainder

private theorem int_range (width value : Nat) (bound : value < 2 ^ width) :
    0 ≤ (value : Int) ∧ (value : Int) < (2 : Int) ^ width := by
  constructor
  · exact Int.natCast_nonneg _
  · have cast := Int.ofNat_lt.mpr bound
    simpa only [Int.natCast_pow] using cast

/-- Both operators return the full same remainder, without narrowing it. -/
theorem value (width left right : Nat)
    (leftRange : left < 2 ^ width) (rightRange : right < 2 ^ width)
    (nonzero : right ≠ 0) :
    SemR.intBin .urem width left right = .ok (left % right) ∧
    TrustIr.semIntBinOp .URem width (left : Int) (right : Int) =
      .ok ((left % right : Nat) : Int) := by
  constructor
  · simp [SemR.intBin, nonzero]
  · have nonzeroInt : (right : Int) ≠ 0 := Int.ofNat_ne_zero.mpr nonzero
    have computed := TrustIr.UnsignedRemainderWp.value width left right
      (int_range width left leftRange) (int_range width right rightRange) nonzeroInt
    simpa only [Int.natCast_emod] using computed

/-- Both reject the actual zero-divisor undefined behavior. -/
theorem zero (width left : Nat) :
    SemR.intBin .urem width left 0 = .ub "unsigned remainder by zero" ∧
    TrustIr.semIntBinOp .URem width (left : Int) 0 =
      .error (.ub "unsigned remainder by zero") := by
  exact ⟨by simp [SemR.intBin], TrustIr.UnsignedRemainderWp.zero width left⟩

theorem wp_iff (width left right : Nat)
    (leftRange : left < 2 ^ width) (rightRange : right < 2 ^ width)
    (post : Int → Prop) :
    (∃ returned, SemR.intBin .urem width left right = .ok returned ∧
      post (returned : Int)) ↔
    (∃ returned, TrustIr.semIntBinOp .URem width (left : Int) (right : Int) =
      .ok returned ∧ post returned) := by
  by_cases nonzero : right = 0
  · subst right
    simp [SemR.intBin, TrustIr.semIntBinOp]
  · obtain ⟨source, target⟩ := value width left right leftRange rightRange nonzero
    rw [source, target]
    simp

/-- Discarding the remainder cannot discharge the nonzero obligation. -/
theorem dead_result_iff (width left right : Nat)
    (leftRange : left < 2 ^ width) (rightRange : right < 2 ^ width) :
    (∃ returned, SemR.intBin .urem width left right = .ok returned) ↔ right ≠ 0 := by
  have agreement := wp_iff width left right leftRange rightRange (fun _ => True)
  have defined := TrustIr.UnsignedRemainderWp.dead_result_wp_iff width left right
    (int_range width left leftRange) (int_range width right rightRange)
  simp only [and_true] at agreement
  simpa only [Int.ofNat_ne_zero] using agreement.trans defined

end SemR.CanonicalUnsignedRemainder
