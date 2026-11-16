-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0
import TrustIr.Proofs.AYBitVecUnsignedDiv
import TrustIr.Proofs.AssertStep

namespace TrustIr.UnsignedDivisionWp

/-- The canonical quotient is already within its original unsigned width.
This reuses the checked BitVec quotient identity rather than another evaluator. -/
theorem quotient_range (width : Nat) (left right : Int)
    (leftRange : 0 ≤ left ∧ left < (2 : Int) ^ width)
    (rightRange : 0 ≤ right ∧ right < (2 : Int) ^ width) :
    0 ≤ left / right ∧ left / right < (2 : Int) ^ width := by
  have exactValue := TrustIrExpr.bitvec_udiv_value width left right leftRange rightRange
  rw [← exactValue]
  constructor
  · exact Int.ofNat_nonneg _
  · have bound := Int.ofNat_lt.mpr
      (BitVec.udiv (BitVec.ofInt width left) (BitVec.ofInt width right)).isLt
    simpa only [Int.natCast_pow] using bound

/-- Division of canonical unsigned inputs cannot exceed the dividend. -/
theorem quotient_le_left (width : Nat) (left right : Int)
    (leftRange : 0 ≤ left ∧ left < (2 : Int) ^ width)
    (rightRange : 0 ≤ right ∧ right < (2 : Int) ^ width) :
    left / right ≤ left := by
  calc
    left / right = Int.ofNat (BitVec.udiv
        (BitVec.ofInt width left) (BitVec.ofInt width right)).toNat :=
      (TrustIrExpr.bitvec_udiv_value width left right leftRange rightRange).symm
    _ ≤ Int.ofNat (BitVec.ofInt width left).toNat :=
      Int.ofNat_le.mpr (Nat.div_le_self _ _)
    _ = left := TrustIrExpr.bitvec_ofInt_toNat width left leftRange.1 leftRange.2

/-- Actual canonical IR execution equals integer Euclidean division only with
its mandatory nonzero divisor. There is no modular result correction. -/
theorem value (width : Nat) (left right : Int)
    (leftRange : 0 ≤ left ∧ left < (2 : Int) ^ width)
    (rightRange : 0 ≤ right ∧ right < (2 : Int) ^ width) (nonzero : right ≠ 0) :
    semIntBinOp .UDiv width left right = .ok (left / right) := by
  have range := quotient_range width left right leftRange rightRange
  simp only [semIntBinOp, beq_iff_eq, nonzero, if_false]
  simp only [Int.add_emod, Int.emod_emod, Int.emod_self, Int.add_zero]
  rw [Int.emod_eq_of_lt range.1 range.2]

/-- The full success-and-postcondition question of canonical unsigned division.
The domain remains owed even when `post` ignores the quotient. -/
theorem wp_iff (width : Nat) (left right : Int)
    (leftRange : 0 ≤ left ∧ left < (2 : Int) ^ width)
    (rightRange : 0 ≤ right ∧ right < (2 : Int) ^ width) (post : Int → Prop) :
    (∃ returned, semIntBinOp .UDiv width left right = .ok returned ∧ post returned) ↔
      right ≠ 0 ∧ post (left / right) := by
  by_cases zero : right = 0
  · simp [zero, semIntBinOp]
  · rw [value width left right leftRange rightRange zero]
    simp [zero]

/-- Zero remains undefined even if the quotient would be discarded. -/
theorem zero (width : Nat) (left : Int) :
    semIntBinOp .UDiv width left 0 = .error (.ub "unsigned division by zero") := by
  simp [semIntBinOp]

/-- The same rule at the actual typed U64 value-operation boundary. -/
theorem u64_wp_iff (left right : Int)
    (leftRange : 0 ≤ left ∧ left < (2 : Int) ^ 64)
    (rightRange : 0 ≤ right ∧ right < (2 : Int) ^ 64) (post : Value → Prop) :
    (∃ returned, semBinOpValues .UDiv .U64 (.int 64 left) (.int 64 right) =
      .ok returned ∧ post returned) ↔ right ≠ 0 ∧ post (.int 64 (left / right)) := by
  by_cases zero : right = 0
  · simp [semBinOpValues, zero, semIntBinOp, bind, Except.bind, pure, Except.pure]
  · have computed := value 64 left right leftRange rightRange zero
    simp [semBinOpValues, computed, zero, bind, Except.bind, pure, Except.pure]

/-- Success still owes a nonzero divisor when the continuation is `True`. -/
theorem dead_result_wp_iff (width : Nat) (left right : Int)
    (leftRange : 0 ≤ left ∧ left < (2 : Int) ^ width)
    (rightRange : 0 ≤ right ∧ right < (2 : Int) ^ width) :
    (∃ returned, semIntBinOp .UDiv width left right = .ok returned) ↔ right ≠ 0 := by
  simpa using wp_iff width left right leftRange rightRange (fun _ => True)

end TrustIr.UnsignedDivisionWp
