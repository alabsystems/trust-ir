-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0
import TrustIr.Proofs.BitVecUnsignedValues
import TrustIr.Semantics.Arith

namespace TrustIr.UnsignedRemainderWp

/-- The canonical unsigned remainder needs no further result-width correction. -/
theorem remainder_range (width : Nat) (left right : Int)
    (leftRange : 0 ≤ left ∧ left < (2 : Int) ^ width)
    (rightRange : 0 ≤ right ∧ right < (2 : Int) ^ width) :
    0 ≤ left % right ∧ left % right < (2 : Int) ^ width := by
  have exactValue := TrustIrExpr.bitvec_umod_value width left right leftRange rightRange
  rw [← exactValue]
  constructor
  · trustIrCompilerProof
      { exact Int.ofNat_nonneg _ }
      { exact Int.natCast_nonneg _ }
  · have bound := Int.ofNat_lt.mpr
      (BitVec.umod (BitVec.ofInt width left) (BitVec.ofInt width right)).isLt
    simpa only [Int.natCast_pow] using bound

/-- Actual IR remainder execution, with the mandatory nonzero divisor. -/
theorem value (width : Nat) (left right : Int)
    (leftRange : 0 ≤ left ∧ left < (2 : Int) ^ width)
    (rightRange : 0 ≤ right ∧ right < (2 : Int) ^ width) (nonzero : right ≠ 0) :
    semIntBinOp .URem width left right = .ok (left % right) := by
  have range := remainder_range width left right leftRange rightRange
  simp only [semIntBinOp, beq_iff_eq, nonzero, if_false]
  simp only [Int.add_emod, Int.emod_emod, Int.emod_self, Int.add_zero]
  rw [Int.emod_eq_of_lt range.1 range.2]

/-- The complete success-and-continuation condition retains definedness. -/
theorem wp_iff (width : Nat) (left right : Int)
    (leftRange : 0 ≤ left ∧ left < (2 : Int) ^ width)
    (rightRange : 0 ≤ right ∧ right < (2 : Int) ^ width) (post : Int → Prop) :
    (∃ returned, semIntBinOp .URem width left right = .ok returned ∧ post returned) ↔
      right ≠ 0 ∧ post (left % right) := by
  by_cases zero : right = 0
  · simp [zero, semIntBinOp]
  · rw [value width left right leftRange rightRange zero]
    simp [zero]

theorem zero (width : Nat) (left : Int) :
    semIntBinOp .URem width left 0 = .error (.ub "unsigned remainder by zero") := by
  simp [semIntBinOp]

/-- The actual typed U64 operation has the same continuation condition. -/
theorem u64_wp_iff (left right : Int)
    (leftRange : 0 ≤ left ∧ left < (2 : Int) ^ 64)
    (rightRange : 0 ≤ right ∧ right < (2 : Int) ^ 64) (post : Value → Prop) :
    (∃ returned, semBinOpValues .URem .U64 (.int 64 left) (.int 64 right) =
      .ok returned ∧ post returned) ↔ right ≠ 0 ∧ post (.int 64 (left % right)) := by
  by_cases zero : right = 0
  · simp [semBinOpValues, zero, semIntBinOp, bind, Except.bind]
  · have computed := value 64 left right leftRange rightRange zero
    simp [semBinOpValues, computed, zero, bind, Except.bind, pure, Except.pure]

theorem dead_result_wp_iff (width : Nat) (left right : Int)
    (leftRange : 0 ≤ left ∧ left < (2 : Int) ^ width)
    (rightRange : 0 ≤ right ∧ right < (2 : Int) ^ width) :
    (∃ returned, semIntBinOp .URem width left right = .ok returned) ↔ right ≠ 0 := by
  simpa using wp_iff width left right leftRange rightRange (fun _ => True)

end TrustIr.UnsignedRemainderWp
