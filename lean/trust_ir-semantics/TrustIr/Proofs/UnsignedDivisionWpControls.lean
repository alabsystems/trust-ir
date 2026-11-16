-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0
import TrustIr.Proofs.UnsignedDivisionWp

namespace TrustIr.UnsignedDivisionWp.Controls

/-- The actual nonnegative quotient, including the complete U64 upper half. -/
theorem u64_max_half : semIntBinOp .UDiv 64 18446744073709551615 2 =
    .ok 9223372036854775807 := by
  exact value 64 _ _ (by decide) (by decide) (by decide)

theorem u32_max_half : semIntBinOp .UDiv 32 4294967295 2 = .ok 2147483647 := by
  exact value 32 _ _ (by decide) (by decide) (by decide)

theorem u8_max_half : semIntBinOp .UDiv 8 255 2 = .ok 127 := by
  exact value 8 _ _ (by decide) (by decide) (by decide)

theorem division_by_one (width : Nat) (left : Int)
    (leftRange : 0 ≤ left ∧ left < (2 : Int) ^ width)
    (oneRange : (1 : Int) < (2 : Int) ^ width) :
    semIntBinOp .UDiv width left 1 = .ok left := by
  simpa using value width left 1 leftRange ⟨by decide, oneRange⟩ (by decide)

theorem zero_has_no_success : ¬ ∃ returned,
    semIntBinOp .UDiv 64 1 0 = .ok returned := by
  simp [zero]

theorem false_postcondition_has_no_success : ¬ ∃ returned,
    semIntBinOp .UDiv 8 3 2 = .ok returned ∧ returned = 3 := by
  have computed : semIntBinOp .UDiv 8 3 2 = .ok 1 :=
    value 8 _ _ (by decide) (by decide) (by decide)
  simp [computed]

theorem dead_quotient_still_requires_guard :
    ¬ ∃ returned, semIntBinOp .UDiv 8 0 0 = .ok returned := by
  have exactGuard := dead_result_wp_iff 8 0 0 (by decide) (by decide)
  simpa using exactGuard

private def assertionState (value : Bool) : MachineState :=
  (MachineState.empty.bindValue (.bool value)).2

theorem true_assert_has_actual_continuation :
    ∃ result after, Sem.run (stepInst (.Assert ⟨0⟩ .DivByZero none) .le64)
      (assertionState true) = .ok (result, after) := by
  have exactRule := assert_step_wp_iff ⟨0⟩ .DivByZero none .le64
    (assertionState true) true (by rfl) (fun _ => True)
  simpa using exactRule

theorem false_assert_has_no_continuation :
    ¬ ∃ result after, Sem.run (stepInst (.Assert ⟨0⟩ .DivByZero none) .le64)
      (assertionState false) = .ok (result, after) := by
  have exactRule := assert_step_wp_iff ⟨0⟩ .DivByZero none .le64
    (assertionState false) false (by rfl) (fun _ => True)
  simpa using exactRule

theorem false_assert_preserves_original_panic :
    Sem.run (stepInst (.Assert ⟨0⟩ .DivByZero none) .le64) (assertionState false) =
      .error (.panic "attempt to divide by zero" none) := by rfl

theorem integer_condition_is_not_boolean_truthiness :
    Sem.run (stepInst (.Assert ⟨0⟩ .DivByZero none) .le64)
      (MachineState.empty.bindValue (.int 8 1)).2 =
      .error (.typeError "Assert: non-boolean condition") := by rfl

theorem mismatched_width_is_not_a_quotient :
    semBinOpValues .UDiv .U64 (.int 64 1) (.int 32 1) =
      .error (.typeError "BinOp: mismatched integer widths") := by rfl

theorem unsigned_opcode_reads_unsigned_residues :
    semBinOpValues .UDiv .I8 (.int 8 128) (.int 8 255) = .ok (.int 8 0) := by rfl

end TrustIr.UnsignedDivisionWp.Controls

#trustIrAxioms TrustIr.sem_run_bind_eq <= [propext, Classical.choice, Quot.sound]
#trustIrAxioms TrustIr.semAssertFail_run_not_ok <= [propext, Classical.choice, Quot.sound]
#trustIrAxioms TrustIr.assert_step_wp_iff <= [propext, Classical.choice, Quot.sound]
#trustIrAxioms TrustIr.UnsignedDivisionWp.quotient_range <= [propext, Classical.choice, Quot.sound]
#trustIrAxioms TrustIr.UnsignedDivisionWp.quotient_le_left <= [propext, Classical.choice, Quot.sound]
#trustIrAxioms TrustIr.UnsignedDivisionWp.value <= [propext, Classical.choice, Quot.sound]
#trustIrAxioms TrustIr.UnsignedDivisionWp.wp_iff <= [propext, Classical.choice, Quot.sound]
#trustIrAxioms TrustIr.UnsignedDivisionWp.u64_wp_iff <= [propext, Classical.choice, Quot.sound]
#trustIrAxioms TrustIr.UnsignedDivisionWp.dead_result_wp_iff <= [propext, Classical.choice, Quot.sound]
#trustIrAxioms TrustIr.UnsignedDivisionWp.zero <= [propext, Classical.choice, Quot.sound]
