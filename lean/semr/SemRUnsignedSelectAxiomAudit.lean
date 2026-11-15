/- Exact transitive Ax0 guards for every exported rule and its controls.
   A placeholder, native evaluator axiom, or new assumption fails this build. -/
import SemRUnsignedSelectCheck
set_option format.width 10000

/-- info: 'SemRUnsignedSelect.checkedUInt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SemRUnsignedSelect.checkedUInt

/-- info: 'SemRUnsignedSelect.constUInt_step' depends on axioms: [propext] -/
#guard_msgs in
#print axioms SemRUnsignedSelect.constUInt_step

/-- info: 'SemRUnsignedSelect.copyUInt_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SemRUnsignedSelect.copyUInt_step

/-- info: 'SemRUnsignedSelect.selectUInt_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SemRUnsignedSelect.selectUInt_step

/-- info: 'SemRUnsignedSelect.icmpEqUInt_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SemRUnsignedSelect.icmpEqUInt_step

/-- info: 'SemRUnsignedSelect.returnUInt_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SemRUnsignedSelect.returnUInt_step

/-- info: 'SemRUnsignedSelect.at_pc' depends on axioms: [propext] -/
#guard_msgs in
#print axioms SemRUnsignedSelect.at_pc

/-- info: 'SemRUnsignedSelect.constUInt_wp_step' depends on axioms: [propext] -/
#guard_msgs in
#print axioms SemRUnsignedSelect.constUInt_wp_step

/-- info: 'SemRUnsignedSelect.copyUInt_wp_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SemRUnsignedSelect.copyUInt_wp_step

/-- info: 'SemRUnsignedSelect.selectUInt_wp_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SemRUnsignedSelect.selectUInt_wp_step

/-- info: 'SemRUnsignedSelect.icmpEqUInt_wp_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SemRUnsignedSelect.icmpEqUInt_wp_step

/-- info: 'SemRUnsignedSelect.returnUInt_wp_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SemRUnsignedSelect.returnUInt_wp_step

/-- info: 'SemRUnsignedSelectCheck.symbolic_select' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SemRUnsignedSelectCheck.symbolic_select

/-- info: 'SemRUnsignedSelectCheck.u64_max_is_in_the_original_domain' does not depend on any axioms -/
#guard_msgs in
#print axioms SemRUnsignedSelectCheck.u64_max_is_in_the_original_domain

/-- info: 'SemRUnsignedSelectCheck.u64_max_const_exact' depends on axioms: [propext] -/
#guard_msgs in
#print axioms SemRUnsignedSelectCheck.u64_max_const_exact

/-- info: 'SemRUnsignedSelectCheck.u64_max_select_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SemRUnsignedSelectCheck.u64_max_select_exact

/-- info: 'SemRUnsignedSelectCheck.u64_max_compare_zero_is_false' depends on axioms: [propext] -/
#guard_msgs in
#print axioms SemRUnsignedSelectCheck.u64_max_compare_zero_is_false

/-- info: 'SemRUnsignedSelectCheck.u64_max_return_exact' depends on axioms: [propext] -/
#guard_msgs in
#print axioms SemRUnsignedSelectCheck.u64_max_return_exact

/-- info: 'SemRUnsignedSelectCheck.unselected_out_of_range_refuses' depends on axioms: [propext] -/
#guard_msgs in
#print axioms SemRUnsignedSelectCheck.unselected_out_of_range_refuses

/-- info: 'SemRUnsignedSelectCheck.unselected_wrong_width_refuses' depends on axioms: [propext] -/
#guard_msgs in
#print axioms SemRUnsignedSelectCheck.unselected_wrong_width_refuses

/-- info: 'SemRUnsignedSelectCheck.unselected_missing_value_refuses' depends on axioms: [propext] -/
#guard_msgs in
#print axioms SemRUnsignedSelectCheck.unselected_missing_value_refuses

/-- info: 'SemRUnsignedSelectCheck.integer_condition_refuses' depends on axioms: [propext] -/
#guard_msgs in
#print axioms SemRUnsignedSelectCheck.integer_condition_refuses

/-- info: 'SemRUnsignedSelectCheck.poisoned_condition_is_ub' depends on axioms: [propext] -/
#guard_msgs in
#print axioms SemRUnsignedSelectCheck.poisoned_condition_is_ub

/-- info: 'SemRUnsignedSelectCheck.missing_result_refuses' depends on axioms: [propext] -/
#guard_msgs in
#print axioms SemRUnsignedSelectCheck.missing_result_refuses

/-- info: 'SemRUnsignedSelectCheck.different_actual_instruction_cannot_supply_select_pc' does not depend on any axioms -/
#guard_msgs in
#print axioms SemRUnsignedSelectCheck.different_actual_instruction_cannot_supply_select_pc

/-- info: 'SemRUnsignedSelectCheck.swapped_arms_are_not_the_original_result' depends on axioms: [propext] -/
#guard_msgs in
#print axioms SemRUnsignedSelectCheck.swapped_arms_are_not_the_original_result

/-- info: 'SemRUnsignedSelectCheck.unselected_typed_poison_can_be_moved' depends on axioms: [propext] -/
#guard_msgs in
#print axioms SemRUnsignedSelectCheck.unselected_typed_poison_can_be_moved

/-- info: 'SemRUnsignedSelectCheck.selected_poison_return_is_ub' depends on axioms: [propext] -/
#guard_msgs in
#print axioms SemRUnsignedSelectCheck.selected_poison_return_is_ub

