/- Exact transitive axiom guards for declaration/read/cast contracts. -/
import SemREnumDiscriminantCheck
set_option format.width 10000

/-- info: 'SemR.EntryDomain.enum_tag_read_success' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SemR.EntryDomain.enum_tag_read_success

/-- info: 'SemR.EntryDomain.checked_tag_cast' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SemR.EntryDomain.checked_tag_cast

/-- info: 'SemR.EntryDomain.enum_discriminant_cast' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SemR.EntryDomain.enum_discriminant_cast

/-- info: 'SemR.EnumDiscriminantCheck.actual_signed_read_32' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SemR.EnumDiscriminantCheck.actual_signed_read_32

/-- info: 'SemR.EnumDiscriminantCheck.actual_signed_read_64' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SemR.EnumDiscriminantCheck.actual_signed_read_64

/-- info: 'SemR.EnumDiscriminantCheck.connected_contract' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SemR.EnumDiscriminantCheck.connected_contract

/-- info: 'SemR.EnumDiscriminantCheck.unsigned_high_bit_is_not_signed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SemR.EnumDiscriminantCheck.unsigned_high_bit_is_not_signed

/-- info: 'SemR.EnumDiscriminantCheck.signed_zero_extension_is_wrong' depends on axioms: [propext] -/
#guard_msgs in
#print axioms SemR.EnumDiscriminantCheck.signed_zero_extension_is_wrong

/-- info: 'SemR.EnumDiscriminantCheck.signed_switch_first_case' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SemR.EnumDiscriminantCheck.signed_switch_first_case

/-- info: 'SemR.EnumDiscriminantCheck.wrong_extension_switch_misses' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SemR.EnumDiscriminantCheck.wrong_extension_switch_misses

/-- info: 'SemR.EnumDiscriminantCheck.unknown_tag_refuses' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SemR.EnumDiscriminantCheck.unknown_tag_refuses

/-- info: 'SemR.EnumDiscriminantCheck.unknown_nominal_refuses' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SemR.EnumDiscriminantCheck.unknown_nominal_refuses

/-- info: 'SemR.EnumDiscriminantCheck.unbounded_raw_read_refuses' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SemR.EnumDiscriminantCheck.unbounded_raw_read_refuses

/-- info: 'SemR.EnumDiscriminantCheck.unsigned_entry_source_width_keeps_its_value' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SemR.EnumDiscriminantCheck.unsigned_entry_source_width_keeps_its_value
