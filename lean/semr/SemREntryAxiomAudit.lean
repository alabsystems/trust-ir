/- Copyright 2026 Andrew Yates. Apache-2.0.
   Mechanical transitive-axiom guards: no domain-specific axiom may replace
   the checked operational inversions. -/
import SemREntry

/-- info: 'SemR.EntryDomain.posOf_some_lookup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SemR.EntryDomain.posOf_some_lookup

/-- info: 'SemR.EntryDomain.nth_some_member' depends on axioms: [propext] -/
#guard_msgs in
#print axioms SemR.EntryDomain.nth_some_member

/-- info: 'SemR.EntryDomain.findEnum_identity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SemR.EntryDomain.findEnum_identity

/-- info: 'SemR.EntryDomain.activeFields_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SemR.EntryDomain.activeFields_exact

/-- info: 'SemR.EntryDomain.activeFields_declared_tag' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SemR.EntryDomain.activeFields_declared_tag

/-- info: 'SemR.EntryDomain.checkLane_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SemR.EntryDomain.checkLane_exact

/-- info: 'SemR.EntryDomain.checkLane_nominal_field' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SemR.EntryDomain.checkLane_nominal_field
