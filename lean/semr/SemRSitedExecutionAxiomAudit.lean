/- Copyright 2026 Andrew Yates. Apache-2.0. -/
import SemRSitedExecutionCheck

/-- info: 'SemR.step_complete' depends on axioms: [propext] -/
#guard_msgs in
#print axioms SemR.step_complete

/-- info: 'SemR.step_sound' depends on axioms: [propext] -/
#guard_msgs in
#print axioms SemR.step_sound

/-- info: 'SemR.run_sound' depends on axioms: [propext] -/
#guard_msgs in
#print axioms SemR.run_sound

/-- info: 'SemR.run_complete' depends on axioms: [propext] -/
#guard_msgs in
#print axioms SemR.run_complete

/-- info: 'SemR.returned_excludes_body_violation' depends on axioms: [propext] -/
#guard_msgs in
#print axioms SemR.returned_excludes_body_violation

/-- info: 'SemR.SitedExecution.word_typed' depends on axioms: [propext] -/
#guard_msgs in
#print axioms SemR.SitedExecution.word_typed

/-- info: 'SemR.SitedExecution.result_le' depends on axioms: [propext] -/
#guard_msgs in
#print axioms SemR.SitedExecution.result_le

/-- info: 'SemR.SitedExecution.result_bound' depends on axioms: [propext] -/
#guard_msgs in
#print axioms SemR.SitedExecution.result_bound

/-- info: 'SemR.SitedExecution.guard_value' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SemR.SitedExecution.guard_value

/-- info: 'SemR.SitedExecution.arithmetic_value' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SemR.SitedExecution.arithmetic_value

/-- info: 'SemR.SitedExecution.start_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SemR.SitedExecution.start_exact

/-- info: 'SemR.SitedExecution.nonzero_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SemR.SitedExecution.nonzero_run

/-- info: 'SemR.SitedExecution.zero_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SemR.SitedExecution.zero_run

/-- info: 'SemR.SitedExecution.nonzero_exec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SemR.SitedExecution.nonzero_exec

/-- info: 'SemR.SitedExecution.zero_exec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SemR.SitedExecution.zero_exec

/-- info: 'SemR.SitedExecution.nonzero_excludes_body_violation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SemR.SitedExecution.nonzero_excludes_body_violation

/-- info: 'SemR.SitedExecution.Check.div_contract' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SemR.SitedExecution.Check.div_contract

/-- info: 'SemR.SitedExecution.Check.rem_contract' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SemR.SitedExecution.Check.rem_contract

/-- info: 'SemR.SitedExecution.Check.zero_contract' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SemR.SitedExecution.Check.zero_contract

/-- info: 'SemR.SitedExecution.Check.no_bad_contract' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SemR.SitedExecution.Check.no_bad_contract

/-- info: 'SemR.SitedExecution.Check.nonzero_is_essential' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SemR.SitedExecution.Check.nonzero_is_essential

