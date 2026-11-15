-- Copyright 2026 Andrew Yates | Apache-2.0
-- Targeted runner-side audit, outside the default TrustIr core/JSON boundary.
-- Includes every actual public safe declaration attributed to the two new modules.
import TrustIrEval.ModuleRunBatchControls

/- Original legacy printer assertion, retained verbatim for provenance.
/-- info: 'TrustIrEval.ModuleRunBatch.Controls.actual_changed_module_positive' depends on axioms: [propext,
 Quot.sound,
 Classical.choice] -/
#guard_msgs in
#print axioms TrustIrEval.ModuleRunBatch.Controls.actual_changed_module_positive
-/
#trustIrAxiomsExact TrustIrEval.ModuleRunBatch.Controls.actual_changed_module_positive == [propext,
 Quot.sound,
 Classical.choice]

/- Original legacy printer assertion, retained verbatim for provenance.
/-- info: 'TrustIrEval.ModuleRunBatch.Controls.actual_duplicate_ready' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIrEval.ModuleRunBatch.Controls.actual_duplicate_ready
-/
#trustIrAxiomsExact TrustIrEval.ModuleRunBatch.Controls.actual_duplicate_ready == [propext, Classical.choice, Quot.sound]

/- Original legacy printer assertion, retained verbatim for provenance.
/-- info: 'TrustIrEval.ModuleRunBatch.Controls.actual_multifunction_batch' depends on axioms: [propext,
 Quot.sound,
 Classical.choice] -/
#guard_msgs in
#print axioms TrustIrEval.ModuleRunBatch.Controls.actual_multifunction_batch
-/
#trustIrAxiomsExact TrustIrEval.ModuleRunBatch.Controls.actual_multifunction_batch == [propext,
 Quot.sound,
 Classical.choice]

/- Original legacy printer assertion, retained verbatim for provenance.
/-- info: 'TrustIrEval.ModuleRunBatch.Controls.actual_partial_drop_ready' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIrEval.ModuleRunBatch.Controls.actual_partial_drop_ready
-/
#trustIrAxiomsExact TrustIrEval.ModuleRunBatch.Controls.actual_partial_drop_ready == [propext,
 Classical.choice,
 Quot.sound]

/- Original legacy printer assertion, retained verbatim for provenance.
/-- info: 'TrustIrEval.ModuleRunBatch.Controls.bodyless_entry_exact' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIrEval.ModuleRunBatch.Controls.bodyless_entry_exact
-/
#trustIrAxiomsExact TrustIrEval.ModuleRunBatch.Controls.bodyless_entry_exact == [propext, Quot.sound, Classical.choice]

/-- info: 'TrustIrEval.ModuleRunBatch.Controls.declaration' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIrEval.ModuleRunBatch.Controls.declaration

/-- info: 'TrustIrEval.ModuleRunBatch.Controls.dropBlock' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIrEval.ModuleRunBatch.Controls.dropBlock

/-- info: 'TrustIrEval.ModuleRunBatch.Controls.dropFunction' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIrEval.ModuleRunBatch.Controls.dropFunction

/-- info: 'TrustIrEval.ModuleRunBatch.Controls.dropSource' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIrEval.ModuleRunBatch.Controls.dropSource

/-- info: 'TrustIrEval.ModuleRunBatch.Controls.dropTarget' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIrEval.ModuleRunBatch.Controls.dropTarget

/-- info: 'TrustIrEval.ModuleRunBatch.Controls.duplicateModule' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIrEval.ModuleRunBatch.Controls.duplicateModule

/-- info: 'TrustIrEval.ModuleRunBatch.Controls.duplicate_raw_preflight' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIrEval.ModuleRunBatch.Controls.duplicate_raw_preflight

/- Original legacy printer assertion, retained verbatim for provenance.
/-- info: 'TrustIrEval.ModuleRunBatch.Controls.duplicate_success' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIrEval.ModuleRunBatch.Controls.duplicate_success
-/
#trustIrAxiomsExact TrustIrEval.ModuleRunBatch.Controls.duplicate_success == [propext, Quot.sound, Classical.choice]

/- Original legacy printer assertion, retained verbatim for provenance.
/-- info: 'TrustIrEval.ModuleRunBatch.Controls.duplicate_zero_fuel' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIrEval.ModuleRunBatch.Controls.duplicate_zero_fuel
-/
#trustIrAxiomsExact TrustIrEval.ModuleRunBatch.Controls.duplicate_zero_fuel == [propext, Quot.sound, Classical.choice]

/- Original legacy printer assertion, retained verbatim for provenance.
/-- info: 'TrustIrEval.ModuleRunBatch.Controls.empty_batch_context_error' depends on axioms: [propext,
 Quot.sound,
 Classical.choice] -/
#guard_msgs in
#print axioms TrustIrEval.ModuleRunBatch.Controls.empty_batch_context_error
-/
#trustIrAxiomsExact TrustIrEval.ModuleRunBatch.Controls.empty_batch_context_error == [propext,
 Quot.sound,
 Classical.choice]

/-- info: 'TrustIrEval.ModuleRunBatch.Controls.identity' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIrEval.ModuleRunBatch.Controls.identity

/- Original legacy printer assertion, retained verbatim for provenance.
/-- info: 'TrustIrEval.ModuleRunBatch.Controls.missing_entry_exact' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIrEval.ModuleRunBatch.Controls.missing_entry_exact
-/
#trustIrAxiomsExact TrustIrEval.ModuleRunBatch.Controls.missing_entry_exact == [propext, Quot.sound, Classical.choice]

/-- info: 'TrustIrEval.ModuleRunBatch.Controls.namespace_overflow_exact' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIrEval.ModuleRunBatch.Controls.namespace_overflow_exact

/- Original legacy printer assertion, retained verbatim for provenance.
/-- info: 'TrustIrEval.ModuleRunBatch.Controls.partial_drop_batch_priority' depends on axioms: [propext,
 Quot.sound,
 Classical.choice] -/
#guard_msgs in
#print axioms TrustIrEval.ModuleRunBatch.Controls.partial_drop_batch_priority
-/
#trustIrAxiomsExact TrustIrEval.ModuleRunBatch.Controls.partial_drop_batch_priority == [propext,
 Quot.sound,
 Classical.choice]

/-- info: 'TrustIrEval.ModuleRunBatch.Controls.partial_drop_source_preflight' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIrEval.ModuleRunBatch.Controls.partial_drop_source_preflight

/- Original legacy printer assertion, retained verbatim for provenance.
/-- info: 'TrustIrEval.ModuleRunBatch.Controls.partial_drop_target_preflight' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIrEval.ModuleRunBatch.Controls.partial_drop_target_preflight
-/
#trustIrAxiomsExact TrustIrEval.ModuleRunBatch.Controls.partial_drop_target_preflight == [propext,
 Classical.choice,
 Quot.sound]

/-- info: 'TrustIrEval.ModuleRunBatch.Controls.signature' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIrEval.ModuleRunBatch.Controls.signature

/-- info: 'TrustIrEval.ModuleRunBatch.blockDrops' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIrEval.ModuleRunBatch.blockDrops

/-- info: 'TrustIrEval.ModuleRunBatch.blockDrops.match_1' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIrEval.ModuleRunBatch.blockDrops.match_1

/-- info: 'TrustIrEval.ModuleRunBatch.blocksDrop_cons' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIrEval.ModuleRunBatch.blocksDrop_cons

/-- info: 'TrustIrEval.ModuleRunBatch.bodyObservation' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIrEval.ModuleRunBatch.bodyObservation

/-- info: 'TrustIrEval.ModuleRunBatch.calleeStep' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIrEval.ModuleRunBatch.calleeStep

/-- info: 'TrustIrEval.ModuleRunBatch.expandedEntry_blockDrops' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIrEval.ModuleRunBatch.expandedEntry_blockDrops

/- Original legacy printer assertion, retained verbatim for provenance.
/-- info: 'TrustIrEval.ModuleRunBatch.expandedEntry_blocksDrop' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIrEval.ModuleRunBatch.expandedEntry_blocksDrop
-/
#trustIrAxiomsExact TrustIrEval.ModuleRunBatch.expandedEntry_blocksDrop == [propext]

/- Original legacy printer assertion, retained verbatim for provenance.
/-- info: 'TrustIrEval.ModuleRunBatch.expandedEntry_calleeStep' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIrEval.ModuleRunBatch.expandedEntry_calleeStep
-/
#trustIrAxiomsExact TrustIrEval.ModuleRunBatch.expandedEntry_calleeStep == [propext, Quot.sound]

/- Original legacy printer assertion, retained verbatim for provenance.
/-- info: 'TrustIrEval.ModuleRunBatch.initialState_cleared' depends on axioms: [Classical.choice, propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIrEval.ModuleRunBatch.initialState_cleared
-/
#trustIrAxiomsPinned TrustIrEval.ModuleRunBatch.initialState_cleared == [Classical.choice, propext, Quot.sound] modern [propext]

/-- info: 'TrustIrEval.ModuleRunBatch.installFirst_runnerFields' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIrEval.ModuleRunBatch.installFirst_runnerFields

/- Original legacy printer assertion, retained verbatim for provenance.
/-- info: 'TrustIrEval.ModuleRunBatch.list_any_append' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIrEval.ModuleRunBatch.list_any_append
-/
#trustIrAxiomsExact TrustIrEval.ModuleRunBatch.list_any_append == [propext]

/- Original legacy printer assertion, retained verbatim for provenance.
/-- info: 'TrustIrEval.ModuleRunBatch.lowerFunction_bodyObservation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIrEval.ModuleRunBatch.lowerFunction_bodyObservation
-/
#trustIrAxiomsExact TrustIrEval.ModuleRunBatch.lowerFunction_bodyObservation == [propext, Classical.choice, Quot.sound]

/- Original legacy printer assertion, retained verbatim for provenance.
/-- info: 'TrustIrEval.ModuleRunBatch.plans_blocksDrop' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIrEval.ModuleRunBatch.plans_blocksDrop
-/
#trustIrAxiomsExact TrustIrEval.ModuleRunBatch.plans_blocksDrop == [propext, Quot.sound]

/- Original legacy printer assertion, retained verbatim for provenance.
/-- info: 'TrustIrEval.ModuleRunBatch.plans_callees' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIrEval.ModuleRunBatch.plans_callees
-/
#trustIrAxiomsExact TrustIrEval.ModuleRunBatch.plans_callees == [propext, Quot.sound]

/- Original legacy printer assertion, retained verbatim for provenance.
/-- info: 'TrustIrEval.ModuleRunBatch.produced_lookupObservation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIrEval.ModuleRunBatch.produced_lookupObservation
-/
#trustIrAxiomsExact TrustIrEval.ModuleRunBatch.produced_lookupObservation == [propext, Classical.choice, Quot.sound]

/- Original legacy printer assertion, retained verbatim for provenance.
/-- info: 'TrustIrEval.ModuleRunBatch.reachableGo_eq' depends on axioms: [Classical.choice, propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIrEval.ModuleRunBatch.reachableGo_eq
-/
#trustIrAxiomsPinned TrustIrEval.ModuleRunBatch.reachableGo_eq == [Classical.choice, propext, Quot.sound] modern [propext, Quot.sound]

/- Original legacy printer assertion, retained verbatim for provenance.
/-- info: 'TrustIrEval.ModuleRunBatch.reachableGo_step' depends on axioms: [Classical.choice, propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIrEval.ModuleRunBatch.reachableGo_step
-/
#trustIrAxiomsPinned TrustIrEval.ModuleRunBatch.reachableGo_step == [Classical.choice, propext, Quot.sound] modern [propext]

/-- info: 'TrustIrEval.ModuleRunBatch.reachableGo_step.match_1' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIrEval.ModuleRunBatch.reachableGo_step.match_1

/- Original legacy printer assertion, retained verbatim for provenance.
/-- info: 'TrustIrEval.ModuleRunBatch.transform_ready_reachableDecodeFailure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIrEval.ModuleRunBatch.transform_ready_reachableDecodeFailure
-/
#trustIrAxiomsExact TrustIrEval.ModuleRunBatch.transform_ready_reachableDecodeFailure == [propext,
 Classical.choice,
 Quot.sound]

/- Original legacy printer assertion, retained verbatim for provenance.
/-- info: 'TrustIrEval.ModuleRunBatch.transform_ready_runBatch' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIrEval.ModuleRunBatch.transform_ready_runBatch
-/
#trustIrAxiomsExact TrustIrEval.ModuleRunBatch.transform_ready_runBatch == [propext, Classical.choice, Quot.sound]

/- Original legacy printer assertion, retained verbatim for provenance.
/-- info: 'TrustIrEval.ModuleRunBatch.transform_ready_runOneWithInitialState' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIrEval.ModuleRunBatch.transform_ready_runOneWithInitialState
-/
#trustIrAxiomsExact TrustIrEval.ModuleRunBatch.transform_ready_runOneWithInitialState == [propext,
 Classical.choice,
 Quot.sound]

/- Original legacy printer assertion, retained verbatim for provenance.
/-- info: 'TrustIrEval.ModuleRunBatch.transform_ready_runnerFields' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIrEval.ModuleRunBatch.transform_ready_runnerFields
-/
#trustIrAxiomsExact TrustIrEval.ModuleRunBatch.transform_ready_runnerFields == [propext, Classical.choice, Quot.sound]

/- Original legacy printer assertion, retained verbatim for provenance.
/-- info: 'TrustIrEval.ModuleRunBatch.verdict_eq_of_entry_observe_eq' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIrEval.ModuleRunBatch.verdict_eq_of_entry_observe_eq
-/
#trustIrAxiomsExact TrustIrEval.ModuleRunBatch.verdict_eq_of_entry_observe_eq == [propext, Quot.sound, Classical.choice]

/-- info: 'TrustIrEval.ModuleRunBatch.verdict_eq_of_entry_observe_eq.match_1' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIrEval.ModuleRunBatch.verdict_eq_of_entry_observe_eq.match_1

/-- info: 'TrustIrEval.reachableDecodeFailure.go.eq_1' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIrEval.reachableDecodeFailure.go.eq_1

/- Original legacy printer assertion, retained verbatim for provenance.
/-- info: 'TrustIrEval.reachableDecodeFailure.go.eq_2' depends on axioms: [Quot.sound] -/
#guard_msgs in
#print axioms TrustIrEval.reachableDecodeFailure.go.eq_2
-/
#trustIrAxiomsPinned TrustIrEval.reachableDecodeFailure.go.eq_2 == [Quot.sound] modern []

/-- info: 'TrustIrEval.reachableDecodeFailure.go.eq_3' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIrEval.reachableDecodeFailure.go.eq_3
