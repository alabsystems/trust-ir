-- Copyright 2026 Andrew Yates | Apache-2.0
-- New actual decoded CFG correspondence and controls. The moved computational
-- declarations retain their original guard records in AxiomAudit.
import TrustIr.Proofs.DecodedCFGControls

/-- info: 'TrustIrEval.DecodedCFG.Controls.actual_duplicate_first_row' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIrEval.DecodedCFG.Controls.actual_duplicate_first_row

/-- info: 'TrustIrEval.DecodedCFG.Controls.actual_empty_cfg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIrEval.DecodedCFG.Controls.actual_empty_cfg

/-- info: 'TrustIrEval.DecodedCFG.Controls.actual_neighbor_missing' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIrEval.DecodedCFG.Controls.actual_neighbor_missing

/-- info: 'TrustIrEval.DecodedCFG.Controls.actual_sparse_high_row' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIrEval.DecodedCFG.Controls.actual_sparse_high_row

/-- info: 'TrustIrEval.DecodedCFG.Controls.actual_zero_row' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIrEval.DecodedCFG.Controls.actual_zero_row

/- Original legacy printer record, preserved verbatim:
/-- info: 'TrustIrEval.DecodedCFG.Controls.complete_context_original_spec' depends on axioms: [propext,
 Quot.sound,
 Classical.choice] -/
#guard_msgs in
#print axioms TrustIrEval.DecodedCFG.Controls.complete_context_original_spec
-/
#trustIrAxiomsExact TrustIrEval.DecodedCFG.Controls.complete_context_original_spec == [propext, Quot.sound, Classical.choice]

/-- info: 'TrustIrEval.DecodedCFG.Controls.original_missing_signature_error' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIrEval.DecodedCFG.Controls.original_missing_signature_error

/-- info: 'TrustIrEval.DecodedCFG.evalFunctionListSpec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIrEval.DecodedCFG.evalFunctionListSpec

/-- info: 'TrustIrEval.DecodedCFG.evalFunctionListSpec.match_1' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIrEval.DecodedCFG.evalFunctionListSpec.match_1

/-- info: 'TrustIrEval.DecodedCFG.evalFunctionListSpec.match_2' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIrEval.DecodedCFG.evalFunctionListSpec.match_2

/-- info: 'TrustIrEval.DecodedCFG.evalFunctionListSpec.match_3' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIrEval.DecodedCFG.evalFunctionListSpec.match_3

/-- info: 'TrustIrEval.DecodedCFG.evalFunctionOfWithTypes_eq_listSpec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIrEval.DecodedCFG.evalFunctionOfWithTypes_eq_listSpec

/-- info: 'TrustIrEval.DecodedCFG.indexedCFG_eq_cfgOf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIrEval.DecodedCFG.indexedCFG_eq_cfgOf
