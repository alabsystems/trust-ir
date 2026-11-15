-- Copyright 2026 Andrew Yates | Apache-2.0
-- Exact public-declaration guards for the shared decoded Module/coroutine bridge.
-- These are model proofs, not raw-entry refinement or native admission.
import TrustIr.DecodedModule
import TrustIr.DecodedContext
import TrustIr.Proofs.GenericCoroModuleFactory
import TrustIr.Proofs.GenericCoroModuleFactoryControls
import TrustIr.Proofs.GenericCoroAllBlocksContext
import TrustIr.Proofs.NatRBMapInsert
import TrustIr.Proofs.GenericCoroHeaderMaps
import TrustIr.Proofs.NatRBMapInsertControls
import TrustIr.Proofs.GenericCoroModuleContext
import TrustIr.Proofs.GenericCoroAllBlocksEntryEffects
import TrustIr.Proofs.GenericCoroEntryObservation
import TrustIr.Proofs.GenericCoroModuleEntryEffects
import TrustIr.Proofs.GenericCoroModuleContextControls

/-- info: 'Lean.RBNode.find.eq_1' does not depend on any axioms -/
#guard_msgs in
#print axioms Lean.RBNode.find.eq_1

/-- info: 'Lean.RBNode.find.eq_2' does not depend on any axioms -/
#guard_msgs in
#print axioms Lean.RBNode.find.eq_2

/-- info: 'Lean.RBNode.ins.eq_1' does not depend on any axioms -/
#guard_msgs in
#print axioms Lean.RBNode.ins.eq_1

/-- info: 'Lean.RBNode.ins.eq_2' does not depend on any axioms -/
#guard_msgs in
#print axioms Lean.RBNode.ins.eq_2

/-- info: 'Lean.RBNode.ins.eq_3' does not depend on any axioms -/
#guard_msgs in
#print axioms Lean.RBNode.ins.eq_3

/-- info: 'TrustIr.GenericCoro.AllBlocksContext.Controls.both_mutual_factory_results_are_expanded' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.AllBlocksContext.Controls.both_mutual_factory_results_are_expanded

/-- info: 'TrustIr.GenericCoro.AllBlocksContext.Controls.direct' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.AllBlocksContext.Controls.direct

/-- info: 'TrustIr.GenericCoro.AllBlocksContext.Controls.duplicate_key_composition_preserves_winning_occurrence' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.AllBlocksContext.Controls.duplicate_key_composition_preserves_winning_occurrence

/-- info: 'TrustIr.GenericCoro.AllBlocksContext.Controls.graph' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.AllBlocksContext.Controls.graph

/-- info: 'TrustIr.GenericCoro.AllBlocksContext.Controls.header' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.AllBlocksContext.Controls.header

/-- info: 'TrustIr.GenericCoro.AllBlocksContext.Controls.signature' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.AllBlocksContext.Controls.signature

/-- info: 'TrustIr.GenericCoro.AllBlocksContext.Controls.two_updated_mutual_entries_preserve_every_framed_call' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.AllBlocksContext.Controls.two_updated_mutual_entries_preserve_every_framed_call

/-- info: 'TrustIr.GenericCoro.AllBlocksContext.Controls.undefined_and_bodyless_other_entries_keep_exact_errors' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.AllBlocksContext.Controls.undefined_and_bodyless_other_entries_keep_exact_errors

/-- info: 'TrustIr.GenericCoro.AllBlocksContext.FactoryReplacement' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.AllBlocksContext.FactoryReplacement

/-- info: 'TrustIr.GenericCoro.AllBlocksContext.FactoryReplacement.framedCallsEquivalent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.AllBlocksContext.FactoryReplacement.framedCallsEquivalent

/-- info: 'TrustIr.GenericCoro.AllBlocksContext.FramedCallsEquivalent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.AllBlocksContext.FramedCallsEquivalent

/-- info: 'TrustIr.GenericCoro.AllBlocksContext.FramedCallsEquivalent.refl' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.AllBlocksContext.FramedCallsEquivalent.refl

/-- info: 'TrustIr.GenericCoro.AllBlocksContext.FramedCallsEquivalent.run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.AllBlocksContext.FramedCallsEquivalent.run

/-- info: 'TrustIr.GenericCoro.AllBlocksContext.FramedCallsEquivalent.symm' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.AllBlocksContext.FramedCallsEquivalent.symm

/-- info: 'TrustIr.GenericCoro.AllBlocksContext.FramedCallsEquivalent.trans' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.AllBlocksContext.FramedCallsEquivalent.trans

/-- info: 'TrustIr.GenericCoro.AllBlocksContext.FunctionUpdate' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.AllBlocksContext.FunctionUpdate

/-- info: 'TrustIr.GenericCoro.AllBlocksContext.FunctionUpdate.casesOn' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.AllBlocksContext.FunctionUpdate.casesOn

/-- info: 'TrustIr.GenericCoro.AllBlocksContext.FunctionUpdate.id' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.AllBlocksContext.FunctionUpdate.id

/-- info: 'TrustIr.GenericCoro.AllBlocksContext.FunctionUpdate.mk' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.AllBlocksContext.FunctionUpdate.mk

/-- info: 'TrustIr.GenericCoro.AllBlocksContext.FunctionUpdate.mk.inj' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.AllBlocksContext.FunctionUpdate.mk.inj

/-- info: 'TrustIr.GenericCoro.AllBlocksContext.FunctionUpdate.mk.injEq' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.AllBlocksContext.FunctionUpdate.mk.injEq

/-- info: 'TrustIr.GenericCoro.AllBlocksContext.FunctionUpdate.mk.sizeOf_spec' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.AllBlocksContext.FunctionUpdate.mk.sizeOf_spec

/-- info: 'TrustIr.GenericCoro.AllBlocksContext.FunctionUpdate.noConfusion' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.AllBlocksContext.FunctionUpdate.noConfusion

/-- info: 'TrustIr.GenericCoro.AllBlocksContext.FunctionUpdate.noConfusionType' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.AllBlocksContext.FunctionUpdate.noConfusionType

/-- info: 'TrustIr.GenericCoro.AllBlocksContext.FunctionUpdate.rec' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.AllBlocksContext.FunctionUpdate.rec

/-- info: 'TrustIr.GenericCoro.AllBlocksContext.FunctionUpdate.recOn' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.AllBlocksContext.FunctionUpdate.recOn

/-- info: 'TrustIr.GenericCoro.AllBlocksContext.FunctionUpdate.source' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.AllBlocksContext.FunctionUpdate.source

/-- info: 'TrustIr.GenericCoro.AllBlocksContext.FunctionUpdate.target' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.AllBlocksContext.FunctionUpdate.target

/-- info: 'TrustIr.GenericCoro.AllBlocksContext.functions_expanded_framedCallsEquivalent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.AllBlocksContext.functions_expanded_framedCallsEquivalent

/-- info: 'TrustIr.GenericCoro.AllBlocksContext.installFirst' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.AllBlocksContext.installFirst

/-- info: 'TrustIr.GenericCoro.AllBlocksContext.installFirst_framedCallsEquivalent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.AllBlocksContext.installFirst_framedCallsEquivalent

/-- info: 'TrustIr.GenericCoro.AllBlocksContext.installFirst_functions' depends on axioms: [Quot.sound, propext] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.AllBlocksContext.installFirst_functions

/-- info: 'TrustIr.GenericCoro.AllBlocksContext.installFirst_functions.match_1' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.AllBlocksContext.installFirst_functions.match_1

/-- info: 'TrustIr.GenericCoro.AllBlocksContext.lowerRows_framedCallsEquivalent' depends on axioms: [propext,
 Quot.sound,
 Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.AllBlocksContext.lowerRows_framedCallsEquivalent

/-- info: 'TrustIr.GenericCoro.HeaderMaps.firstValue_header' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.HeaderMaps.firstValue_header

/-- info: 'TrustIr.GenericCoro.HeaderMaps.localTypeHeadersOf_direct' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.HeaderMaps.localTypeHeadersOf_direct

/-- info: 'TrustIr.GenericCoro.HeaderMaps.localTypeHeadersOf_eq' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.HeaderMaps.localTypeHeadersOf_eq

/-- info: 'TrustIr.GenericCoro.HeaderMaps.localTypeHeadersOf_signatures' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.HeaderMaps.localTypeHeadersOf_signatures

/-- info: 'TrustIr.GenericCoro.HeaderMaps.original_fold_classifier' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.HeaderMaps.original_fold_classifier

/-- info: 'TrustIr.GenericCoro.ModuleContext.ContextCallsEquivalent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.ModuleContext.ContextCallsEquivalent

/-- info: 'TrustIr.GenericCoro.ModuleContext.ContextCallsEquivalent.match_1' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.ModuleContext.ContextCallsEquivalent.match_1

/-- info: 'TrustIr.GenericCoro.ModuleContext.EvaluatedOccurrence' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.ModuleContext.EvaluatedOccurrence

/-- info: 'TrustIr.GenericCoro.ModuleContext.lowerFunction_evaluated' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.ModuleContext.lowerFunction_evaluated

/-- info: 'TrustIr.GenericCoro.ModuleContext.lowerFunction_imageRoots' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.ModuleContext.lowerFunction_imageRoots

/-- info: 'TrustIr.GenericCoro.ModuleContext.produced_context_calls' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.ModuleContext.produced_context_calls

/-- info: 'TrustIr.GenericCoro.ModuleContext.produced_evaluated' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.ModuleContext.produced_evaluated

/-- info: 'TrustIr.GenericCoro.ModuleContext.transform_ready_context_calls' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.ModuleContext.transform_ready_context_calls

/-- info: 'TrustIr.GenericCoro.ModuleContext.transform_ready_runCallReq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.ModuleContext.transform_ready_runCallReq

/-- info: 'TrustIr.GenericCoro.ModuleFactory.Controls.absent_function_signature_refuses' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.ModuleFactory.Controls.absent_function_signature_refuses

/-- info: 'TrustIr.GenericCoro.ModuleFactory.Controls.actual_all_other_fields' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.ModuleFactory.Controls.actual_all_other_fields

/-- info: 'TrustIr.GenericCoro.ModuleFactory.Controls.actual_ast_headers_and_order' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.ModuleFactory.Controls.actual_ast_headers_and_order

/-- info: 'TrustIr.GenericCoro.ModuleFactory.Controls.actual_call_prefix_preparation_provenance' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.ModuleFactory.Controls.actual_call_prefix_preparation_provenance

/-- info: 'TrustIr.GenericCoro.ModuleFactory.Controls.actual_multifunction_ast' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.ModuleFactory.Controls.actual_multifunction_ast

/-- info: 'TrustIr.GenericCoro.ModuleFactory.Controls.actual_no_suspend_terminators' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.ModuleFactory.Controls.actual_no_suspend_terminators

/-- info: 'TrustIr.GenericCoro.ModuleFactory.Controls.actual_produced_not_assumed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.ModuleFactory.Controls.actual_produced_not_assumed

/-- info: 'TrustIr.GenericCoro.ModuleFactory.Controls.callPrefix' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.ModuleFactory.Controls.callPrefix

/-- info: 'TrustIr.GenericCoro.ModuleFactory.Controls.caller' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.ModuleFactory.Controls.caller

/-- info: 'TrustIr.GenericCoro.ModuleFactory.Controls.coroutine' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.ModuleFactory.Controls.coroutine

/-- info: 'TrustIr.GenericCoro.ModuleFactory.Controls.declaration' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.ModuleFactory.Controls.declaration

/-- info: 'TrustIr.GenericCoro.ModuleFactory.Controls.declaration_header_types_real_call_prefix' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.ModuleFactory.Controls.declaration_header_types_real_call_prefix

/-- info: 'TrustIr.GenericCoro.ModuleFactory.Controls.declarations_keep_bodyless_status' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.ModuleFactory.Controls.declarations_keep_bodyless_status

/-- info: 'TrustIr.GenericCoro.ModuleFactory.Controls.duplicate_function_occurrences_both_emitted' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.ModuleFactory.Controls.duplicate_function_occurrences_both_emitted

/-- info: 'TrustIr.GenericCoro.ModuleFactory.Controls.duplicate_id_first_missing_signature_stays_missing' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.ModuleFactory.Controls.duplicate_id_first_missing_signature_stays_missing

/-- info: 'TrustIr.GenericCoro.ModuleFactory.Controls.duplicate_id_first_signature_stays_first' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.ModuleFactory.Controls.duplicate_id_first_signature_stays_first

/-- info: 'TrustIr.GenericCoro.ModuleFactory.Controls.emitted' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.ModuleFactory.Controls.emitted

/-- info: 'TrustIr.GenericCoro.ModuleFactory.Controls.empty_module_identity' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.ModuleFactory.Controls.empty_module_identity

/-- info: 'TrustIr.GenericCoro.ModuleFactory.Controls.expandedCaller' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.ModuleFactory.Controls.expandedCaller

/-- info: 'TrustIr.GenericCoro.ModuleFactory.Controls.forged_declaration_has_explicit_error' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.ModuleFactory.Controls.forged_declaration_has_explicit_error

/-- info: 'TrustIr.GenericCoro.ModuleFactory.Controls.inference_failure_rolls_back' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.ModuleFactory.Controls.inference_failure_rolls_back

/-- info: 'TrustIr.GenericCoro.ModuleFactory.Controls.malformed_payload_is_not_relabelled' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.ModuleFactory.Controls.malformed_payload_is_not_relabelled

/-- info: 'TrustIr.GenericCoro.ModuleFactory.Controls.no_suspend_needs_no_capacity' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.ModuleFactory.Controls.no_suspend_needs_no_capacity

/-- info: 'TrustIr.GenericCoro.ModuleFactory.Controls.ordinary' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.ModuleFactory.Controls.ordinary

/-- info: 'TrustIr.GenericCoro.ModuleFactory.Controls.preparationTag' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.ModuleFactory.Controls.preparationTag

/-- info: 'TrustIr.GenericCoro.ModuleFactory.Controls.preparationTag.match_1' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.ModuleFactory.Controls.preparationTag.match_1

/-- info: 'TrustIr.GenericCoro.ModuleFactory.Controls.real_partial_capacity_certificate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.ModuleFactory.Controls.real_partial_capacity_certificate

/-- info: 'TrustIr.GenericCoro.ModuleFactory.Controls.retained_decode_failure_rolls_back' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.ModuleFactory.Controls.retained_decode_failure_rolls_back

/-- info: 'TrustIr.GenericCoro.ModuleFactory.Controls.source' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.ModuleFactory.Controls.source

/-- info: 'TrustIr.GenericCoro.ModuleFactory.Controls.source_error_precedes_zero_capacity' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.ModuleFactory.Controls.source_error_precedes_zero_capacity

/-- info: 'TrustIr.GenericCoro.ModuleFactory.Controls.target' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.ModuleFactory.Controls.target

/-- info: 'TrustIr.GenericCoro.ModuleFactory.FunctionHeader' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.ModuleFactory.FunctionHeader

/-- info: 'TrustIr.GenericCoro.ModuleFactory.FunctionLaw' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.ModuleFactory.FunctionLaw

/-- info: 'TrustIr.GenericCoro.ModuleFactory.FunctionsLaw' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.ModuleFactory.FunctionsLaw

/-- info: 'TrustIr.GenericCoro.ModuleFactory.FunctionsLaw.below' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.ModuleFactory.FunctionsLaw.below

/-- info: 'TrustIr.GenericCoro.ModuleFactory.FunctionsLaw.below.casesOn' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.ModuleFactory.FunctionsLaw.below.casesOn

/-- info: 'TrustIr.GenericCoro.ModuleFactory.FunctionsLaw.below.cons' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.ModuleFactory.FunctionsLaw.below.cons

/-- info: 'TrustIr.GenericCoro.ModuleFactory.FunctionsLaw.below.nil' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.ModuleFactory.FunctionsLaw.below.nil

/-- info: 'TrustIr.GenericCoro.ModuleFactory.FunctionsLaw.below.rec' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.ModuleFactory.FunctionsLaw.below.rec

/-- info: 'TrustIr.GenericCoro.ModuleFactory.FunctionsLaw.brecOn' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.ModuleFactory.FunctionsLaw.brecOn

/-- info: 'TrustIr.GenericCoro.ModuleFactory.FunctionsLaw.casesOn' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.ModuleFactory.FunctionsLaw.casesOn

/-- info: 'TrustIr.GenericCoro.ModuleFactory.FunctionsLaw.cons' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.ModuleFactory.FunctionsLaw.cons

/-- info: 'TrustIr.GenericCoro.ModuleFactory.FunctionsLaw.declarations' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.ModuleFactory.FunctionsLaw.declarations

/-- info: 'TrustIr.GenericCoro.ModuleFactory.FunctionsLaw.headerIndex' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.ModuleFactory.FunctionsLaw.headerIndex

/-- info: 'TrustIr.GenericCoro.ModuleFactory.FunctionsLaw.headers' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.ModuleFactory.FunctionsLaw.headers

/-- info: 'TrustIr.GenericCoro.ModuleFactory.FunctionsLaw.nil' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.ModuleFactory.FunctionsLaw.nil

/-- info: 'TrustIr.GenericCoro.ModuleFactory.FunctionsLaw.noSuspends' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.ModuleFactory.FunctionsLaw.noSuspends

/-- info: 'TrustIr.GenericCoro.ModuleFactory.FunctionsLaw.rec' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.ModuleFactory.FunctionsLaw.rec

/-- info: 'TrustIr.GenericCoro.ModuleFactory.FunctionsLaw.recOn' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.ModuleFactory.FunctionsLaw.recOn

/-- info: 'TrustIr.GenericCoro.ModuleFactory.Outcome' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.ModuleFactory.Outcome

/-- info: 'TrustIr.GenericCoro.ModuleFactory.Outcome.casesOn' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.ModuleFactory.Outcome.casesOn

/-- info: 'TrustIr.GenericCoro.ModuleFactory.Outcome.noConfusion' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.ModuleFactory.Outcome.noConfusion

/-- info: 'TrustIr.GenericCoro.ModuleFactory.Outcome.noConfusionType' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.ModuleFactory.Outcome.noConfusionType

/-- info: 'TrustIr.GenericCoro.ModuleFactory.Outcome.ready' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.ModuleFactory.Outcome.ready

/-- info: 'TrustIr.GenericCoro.ModuleFactory.Outcome.ready.inj' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.ModuleFactory.Outcome.ready.inj

/-- info: 'TrustIr.GenericCoro.ModuleFactory.Outcome.ready.injEq' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.ModuleFactory.Outcome.ready.injEq

/-- info: 'TrustIr.GenericCoro.ModuleFactory.Outcome.ready.sizeOf_spec' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.ModuleFactory.Outcome.ready.sizeOf_spec

/-- info: 'TrustIr.GenericCoro.ModuleFactory.Outcome.rec' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.ModuleFactory.Outcome.rec

/-- info: 'TrustIr.GenericCoro.ModuleFactory.Outcome.recOn' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.ModuleFactory.Outcome.recOn

/-- info: 'TrustIr.GenericCoro.ModuleFactory.Outcome.rejected' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.ModuleFactory.Outcome.rejected

/-- info: 'TrustIr.GenericCoro.ModuleFactory.Outcome.rejected.inj' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.ModuleFactory.Outcome.rejected.inj

/-- info: 'TrustIr.GenericCoro.ModuleFactory.Outcome.rejected.injEq' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.ModuleFactory.Outcome.rejected.injEq

/-- info: 'TrustIr.GenericCoro.ModuleFactory.Outcome.rejected.sizeOf_spec' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.ModuleFactory.Outcome.rejected.sizeOf_spec

/-- info: 'TrustIr.GenericCoro.ModuleFactory.PreparedAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.ModuleFactory.PreparedAt

/-- info: 'TrustIr.GenericCoro.ModuleFactory.Problem' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.ModuleFactory.Problem

/-- info: 'TrustIr.GenericCoro.ModuleFactory.Problem.capacity' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.ModuleFactory.Problem.capacity

/-- info: 'TrustIr.GenericCoro.ModuleFactory.Problem.capacity.inj' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.ModuleFactory.Problem.capacity.inj

/-- info: 'TrustIr.GenericCoro.ModuleFactory.Problem.capacity.injEq' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.ModuleFactory.Problem.capacity.injEq

/-- info: 'TrustIr.GenericCoro.ModuleFactory.Problem.capacity.sizeOf_spec' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.ModuleFactory.Problem.capacity.sizeOf_spec

/-- info: 'TrustIr.GenericCoro.ModuleFactory.Problem.casesOn' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.ModuleFactory.Problem.casesOn

/-- info: 'TrustIr.GenericCoro.ModuleFactory.Problem.decode' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.ModuleFactory.Problem.decode

/-- info: 'TrustIr.GenericCoro.ModuleFactory.Problem.decode.inj' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.ModuleFactory.Problem.decode.inj

/-- info: 'TrustIr.GenericCoro.ModuleFactory.Problem.decode.injEq' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.ModuleFactory.Problem.decode.injEq

/-- info: 'TrustIr.GenericCoro.ModuleFactory.Problem.decode.sizeOf_spec' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.ModuleFactory.Problem.decode.sizeOf_spec

/-- info: 'TrustIr.GenericCoro.ModuleFactory.Problem.inference' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.ModuleFactory.Problem.inference

/-- info: 'TrustIr.GenericCoro.ModuleFactory.Problem.inference.inj' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.ModuleFactory.Problem.inference.inj

/-- info: 'TrustIr.GenericCoro.ModuleFactory.Problem.inference.injEq' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.ModuleFactory.Problem.inference.injEq

/-- info: 'TrustIr.GenericCoro.ModuleFactory.Problem.inference.sizeOf_spec' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.ModuleFactory.Problem.inference.sizeOf_spec

/-- info: 'TrustIr.GenericCoro.ModuleFactory.Problem.noConfusion' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.ModuleFactory.Problem.noConfusion

/-- info: 'TrustIr.GenericCoro.ModuleFactory.Problem.noConfusionType' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.ModuleFactory.Problem.noConfusionType

/-- info: 'TrustIr.GenericCoro.ModuleFactory.Problem.rec' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.ModuleFactory.Problem.rec

/-- info: 'TrustIr.GenericCoro.ModuleFactory.Problem.recOn' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.ModuleFactory.Problem.recOn

/-- info: 'TrustIr.GenericCoro.ModuleFactory.Produced' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.ModuleFactory.Produced

/-- info: 'TrustIr.GenericCoro.ModuleFactory.Produced.below' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.ModuleFactory.Produced.below

/-- info: 'TrustIr.GenericCoro.ModuleFactory.Produced.below.casesOn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.ModuleFactory.Produced.below.casesOn

/-- info: 'TrustIr.GenericCoro.ModuleFactory.Produced.below.cons' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.ModuleFactory.Produced.below.cons

/-- info: 'TrustIr.GenericCoro.ModuleFactory.Produced.below.nil' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.ModuleFactory.Produced.below.nil

/-- info: 'TrustIr.GenericCoro.ModuleFactory.Produced.below.rec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.ModuleFactory.Produced.below.rec

/-- info: 'TrustIr.GenericCoro.ModuleFactory.Produced.brecOn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.ModuleFactory.Produced.brecOn

/-- info: 'TrustIr.GenericCoro.ModuleFactory.Produced.casesOn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.ModuleFactory.Produced.casesOn

/-- info: 'TrustIr.GenericCoro.ModuleFactory.Produced.cons' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.ModuleFactory.Produced.cons

/-- info: 'TrustIr.GenericCoro.ModuleFactory.Produced.nil' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.ModuleFactory.Produced.nil

/-- info: 'TrustIr.GenericCoro.ModuleFactory.Produced.prepared' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.ModuleFactory.Produced.prepared

/-- info: 'TrustIr.GenericCoro.ModuleFactory.Produced.rec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.ModuleFactory.Produced.rec

/-- info: 'TrustIr.GenericCoro.ModuleFactory.Produced.recOn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.ModuleFactory.Produced.recOn

/-- info: 'TrustIr.GenericCoro.ModuleFactory.RowExpansion' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.ModuleFactory.RowExpansion

/-- info: 'TrustIr.GenericCoro.ModuleFactory.RowExpansion.capacity' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.ModuleFactory.RowExpansion.capacity

/-- info: 'TrustIr.GenericCoro.ModuleFactory.RowExpansion.capacity.inj' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.ModuleFactory.RowExpansion.capacity.inj

/-- info: 'TrustIr.GenericCoro.ModuleFactory.RowExpansion.capacity.injEq' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.ModuleFactory.RowExpansion.capacity.injEq

/-- info: 'TrustIr.GenericCoro.ModuleFactory.RowExpansion.capacity.sizeOf_spec' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.ModuleFactory.RowExpansion.capacity.sizeOf_spec

/-- info: 'TrustIr.GenericCoro.ModuleFactory.RowExpansion.casesOn' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.ModuleFactory.RowExpansion.casesOn

/-- info: 'TrustIr.GenericCoro.ModuleFactory.RowExpansion.expanded' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.ModuleFactory.RowExpansion.expanded

/-- info: 'TrustIr.GenericCoro.ModuleFactory.RowExpansion.expanded.inj' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.ModuleFactory.RowExpansion.expanded.inj

/-- info: 'TrustIr.GenericCoro.ModuleFactory.RowExpansion.expanded.injEq' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.ModuleFactory.RowExpansion.expanded.injEq

/-- info: 'TrustIr.GenericCoro.ModuleFactory.RowExpansion.expanded.sizeOf_spec' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.ModuleFactory.RowExpansion.expanded.sizeOf_spec

/-- info: 'TrustIr.GenericCoro.ModuleFactory.RowExpansion.noConfusion' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.ModuleFactory.RowExpansion.noConfusion

/-- info: 'TrustIr.GenericCoro.ModuleFactory.RowExpansion.noConfusionType' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.ModuleFactory.RowExpansion.noConfusionType

/-- info: 'TrustIr.GenericCoro.ModuleFactory.RowExpansion.rec' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.ModuleFactory.RowExpansion.rec

/-- info: 'TrustIr.GenericCoro.ModuleFactory.RowExpansion.recOn' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.ModuleFactory.RowExpansion.recOn

/-- info: 'TrustIr.GenericCoro.ModuleFactory.RowExpansion.toFunctions' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.ModuleFactory.RowExpansion.toFunctions

/-- info: 'TrustIr.GenericCoro.ModuleFactory.RowExpansion.toFunctions.match_1' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.ModuleFactory.RowExpansion.toFunctions.match_1

/-- info: 'TrustIr.GenericCoro.ModuleFactory.RowExpansion.unchanged' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.ModuleFactory.RowExpansion.unchanged

/-- info: 'TrustIr.GenericCoro.ModuleFactory.RowExpansion.unchanged.inj' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.ModuleFactory.RowExpansion.unchanged.inj

/-- info: 'TrustIr.GenericCoro.ModuleFactory.RowExpansion.unchanged.injEq' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.ModuleFactory.RowExpansion.unchanged.injEq

/-- info: 'TrustIr.GenericCoro.ModuleFactory.RowExpansion.unchanged.sizeOf_spec' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.ModuleFactory.RowExpansion.unchanged.sizeOf_spec

/-- info: 'TrustIr.GenericCoro.ModuleFactory.RowsReady' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.ModuleFactory.RowsReady

/-- info: 'TrustIr.GenericCoro.ModuleFactory.directHeaders' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.ModuleFactory.directHeaders

/-- info: 'TrustIr.GenericCoro.ModuleFactory.firstHeader' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.ModuleFactory.firstHeader

/-- info: 'TrustIr.GenericCoro.ModuleFactory.firstHeader.eq_1' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.ModuleFactory.firstHeader.eq_1

/-- info: 'TrustIr.GenericCoro.ModuleFactory.firstHeader.eq_2' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.ModuleFactory.firstHeader.eq_2

/-- info: 'TrustIr.GenericCoro.ModuleFactory.firstHeader.match_1' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.ModuleFactory.firstHeader.match_1

/-- info: 'TrustIr.GenericCoro.ModuleFactory.functionHeader' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.ModuleFactory.functionHeader

/-- info: 'TrustIr.GenericCoro.ModuleFactory.headerIndex' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.ModuleFactory.headerIndex

/-- info: 'TrustIr.GenericCoro.ModuleFactory.headerIndex_find' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.ModuleFactory.headerIndex_find

/-- info: 'TrustIr.GenericCoro.ModuleFactory.lowerFunction' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.ModuleFactory.lowerFunction

/-- info: 'TrustIr.GenericCoro.ModuleFactory.lowerFunction.match_1' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.ModuleFactory.lowerFunction.match_1

/-- info: 'TrustIr.GenericCoro.ModuleFactory.lowerFunction.match_2' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.ModuleFactory.lowerFunction.match_2

/-- info: 'TrustIr.GenericCoro.ModuleFactory.lowerFunction.match_3' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.ModuleFactory.lowerFunction.match_3

/-- info: 'TrustIr.GenericCoro.ModuleFactory.lowerFunction_decode_error' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.ModuleFactory.lowerFunction_decode_error

/-- info: 'TrustIr.GenericCoro.ModuleFactory.lowerFunction_law' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.ModuleFactory.lowerFunction_law

/-- info: 'TrustIr.GenericCoro.ModuleFactory.lowerFunction_prepared' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.ModuleFactory.lowerFunction_prepared

/-- info: 'TrustIr.GenericCoro.ModuleFactory.lowerFunctionsLoop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.ModuleFactory.lowerFunctionsLoop

/-- info: 'TrustIr.GenericCoro.ModuleFactory.lowerFunctionsLoop.eq_1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.ModuleFactory.lowerFunctionsLoop.eq_1

/-- info: 'TrustIr.GenericCoro.ModuleFactory.lowerFunctionsLoop.eq_2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.ModuleFactory.lowerFunctionsLoop.eq_2

/-- info: 'TrustIr.GenericCoro.ModuleFactory.lowerFunctionsLoop.match_1' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.ModuleFactory.lowerFunctionsLoop.match_1

/-- info: 'TrustIr.GenericCoro.ModuleFactory.lowerFunctionsLoop_error' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.ModuleFactory.lowerFunctionsLoop_error

/-- info: 'TrustIr.GenericCoro.ModuleFactory.lowerFunctionsLoop_produced' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.ModuleFactory.lowerFunctionsLoop_produced

/-- info: 'TrustIr.GenericCoro.ModuleFactory.lowerFunctionsLoop_ready' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.ModuleFactory.lowerFunctionsLoop_ready

/-- info: 'TrustIr.GenericCoro.ModuleFactory.noSuspendBody' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.ModuleFactory.noSuspendBody

/-- info: 'TrustIr.GenericCoro.ModuleFactory.prepareRows' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.ModuleFactory.prepareRows

/-- info: 'TrustIr.GenericCoro.ModuleFactory.prepareRows.match_1' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.ModuleFactory.prepareRows.match_1

/-- info: 'TrustIr.GenericCoro.ModuleFactory.prepareRows.proof_1' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.ModuleFactory.prepareRows.proof_1

/-- info: 'TrustIr.GenericCoro.ModuleFactory.prepareRows_error_source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.ModuleFactory.prepareRows_error_source

/-- info: 'TrustIr.GenericCoro.ModuleFactory.prepareRows_ready' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.ModuleFactory.prepareRows_ready

/-- info: 'TrustIr.GenericCoro.ModuleFactory.prepareRows_toFunctions' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.ModuleFactory.prepareRows_toFunctions

/-- info: 'TrustIr.GenericCoro.ModuleFactory.sameHeader' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.ModuleFactory.sameHeader

/-- info: 'TrustIr.GenericCoro.ModuleFactory.sameHeader_header' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.ModuleFactory.sameHeader_header

/-- info: 'TrustIr.GenericCoro.ModuleFactory.sameHeader_id' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.ModuleFactory.sameHeader_id

/-- info: 'TrustIr.GenericCoro.ModuleFactory.sameHeader_ty' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.ModuleFactory.sameHeader_ty

/-- info: 'TrustIr.GenericCoro.ModuleFactory.suspendCount_zero_of_any' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.ModuleFactory.suspendCount_zero_of_any

/-- info: 'TrustIr.GenericCoro.ModuleFactory.transform' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.ModuleFactory.transform

/-- info: 'TrustIr.GenericCoro.ModuleFactory.transform.match_1' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.ModuleFactory.transform.match_1

/-- info: 'TrustIr.GenericCoro.ModuleFactory.transform_declarations' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.ModuleFactory.transform_declarations

/-- info: 'TrustIr.GenericCoro.ModuleFactory.transform_directHeaders' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.ModuleFactory.transform_directHeaders

/-- info: 'TrustIr.GenericCoro.ModuleFactory.transform_headers' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.ModuleFactory.transform_headers

/-- info: 'TrustIr.GenericCoro.ModuleFactory.transform_noSuspends' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.ModuleFactory.transform_noSuspends

/-- info: 'TrustIr.GenericCoro.ModuleFactory.transform_produced' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.ModuleFactory.transform_produced

/-- info: 'TrustIr.GenericCoro.ModuleFactory.transform_ready' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.ModuleFactory.transform_ready

/-- info: 'TrustIr.GenericCoro.ModuleFactory.transform_rejected_at' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.ModuleFactory.transform_rejected_at

/-- info: 'TrustIr.GenericCoro.ModuleFactory.transform_rejected_original' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.ModuleFactory.transform_rejected_original

/-- info: 'TrustIr.NatRBMapInsert.Ascending' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.NatRBMapInsert.Ascending

/-- info: 'TrustIr.NatRBMapInsert.Ascending.below' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.NatRBMapInsert.Ascending.below

/-- info: 'TrustIr.NatRBMapInsert.Ascending.below.casesOn' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.NatRBMapInsert.Ascending.below.casesOn

/-- info: 'TrustIr.NatRBMapInsert.Ascending.below.cons' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.NatRBMapInsert.Ascending.below.cons

/-- info: 'TrustIr.NatRBMapInsert.Ascending.below.nil' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.NatRBMapInsert.Ascending.below.nil

/-- info: 'TrustIr.NatRBMapInsert.Ascending.below.rec' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.NatRBMapInsert.Ascending.below.rec

/-- info: 'TrustIr.NatRBMapInsert.Ascending.brecOn' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.NatRBMapInsert.Ascending.brecOn

/-- info: 'TrustIr.NatRBMapInsert.Ascending.casesOn' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.NatRBMapInsert.Ascending.casesOn

/-- info: 'TrustIr.NatRBMapInsert.Ascending.cons' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.NatRBMapInsert.Ascending.cons

/-- info: 'TrustIr.NatRBMapInsert.Ascending.cross' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.NatRBMapInsert.Ascending.cross

/-- info: 'TrustIr.NatRBMapInsert.Ascending.insert_rows' depends on axioms: [Classical.choice, propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.NatRBMapInsert.Ascending.insert_rows

/-- info: 'TrustIr.NatRBMapInsert.Ascending.insert_rows.match_1' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.NatRBMapInsert.Ascending.insert_rows.match_1

/-- info: 'TrustIr.NatRBMapInsert.Ascending.left' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.NatRBMapInsert.Ascending.left

/-- info: 'TrustIr.NatRBMapInsert.Ascending.nil' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.NatRBMapInsert.Ascending.nil

/-- info: 'TrustIr.NatRBMapInsert.Ascending.rec' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.NatRBMapInsert.Ascending.rec

/-- info: 'TrustIr.NatRBMapInsert.Ascending.recOn' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.NatRBMapInsert.Ascending.recOn

/-- info: 'TrustIr.NatRBMapInsert.Ascending.right' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.NatRBMapInsert.Ascending.right

/-- info: 'TrustIr.NatRBMapInsert.Controls.actual_duplicate_function_header_classifier' depends on axioms: [propext,
 Quot.sound,
 Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.NatRBMapInsert.Controls.actual_duplicate_function_header_classifier

/-- info: 'TrustIr.NatRBMapInsert.Controls.actual_original_helper_duplicate_control' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.NatRBMapInsert.Controls.actual_original_helper_duplicate_control

/-- info: 'TrustIr.NatRBMapInsert.Controls.actual_original_helper_instantiates_classifier_bridge' depends on axioms: [propext,
 Quot.sound,
 Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.NatRBMapInsert.Controls.actual_original_helper_instantiates_classifier_bridge

/-- info: 'TrustIr.NatRBMapInsert.Controls.duplicate_insert_overwrites_only_selected_key' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.NatRBMapInsert.Controls.duplicate_insert_overwrites_only_selected_key

/-- info: 'TrustIr.NatRBMapInsert.Controls.first_missing_function_signature_not_recovered' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.NatRBMapInsert.Controls.first_missing_function_signature_not_recovered

/-- info: 'TrustIr.NatRBMapInsert.Controls.first_none_payload_is_occupied' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.NatRBMapInsert.Controls.first_none_payload_is_occupied

/-- info: 'TrustIr.NatRBMapInsert.Controls.first_wins_and_missing' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.NatRBMapInsert.Controls.first_wins_and_missing

/-- info: 'TrustIr.NatRBMapInsert.Controls.four_actual_rotation_paths' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.NatRBMapInsert.Controls.four_actual_rotation_paths

/-- info: 'TrustIr.NatRBMapInsert.Controls.function' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.NatRBMapInsert.Controls.function

/-- info: 'TrustIr.NatRBMapInsert.Controls.insertAllFrom' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.NatRBMapInsert.Controls.insertAllFrom

/-- info: 'TrustIr.NatRBMapInsert.Controls.insertAllFrom_history' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.NatRBMapInsert.Controls.insertAllFrom_history

/-- info: 'TrustIr.NatRBMapInsert.Controls.mapOf' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.NatRBMapInsert.Controls.mapOf

/-- info: 'TrustIr.NatRBMapInsert.Controls.mapOf_history' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.NatRBMapInsert.Controls.mapOf_history

/-- info: 'TrustIr.NatRBMapInsert.Controls.module' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.NatRBMapInsert.Controls.module

/-- info: 'TrustIr.NatRBMapInsert.Controls.optionEntries' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.NatRBMapInsert.Controls.optionEntries

/-- info: 'TrustIr.NatRBMapInsert.Controls.overwrite_after_rotation' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.NatRBMapInsert.Controls.overwrite_after_rotation

/-- info: 'TrustIr.NatRBMapInsert.Controls.overwrite_exact_others_retained' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.NatRBMapInsert.Controls.overwrite_exact_others_retained

/-- info: 'TrustIr.NatRBMapInsert.Controls.signatures' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.NatRBMapInsert.Controls.signatures

/-- info: 'TrustIr.NatRBMapInsert.Controls.sparse_high_keys' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.NatRBMapInsert.Controls.sparse_high_keys

/-- info: 'TrustIr.NatRBMapInsert.Controls.unordered_node_is_not_covered' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.NatRBMapInsert.Controls.unordered_node_is_not_covered

/-- info: 'TrustIr.NatRBMapInsert.InsertOnly' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.NatRBMapInsert.InsertOnly

/-- info: 'TrustIr.NatRBMapInsert.InsertOnly.below' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.NatRBMapInsert.InsertOnly.below

/-- info: 'TrustIr.NatRBMapInsert.InsertOnly.below.casesOn' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.NatRBMapInsert.InsertOnly.below.casesOn

/-- info: 'TrustIr.NatRBMapInsert.InsertOnly.below.empty' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.NatRBMapInsert.InsertOnly.below.empty

/-- info: 'TrustIr.NatRBMapInsert.InsertOnly.below.insert' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.NatRBMapInsert.InsertOnly.below.insert

/-- info: 'TrustIr.NatRBMapInsert.InsertOnly.below.rec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.NatRBMapInsert.InsertOnly.below.rec

/-- info: 'TrustIr.NatRBMapInsert.InsertOnly.brecOn' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.NatRBMapInsert.InsertOnly.brecOn

/-- info: 'TrustIr.NatRBMapInsert.InsertOnly.casesOn' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.NatRBMapInsert.InsertOnly.casesOn

/-- info: 'TrustIr.NatRBMapInsert.InsertOnly.empty' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.NatRBMapInsert.InsertOnly.empty

/-- info: 'TrustIr.NatRBMapInsert.InsertOnly.insert' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.NatRBMapInsert.InsertOnly.insert

/-- info: 'TrustIr.NatRBMapInsert.InsertOnly.ordered' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.NatRBMapInsert.InsertOnly.ordered

/-- info: 'TrustIr.NatRBMapInsert.InsertOnly.rec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.NatRBMapInsert.InsertOnly.rec

/-- info: 'TrustIr.NatRBMapInsert.InsertOnly.recOn' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.NatRBMapInsert.InsertOnly.recOn

/-- info: 'TrustIr.NatRBMapInsert.Ordered' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.NatRBMapInsert.Ordered

/-- info: 'TrustIr.NatRBMapInsert.find?_empty' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.NatRBMapInsert.find?_empty

/-- info: 'TrustIr.NatRBMapInsert.find?_insert' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.NatRBMapInsert.find?_insert

/-- info: 'TrustIr.NatRBMapInsert.find_eq_lookupRows' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.NatRBMapInsert.find_eq_lookupRows

/-- info: 'TrustIr.NatRBMapInsert.find_insert' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.NatRBMapInsert.find_insert

/-- info: 'TrustIr.NatRBMapInsert.firstValue' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.NatRBMapInsert.firstValue

/-- info: 'TrustIr.NatRBMapInsert.firstValue.eq_1' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.NatRBMapInsert.firstValue.eq_1

/-- info: 'TrustIr.NatRBMapInsert.firstValue.eq_2' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.NatRBMapInsert.firstValue.eq_2

/-- info: 'TrustIr.NatRBMapInsert.firstValue.match_1' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.NatRBMapInsert.firstValue.match_1

/-- info: 'TrustIr.NatRBMapInsert.firstWinsFrom' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.NatRBMapInsert.firstWinsFrom

/-- info: 'TrustIr.NatRBMapInsert.firstWinsFrom_find' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.NatRBMapInsert.firstWinsFrom_find

/-- info: 'TrustIr.NatRBMapInsert.firstWinsFrom_insertOnly' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.NatRBMapInsert.firstWinsFrom_insertOnly

/-- info: 'TrustIr.NatRBMapInsert.firstWins_empty_find' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.NatRBMapInsert.firstWins_empty_find

/-- info: 'TrustIr.NatRBMapInsert.insertRows' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.NatRBMapInsert.insertRows

/-- info: 'TrustIr.NatRBMapInsert.insertRows.eq_1' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.NatRBMapInsert.insertRows.eq_1

/-- info: 'TrustIr.NatRBMapInsert.insertRows.eq_2' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.NatRBMapInsert.insertRows.eq_2

/-- info: 'TrustIr.NatRBMapInsert.insertRows.match_1' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.NatRBMapInsert.insertRows.match_1

/-- info: 'TrustIr.NatRBMapInsert.insertRows.match_2' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.NatRBMapInsert.insertRows.match_2

/-- info: 'TrustIr.NatRBMapInsert.insertRows_append_before' depends on axioms: [Classical.choice, propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.NatRBMapInsert.insertRows_append_before

/-- info: 'TrustIr.NatRBMapInsert.insertRows_mem' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.NatRBMapInsert.insertRows_mem

/-- info: 'TrustIr.NatRBMapInsert.insertRows_skip_prefix' depends on axioms: [Classical.choice, propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.NatRBMapInsert.insertRows_skip_prefix

/-- info: 'TrustIr.NatRBMapInsert.lookupRows' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.NatRBMapInsert.lookupRows

/-- info: 'TrustIr.NatRBMapInsert.lookupRows.eq_1' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.NatRBMapInsert.lookupRows.eq_1

/-- info: 'TrustIr.NatRBMapInsert.lookupRows.eq_2' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.NatRBMapInsert.lookupRows.eq_2

/-- info: 'TrustIr.NatRBMapInsert.lookupRows.match_1' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.NatRBMapInsert.lookupRows.match_1

/-- info: 'TrustIr.NatRBMapInsert.lookupRows_append' depends on axioms: [Classical.choice, propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.NatRBMapInsert.lookupRows_append

/-- info: 'TrustIr.NatRBMapInsert.lookupRows_append.match_1' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.NatRBMapInsert.lookupRows_append.match_1

/-- info: 'TrustIr.NatRBMapInsert.lookupRows_insert' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.NatRBMapInsert.lookupRows_insert

/-- info: 'TrustIr.NatRBMapInsert.lookupRows_none' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.NatRBMapInsert.lookupRows_none

/-- info: 'TrustIr.NatRBMapInsert.ordered_insert' depends on axioms: [Classical.choice, propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.NatRBMapInsert.ordered_insert

/-- info: 'TrustIr.NatRBMapInsert.ordered_node' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.NatRBMapInsert.ordered_node

/-- info: 'TrustIr.NatRBMapInsert.prefer' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.NatRBMapInsert.prefer

/-- info: 'TrustIr.NatRBMapInsert.prefer.match_1' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.NatRBMapInsert.prefer.match_1

/-- info: 'TrustIr.NatRBMapInsert.rows' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.NatRBMapInsert.rows

/-- info: 'TrustIr.NatRBMapInsert.rows.eq_1' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.NatRBMapInsert.rows.eq_1

/-- info: 'TrustIr.NatRBMapInsert.rows.eq_2' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.NatRBMapInsert.rows.eq_2

/-- info: 'TrustIr.NatRBMapInsert.rows.match_1' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.NatRBMapInsert.rows.match_1

/-- info: 'TrustIr.NatRBMapInsert.rows_balance1' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.NatRBMapInsert.rows_balance1

/-- info: 'TrustIr.NatRBMapInsert.rows_balance2' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.NatRBMapInsert.rows_balance2

/-- info: 'TrustIr.NatRBMapInsert.rows_ins' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.NatRBMapInsert.rows_ins

/-- info: 'TrustIr.NatRBMapInsert.rows_insert' depends on axioms: [Classical.choice, propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.NatRBMapInsert.rows_insert

/-- info: 'TrustIr.NatRBMapInsert.rows_setBlack' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.NatRBMapInsert.rows_setBlack

/-- info: 'TrustIrEval.D' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIrEval.D

/-- info: 'TrustIrEval.DecodeError' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIrEval.DecodeError

/-- info: 'TrustIrEval.DecodeError.casesOn' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIrEval.DecodeError.casesOn

/-- info: 'TrustIrEval.DecodeError.malformed' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIrEval.DecodeError.malformed

/-- info: 'TrustIrEval.DecodeError.malformed.inj' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIrEval.DecodeError.malformed.inj

/-- info: 'TrustIrEval.DecodeError.malformed.injEq' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIrEval.DecodeError.malformed.injEq

/-- info: 'TrustIrEval.DecodeError.malformed.sizeOf_spec' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIrEval.DecodeError.malformed.sizeOf_spec

/-- info: 'TrustIrEval.DecodeError.noConfusion' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIrEval.DecodeError.noConfusion

/-- info: 'TrustIrEval.DecodeError.noConfusionType' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIrEval.DecodeError.noConfusionType

/-- info: 'TrustIrEval.DecodeError.rec' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIrEval.DecodeError.rec

/-- info: 'TrustIrEval.DecodeError.recOn' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIrEval.DecodeError.recOn

/-- info: 'TrustIrEval.DecodeError.unsupported' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIrEval.DecodeError.unsupported

/-- info: 'TrustIrEval.DecodeError.unsupported.inj' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIrEval.DecodeError.unsupported.inj

/-- info: 'TrustIrEval.DecodeError.unsupported.injEq' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIrEval.DecodeError.unsupported.injEq

/-- info: 'TrustIrEval.DecodeError.unsupported.sizeOf_spec' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIrEval.DecodeError.unsupported.sizeOf_spec

/-- info: 'TrustIrEval.Function' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIrEval.Function

/-- info: 'TrustIrEval.Function.blocks' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIrEval.Function.blocks

/-- info: 'TrustIrEval.Function.callingConvention' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIrEval.Function.callingConvention

/-- info: 'TrustIrEval.Function.casesOn' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIrEval.Function.casesOn

/-- info: 'TrustIrEval.Function.entry' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIrEval.Function.entry

/-- info: 'TrustIrEval.Function.id' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIrEval.Function.id

/-- info: 'TrustIrEval.Function.isDeclaration' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIrEval.Function.isDeclaration

/-- info: 'TrustIrEval.Function.mk' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIrEval.Function.mk

/-- info: 'TrustIrEval.Function.mk.inj' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIrEval.Function.mk.inj

/-- info: 'TrustIrEval.Function.mk.injEq' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIrEval.Function.mk.injEq

/-- info: 'TrustIrEval.Function.mk.sizeOf_spec' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIrEval.Function.mk.sizeOf_spec

/-- info: 'TrustIrEval.Function.name' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIrEval.Function.name

/-- info: 'TrustIrEval.Function.noConfusion' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIrEval.Function.noConfusion

/-- info: 'TrustIrEval.Function.noConfusionType' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIrEval.Function.noConfusionType

/-- info: 'TrustIrEval.Function.rec' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIrEval.Function.rec

/-- info: 'TrustIrEval.Function.recOn' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIrEval.Function.recOn

/-- info: 'TrustIrEval.Function.ty' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIrEval.Function.ty

/-- info: 'TrustIrEval.Module' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIrEval.Module

/-- info: 'TrustIrEval.Module.byteModel' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIrEval.Module.byteModel

/-- info: 'TrustIrEval.Module.casesOn' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIrEval.Module.casesOn

/-- info: 'TrustIrEval.Module.closureLayouts' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIrEval.Module.closureLayouts

/-- info: 'TrustIrEval.Module.closureTys' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIrEval.Module.closureTys

/-- info: 'TrustIrEval.Module.dropGlue' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIrEval.Module.dropGlue

/-- info: 'TrustIrEval.Module.enums' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIrEval.Module.enums

/-- info: 'TrustIrEval.Module.funcTys' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIrEval.Module.funcTys

/-- info: 'TrustIrEval.Module.functions' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIrEval.Module.functions

/-- info: 'TrustIrEval.Module.globals' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIrEval.Module.globals

/-- info: 'TrustIrEval.Module.hasTargetInfo' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIrEval.Module.hasTargetInfo

/-- info: 'TrustIrEval.Module.mk' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIrEval.Module.mk

/-- info: 'TrustIrEval.Module.mk.inj' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIrEval.Module.mk.inj

/-- info: 'TrustIrEval.Module.mk.injEq' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIrEval.Module.mk.injEq

/-- info: 'TrustIrEval.Module.mk.sizeOf_spec' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIrEval.Module.mk.sizeOf_spec

/-- info: 'TrustIrEval.Module.noConfusion' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIrEval.Module.noConfusion

/-- info: 'TrustIrEval.Module.noConfusionType' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIrEval.Module.noConfusionType

/-- info: 'TrustIrEval.Module.rec' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIrEval.Module.rec

/-- info: 'TrustIrEval.Module.recOn' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIrEval.Module.recOn

/-- info: 'TrustIrEval.Module.records' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIrEval.Module.records

/-- info: 'TrustIrEval.Module.structs' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIrEval.Module.structs

/-- info: 'TrustIrEval.Module.tupleLayouts' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIrEval.Module.tupleLayouts

/-- info: 'TrustIrEval.Module.types' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIrEval.Module.types

/-- info: 'TrustIrEval.Node' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIrEval.Node

/-- info: 'TrustIrEval.Node.casesOn' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIrEval.Node.casesOn

/-- info: 'TrustIrEval.Node.inst' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIrEval.Node.inst

/-- info: 'TrustIrEval.Node.mk' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIrEval.Node.mk

/-- info: 'TrustIrEval.Node.mk.inj' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIrEval.Node.mk.inj

/-- info: 'TrustIrEval.Node.mk.injEq' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIrEval.Node.mk.injEq

/-- info: 'TrustIrEval.Node.mk.sizeOf_spec' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIrEval.Node.mk.sizeOf_spec

/-- info: 'TrustIrEval.Node.noConfusion' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIrEval.Node.noConfusion

/-- info: 'TrustIrEval.Node.noConfusionType' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIrEval.Node.noConfusionType

/-- info: 'TrustIrEval.Node.rec' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIrEval.Node.rec

/-- info: 'TrustIrEval.Node.recOn' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIrEval.Node.recOn

/-- info: 'TrustIrEval.Node.results' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIrEval.Node.results

/-- info: 'TrustIrEval.blocksDrop' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIrEval.blocksDrop

/-- info: 'TrustIrEval.blocksDrop.match_1' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIrEval.blocksDrop.match_1

/-- info: 'TrustIrEval.calleesOf' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIrEval.calleesOf

/-- info: 'TrustIrEval.calleesOf.match_1' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIrEval.calleesOf.match_1

/-- info: 'TrustIrEval.calleesOfInst' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIrEval.calleesOfInst

/-- info: 'TrustIrEval.calleesOfInst.match_1' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIrEval.calleesOfInst.match_1

/-- info: 'TrustIrEval.cfgOf' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIrEval.cfgOf

/-- info: 'TrustIrEval.contextOf' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIrEval.contextOf

/-- info: 'TrustIrEval.contextOf.match_1' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIrEval.contextOf.match_1

/-- info: 'TrustIrEval.FunctionLookup.findFunction.match_1' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIrEval.FunctionLookup.findFunction.match_1

/-- info: 'TrustIrEval.FunctionLookup.findError.match_1' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIrEval.FunctionLookup.findError.match_1

/-- info: 'TrustIrEval.FunctionLookup.findError.match_2' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIrEval.FunctionLookup.findError.match_2

/-- info: 'TrustIrEval.FunctionLookup.prepareSourceFrom.match_1' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIrEval.FunctionLookup.prepareSourceFrom.match_1

/-- info: 'TrustIrEval.dropGlueOf' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIrEval.dropGlueOf

/-- info: 'TrustIrEval.evalFunctionOf' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIrEval.evalFunctionOf

/-- info: 'TrustIrEval.evalFunctionOf.match_1' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIrEval.evalFunctionOf.match_1

/-- info: 'TrustIrEval.evalFunctionOfWithTypes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIrEval.evalFunctionOfWithTypes

/-- info: 'TrustIrEval.evalFunctionOfWithTypes.match_1' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIrEval.evalFunctionOfWithTypes.match_1

/-- info: 'TrustIrEval.evalFunctionOfWithTypes.match_2' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIrEval.evalFunctionOfWithTypes.match_2

/-- info: 'TrustIrEval.instInhabitedDecodeError' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIrEval.instInhabitedDecodeError

/-- info: 'TrustIrEval.instReprDecodeError' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIrEval.instReprDecodeError

/-- info: 'TrustIrEval.localTypeHeadersOf' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIrEval.localTypeHeadersOf

/-- info: 'TrustIrEval.malformed' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIrEval.malformed

/-- info: 'TrustIrEval.memoryRootsOfInst_eq' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIrEval.memoryRootsOfInst_eq

/-- info: 'TrustIrEval.memoryServiceOf_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIrEval.memoryServiceOf_eq

/-- info: 'TrustIrEval.unsupported' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIrEval.unsupported


-- Actual raw-entry effects and public entry observation.

/-- info: 'TrustIr.GenericCoro.AllBlocksEntryEffects.Controls.mutual_factories_and_duplicate_have_raw_entry_effects' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.AllBlocksEntryEffects.Controls.mutual_factories_and_duplicate_have_raw_entry_effects

/-- info: 'TrustIr.GenericCoro.AllBlocksEntryEffects.EntryEffects' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.AllBlocksEntryEffects.EntryEffects

/-- info: 'TrustIr.GenericCoro.AllBlocksEntryEffects.EntryEffects.casesOn' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.AllBlocksEntryEffects.EntryEffects.casesOn

/-- info: 'TrustIr.GenericCoro.AllBlocksEntryEffects.EntryEffects.effects' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.AllBlocksEntryEffects.EntryEffects.effects

/-- info: 'TrustIr.GenericCoro.AllBlocksEntryEffects.EntryEffects.headers' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.AllBlocksEntryEffects.EntryEffects.headers

/-- info: 'TrustIr.GenericCoro.AllBlocksEntryEffects.EntryEffects.maxDepth' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.AllBlocksEntryEffects.EntryEffects.maxDepth

/-- info: 'TrustIr.GenericCoro.AllBlocksEntryEffects.EntryEffects.mk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.AllBlocksEntryEffects.EntryEffects.mk

/-- info: 'TrustIr.GenericCoro.AllBlocksEntryEffects.EntryEffects.noConfusion' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.AllBlocksEntryEffects.EntryEffects.noConfusion

/-- info: 'TrustIr.GenericCoro.AllBlocksEntryEffects.EntryEffects.noConfusionType' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.AllBlocksEntryEffects.EntryEffects.noConfusionType

/-- info: 'TrustIr.GenericCoro.AllBlocksEntryEffects.EntryEffects.rec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.AllBlocksEntryEffects.EntryEffects.rec

/-- info: 'TrustIr.GenericCoro.AllBlocksEntryEffects.EntryEffects.recOn' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.AllBlocksEntryEffects.EntryEffects.recOn

/-- info: 'TrustIr.GenericCoro.AllBlocksEntryEffects.EntryEffects.refl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.AllBlocksEntryEffects.EntryEffects.refl

/-- info: 'TrustIr.GenericCoro.AllBlocksEntryEffects.EntryEffects.trans' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.AllBlocksEntryEffects.EntryEffects.trans

/-- info: 'TrustIr.GenericCoro.AllBlocksEntryEffects.effectRelation_trans' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.AllBlocksEntryEffects.effectRelation_trans

/-- info: 'TrustIr.GenericCoro.AllBlocksEntryEffects.factoryReplacement_entryEffects' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.AllBlocksEntryEffects.factoryReplacement_entryEffects

/-- info: 'TrustIr.GenericCoro.AllBlocksEntryEffects.functions_expanded_entryEffects' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.AllBlocksEntryEffects.functions_expanded_entryEffects

/-- info: 'TrustIr.GenericCoro.AllBlocksEntryEffects.headerRelated_trans' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.AllBlocksEntryEffects.headerRelated_trans

/-- info: 'TrustIr.GenericCoro.AllBlocksEntryEffects.installFirst_entryEffects' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.AllBlocksEntryEffects.installFirst_entryEffects

/-- info: 'TrustIr.GenericCoro.AllBlocksEntryEffects.lowerRows_entryEffects' depends on axioms: [propext,
 Quot.sound,
 Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.AllBlocksEntryEffects.lowerRows_entryEffects

/-- info: 'TrustIr.GenericCoro.EntryObservation.entry_effect_of_steps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.EntryObservation.entry_effect_of_steps

/-- info: 'TrustIr.GenericCoro.EntryObservation.entry_observe_eq_of_steps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.EntryObservation.entry_observe_eq_of_steps

/-- info: 'TrustIr.GenericCoro.EntryObservation.exitUnwinding_effect' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.EntryObservation.exitUnwinding_effect

/-- info: 'TrustIr.GenericCoro.EntryObservation.missing_entry_observe_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.EntryObservation.missing_entry_observe_eq

/-- info: 'TrustIr.GenericCoro.EntryObservation.observe' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.EntryObservation.observe

/-- info: 'TrustIr.GenericCoro.EntryObservation.observe_eq_of_effectRelation' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.EntryObservation.observe_eq_of_effectRelation

/-- info: 'TrustIr.GenericCoro.EntryObservation.returnGuard_effect' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.EntryObservation.returnGuard_effect

/-- info: 'TrustIr.GenericCoro.ModuleContext.produced_context_updates' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.ModuleContext.produced_context_updates

/-- info: 'TrustIr.GenericCoro.ModuleEntryEffects.entry_observe_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.ModuleEntryEffects.entry_observe_eq

/-- info: 'TrustIr.GenericCoro.ModuleEntryEffects.produced_context_entryEffects' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.ModuleEntryEffects.produced_context_entryEffects

/-- info: 'TrustIr.GenericCoro.ModuleEntryEffects.transform_ready_constructed_entry_observe_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.ModuleEntryEffects.transform_ready_constructed_entry_observe_eq

/-- info: 'TrustIr.GenericCoro.ModuleEntryEffects.transform_ready_entryEffects' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.ModuleEntryEffects.transform_ready_entryEffects

/-- info: 'TrustIr.GenericCoro.ModuleEntryEffects.transform_ready_entry_observe_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.ModuleEntryEffects.transform_ready_entry_observe_eq

/-- info: 'TrustIr.GenericCoro.ModuleEntryEffects.transform_ready_initial_entry_observe_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.ModuleEntryEffects.transform_ready_initial_entry_observe_eq


-- Closed actual produced-module execution controls.

/-- info: 'TrustIr.GenericCoro.ModuleContext.Controls.actual_mutual_publication' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.ModuleContext.Controls.actual_mutual_publication

/-- info: 'TrustIr.GenericCoro.ModuleContext.Controls.actual_mutual_tables_preserve_every_entry' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.ModuleContext.Controls.actual_mutual_tables_preserve_every_entry

/-- info: 'TrustIr.GenericCoro.ModuleContext.Controls.actual_source_context_built' depends on axioms: [propext,
 Quot.sound,
 Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.ModuleContext.Controls.actual_source_context_built

/-- info: 'TrustIr.GenericCoro.ModuleContext.Controls.actual_target_context_built' depends on axioms: [propext,
 Quot.sound,
 Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.ModuleContext.Controls.actual_target_context_built

/-- info: 'TrustIr.GenericCoro.ModuleContext.Controls.arguments' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.ModuleContext.Controls.arguments

/-- info: 'TrustIr.GenericCoro.ModuleContext.Controls.caller' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.ModuleContext.Controls.caller

/-- info: 'TrustIr.GenericCoro.ModuleContext.Controls.caller.match_1' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.ModuleContext.Controls.caller.match_1

/-- info: 'TrustIr.GenericCoro.ModuleContext.Controls.concrete_complete_runs_equal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.ModuleContext.Controls.concrete_complete_runs_equal

/-- info: 'TrustIr.GenericCoro.ModuleContext.Controls.concrete_source_mutual_call_succeeds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.ModuleContext.Controls.concrete_source_mutual_call_succeeds

/-- info: 'TrustIr.GenericCoro.ModuleContext.Controls.concrete_target_mutual_call_succeeds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.ModuleContext.Controls.concrete_target_mutual_call_succeeds

/-- info: 'TrustIr.GenericCoro.ModuleContext.Controls.observation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.ModuleContext.Controls.observation

/-- info: 'TrustIr.GenericCoro.ModuleContext.Controls.source' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.ModuleContext.Controls.source

/-- info: 'TrustIr.GenericCoro.ModuleContext.Controls.sourceContext' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.ModuleContext.Controls.sourceContext

/-- info: 'TrustIr.GenericCoro.ModuleContext.Controls.sourceContext.match_1' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.ModuleContext.Controls.sourceContext.match_1

/-- info: 'TrustIr.GenericCoro.ModuleContext.Controls.target' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.ModuleContext.Controls.target

/-- info: 'TrustIr.GenericCoro.ModuleContext.Controls.targetContext' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.ModuleContext.Controls.targetContext

