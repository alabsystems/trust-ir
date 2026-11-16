import TrustIr.Proofs.AxiomAuditCompat
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

#trustIrAxiomsPinned Lean.RBNode.find.eq_1 == [] modern []

#trustIrAxiomsPinned Lean.RBNode.find.eq_2 == [] modern []

#trustIrAxiomsByCompiler Lean.RBNode.ins.eq_1 == [] modern [propext]

#trustIrAxiomsByCompiler Lean.RBNode.ins.eq_2 == [] modern [propext]

#trustIrAxiomsByCompiler Lean.RBNode.ins.eq_3 == [] modern [propext]

#trustIrAxiomsPinned TrustIr.GenericCoro.AllBlocksContext.Controls.both_mutual_factory_results_are_expanded == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.AllBlocksContext.Controls.direct == [] modern []

#trustIrAxiomsPinned TrustIr.GenericCoro.AllBlocksContext.Controls.duplicate_key_composition_preserves_winning_occurrence == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.AllBlocksContext.Controls.graph == [] modern []

#trustIrAxiomsPinned TrustIr.GenericCoro.AllBlocksContext.Controls.header == [] modern []

#trustIrAxiomsPinned TrustIr.GenericCoro.AllBlocksContext.Controls.signature == [] modern []

#trustIrAxiomsPinned TrustIr.GenericCoro.AllBlocksContext.Controls.two_updated_mutual_entries_preserve_every_framed_call == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.AllBlocksContext.Controls.undefined_and_bodyless_other_entries_keep_exact_errors == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.AllBlocksContext.FactoryReplacement == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.AllBlocksContext.FactoryReplacement.framedCallsEquivalent == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.AllBlocksContext.FramedCallsEquivalent == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.AllBlocksContext.FramedCallsEquivalent.refl == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.AllBlocksContext.FramedCallsEquivalent.run == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.AllBlocksContext.FramedCallsEquivalent.symm == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.AllBlocksContext.FramedCallsEquivalent.trans == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.AllBlocksContext.FunctionUpdate == [] modern []

#trustIrAxiomsPinned TrustIr.GenericCoro.AllBlocksContext.FunctionUpdate.casesOn == [] modern []

#trustIrAxiomsPinned TrustIr.GenericCoro.AllBlocksContext.FunctionUpdate.id == [] modern []

#trustIrAxiomsPinned TrustIr.GenericCoro.AllBlocksContext.FunctionUpdate.mk == [] modern []

#trustIrAxiomsPinned TrustIr.GenericCoro.AllBlocksContext.FunctionUpdate.mk.inj == [] modern []

#trustIrAxiomsPinned TrustIr.GenericCoro.AllBlocksContext.FunctionUpdate.mk.injEq == [propext] modern [propext]

#trustIrAxiomsPinned TrustIr.GenericCoro.AllBlocksContext.FunctionUpdate.mk.sizeOf_spec == [] modern []

#trustIrAxiomsPinned TrustIr.GenericCoro.AllBlocksContext.FunctionUpdate.noConfusion == [] modern []

#trustIrAxiomsPinned TrustIr.GenericCoro.AllBlocksContext.FunctionUpdate.noConfusionType == [] modern []

#trustIrAxiomsPinned TrustIr.GenericCoro.AllBlocksContext.FunctionUpdate.rec == [] modern []

#trustIrAxiomsPinned TrustIr.GenericCoro.AllBlocksContext.FunctionUpdate.recOn == [] modern []

#trustIrAxiomsPinned TrustIr.GenericCoro.AllBlocksContext.FunctionUpdate.source == [] modern []

#trustIrAxiomsPinned TrustIr.GenericCoro.AllBlocksContext.FunctionUpdate.target == [] modern []

#trustIrAxiomsPinned TrustIr.GenericCoro.AllBlocksContext.functions_expanded_framedCallsEquivalent == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.AllBlocksContext.installFirst == [] modern []

#trustIrAxiomsPinned TrustIr.GenericCoro.AllBlocksContext.installFirst_framedCallsEquivalent == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.AllBlocksContext.installFirst_functions == [Quot.sound, propext] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.AllBlocksContext.installFirst_functions.match_1 == [] modern []

#trustIrAxiomsPinned TrustIr.GenericCoro.AllBlocksContext.lowerRows_framedCallsEquivalent == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.HeaderMaps.firstValue_header == [propext] modern [propext]

#trustIrAxiomsPinned TrustIr.GenericCoro.HeaderMaps.localTypeHeadersOf_direct == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.HeaderMaps.localTypeHeadersOf_eq == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.HeaderMaps.localTypeHeadersOf_signatures == [propext, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.HeaderMaps.original_fold_classifier == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.ModuleContext.ContextCallsEquivalent == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.ModuleContext.ContextCallsEquivalent.match_1 == [] modern []

#trustIrAxiomsPinned TrustIr.GenericCoro.ModuleContext.EvaluatedOccurrence == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.ModuleContext.lowerFunction_evaluated == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.ModuleContext.lowerFunction_imageRoots == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.ModuleContext.produced_context_calls == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.ModuleContext.produced_evaluated == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.ModuleContext.transform_ready_context_calls == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.ModuleContext.transform_ready_runCallReq == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.ModuleFactory.Controls.absent_function_signature_refuses == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.ModuleFactory.Controls.actual_all_other_fields == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.ModuleFactory.Controls.actual_ast_headers_and_order == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.ModuleFactory.Controls.actual_call_prefix_preparation_provenance == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.ModuleFactory.Controls.actual_multifunction_ast == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.ModuleFactory.Controls.actual_no_suspend_terminators == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.ModuleFactory.Controls.actual_produced_not_assumed == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.ModuleFactory.Controls.callPrefix == [] modern []

#trustIrAxiomsPinned TrustIr.GenericCoro.ModuleFactory.Controls.caller == [] modern []

#trustIrAxiomsPinned TrustIr.GenericCoro.ModuleFactory.Controls.coroutine == [] modern []

#trustIrAxiomsPinned TrustIr.GenericCoro.ModuleFactory.Controls.declaration == [] modern []

#trustIrAxiomsPinned TrustIr.GenericCoro.ModuleFactory.Controls.declaration_header_types_real_call_prefix == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.ModuleFactory.Controls.declarations_keep_bodyless_status == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.ModuleFactory.Controls.duplicate_function_occurrences_both_emitted == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.ModuleFactory.Controls.duplicate_id_first_missing_signature_stays_missing == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.ModuleFactory.Controls.duplicate_id_first_signature_stays_first == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.ModuleFactory.Controls.emitted == [] modern []

#trustIrAxiomsPinned TrustIr.GenericCoro.ModuleFactory.Controls.empty_module_identity == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.ModuleFactory.Controls.expandedCaller == [] modern []

#trustIrAxiomsPinned TrustIr.GenericCoro.ModuleFactory.Controls.forged_declaration_has_explicit_error == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.ModuleFactory.Controls.inference_failure_rolls_back == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.ModuleFactory.Controls.malformed_payload_is_not_relabelled == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.ModuleFactory.Controls.no_suspend_needs_no_capacity == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.ModuleFactory.Controls.ordinary == [] modern []

#trustIrAxiomsPinned TrustIr.GenericCoro.ModuleFactory.Controls.preparationTag == [] modern []

#trustIrAxiomsPinned TrustIr.GenericCoro.ModuleFactory.Controls.preparationTag.match_1 == [] modern []

#trustIrAxiomsPinned TrustIr.GenericCoro.ModuleFactory.Controls.real_partial_capacity_certificate == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.ModuleFactory.Controls.retained_decode_failure_rolls_back == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.ModuleFactory.Controls.source == [] modern []

#trustIrAxiomsPinned TrustIr.GenericCoro.ModuleFactory.Controls.source_error_precedes_zero_capacity == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.ModuleFactory.Controls.target == [] modern []

#trustIrAxiomsPinned TrustIr.GenericCoro.ModuleFactory.FunctionHeader == [] modern []

#trustIrAxiomsPinned TrustIr.GenericCoro.ModuleFactory.FunctionLaw == [] modern []

#trustIrAxiomsPinned TrustIr.GenericCoro.ModuleFactory.FunctionsLaw == [] modern []

#trustIrAxiomsPinned TrustIr.GenericCoro.ModuleFactory.FunctionsLaw.below == [] modern []

#trustIrAxiomsPinned TrustIr.GenericCoro.ModuleFactory.FunctionsLaw.below.casesOn == [] modern []

#trustIrAxiomsPinned TrustIr.GenericCoro.ModuleFactory.FunctionsLaw.below.cons == [] modern []

#trustIrAxiomsPinned TrustIr.GenericCoro.ModuleFactory.FunctionsLaw.below.nil == [] modern []

#trustIrAxiomsPinned TrustIr.GenericCoro.ModuleFactory.FunctionsLaw.below.rec == [] modern []

#trustIrAxiomsPinned TrustIr.GenericCoro.ModuleFactory.FunctionsLaw.brecOn == [] modern []

#trustIrAxiomsPinned TrustIr.GenericCoro.ModuleFactory.FunctionsLaw.casesOn == [] modern []

#trustIrAxiomsPinned TrustIr.GenericCoro.ModuleFactory.FunctionsLaw.cons == [] modern []

#trustIrAxiomsPinned TrustIr.GenericCoro.ModuleFactory.FunctionsLaw.declarations == [] modern []

#trustIrAxiomsPinned TrustIr.GenericCoro.ModuleFactory.FunctionsLaw.headerIndex == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.ModuleFactory.FunctionsLaw.headers == [propext] modern [propext]

#trustIrAxiomsPinned TrustIr.GenericCoro.ModuleFactory.FunctionsLaw.nil == [] modern []

#trustIrAxiomsPinned TrustIr.GenericCoro.ModuleFactory.FunctionsLaw.noSuspends == [] modern []

#trustIrAxiomsPinned TrustIr.GenericCoro.ModuleFactory.FunctionsLaw.rec == [] modern []

#trustIrAxiomsPinned TrustIr.GenericCoro.ModuleFactory.FunctionsLaw.recOn == [] modern []

#trustIrAxiomsPinned TrustIr.GenericCoro.ModuleFactory.Outcome == [] modern []

#trustIrAxiomsPinned TrustIr.GenericCoro.ModuleFactory.Outcome.casesOn == [] modern []

#trustIrAxiomsPinned TrustIr.GenericCoro.ModuleFactory.Outcome.noConfusion == [] modern []

#trustIrAxiomsPinned TrustIr.GenericCoro.ModuleFactory.Outcome.noConfusionType == [] modern []

#trustIrAxiomsPinned TrustIr.GenericCoro.ModuleFactory.Outcome.ready == [] modern []

#trustIrAxiomsPinned TrustIr.GenericCoro.ModuleFactory.Outcome.ready.inj == [] modern []

#trustIrAxiomsPinned TrustIr.GenericCoro.ModuleFactory.Outcome.ready.injEq == [propext] modern [propext]

#trustIrAxiomsPinned TrustIr.GenericCoro.ModuleFactory.Outcome.ready.sizeOf_spec == [] modern []

#trustIrAxiomsPinned TrustIr.GenericCoro.ModuleFactory.Outcome.rec == [] modern []

#trustIrAxiomsPinned TrustIr.GenericCoro.ModuleFactory.Outcome.recOn == [] modern []

#trustIrAxiomsPinned TrustIr.GenericCoro.ModuleFactory.Outcome.rejected == [] modern []

#trustIrAxiomsPinned TrustIr.GenericCoro.ModuleFactory.Outcome.rejected.inj == [] modern []

#trustIrAxiomsPinned TrustIr.GenericCoro.ModuleFactory.Outcome.rejected.injEq == [propext] modern [propext]

#trustIrAxiomsPinned TrustIr.GenericCoro.ModuleFactory.Outcome.rejected.sizeOf_spec == [] modern []

#trustIrAxiomsPinned TrustIr.GenericCoro.ModuleFactory.PreparedAt == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.ModuleFactory.Problem == [] modern []

#trustIrAxiomsPinned TrustIr.GenericCoro.ModuleFactory.Problem.capacity == [] modern []

#trustIrAxiomsPinned TrustIr.GenericCoro.ModuleFactory.Problem.capacity.inj == [] modern []

#trustIrAxiomsPinned TrustIr.GenericCoro.ModuleFactory.Problem.capacity.injEq == [propext] modern [propext]

#trustIrAxiomsPinned TrustIr.GenericCoro.ModuleFactory.Problem.capacity.sizeOf_spec == [] modern []

#trustIrAxiomsPinned TrustIr.GenericCoro.ModuleFactory.Problem.casesOn == [] modern []

#trustIrAxiomsPinned TrustIr.GenericCoro.ModuleFactory.Problem.decode == [] modern []

#trustIrAxiomsPinned TrustIr.GenericCoro.ModuleFactory.Problem.decode.inj == [] modern []

#trustIrAxiomsPinned TrustIr.GenericCoro.ModuleFactory.Problem.decode.injEq == [propext] modern [propext]

#trustIrAxiomsPinned TrustIr.GenericCoro.ModuleFactory.Problem.decode.sizeOf_spec == [] modern []

#trustIrAxiomsPinned TrustIr.GenericCoro.ModuleFactory.Problem.inference == [] modern []

#trustIrAxiomsPinned TrustIr.GenericCoro.ModuleFactory.Problem.inference.inj == [] modern []

#trustIrAxiomsPinned TrustIr.GenericCoro.ModuleFactory.Problem.inference.injEq == [propext] modern [propext]

#trustIrAxiomsPinned TrustIr.GenericCoro.ModuleFactory.Problem.inference.sizeOf_spec == [] modern []

#trustIrAxiomsPinned TrustIr.GenericCoro.ModuleFactory.Problem.noConfusion == [] modern []

#trustIrAxiomsPinned TrustIr.GenericCoro.ModuleFactory.Problem.noConfusionType == [] modern []

#trustIrAxiomsPinned TrustIr.GenericCoro.ModuleFactory.Problem.rec == [] modern []

#trustIrAxiomsPinned TrustIr.GenericCoro.ModuleFactory.Problem.recOn == [] modern []

#trustIrAxiomsPinned TrustIr.GenericCoro.ModuleFactory.Produced == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.ModuleFactory.Produced.below == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.ModuleFactory.Produced.below.casesOn == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.ModuleFactory.Produced.below.cons == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.ModuleFactory.Produced.below.nil == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.ModuleFactory.Produced.below.rec == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.ModuleFactory.Produced.brecOn == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.ModuleFactory.Produced.casesOn == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.ModuleFactory.Produced.cons == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.ModuleFactory.Produced.nil == [propext, Classical.choice, Quot.sound] modern []

#trustIrAxiomsPinned TrustIr.GenericCoro.ModuleFactory.Produced.prepared == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.ModuleFactory.Produced.rec == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.ModuleFactory.Produced.recOn == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.ModuleFactory.RowExpansion == [] modern []

#trustIrAxiomsPinned TrustIr.GenericCoro.ModuleFactory.RowExpansion.capacity == [] modern []

#trustIrAxiomsPinned TrustIr.GenericCoro.ModuleFactory.RowExpansion.capacity.inj == [] modern []

#trustIrAxiomsPinned TrustIr.GenericCoro.ModuleFactory.RowExpansion.capacity.injEq == [propext] modern [propext]

#trustIrAxiomsPinned TrustIr.GenericCoro.ModuleFactory.RowExpansion.capacity.sizeOf_spec == [] modern []

#trustIrAxiomsPinned TrustIr.GenericCoro.ModuleFactory.RowExpansion.casesOn == [] modern []

#trustIrAxiomsPinned TrustIr.GenericCoro.ModuleFactory.RowExpansion.expanded == [] modern []

#trustIrAxiomsPinned TrustIr.GenericCoro.ModuleFactory.RowExpansion.expanded.inj == [] modern []

#trustIrAxiomsPinned TrustIr.GenericCoro.ModuleFactory.RowExpansion.expanded.injEq == [propext] modern [propext]

#trustIrAxiomsPinned TrustIr.GenericCoro.ModuleFactory.RowExpansion.expanded.sizeOf_spec == [] modern []

#trustIrAxiomsPinned TrustIr.GenericCoro.ModuleFactory.RowExpansion.noConfusion == [] modern []

#trustIrAxiomsPinned TrustIr.GenericCoro.ModuleFactory.RowExpansion.noConfusionType == [] modern []

#trustIrAxiomsPinned TrustIr.GenericCoro.ModuleFactory.RowExpansion.rec == [] modern []

#trustIrAxiomsPinned TrustIr.GenericCoro.ModuleFactory.RowExpansion.recOn == [] modern []

#trustIrAxiomsPinned TrustIr.GenericCoro.ModuleFactory.RowExpansion.toFunctions == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.ModuleFactory.RowExpansion.toFunctions.match_1 == [] modern []

#trustIrAxiomsPinned TrustIr.GenericCoro.ModuleFactory.RowExpansion.unchanged == [] modern []

#trustIrAxiomsPinned TrustIr.GenericCoro.ModuleFactory.RowExpansion.unchanged.inj == [] modern []

#trustIrAxiomsPinned TrustIr.GenericCoro.ModuleFactory.RowExpansion.unchanged.injEq == [propext] modern [propext]

#trustIrAxiomsPinned TrustIr.GenericCoro.ModuleFactory.RowExpansion.unchanged.sizeOf_spec == [] modern []

#trustIrAxiomsPinned TrustIr.GenericCoro.ModuleFactory.RowsReady == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.ModuleFactory.directHeaders == [] modern []

#trustIrAxiomsPinned TrustIr.GenericCoro.ModuleFactory.firstHeader == [] modern []

#trustIrAxiomsPinned TrustIr.GenericCoro.ModuleFactory.firstHeader.eq_1 == [] modern []

#trustIrAxiomsPinned TrustIr.GenericCoro.ModuleFactory.firstHeader.eq_2 == [] modern []

#trustIrAxiomsPinned TrustIr.GenericCoro.ModuleFactory.firstHeader.match_1 == [] modern []

#trustIrAxiomsPinned TrustIr.GenericCoro.ModuleFactory.functionHeader == [] modern []

#trustIrAxiomsPinned TrustIr.GenericCoro.ModuleFactory.headerIndex == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.ModuleFactory.headerIndex_find == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.ModuleFactory.lowerFunction == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.ModuleFactory.lowerFunction.match_1 == [] modern []

#trustIrAxiomsPinned TrustIr.GenericCoro.ModuleFactory.lowerFunction.match_2 == [] modern []

#trustIrAxiomsPinned TrustIr.GenericCoro.ModuleFactory.lowerFunction.match_3 == [] modern []

#trustIrAxiomsPinned TrustIr.GenericCoro.ModuleFactory.lowerFunction_decode_error == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.ModuleFactory.lowerFunction_law == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.ModuleFactory.lowerFunction_prepared == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.ModuleFactory.lowerFunctionsLoop == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.ModuleFactory.lowerFunctionsLoop.eq_1 == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.ModuleFactory.lowerFunctionsLoop.eq_2 == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.ModuleFactory.lowerFunctionsLoop.match_1 == [] modern []

#trustIrAxiomsPinned TrustIr.GenericCoro.ModuleFactory.lowerFunctionsLoop_error == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.ModuleFactory.lowerFunctionsLoop_produced == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.ModuleFactory.lowerFunctionsLoop_ready == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.ModuleFactory.noSuspendBody == [] modern []

#trustIrAxiomsPinned TrustIr.GenericCoro.ModuleFactory.prepareRows == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.ModuleFactory.prepareRows.match_1 == [propext, Quot.sound] modern [propext, Quot.sound]

trustIrCanonicalOnly
/-- info: 'TrustIr.GenericCoro.ModuleFactory.prepareRows.proof_1' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.ModuleFactory.prepareRows.proof_1

#trustIrAxiomsPinned TrustIr.GenericCoro.ModuleFactory.prepareRows_error_source == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.ModuleFactory.prepareRows_ready == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.ModuleFactory.prepareRows_toFunctions == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.ModuleFactory.sameHeader == [] modern []

#trustIrAxiomsPinned TrustIr.GenericCoro.ModuleFactory.sameHeader_header == [] modern []

#trustIrAxiomsPinned TrustIr.GenericCoro.ModuleFactory.sameHeader_id == [] modern []

#trustIrAxiomsPinned TrustIr.GenericCoro.ModuleFactory.sameHeader_ty == [] modern []

#trustIrAxiomsPinned TrustIr.GenericCoro.ModuleFactory.suspendCount_zero_of_any == [propext] modern [propext]

#trustIrAxiomsPinned TrustIr.GenericCoro.ModuleFactory.transform == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.ModuleFactory.transform.match_1 == [] modern []

#trustIrAxiomsPinned TrustIr.GenericCoro.ModuleFactory.transform_declarations == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.ModuleFactory.transform_directHeaders == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.ModuleFactory.transform_headers == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.ModuleFactory.transform_noSuspends == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.ModuleFactory.transform_produced == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.ModuleFactory.transform_ready == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.ModuleFactory.transform_rejected_at == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.ModuleFactory.transform_rejected_original == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.NatRBMapInsert.Ascending == [] modern []

#trustIrAxiomsPinned TrustIr.NatRBMapInsert.Ascending.below == [] modern []

#trustIrAxiomsPinned TrustIr.NatRBMapInsert.Ascending.below.casesOn == [] modern []

#trustIrAxiomsPinned TrustIr.NatRBMapInsert.Ascending.below.cons == [] modern []

#trustIrAxiomsPinned TrustIr.NatRBMapInsert.Ascending.below.nil == [] modern []

#trustIrAxiomsPinned TrustIr.NatRBMapInsert.Ascending.below.rec == [] modern []

#trustIrAxiomsPinned TrustIr.NatRBMapInsert.Ascending.brecOn == [] modern []

#trustIrAxiomsPinned TrustIr.NatRBMapInsert.Ascending.casesOn == [] modern []

#trustIrAxiomsPinned TrustIr.NatRBMapInsert.Ascending.cons == [] modern []

#trustIrAxiomsPinned TrustIr.NatRBMapInsert.Ascending.cross == [propext] modern [propext]

#trustIrAxiomsPinned TrustIr.NatRBMapInsert.Ascending.insert_rows == [Classical.choice, propext, Quot.sound] modern [propext]

trustIrCanonicalOnly
/-- info: 'TrustIr.NatRBMapInsert.Ascending.insert_rows.match_1' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.NatRBMapInsert.Ascending.insert_rows.match_1

#trustIrAxiomsByCompiler TrustIr.NatRBMapInsert.Ascending.left == [] modern [propext]

#trustIrAxiomsPinned TrustIr.NatRBMapInsert.Ascending.nil == [] modern []

#trustIrAxiomsPinned TrustIr.NatRBMapInsert.Ascending.rec == [] modern []

#trustIrAxiomsPinned TrustIr.NatRBMapInsert.Ascending.recOn == [] modern []

#trustIrAxiomsPinned TrustIr.NatRBMapInsert.Ascending.right == [] modern []

#trustIrAxiomsPinned TrustIr.NatRBMapInsert.Controls.actual_duplicate_function_header_classifier == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.NatRBMapInsert.Controls.actual_original_helper_duplicate_control == [propext, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.NatRBMapInsert.Controls.actual_original_helper_instantiates_classifier_bridge == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.NatRBMapInsert.Controls.duplicate_insert_overwrites_only_selected_key == [propext, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.NatRBMapInsert.Controls.first_missing_function_signature_not_recovered == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.NatRBMapInsert.Controls.first_none_payload_is_occupied == [propext, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.NatRBMapInsert.Controls.first_wins_and_missing == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.NatRBMapInsert.Controls.four_actual_rotation_paths == [propext, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.NatRBMapInsert.Controls.function == [] modern []

#trustIrAxiomsPinned TrustIr.NatRBMapInsert.Controls.insertAllFrom == [propext, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.NatRBMapInsert.Controls.insertAllFrom_history == [propext, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.NatRBMapInsert.Controls.mapOf == [propext, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.NatRBMapInsert.Controls.mapOf_history == [propext, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.NatRBMapInsert.Controls.module == [] modern []

#trustIrAxiomsPinned TrustIr.NatRBMapInsert.Controls.optionEntries == [] modern []

#trustIrAxiomsPinned TrustIr.NatRBMapInsert.Controls.overwrite_after_rotation == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.NatRBMapInsert.Controls.overwrite_exact_others_retained == [propext, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.NatRBMapInsert.Controls.signatures == [] modern []

#trustIrAxiomsPinned TrustIr.NatRBMapInsert.Controls.sparse_high_keys == [propext, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.NatRBMapInsert.Controls.unordered_node_is_not_covered == [] modern []

#trustIrAxiomsPinned TrustIr.NatRBMapInsert.InsertOnly == [propext, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.NatRBMapInsert.InsertOnly.below == [propext, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.NatRBMapInsert.InsertOnly.below.casesOn == [propext, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.NatRBMapInsert.InsertOnly.below.empty == [propext, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.NatRBMapInsert.InsertOnly.below.insert == [propext, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.NatRBMapInsert.InsertOnly.below.rec == [propext, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.NatRBMapInsert.InsertOnly.brecOn == [propext, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.NatRBMapInsert.InsertOnly.casesOn == [propext, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.NatRBMapInsert.InsertOnly.empty == [propext, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.NatRBMapInsert.InsertOnly.insert == [propext, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.NatRBMapInsert.InsertOnly.ordered == [propext, Quot.sound, Classical.choice] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.NatRBMapInsert.InsertOnly.rec == [propext, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.NatRBMapInsert.InsertOnly.recOn == [propext, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.NatRBMapInsert.Ordered == [] modern []

#trustIrAxiomsPinned TrustIr.NatRBMapInsert.find?_empty == [propext, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.NatRBMapInsert.find?_insert == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.NatRBMapInsert.find_eq_lookupRows == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.NatRBMapInsert.find_insert == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.NatRBMapInsert.firstValue == [] modern []

#trustIrAxiomsPinned TrustIr.NatRBMapInsert.firstValue.eq_1 == [] modern []

#trustIrAxiomsPinned TrustIr.NatRBMapInsert.firstValue.eq_2 == [] modern []

#trustIrAxiomsPinned TrustIr.NatRBMapInsert.firstValue.match_1 == [] modern []

#trustIrAxiomsPinned TrustIr.NatRBMapInsert.firstWinsFrom == [propext, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.NatRBMapInsert.firstWinsFrom_find == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.NatRBMapInsert.firstWinsFrom_insertOnly == [propext, Quot.sound, Classical.choice] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.NatRBMapInsert.firstWins_empty_find == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.NatRBMapInsert.insertRows == [] modern []

#trustIrAxiomsPinned TrustIr.NatRBMapInsert.insertRows.eq_1 == [] modern []

#trustIrAxiomsPinned TrustIr.NatRBMapInsert.insertRows.eq_2 == [] modern []

#trustIrAxiomsPinned TrustIr.NatRBMapInsert.insertRows.match_1 == [] modern []

trustIrCanonicalOnly
/-- info: 'TrustIr.NatRBMapInsert.insertRows.match_2' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.NatRBMapInsert.insertRows.match_2

#trustIrAxiomsPinned TrustIr.NatRBMapInsert.insertRows_append_before == [Classical.choice, propext, Quot.sound] modern [propext]

#trustIrAxiomsPinned TrustIr.NatRBMapInsert.insertRows_mem == [] modern []

#trustIrAxiomsPinned TrustIr.NatRBMapInsert.insertRows_skip_prefix == [Classical.choice, propext, Quot.sound] modern [propext]

#trustIrAxiomsPinned TrustIr.NatRBMapInsert.lookupRows == [] modern []

#trustIrAxiomsPinned TrustIr.NatRBMapInsert.lookupRows.eq_1 == [] modern []

#trustIrAxiomsPinned TrustIr.NatRBMapInsert.lookupRows.eq_2 == [] modern []

#trustIrAxiomsPinned TrustIr.NatRBMapInsert.lookupRows.match_1 == [] modern []

#trustIrAxiomsPinned TrustIr.NatRBMapInsert.lookupRows_append == [Classical.choice, propext, Quot.sound] modern []

#trustIrAxiomsPinned TrustIr.NatRBMapInsert.lookupRows_append.match_1 == [] modern []

#trustIrAxiomsPinned TrustIr.NatRBMapInsert.lookupRows_insert == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.NatRBMapInsert.lookupRows_none == [] modern []

#trustIrAxiomsPinned TrustIr.NatRBMapInsert.ordered_insert == [Classical.choice, propext, Quot.sound] modern [propext]

#trustIrAxiomsPinned TrustIr.NatRBMapInsert.ordered_node == [propext] modern [propext]

#trustIrAxiomsPinned TrustIr.NatRBMapInsert.prefer == [] modern []

#trustIrAxiomsPinned TrustIr.NatRBMapInsert.prefer.match_1 == [] modern []

#trustIrAxiomsPinned TrustIr.NatRBMapInsert.rows == [] modern []

#trustIrAxiomsPinned TrustIr.NatRBMapInsert.rows.eq_1 == [] modern []

#trustIrAxiomsPinned TrustIr.NatRBMapInsert.rows.eq_2 == [] modern []

#trustIrAxiomsPinned TrustIr.NatRBMapInsert.rows.match_1 == [] modern []

#trustIrAxiomsPinned TrustIr.NatRBMapInsert.rows_balance1 == [propext] modern [propext]

#trustIrAxiomsPinned TrustIr.NatRBMapInsert.rows_balance2 == [propext] modern [propext]

#trustIrAxiomsPinned TrustIr.NatRBMapInsert.rows_ins == [propext, Classical.choice, Quot.sound] modern [propext]

#trustIrAxiomsPinned TrustIr.NatRBMapInsert.rows_insert == [Classical.choice, propext, Quot.sound] modern [propext]

#trustIrAxiomsByCompiler TrustIr.NatRBMapInsert.rows_setBlack == [] modern [propext]

#trustIrAxiomsPinned TrustIrEval.D == [] modern []

#trustIrAxiomsPinned TrustIrEval.DecodeError == [] modern []

#trustIrAxiomsPinned TrustIrEval.DecodeError.casesOn == [] modern []

#trustIrAxiomsPinned TrustIrEval.DecodeError.malformed == [] modern []

#trustIrAxiomsPinned TrustIrEval.DecodeError.malformed.inj == [] modern []

#trustIrAxiomsPinned TrustIrEval.DecodeError.malformed.injEq == [propext] modern [propext]

#trustIrAxiomsPinned TrustIrEval.DecodeError.malformed.sizeOf_spec == [] modern []

#trustIrAxiomsPinned TrustIrEval.DecodeError.noConfusion == [] modern []

#trustIrAxiomsPinned TrustIrEval.DecodeError.noConfusionType == [] modern []

#trustIrAxiomsPinned TrustIrEval.DecodeError.rec == [] modern []

#trustIrAxiomsPinned TrustIrEval.DecodeError.recOn == [] modern []

#trustIrAxiomsPinned TrustIrEval.DecodeError.unsupported == [] modern []

#trustIrAxiomsPinned TrustIrEval.DecodeError.unsupported.inj == [] modern []

#trustIrAxiomsPinned TrustIrEval.DecodeError.unsupported.injEq == [propext] modern [propext]

#trustIrAxiomsPinned TrustIrEval.DecodeError.unsupported.sizeOf_spec == [] modern []

#trustIrAxiomsPinned TrustIrEval.Function == [] modern []

#trustIrAxiomsPinned TrustIrEval.Function.blocks == [] modern []

#trustIrAxiomsPinned TrustIrEval.Function.callingConvention == [] modern []

#trustIrAxiomsPinned TrustIrEval.Function.casesOn == [] modern []

#trustIrAxiomsPinned TrustIrEval.Function.entry == [] modern []

#trustIrAxiomsPinned TrustIrEval.Function.id == [] modern []

#trustIrAxiomsPinned TrustIrEval.Function.isDeclaration == [] modern []

#trustIrAxiomsPinned TrustIrEval.Function.mk == [] modern []

#trustIrAxiomsPinned TrustIrEval.Function.mk.inj == [] modern []

#trustIrAxiomsPinned TrustIrEval.Function.mk.injEq == [propext] modern [propext]

#trustIrAxiomsPinned TrustIrEval.Function.mk.sizeOf_spec == [] modern []

#trustIrAxiomsPinned TrustIrEval.Function.name == [] modern []

#trustIrAxiomsPinned TrustIrEval.Function.noConfusion == [] modern []

#trustIrAxiomsPinned TrustIrEval.Function.noConfusionType == [] modern []

#trustIrAxiomsPinned TrustIrEval.Function.rec == [] modern []

#trustIrAxiomsPinned TrustIrEval.Function.recOn == [] modern []

#trustIrAxiomsPinned TrustIrEval.Function.ty == [] modern []

#trustIrAxiomsPinned TrustIrEval.Module == [] modern []

#trustIrAxiomsPinned TrustIrEval.Module.byteModel == [] modern []

#trustIrAxiomsPinned TrustIrEval.Module.casesOn == [] modern []

#trustIrAxiomsPinned TrustIrEval.Module.closureLayouts == [] modern []

#trustIrAxiomsPinned TrustIrEval.Module.closureTys == [] modern []

#trustIrAxiomsPinned TrustIrEval.Module.dropGlue == [] modern []

#trustIrAxiomsPinned TrustIrEval.Module.enums == [] modern []

#trustIrAxiomsPinned TrustIrEval.Module.funcTys == [] modern []

#trustIrAxiomsPinned TrustIrEval.Module.functions == [] modern []

#trustIrAxiomsPinned TrustIrEval.Module.globals == [] modern []

#trustIrAxiomsPinned TrustIrEval.Module.hasTargetInfo == [] modern []

#trustIrAxiomsPinned TrustIrEval.Module.mk == [] modern []

#trustIrAxiomsPinned TrustIrEval.Module.mk.inj == [] modern []

#trustIrAxiomsPinned TrustIrEval.Module.mk.injEq == [propext] modern [propext]

#trustIrAxiomsPinned TrustIrEval.Module.mk.sizeOf_spec == [] modern []

#trustIrAxiomsPinned TrustIrEval.Module.noConfusion == [] modern []

#trustIrAxiomsPinned TrustIrEval.Module.noConfusionType == [] modern []

#trustIrAxiomsPinned TrustIrEval.Module.rec == [] modern []

#trustIrAxiomsPinned TrustIrEval.Module.recOn == [] modern []

#trustIrAxiomsPinned TrustIrEval.Module.records == [] modern []

#trustIrAxiomsPinned TrustIrEval.Module.structs == [] modern []

#trustIrAxiomsPinned TrustIrEval.Module.tupleLayouts == [] modern []

#trustIrAxiomsPinned TrustIrEval.Module.types == [] modern []

#trustIrAxiomsPinned TrustIrEval.Node == [] modern []

#trustIrAxiomsPinned TrustIrEval.Node.casesOn == [] modern []

#trustIrAxiomsPinned TrustIrEval.Node.inst == [] modern []

#trustIrAxiomsPinned TrustIrEval.Node.mk == [] modern []

#trustIrAxiomsPinned TrustIrEval.Node.mk.inj == [] modern []

#trustIrAxiomsPinned TrustIrEval.Node.mk.injEq == [propext] modern [propext]

#trustIrAxiomsPinned TrustIrEval.Node.mk.sizeOf_spec == [] modern []

#trustIrAxiomsPinned TrustIrEval.Node.noConfusion == [] modern []

#trustIrAxiomsPinned TrustIrEval.Node.noConfusionType == [] modern []

#trustIrAxiomsPinned TrustIrEval.Node.rec == [] modern []

#trustIrAxiomsPinned TrustIrEval.Node.recOn == [] modern []

#trustIrAxiomsPinned TrustIrEval.Node.results == [] modern []

#trustIrAxiomsPinned TrustIrEval.blocksDrop == [] modern []

#trustIrAxiomsPinned TrustIrEval.blocksDrop.match_1 == [] modern []

#trustIrAxiomsPinned TrustIrEval.calleesOf == [] modern []

#trustIrAxiomsPinned TrustIrEval.calleesOf.match_1 == [] modern []

#trustIrAxiomsPinned TrustIrEval.calleesOfInst == [] modern []

#trustIrAxiomsPinned TrustIrEval.calleesOfInst.match_1 == [] modern []

#trustIrAxiomsPinned TrustIrEval.cfgOf == [] modern []

#trustIrAxiomsPinned TrustIrEval.contextOf == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIrEval.contextOf.match_1 == [] modern []

#trustIrAxiomsPinned TrustIrEval.FunctionLookup.findFunction.match_1 == [] modern []

#trustIrAxiomsPinned TrustIrEval.FunctionLookup.findError.match_1 == [] modern []

trustIrCanonicalOnly
/-- info: 'TrustIrEval.FunctionLookup.findError.match_2' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIrEval.FunctionLookup.findError.match_2

#trustIrAxiomsPinned TrustIrEval.FunctionLookup.prepareSourceFrom.match_1 == [] modern []

#trustIrAxiomsPinned TrustIrEval.dropGlueOf == [] modern []

#trustIrAxiomsPinned TrustIrEval.evalFunctionOf == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIrEval.evalFunctionOf.match_1 == [] modern []

#trustIrAxiomsPinned TrustIrEval.evalFunctionOfWithTypes == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIrEval.evalFunctionOfWithTypes.match_1 == [] modern []

trustIrCanonicalOnly
/-- info: 'TrustIrEval.evalFunctionOfWithTypes.match_2' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIrEval.evalFunctionOfWithTypes.match_2

#trustIrAxiomsPinned TrustIrEval.instInhabitedDecodeError == [] modern []

#trustIrAxiomsPinned TrustIrEval.instReprDecodeError == [propext] modern [propext]

#trustIrAxiomsPinned TrustIrEval.localTypeHeadersOf == [propext, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIrEval.malformed == [] modern []

#trustIrAxiomsByCompiler TrustIrEval.memoryRootsOfInst_eq == [] modern [propext]

#trustIrAxiomsPinned TrustIrEval.memoryServiceOf_eq == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIrEval.unsupported == [] modern []


-- Actual raw-entry effects and public entry observation.

#trustIrAxiomsPinned TrustIr.GenericCoro.AllBlocksEntryEffects.Controls.mutual_factories_and_duplicate_have_raw_entry_effects == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.AllBlocksEntryEffects.EntryEffects == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.AllBlocksEntryEffects.EntryEffects.casesOn == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.AllBlocksEntryEffects.EntryEffects.effects == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.AllBlocksEntryEffects.EntryEffects.headers == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.AllBlocksEntryEffects.EntryEffects.maxDepth == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.AllBlocksEntryEffects.EntryEffects.mk == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

trustIrCanonicalOnly
/-- info: 'TrustIr.GenericCoro.AllBlocksEntryEffects.EntryEffects.noConfusion' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.AllBlocksEntryEffects.EntryEffects.noConfusion

trustIrCanonicalOnly
/-- info: 'TrustIr.GenericCoro.AllBlocksEntryEffects.EntryEffects.noConfusionType' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.AllBlocksEntryEffects.EntryEffects.noConfusionType

#trustIrAxiomsPinned TrustIr.GenericCoro.AllBlocksEntryEffects.EntryEffects.rec == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.AllBlocksEntryEffects.EntryEffects.recOn == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.AllBlocksEntryEffects.EntryEffects.refl == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.AllBlocksEntryEffects.EntryEffects.trans == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.AllBlocksEntryEffects.effectRelation_trans == [] modern []

#trustIrAxiomsPinned TrustIr.GenericCoro.AllBlocksEntryEffects.factoryReplacement_entryEffects == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.AllBlocksEntryEffects.functions_expanded_entryEffects == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.AllBlocksEntryEffects.headerRelated_trans == [] modern []

#trustIrAxiomsPinned TrustIr.GenericCoro.AllBlocksEntryEffects.installFirst_entryEffects == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.AllBlocksEntryEffects.lowerRows_entryEffects == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.EntryObservation.entry_effect_of_steps == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.EntryObservation.entry_observe_eq_of_steps == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsByCompiler TrustIr.GenericCoro.EntryObservation.exitUnwinding_effect == [] modern [propext]

#trustIrAxiomsPinned TrustIr.GenericCoro.EntryObservation.missing_entry_observe_eq == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.EntryObservation.observe == [] modern []

#trustIrAxiomsPinned TrustIr.GenericCoro.EntryObservation.observe_eq_of_effectRelation == [propext] modern [propext]

#trustIrAxiomsPinned TrustIr.GenericCoro.EntryObservation.returnGuard_effect == [propext] modern [propext]

#trustIrAxiomsPinned TrustIr.GenericCoro.ModuleContext.produced_context_updates == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.ModuleEntryEffects.entry_observe_eq == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.ModuleEntryEffects.produced_context_entryEffects == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.ModuleEntryEffects.transform_ready_constructed_entry_observe_eq == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.ModuleEntryEffects.transform_ready_entryEffects == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.ModuleEntryEffects.transform_ready_entry_observe_eq == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.ModuleEntryEffects.transform_ready_initial_entry_observe_eq == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]


-- Closed actual produced-module execution controls.

#trustIrAxiomsPinned TrustIr.GenericCoro.ModuleContext.Controls.actual_mutual_publication == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.ModuleContext.Controls.actual_mutual_tables_preserve_every_entry == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.ModuleContext.Controls.actual_source_context_built == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.ModuleContext.Controls.actual_target_context_built == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.ModuleContext.Controls.arguments == [] modern []

#trustIrAxiomsPinned TrustIr.GenericCoro.ModuleContext.Controls.caller == [] modern []

#trustIrAxiomsPinned TrustIr.GenericCoro.ModuleContext.Controls.caller.match_1 == [] modern []

#trustIrAxiomsPinned TrustIr.GenericCoro.ModuleContext.Controls.concrete_complete_runs_equal == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.ModuleContext.Controls.concrete_source_mutual_call_succeeds == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.ModuleContext.Controls.concrete_target_mutual_call_succeeds == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.ModuleContext.Controls.observation == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.ModuleContext.Controls.source == [] modern []

#trustIrAxiomsPinned TrustIr.GenericCoro.ModuleContext.Controls.sourceContext == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.ModuleContext.Controls.sourceContext.match_1 == [] modern []

#trustIrAxiomsPinned TrustIr.GenericCoro.ModuleContext.Controls.target == [] modern []

#trustIrAxiomsPinned TrustIr.GenericCoro.ModuleContext.Controls.targetContext == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]


-- Exact complete modern rosters replace the absent canonical generated names.

trustIrModernOnly
#trustIrModernAxiomFamily TrustIr.GenericCoro.AllBlocksEntryEffects.EntryEffects == [
  TrustIr.GenericCoro.AllBlocksEntryEffects.EntryEffects.casesOn,
  TrustIr.GenericCoro.AllBlocksEntryEffects.EntryEffects.effects,
  TrustIr.GenericCoro.AllBlocksEntryEffects.EntryEffects.headers,
  TrustIr.GenericCoro.AllBlocksEntryEffects.EntryEffects.itemChecks,
  TrustIr.GenericCoro.AllBlocksEntryEffects.EntryEffects.maxDepth,
  TrustIr.GenericCoro.AllBlocksEntryEffects.EntryEffects.mk,
  TrustIr.GenericCoro.AllBlocksEntryEffects.EntryEffects.mk._flat_ctor,
  TrustIr.GenericCoro.AllBlocksEntryEffects.EntryEffects.rec,
  TrustIr.GenericCoro.AllBlocksEntryEffects.EntryEffects.recOn,
  TrustIr.GenericCoro.AllBlocksEntryEffects.EntryEffects.refl,
  TrustIr.GenericCoro.AllBlocksEntryEffects.EntryEffects.trans]
trustIrModernOnly
#trustIrAxiomsExact TrustIr.GenericCoro.AllBlocksEntryEffects.EntryEffects.casesOn == [propext, Classical.choice, Quot.sound]
trustIrModernOnly
#trustIrAxiomsExact TrustIr.GenericCoro.AllBlocksEntryEffects.EntryEffects.effects == [propext, Classical.choice, Quot.sound]
trustIrModernOnly
#trustIrAxiomsExact TrustIr.GenericCoro.AllBlocksEntryEffects.EntryEffects.headers == [propext, Classical.choice, Quot.sound]
trustIrModernOnly
#trustIrAxiomsExact TrustIr.GenericCoro.AllBlocksEntryEffects.EntryEffects.itemChecks == [propext, Classical.choice, Quot.sound]
trustIrModernOnly
#trustIrAxiomsExact TrustIr.GenericCoro.AllBlocksEntryEffects.EntryEffects.maxDepth == [propext, Classical.choice, Quot.sound]
trustIrModernOnly
#trustIrAxiomsExact TrustIr.GenericCoro.AllBlocksEntryEffects.EntryEffects.mk == [propext, Classical.choice, Quot.sound]
trustIrModernOnly
#trustIrAxiomsExact TrustIr.GenericCoro.AllBlocksEntryEffects.EntryEffects.mk._flat_ctor == [propext, Classical.choice, Quot.sound]
trustIrModernOnly
#trustIrAxiomsExact TrustIr.GenericCoro.AllBlocksEntryEffects.EntryEffects.rec == [propext, Classical.choice, Quot.sound]
trustIrModernOnly
#trustIrAxiomsExact TrustIr.GenericCoro.AllBlocksEntryEffects.EntryEffects.recOn == [propext, Classical.choice, Quot.sound]
trustIrModernOnly
#trustIrAxiomsExact TrustIr.GenericCoro.AllBlocksEntryEffects.EntryEffects.refl == [propext, Classical.choice, Quot.sound]
trustIrModernOnly
#trustIrAxiomsExact TrustIr.GenericCoro.AllBlocksEntryEffects.EntryEffects.trans == [propext, Classical.choice, Quot.sound]

trustIrModernOnly
#trustIrModernAxiomFamily TrustIr.GenericCoro.ModuleFactory.prepareRows == [
  TrustIr.GenericCoro.ModuleFactory.prepareRows._proof_1,
  TrustIr.GenericCoro.ModuleFactory.prepareRows.eq_1,
  TrustIr.GenericCoro.ModuleFactory.prepareRows.match_1]
trustIrModernOnly
#trustIrAxiomsExact TrustIr.GenericCoro.ModuleFactory.prepareRows._proof_1 == [propext, Classical.choice, Quot.sound]
trustIrModernOnly
#trustIrAxiomsExact TrustIr.GenericCoro.ModuleFactory.prepareRows.eq_1 == [propext, Classical.choice, Quot.sound]
trustIrModernOnly
#trustIrAxiomsExact TrustIr.GenericCoro.ModuleFactory.prepareRows.match_1 == [propext, Quot.sound]

trustIrModernOnly
#trustIrModernAxiomFamily TrustIr.NatRBMapInsert.Ascending.insert_rows == [
  TrustIr.NatRBMapInsert.Ascending.insert_rows.match_1_1]
trustIrModernOnly
#trustIrAxiomsExact TrustIr.NatRBMapInsert.Ascending.insert_rows.match_1_1 == []

trustIrModernOnly
#trustIrModernAxiomFamily TrustIr.NatRBMapInsert.insertRows == [
  TrustIr.NatRBMapInsert.insertRows._f,
  TrustIr.NatRBMapInsert.insertRows._sunfold,
  TrustIr.NatRBMapInsert.insertRows._unsafe_rec,
  TrustIr.NatRBMapInsert.insertRows.eq_1,
  TrustIr.NatRBMapInsert.insertRows.eq_2,
  TrustIr.NatRBMapInsert.insertRows.eq_def,
  TrustIr.NatRBMapInsert.insertRows.match_1,
  TrustIr.NatRBMapInsert.insertRows.match_3]
trustIrModernOnly
#trustIrAxiomsExact TrustIr.NatRBMapInsert.insertRows._f == []
trustIrModernOnly
#trustIrAxiomsExact TrustIr.NatRBMapInsert.insertRows._sunfold == []
trustIrModernOnly
#trustIrAxiomsExact TrustIr.NatRBMapInsert.insertRows._unsafe_rec == []
trustIrModernOnly
#trustIrAxiomsExact TrustIr.NatRBMapInsert.insertRows.eq_1 == []
trustIrModernOnly
#trustIrAxiomsExact TrustIr.NatRBMapInsert.insertRows.eq_2 == []
trustIrModernOnly
#trustIrAxiomsExact TrustIr.NatRBMapInsert.insertRows.eq_def == []
trustIrModernOnly
#trustIrAxiomsExact TrustIr.NatRBMapInsert.insertRows.match_1 == []
trustIrModernOnly
#trustIrAxiomsExact TrustIr.NatRBMapInsert.insertRows.match_3 == []

trustIrModernOnly
#trustIrModernAxiomFamily TrustIrEval.FunctionLookup.findError == [
  TrustIrEval.FunctionLookup.findError.match_1,
  TrustIrEval.FunctionLookup.findError.match_3]
trustIrModernOnly
#trustIrAxiomsExact TrustIrEval.FunctionLookup.findError.match_1 == []
trustIrModernOnly
#trustIrAxiomsExact TrustIrEval.FunctionLookup.findError.match_3 == []

trustIrModernOnly
#trustIrModernAxiomFamily TrustIrEval.evalFunctionOfWithTypes == [
  TrustIrEval.evalFunctionOfWithTypes._sparseCasesOn_3,
  TrustIrEval.evalFunctionOfWithTypes._sparseCasesOn_3.else_eq,
  TrustIrEval.evalFunctionOfWithTypes.eq_1,
  TrustIrEval.evalFunctionOfWithTypes.match_1,
  TrustIrEval.evalFunctionOfWithTypes.match_3]
trustIrModernOnly
#trustIrAxiomsExact TrustIrEval.evalFunctionOfWithTypes._sparseCasesOn_3 == [propext]
trustIrModernOnly
#trustIrAxiomsExact TrustIrEval.evalFunctionOfWithTypes._sparseCasesOn_3.else_eq == [propext]
trustIrModernOnly
#trustIrAxiomsExact TrustIrEval.evalFunctionOfWithTypes.eq_1 == [propext, Classical.choice, Quot.sound]
trustIrModernOnly
#trustIrAxiomsExact TrustIrEval.evalFunctionOfWithTypes.match_1 == []
trustIrModernOnly
#trustIrAxiomsExact TrustIrEval.evalFunctionOfWithTypes.match_3 == [propext]
