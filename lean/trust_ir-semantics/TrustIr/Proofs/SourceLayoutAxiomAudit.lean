-- Copyright 2026 Andrew Yates | Apache-2.0
import TrustIr.Proofs.SourceLayoutProps

-- Exact observed dependencies; no new project axioms or native proof hooks.

#trustIrAxiomsPinned TrustIr.SourceLayout.Available.find_domain == [propext] modern [propext]

#trustIrAxiomsPinned TrustIr.SourceLayout.Available.erase_size_lt == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.erase_length_lt == [Quot.sound, propext] modern []

#trustIrAxiomsPinned TrustIr.SourceLayout.solve_cached == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.solve_done == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.same_type_same_bucket == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.checked_ok == [Classical.choice, propext, Quot.sound] modern []

#trustIrAxiomsPinned TrustIr.SourceLayoutProps.pointer32 == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayoutProps.pointer64 == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayoutProps.pointer_cuts_nominal_cycle == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayoutProps.reordered_offsets == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayoutProps.source_never_has_no_alignment == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayoutProps.execution_never_refuses == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayoutProps.closure_source_offsets == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayoutProps.closure_execution_refuses == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayoutProps.tuple_without_descriptor_is_not_source_layout == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayoutProps.tuple_without_descriptor_execution_canonical == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayoutProps.global_tuple_rows_follow_closure_frames == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayoutProps.declared_tuple_summary_does_not_admit_a_closure_codec == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayoutProps.unused_bad_closure_dependency_refuses_tuple_execution == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayoutProps.unrelated_pointer_ignores_bad_closure_dependency == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayoutProps.struct_without_metadata_is_not_source_layout == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayoutProps.struct_without_metadata_execution_canonical == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayoutProps.partial_struct_metadata_refuses == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayoutProps.packed_field_alignment_is_clamped == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayoutProps.zero_array_still_resolves_its_cycle == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayoutProps.inhabit_cycle_is_not_a_proof == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayoutProps.inhabit_cycle_with_never_has_a_finite_witness == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayoutProps.empty_array_of_never_is_inhabited == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayoutProps.inhabit_requires_every_duplicate_definition == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayoutProps.colliding_buckets_still_check_actual_source_identity == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayoutProps.noncanonical_execution_refuses_before_layout == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayoutProps.repeated_roots_share_the_prepared_graph == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayoutProps.canonical_enum_assembly_uses_absolute_offsets == [] modern []

#trustIrAxiomsPinned TrustIr.SourceLayoutProps.DuplicateSelectionControls.shape_uses_first == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayoutProps.DuplicateSelectionControls.execution_uses_matching_position == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayoutProps.DuplicateSelectionControls.group_retains_both_in_source_order == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayoutProps.DuplicateSelectionControls.first_rule_alone_is_enabled == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayoutProps.DuplicateSelectionControls.actual_solver_requires_the_other_definition == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayoutProps.DuplicateSelectionControls.absent_id_is_not_selected == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]
