-- Copyright 2026 Andrew Yates | Apache-2.0
import TrustIr.Proofs.AggregateImageProps
import TrustIr.Proofs.TransformRefinementCtx

-- Exact observed dependencies, including full-outcome CFG congruences,
-- held-memory frames and actual uninhabited-variant plan preparation.

#trustIrAxiomsPinned TrustIr.HeldMemoryFrames.semLoadValueUsing_eqv == [Classical.choice, propext, Quot.sound] modern [propext]

#trustIrAxiomsPinned TrustIr.HeldMemoryFrames.aggregateLoadValue_eqv == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.HeldMemoryFrames.aggregateStoreValue_eqv == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateImageProps.forgetUnwritten_world == [] modern []

#trustIrAxiomsPinned TrustIr.AggregateImageProps.forgetUnwritten_zero == [] modern []

#trustIrAxiomsPinned TrustIr.AggregateImageProps.recordUnwritten_empty == [] modern []

#trustIrAxiomsPinned TrustIr.AggregateImageProps.canonical_layout_ignores_aggregate_service == [propext] modern [propext]

#trustIrAxiomsPinned TrustIr.AggregateImageProps.padded_image_keeps_padding_absent == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateImageProps.packed_image_has_no_synthesized_padding == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateImageProps.padding_is_not_covered == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateImageProps.missing_live_field_is_covered == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateImageProps.padded_decode_ignores_padding == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateImageProps.field_census_refuses == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateImageProps.integer_width_refuses == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateImageProps.unwritten_field_has_separate_record == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateImageProps.unexplained_hole_refuses == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateImageProps.explained_whole_field_recovers_uninit == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateImageProps.partial_scalar_field_cannot_recover_uninit == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateImageProps.arrays_do_not_inherit_unwritten_permission == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateImageProps.nested_char_transports_raw_carrier == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateImageProps.scalar_char_keeps_unicode_boundary == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateImageProps.overwritten_low_record_is_clipped == [] modern []

#trustIrAxiomsPinned TrustIr.AggregateImageProps.overwritten_middle_record_splits == [] modern []

#trustIrAxiomsPinned TrustIr.AggregateImageProps.overwrite_clears_record == [] modern []

#trustIrAxiomsPinned TrustIr.AggregateImageProps.allocation_identity_is_required == [] modern []

#trustIrAxiomsPinned TrustIr.AggregateImageProps.copying_absent_bytes_creates_no_record == [] modern []

#trustIrAxiomsPinned TrustIr.AggregateImageProps.zero_sized_unwritten_record_is_omitted == [] modern []

#trustIrAxiomsPinned TrustIr.AggregateImageProps.equality_keeps_pointer_provenance == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.lookupFunctionHeader_mapFunctionCFGs == [propext] modern [propext]

#trustIrAxiomsPinned TrustIr.functionHeader_matches_mapCFG == [] modern []

#trustIrAxiomsPinned TrustIr.functionErrors_mapFunctionCFGs == [] modern []

#trustIrAxiomsPinned TrustIr.checkSeqMapElement_mapFunctionCFGs == [propext, Classical.choice, Quot.sound] modern [propext]

#trustIrAxiomsPinned TrustIr.memoryLayout_mapFunctionCFGs == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.loadMemoryValue_mapFunctionCFGs == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.storeMemoryValue_mapFunctionCFGs == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.Ty.hasCanonicalMemoryLayout_eq == [propext, Quot.sound] modern [propext]

#trustIrAxiomsPinned TrustIr.EvalContext.semGEPUsing_canonical == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateImageProps.inhabited_variant_ignores_dead_payload == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateImageProps.inhabited_variant_encodes_with_dead_payload_absent == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateImageProps.covered_dead_tag_is_ub_before_missing_payload == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateImageProps.initialized_dead_tag_is_ub == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateImageProps.dead_value_store_is_type_error == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateImageProps.unknown_tag_is_ub == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateImageProps.missing_tag_remains_uninitialized == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateImageProps.zero_byte_untagged_dead_is_ub == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateImageProps.standalone_never_image_query_remains_refused == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateImageProps.actual_preparation_keeps_only_executable_variant_payloads == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]


#trustIrAxiomsPinned TrustIr.AggregateImageProps.zeroUninit_byte == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateImageProps.zeroUninit_extent == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]
