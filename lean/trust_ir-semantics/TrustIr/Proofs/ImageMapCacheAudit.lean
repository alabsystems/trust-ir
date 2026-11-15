-- Copyright 2026 Andrew Yates | Apache-2.0
import TrustIr.Proofs.ByteImageMapCacheRefinement

-- Logical refinement only; physical/native implementation duties remain open.
#trustIrAxioms TrustIr.ByteImage.Tree.mapStepBelow_eq_mapStep <= [propext, Classical.choice, Quot.sound]
#trustIrAxioms TrustIr.ByteImage.MapNodeView.mapStep_eq_mapStep <= [propext, Classical.choice, Quot.sound]
#trustIrAxioms TrustIr.ByteImage.mapRefKeyed_hit <= [propext, Classical.choice, Quot.sound]
#trustIrAxioms TrustIr.ByteImage.mapRefKeyed_miss <= [propext, Classical.choice, Quot.sound]
#trustIrAxioms TrustIr.ByteImage.MapCacheLaws.find_empty_capacity <= [propext, Classical.choice, Quot.sound]
#trustIrAxioms TrustIr.ByteImage.MapCacheLaws.find_empty <= [propext, Classical.choice, Quot.sound]
#trustIrAxioms TrustIr.ByteImage.MapCacheLaws.find_insert <= [propext, Classical.choice, Quot.sound]
#trustIrAxioms TrustIr.ByteImage.ImageMapRefinement.stateInvariant_empty <= [propext, Classical.choice, Quot.sound]
#trustIrAxioms TrustIr.ByteImage.ImageMapRefinement.stateInvariant_insert <= [propext, Classical.choice, Quot.sound]
#trustIrAxioms TrustIr.ByteImage.ImageMapRefinement.viewStep_refines <= [propext, Classical.choice, Quot.sound]
#trustIrAxioms TrustIr.ByteImage.ImageMapRefinement.mapRefKeyed_refines <= [propext, Classical.choice, Quot.sound]
#trustIrAxioms TrustIr.ByteImage.ImageMapRefinement.mapRefKeyed_empty_refines <= [propext, Classical.choice, Quot.sound]
#trustIrAxioms TrustIr.ByteImage.ImageMapRefinement.mapRefKeyed_empty_image_refines <= [propext, Classical.choice, Quot.sound]

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for module in env.header.moduleNames do
    if module.toString.startsWith "TrustIrRuntime" then
      throwError "runtime module entered the reference-cache logical proof closure: {module}"
  logInfo "IMAGE_MAP_REFERENCE_CACHE_LOGICAL_REFINEMENT physical_ID_source_lifetime_observation_ABI=UNPROVED"
