-- Copyright 2026 Andrew Yates | Apache-2.0
import Lean
import TrustIr.State.ByteImage

-- The standard Lean-core axioms are explicit; no runtime/native/sorry axiom is allowed.
#trustIrAxioms TrustIr.ByteImage.Tree.mapStep_refines <= [propext, Classical.choice, Quot.sound]
#trustIrAxioms TrustIr.ByteImage.Tree.mapStep_pure <= [propext, Classical.choice, Quot.sound]

#trustIrAxioms TrustIr.ByteImage.Tree.mapCacheStep_hit <= [propext, Classical.choice, Quot.sound]
#trustIrAxioms TrustIr.ByteImage.Tree.mapCacheStep_miss <= [propext, Classical.choice, Quot.sound]
#trustIrAxioms TrustIr.ByteImage.tree_cast_of_image_eq <= [propext, Classical.choice, Quot.sound]
#trustIrAxioms TrustIr.ByteImage.Tree.mapCacheStep_refines <= [propext, Classical.choice, Quot.sound]

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for module in env.header.moduleNames do
    if module.toString.startsWith "TrustIrRuntime" then
      throwError "runtime module entered the shared-step logical proof closure: {module}"
  logInfo "IMAGE_MAP_SHARED_STEP_PROOF_IMPORTS_SAFE cache_and_machine_correspondence=UNPROVED"
