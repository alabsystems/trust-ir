-- Copyright 2026 Andrew Yates | Apache-2.0
import Lean
import Lean.Replay
import SemRFrameChecks

/-! Audit every declaration of each of the eight frame components, including
private/generated declarations, and replay it in a fresh kernel environment
containing only that component's imports. This is same-kernel proof checking,
not independent Clean replay, provider fidelity or native/caller authority. -/

open Lean Elab Command in
run_cmd do
  let env := (← getEnv).setExporting false
  let modules := env.header.moduleNames
  let components : List Name := [`SemRFrameMemory, `SemRFrameMemoryChecks, `SemRPlacedFrame, `SemRPlacedFrameChecks, `SemRFramePair, `SemRFramePairChecks, `SemRFrameStep, `SemRFrameCaller]
  let required : List (Name × Name) := [
    (`SemRFrameMemory, `SemR.MemoryEmbedding.Embeds.private_frame_writes),
    (`SemRFrameMemory, `SemR.MemoryEmbedding.Embeds.written_u8),
    (`SemRFrameMemory, `SemR.MemoryEmbedding.storeStep_u8_core),
    (`SemRFrameMemory, `SemR.MemoryEmbedding.accessAt_u8),
    (`SemRFrameMemory, `SemR.MemoryEmbedding.storeStep_u8),
    (`SemRFrameMemory, `SemR.MemoryEmbedding.loadStep_u8),
    (`SemRFrameMemory, `SemR.MemoryEmbedding.castStep_trunc_u64_u8),
    (`SemRFrameMemory, `SemR.MemoryEmbedding.castStep_zext_u8_u64),
    (`SemRFrameMemory, `SemR.MemoryEmbedding.step_u8_of_storeStep),
    (`SemRFrameMemory, `SemR.MemoryEmbedding.loadStep_u8_core),
    (`SemRFrameMemory, `SemR.MemoryEmbedding.castStep_core),
    (`SemRFrameMemory, `SemR.MemoryEmbedding.retStep_preserves_data),
    (`SemRFrameMemory, `SemR.MemoryEmbedding.Embeds.after_allocates),
    (`SemRFrameMemory, `SemR.MemoryEmbedding.FrameAllocationInput.actual_frame),
    (`SemRFrameMemoryChecks, `SemR.MemoryEmbedding.Checks.observed_o0_windows_preserve),
    (`SemRPlacedFrame, `SemR.MemoryEmbedding.FrameRecordInput.separates),
    (`SemRPlacedFrame, `SemR.MemoryEmbedding.FrameRecordInput.write),
    (`SemRPlacedFrame, `SemR.MemoryEmbedding.FrameRecordInput.source_access_apart),
    (`SemRPlacedFrameChecks, `SemR.MemoryEmbedding.PlacedChecks.below_source_is_admitted),
    (`SemRPlacedFrameChecks, `SemR.MemoryEmbedding.PlacedChecks.lower_frame_pair_preserves),
    (`SemRFramePair, `SemR.MemoryEmbedding.FramePair.rawWriteBytes_cons),
    (`SemRFramePair, `SemR.MemoryEmbedding.FramePair.raw_represents_write),
    (`SemRFramePair, `SemR.MemoryEmbedding.FramePair.save_restore_exact),
    (`SemRFramePair, `SemR.MemoryEmbedding.FramePair.placed_pair_raw_readback),
    (`SemRFramePairChecks, `SemR.MemoryEmbedding.FramePair.Checks.uninitialized_pair),
    (`SemRFramePairChecks, `SemR.MemoryEmbedding.FramePair.Checks.initialized_pair),
    (`SemRFramePairChecks, `SemR.MemoryEmbedding.FramePair.Checks.initialized_source_store_agreement),
    (`SemRFramePairChecks, `SemR.MemoryEmbedding.FramePair.Checks.initialized_u8_store_executes),
    (`SemRFramePairChecks, `SemR.MemoryEmbedding.FramePair.Checks.arbitrary_u8_store_executes),
    (`SemRFramePairChecks, `SemR.MemoryEmbedding.FramePair.Checks.initialized_u8_load_executes),
    (`SemRFramePairChecks, `SemR.MemoryEmbedding.FramePair.Checks.initialized_u8_load_source_raw),
    (`SemRFramePairChecks, `SemR.MemoryEmbedding.FramePair.Checks.initialized_u8_store_reaches_terminal),
    (`SemRFramePairChecks, `SemR.MemoryEmbedding.FramePair.Checks.initialized_u8_source_raw),
    (`SemRFramePairChecks, `SemR.MemoryEmbedding.FramePair.Checks.initialized_u8_preserves_other_source_bytes),
    (`SemRFramePairChecks, `SemR.MemoryEmbedding.FramePair.Checks.source_u8_poison_is_not_initialized),
    (`SemRFramePairChecks, `SemR.MemoryEmbedding.FramePair.Checks.source_u8_bad_accesses_refuse),
    (`SemRFramePairChecks, `SemR.MemoryEmbedding.FramePair.Checks.source_path_computations),
    (`SemRFramePairChecks, `SemR.MemoryEmbedding.FramePair.Checks.source_path_derives_each_operation_from_entry_values),
    (`SemRFramePairChecks, `SemR.MemoryEmbedding.FramePair.Checks.original_b8_module_decodes),
    (`SemRFramePairChecks, `SemR.MemoryEmbedding.FramePair.Checks.original_b8_source_execution),
    (`SemRFramePairChecks, `SemR.MemoryEmbedding.FramePair.Checks.source_path_reaches_caller_return),
    (`SemRFramePairChecks, `SemR.MemoryEmbedding.FramePair.Checks.source_path_changed_inputs_refuse),
    (`SemRFramePairChecks, `SemR.MemoryEmbedding.FramePair.Checks.source_path_alias_keeps_loaded_value),
    (`SemRFramePairChecks, `SemR.MemoryEmbedding.FramePair.Checks.saved_frame_differs_from_bare_source),
    (`SemRFrameStep, `SemR.MemoryEmbedding.FrameStep.effectStoreBytes_cons),
    (`SemRFrameStep, `SemR.MemoryEmbedding.FrameStep.save_step),
    (`SemRFrameStep, `SemR.MemoryEmbedding.FrameStep.effectStore64_eq),
    (`SemRFrameCaller, `SemR.MemoryEmbedding.FrameCaller.save_call_restore),
    (`SemRFrameCaller, `SemR.MemoryEmbedding.FrameCaller.overwritten_lr_refuses_agreement),
    (`SemRFrameCaller, `SemR.MemoryEmbedding.FrameCaller.separate_store_agreement),
    (`SemRFrameCaller, `SemR.MemoryEmbedding.FrameCaller.source_store_separate),
    (`SemRFrameCaller, `SemR.MemoryEmbedding.FrameCaller.source_store_agreement),
    (`SemRFrameCaller, `SemR.MemoryEmbedding.FrameCaller.source_u8_store_raw),
    (`SemRFrameCaller, `SemR.MemoryEmbedding.FrameCaller.source_u8_store_derived_raw),
    (`SemRFrameCaller, `SemR.MemoryEmbedding.FrameCaller.source_u8_load_derived_raw),
    (`SemRFrameCaller, `SemR.MemoryEmbedding.FrameCaller.source_u8_load_store_path),
    (`SemRFrameCaller, `SemR.MemoryEmbedding.FrameCaller.source_u8_load_store_derived_raw),
    (`SemRFrameCaller, `SemR.MemoryEmbedding.FrameCaller.saved_lr_not_separate)
  ]
  unless components.length == 8 && components.eraseDups.length == 8 do
    throwError "Frame audit: exactly eight distinct frame components are required"
  for (owner, _) in required do
    unless components.contains owner do
      throwError "Frame audit: required component omitted: {owner}"
  let mut declarations := 0
  let mut theorems := 0
  let mut replayCount := 0
  for component in components do
    let some index := modules.toList.idxOf? component
      | throwError "Frame audit: component was not imported: {component}"
    let mut targets : Std.HashMap Name ConstantInfo := {}
    let mut componentTheorems := 0
    for (name, info) in env.constants.toList do
      if let some origin := env.getModuleIdxFor? name then
        if origin.toNat == index then
          if info.isUnsafe || info.isPartial then
            throwError "Frame audit: unsafe/partial declaration {name}"
          match info with
          | .axiomInfo _ | .opaqueInfo _ =>
            throwError "Frame audit: axiom/opaque declaration {name}"
          | .thmInfo _ => componentTheorems := componentTheorems + 1
          | _ => pure ()
          for axiomName in ← collectAxioms name do
            unless [``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
              throwError "Frame audit: forbidden axiom {axiomName} in {name}"
          targets := targets.insert name info
    if targets.isEmpty || componentTheorems == 0 then
      throwError "Frame audit: empty component declaration/theorem inventory: {component}"
    for (owner, name) in required do
      if owner == component then
        let some info := targets[name]?
          | throwError "Frame audit: required theorem missing from {component}: {name}"
        match info with
        | .thmInfo _ => pure ()
        | _ => throwError "Frame audit: required declaration is not a theorem: {name}"
    let imports := env.header.moduleData[index]!.imports
    let replayed ← liftIO do
      let base ← importModules imports {} 0
      for (name, _) in targets.toList do
        if (base.toKernelEnv.find? name).isSome then
          throw (IO.userError s!"Frame audit: replay base already contains {name}")
      Environment.replay targets base
    for (name, expected) in targets.toList do
      let some actual := replayed.toKernelEnv.find? name
        | throwError "Frame audit: declaration was not replayed: {name}"
      unless actual.type == expected.type && actual.value? == expected.value? do
        throwError "Frame audit: replayed declaration changed: {name}"
    declarations := declarations + targets.size
    theorems := theorems + componentTheorems
    replayCount := replayCount + targets.size
    logInfo s!"semr-frame component: module={component} declarations={targets.size} theorems={componentTheorems} replayed={targets.size} native-evaluations=0"
  logInfo s!"semr-frame audit: declarations={declarations} theorems={theorems} replayed={replayCount} native-evaluations=0"
