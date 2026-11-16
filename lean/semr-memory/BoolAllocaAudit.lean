-- Copyright 2026 Andrew Yates
-- Licensed under the Apache License, Version 2.0

import Lean
import Lean.Replay
import SemRBoolAlloca

/-! Inventory and same-kernel replay of every component-owned declaration.
The independent Clean replay remains a separate qualification obligation.
-/

open Lean Elab Command in
run_cmd do
  let env := (← getEnv).setExporting false
  let modules := env.header.moduleNames
  let some index := modules.toList.idxOf? `SemRBoolAlloca
    | throwError "Bool Alloca audit: proof module was not imported"
  let mut targets : Std.HashMap Name ConstantInfo := {}
  let mut theorems := 0
  for (name, info) in env.constants.toList do
    if let some origin := env.getModuleIdxFor? name then
      if origin.toNat == index then
        if info.isUnsafe || info.isPartial then
          throwError "Bool Alloca audit: unsafe/partial declaration {name}"
        match info with
        | .axiomInfo _ | .opaqueInfo _ =>
          throwError "Bool Alloca audit: axiom/opaque declaration {name}"
        | .thmInfo _ => theorems := theorems + 1
        | _ => pure ()
        for axiomName in ← collectAxioms name do
          unless [``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
            throwError "Bool Alloca audit: forbidden axiom {axiomName} in {name}"
        targets := targets.insert name info
  if targets.isEmpty then
    throwError "Bool Alloca audit: an empty declaration inventory is not a pass"
  for required in [
      `SemR.BoolMemory.semAlloca_bool_result,
      `SemR.BoolMemory.semAlloca_bool_checked_result,
      `SemR.BoolMemory.semAlloca_bool_address_exhaustion,
      `SemR.BoolMemory.semAlloca_bool_identifier_exhaustion,
      `SemR.BoolMemory.semAlloca_bool_exhaustion_is_not_success,
      `SemR.BoolMemory.boolAlloca_result_id,
      `SemR.BoolMemory.boolAlloca_result_memory,
      `SemR.BoolMemory.boolAlloca_next_value,
      `SemR.BoolMemory.boolAlloca_fresh,
      `SemR.BoolMemory.boolAlloca_new_cell,
      `SemR.BoolMemory.boolAlloca_new_pointer,
      `SemR.BoolMemory.boolAlloca_owned_permission,
      `SemR.BoolMemory.boolAlloca_other_permission,
      `SemR.BoolMemory.boolAlloca_other_local,
      `SemR.BoolMemory.boolAlloca_preserves_cell,
      `SemR.BoolMemory.boolAlloca_other_state,
      `SemR.BoolMemory.semAlloca_bool_then_load_poison,
      `SemR.BoolMemory.semAlloca_bool_then_strict_load_refuses,
      `SemR.BoolMemory.semAlloca_bool_empty_plain_poison,
      `SemR.BoolMemory.semAlloca_bool_zero_alignment_refuses,
      `SemR.BoolMemory.boolAlloca_reused_ssa_control,
      `SemR.BoolMemory.semAlloca_bool_exhausted_identity_refuses,
      `SemR.BoolMemory.semAlloca_bool_exhausted_address_refuses] do
    unless targets.contains required do
      throwError "Bool Alloca audit: required theorem missing: {required}"
  let imports := env.header.moduleData[index]!.imports
  let replayed ← liftIO do
    let base ← importModules imports {} 0
    for (name, _) in targets.toList do
      if (base.toKernelEnv.find? name).isSome then
        throw (IO.userError s!"Bool Alloca audit: replay base already contains {name}")
    Environment.replay targets base
  for (name, expected) in targets.toList do
    let some actual := replayed.toKernelEnv.find? name
      | throwError "Bool Alloca audit: declaration was not replayed: {name}"
    unless actual.type == expected.type && actual.value? == expected.value? do
      throwError "Bool Alloca audit: replayed declaration changed: {name}"
  logInfo s!"semr-bool-alloca audit: declarations={targets.size} theorems={theorems} replayed={targets.size} native-evaluations=0"
