-- Copyright 2026 Andrew Yates
-- Licensed under the Apache License, Version 2.0

import Lean
import Lean.Replay
import SemRBoolAccess

/-! Standing audit of every declaration of this proof component, including
private/generated declarations. Replay uses the same Lean kernel on top of
the component's imports; the independent Clean reference replay is separate.
No new axiom, opaque, unsafe/partial declaration or native evaluation is
accepted as a proof. This audit grants no compiler or obligation authority.
-/

open Lean Elab Command in
run_cmd do
  let env := (← getEnv).setExporting false
  let modules := env.header.moduleNames
  let some index := modules.toList.idxOf? `SemRBoolAccess
    | throwError "Bool access audit: proof module was not imported"
  let mut targets : Std.HashMap Name ConstantInfo := {}
  let mut theorems := 0
  for (name, info) in env.constants.toList do
    if let some origin := env.getModuleIdxFor? name then
      if origin.toNat == index then
        if info.isUnsafe || info.isPartial then
          throwError "Bool access audit: unsafe/partial declaration {name}"
        match info with
        | .axiomInfo _ | .opaqueInfo _ =>
          throwError "Bool access audit: axiom/opaque declaration {name}"
        | .thmInfo _ => theorems := theorems + 1
        | _ => pure ()
        for axiomName in ← collectAxioms name do
          unless [``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
            throwError "Bool access audit: forbidden axiom {axiomName} in {name}"
        targets := targets.insert name info
  if targets.isEmpty then
    throwError "Bool access audit: an empty declaration inventory is not a pass"
  for required in [
      `SemR.BoolMemory.checked_access_cell,
      `SemR.BoolMemory.semLoad_bool_cell,
      `SemR.BoolMemory.semLoad_poison_cell,
      `SemR.BoolMemory.semLoad_strict_poison_refuses,
      `SemR.BoolMemory.semStore_bool_cell,
      `SemR.BoolMemory.semStore_poison_cell,
      `SemR.BoolMemory.semStore_strict_poison_refuses,
      `SemR.BoolMemory.semStore_bool_preserves_cell,
      `SemR.BoolMemory.semStore_poison_preserves_cell,
      `SemR.BoolMemory.semStore_bool_then_load,
      `SemR.BoolMemory.semStore_poison_then_load,
      `SemR.BoolMemory.semLoad_wrong_allocation_refuses,
      `SemR.BoolMemory.semStore_wrong_allocation_refuses,
      `SemR.BoolMemory.semLoad_missing_provenance_refuses,
      `SemR.BoolMemory.semLoad_dead_allocation_refuses,
      `SemR.BoolMemory.semLoad_unknown_allocation_refuses,
      `SemR.BoolMemory.semLoad_declared_alignment_refuses,
      `SemR.BoolMemory.semLoad_plain_poison_control,
      `SemR.BoolMemory.semLoad_strict_poison_control] do
    unless targets.contains required do
      throwError "Bool access audit: required theorem missing: {required}"
  let imports := env.header.moduleData[index]!.imports
  let replayed ← liftIO do
    let base ← importModules imports {} 0
    for (name, _) in targets.toList do
      if (base.toKernelEnv.find? name).isSome then
        throw (IO.userError s!"Bool access audit: replay base already contains {name}")
    Environment.replay targets base
  for (name, expected) in targets.toList do
    -- Environment.replay returns a kernel environment. Its newly checked
    -- declarations need not be in the elaborator's asynchronous/public view.
    let some actual := replayed.toKernelEnv.find? name
      | throwError "Bool access audit: declaration was not replayed: {name}"
    unless actual.type == expected.type && actual.value? == expected.value? do
      throwError "Bool access audit: replayed declaration changed: {name}"
  logInfo s!"semr-bool-access audit: declarations={targets.size} theorems={theorems} replayed={targets.size} native-evaluations=0"
