-- Copyright 2026 Andrew Yates
-- Licensed under the Apache License, Version 2.0

import Lean
import Lean.Replay
import SemRBoolHeap

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
  let some index := modules.toList.idxOf? `SemRBoolHeap
    | throwError "Bool heap audit: proof module was not imported"
  let mut targets : Std.HashMap Name ConstantInfo := {}
  let mut theorems := 0
  for (name, info) in env.constants.toList do
    if let some origin := env.getModuleIdxFor? name then
      if origin.toNat == index then
        if info.isUnsafe || info.isPartial then
          throwError "Bool heap audit: unsafe/partial declaration {name}"
        match info with
        | .axiomInfo _ | .opaqueInfo _ =>
          throwError "Bool heap audit: axiom/opaque declaration {name}"
        | .thmInfo _ => theorems := theorems + 1
        | _ => pure ()
        for axiomName in ← collectAxioms name do
          unless [``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
            throwError "Bool heap audit: forbidden axiom {axiomName} in {name}"
        targets := targets.insert name info
  if targets.isEmpty then
    throwError "Bool heap audit: an empty declaration inventory is not a pass"
  for required in [
      `SemR.BoolMemory.heapBase_injective,
      `SemR.BoolMemory.heapBase_disjoint,
      `SemR.BoolMemory.empty_heap,
      `SemR.BoolMemory.HeapAt.cell_identity_below,
      `SemR.BoolMemory.HeapAt.cell_exists,
      `SemR.BoolMemory.HeapAt.ids_nodup,
      `SemR.BoolMemory.HeapAt.cell_identity_injective,
      `SemR.BoolMemory.HeapAt.cell_bounds,
      `SemR.BoolMemory.HeapAt.cells_disjoint,
      `SemR.BoolMemory.HeapAt.cell_at,
      `SemR.BoolMemory.HeapAt.allocation_ids_nodup,
      `SemR.BoolMemory.HeapAt.allocation_identity_below,
      `SemR.BoolMemory.HeapAt.allocation_identity_injective,
      `SemR.BoolMemory.HeapAt.allocation_bounds,
      `SemR.BoolMemory.HeapAt.allocations_disjoint,
      `SemR.BoolMemory.HeapAt.findCell_at,
      `SemR.BoolMemory.HeapAt.allocation_guard,
      `SemR.BoolMemory.HeapAt.allocate,
      `SemR.BoolMemory.HeapAt.store_bool,
      `SemR.BoolMemory.HeapAt.store_poison,
      `SemR.BoolMemory.HeapAt.semStore_bool,
      `SemR.BoolMemory.HeapAt.semStore_poison,
      `SemR.BoolMemory.duplicate_cell_ids_refuse,
      `SemR.BoolMemory.two_allocations_have_distinct_bases,
      `SemR.BoolMemory.second_allocation_placement,
      `SemR.BoolMemory.store_first_other_cell_readback,
      `SemR.BoolMemory.store_first_preserves_second_poison] do
    unless targets.contains required do
      throwError "Bool heap audit: required theorem missing: {required}"
  let imports := env.header.moduleData[index]!.imports
  let replayed ← liftIO do
    let base ← importModules imports {} 0
    for (name, _) in targets.toList do
      if (base.toKernelEnv.find? name).isSome then
        throw (IO.userError s!"Bool heap audit: replay base already contains {name}")
    Environment.replay targets base
  for (name, expected) in targets.toList do
    -- Environment.replay returns a kernel environment. Its newly checked
    -- declarations need not be in the elaborator's asynchronous/public view.
    let some actual := replayed.toKernelEnv.find? name
      | throwError "Bool heap audit: declaration was not replayed: {name}"
    unless actual.type == expected.type && actual.value? == expected.value? do
      throwError "Bool heap audit: replayed declaration changed: {name}"
  logInfo s!"semr-bool-heap audit: declarations={targets.size} theorems={theorems} replayed={targets.size} native-evaluations=0"
