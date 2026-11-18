-- Copyright 2026 Andrew Yates
-- Licensed under the Apache License, Version 2.0

import Lean
import Lean.Replay
import SemRUnsignedRemainderChecks

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
  let some index := modules.toList.idxOf? `SemRUnsignedRemainder
    | throwError "Unsigned remainder relation audit: proof module was not imported"
  let mut targets : Std.HashMap Name ConstantInfo := {}
  let mut theorems := 0
  for (name, info) in env.constants.toList do
    if let some origin := env.getModuleIdxFor? name then
      if origin.toNat == index || modules[origin.toNat]! == `SemRUnsignedRemainderChecks ||
          modules[origin.toNat]! == `TrustIr.Proofs.UnsignedRemainderWp then
        if info.isUnsafe || info.isPartial then
          throwError "Unsigned remainder relation audit: unsafe/partial declaration {name}"
        match info with
        | .axiomInfo _ | .opaqueInfo _ =>
          throwError "Unsigned remainder relation audit: axiom/opaque declaration {name}"
        | .thmInfo _ => theorems := theorems + 1
        | _ => pure ()
        for axiomName in ← collectAxioms name do
          unless [``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
            throwError "Unsigned remainder relation audit: forbidden axiom {axiomName} in {name}"
        targets := targets.insert name info
  if targets.isEmpty then
    throwError "Unsigned remainder relation audit: an empty declaration inventory is not a pass"
  for required in [
      `SemR.CanonicalUnsignedRemainder.value,
      `SemR.CanonicalUnsignedRemainder.zero,
      `SemR.CanonicalUnsignedRemainder.wp_iff,
      `SemR.CanonicalUnsignedRemainder.dead_result_iff,
      `TrustIr.UnsignedRemainderWp.remainder_range,
      `TrustIr.UnsignedRemainderWp.value,
      `TrustIr.UnsignedRemainderWp.wp_iff,
      `TrustIr.UnsignedRemainderWp.zero,
      `TrustIr.UnsignedRemainderWp.u64_wp_iff,
      `TrustIr.UnsignedRemainderWp.dead_result_wp_iff] do
    unless targets.contains required do
      throwError "Unsigned remainder relation audit: required theorem missing: {required}"
  let imports : Array Import := #[{ module := `SemR },
    { module := `TrustIr.Proofs.BitVecUnsignedValues },
    { module := `TrustIr.Semantics.Arith }]
  let replayed ← liftIO do
    let base ← importModules imports {} 0
    for (name, _) in targets.toList do
      if (base.toKernelEnv.find? name).isSome then
        throw (IO.userError s!"Unsigned remainder relation audit: replay base already contains {name}")
    Environment.replay targets base
  for (name, expected) in targets.toList do
    -- Environment.replay returns a kernel environment. Its newly checked
    -- declarations need not be in the elaborator's asynchronous/public view.
    let some actual := replayed.toKernelEnv.find? name
      | throwError "Unsigned remainder relation audit: declaration was not replayed: {name}"
    unless actual.type == expected.type && actual.value? == expected.value? do
      throwError "Unsigned remainder relation audit: replayed declaration changed: {name}"
  logInfo s!"semr-unsigned-remainder audit: declarations={targets.size} theorems={theorems} replayed={targets.size} native-evaluations=0"
