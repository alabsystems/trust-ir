-- Copyright 2026 Andrew Yates
-- Licensed under the Apache License, Version 2.0

import Lean
import Lean.Replay
import SemRScalarStepChecks

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
  let some index := modules.toList.idxOf? `SemRScalarStep
    | throwError "Scalar step relation audit: proof module was not imported"
  let mut targets : Std.HashMap Name ConstantInfo := {}
  let mut theorems := 0
  for (name, info) in env.constants.toList do
    if let some origin := env.getModuleIdxFor? name then
      if origin.toNat == index || modules[origin.toNat]! == `SemRScalarStepChecks then
        if info.isUnsafe || info.isPartial then
          throwError "Scalar step relation audit: unsafe/partial declaration {name}"
        match info with
        | .axiomInfo _ | .opaqueInfo _ =>
          throwError "Scalar step relation audit: axiom/opaque declaration {name}"
        | .thmInfo _ => theorems := theorems + 1
        | _ => pure ()
        for axiomName in ← collectAxioms name do
          unless [``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
            throwError "Scalar step relation audit: forbidden axiom {axiomName} in {name}"
        targets := targets.insert name info
  if targets.isEmpty then
    throwError "Scalar step relation audit: an empty declaration inventory is not a pass"
  for required in [
      `SemR.CanonicalScalarStep.source_step,
      `SemR.CanonicalScalarStep.target_step_raw,
      `SemR.CanonicalScalarStep.target_after_lookup,
      `SemR.CanonicalScalarStep.registers_preserved,
      `SemR.CanonicalScalarStep.division_step_wp_iff,
      `SemR.CanonicalScalarStep.division_step_registers_iff,
      `SemR.CanonicalScalarStep.Controls.source_actual_step,
      `SemR.CanonicalScalarStep.Controls.target_actual_step,
      `SemR.CanonicalScalarStep.Controls.zero_refuses_both_steps,
      `SemR.CanonicalScalarStep.Controls.missing_freshness_cannot_preserve_register_agreement,
      `SemR.CanonicalScalarStep.Controls.occupied_temporary_initial_registers_agree,
      `SemR.CanonicalScalarStep.Controls.input_alias_actual_steps,
      `SemR.CanonicalScalarStep.Controls.original_destination_declaration_is_checked,
      `SemR.CanonicalScalarStep.Controls.false_postcondition_stays_false] do
    unless targets.contains required do
      throwError "Scalar step relation audit: required theorem missing: {required}"
  let imports := env.header.moduleData[index]!.imports
  let replayed ← liftIO do
    let base ← importModules imports {} 0
    for (name, _) in targets.toList do
      if (base.toKernelEnv.find? name).isSome then
        throw (IO.userError s!"Scalar step relation audit: replay base already contains {name}")
    Environment.replay targets base
  for (name, expected) in targets.toList do
    -- Environment.replay returns a kernel environment. Its newly checked
    -- declarations need not be in the elaborator's asynchronous/public view.
    let some actual := replayed.toKernelEnv.find? name
      | throwError "Scalar step relation audit: declaration was not replayed: {name}"
    unless actual.type == expected.type && actual.value? == expected.value? do
      throwError "Scalar step relation audit: replayed declaration changed: {name}"
  logInfo s!"semr-scalar-step audit: declarations={targets.size} theorems={theorems} replayed={targets.size} native-evaluations=0"
