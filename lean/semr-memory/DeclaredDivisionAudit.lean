-- Copyright 2026 Andrew Yates
-- Licensed under the Apache License, Version 2.0

import Lean
import Lean.Replay
import SemRDeclaredDivisionCanonical

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
  let some index := modules.toList.idxOf? `SemRDeclaredDivisionReturn
    | throwError "Declared division relation audit: proof module was not imported"
  let mut targets : Std.HashMap Name ConstantInfo := {}
  let mut theorems := 0
  for (name, info) in env.constants.toList do
    if let some origin := env.getModuleIdxFor? name then
      if origin.toNat == index ||
          [`SemRDeclaredDivisionChecks, `SemRStructLayout, `SemRStructLayoutChecks,
            `SemRDeclaredDivisionPacket, `SemRDeclaredDivisionCanonical,
            `TrustIrEval.ConstantLayerControls].contains
            modules[origin.toNat]! then
        if info.isUnsafe || info.isPartial then
          throwError "Declared division relation audit: unsafe/partial declaration {name}"
        match info with
        | .axiomInfo _ | .opaqueInfo _ =>
          throwError "Declared division relation audit: axiom/opaque declaration {name}"
        | .thmInfo _ => theorems := theorems + 1
        | _ => pure ()
        for axiomName in ← collectAxioms name do
          unless [``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
            throwError "Declared division relation audit: forbidden axiom {axiomName} in {name}"
        targets := targets.insert name info
  if targets.isEmpty then
    throwError "Declared division relation audit: an empty declaration inventory is not a pass"
  for required in [
      `SemR.CanonicalDeclaredDivision.source_start,
      `SemR.CanonicalDeclaredDivision.source_function,
      `SemR.CanonicalDeclaredDivision.target_parameter_binding,
      `SemR.CanonicalDeclaredDivision.target_entry_fresh,
      `SemR.CanonicalDeclaredDivision.target_constant_fresh,
      `SemR.CanonicalDeclaredDivision.target_constant_step,
      `SemR.CanonicalDeclaredDivision.target_entry_block,
      `SemR.CanonicalDeclaredDivision.target_entry_checks,
      `SemR.CanonicalDeclaredDivision.target_function,
      `SemR.CanonicalDeclaredDivision.function_wp_iff,
      `SemR.CanonicalDeclaredDivision.Packet.original_body_execution,
      `SemR.CanonicalDeclaredDivision.Packet.original_canonical_return_iff,
      `SemR.CanonicalDeclaredDivision.Packet.original_source_decodes,
      `SemR.CanonicalDeclaredDivision.Packet.original_context_prepares,
      `TrustIrEval.ConstantLayerControls.public_scalar_int_uses_the_original_layer,
      `SemR.CanonicalStructLayout.query_uses_canonical,
      `SemR.CanonicalStructLayout.fields_preserve_offsets,
      `SemR.CanonicalDeclaredDivision.Checks.false_post_has_no_success_witness,
      `SemR.CanonicalDeclaredDivision.Checks.discarded_quotient_still_owes_domain] do
    unless targets.contains required do
      throwError "Declared division relation audit: required theorem missing: {required}"
  let imports : Array Import := #[{ module := `SemRScalarReturn },
    { module := `SemRUnsignedSelect }, { module := `TrustIr.Layout.Service },
    { module := `TrustIrEval.Decode }, { module := `TrustIr.DecodedContext }]
  let replayed ← liftIO do
    let base ← importModules imports {} 0
    for (name, _) in targets.toList do
      if (base.toKernelEnv.find? name).isSome then
        throw (IO.userError s!"Declared division relation audit: replay base already contains {name}")
    Environment.replay targets base
  for (name, expected) in targets.toList do
    -- Environment.replay returns a kernel environment. Its newly checked
    -- declarations need not be in the elaborator's asynchronous/public view.
    let some actual := replayed.toKernelEnv.find? name
      | throwError "Declared division relation audit: declaration was not replayed: {name}"
    -- Exact expression read-back includes theorem bodies and binder metadata.
    -- This comparison makes no complete ConstantInfo metadata-identity claim.
    let sameValue :=
      match actual.value? (allowOpaque := true), expected.value? (allowOpaque := true) with
      | some actualValue, some expectedValue => Expr.equal actualValue expectedValue
      | none, none => true
      | _, _ => false
    unless Expr.equal actual.type expected.type && sameValue do
      throwError "Declared division relation audit: replayed declaration type/body changed: {name}"
  logInfo s!"semr-declared-division audit: declarations={targets.size} theorems={theorems} replayed={targets.size} native-evaluations=0"
