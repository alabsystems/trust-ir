-- Copyright 2026 Andrew Yates | Apache-2.0
-- Focused same-kernel replay of the entire changed logical module. Not a second kernel.
import Lean.Replay
import TrustIr.State.ByteImage

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut targets : HashMap Name ConstantInfo := {}
  for (name, ci) in env.constants.map₁.toList do
    if let some index := env.getModuleIdxFor? name then
      if env.header.moduleNames[index.toNat]! == `TrustIr.State.ByteImage then
        unless ci.isUnsafe do targets := targets.insert name ci
  for required in [``TrustIr.ByteImage.Tree.mapStep,
      ``TrustIr.ByteImage.Tree.mapStep_refines, ``TrustIr.ByteImage.Tree.mapStep_pure,
      ``TrustIr.ByteImage.Tree.mapCacheStep, ``TrustIr.ByteImage.Tree.mapCacheStep_refines] do
    unless targets.contains required do throwError "missing shared-step replay target: {required}"
  -- ByteImage itself is deliberately absent from this base environment.
  let base ← liftIO <| importModules #[{ module := `TrustIr.CompilerCompat },
    { module := `Lean.Replay }] {} 0
  unless !(base.contains ``TrustIr.ByteImage.Tree.mapStep) do
    throwError "vacuous shared-step replay base"
  let replayed ← liftIO <| Environment.replay targets base
  let mut partialBodies : Array Name := #[]
  for (name, ci) in targets.toList do
    if replayed.contains name then continue
    match ci with
    | .defnInfo definition =>
      if definition.safety == .partial then partialBodies := partialBodies.push name
      else throwError "shared-step kernel replay skipped {name}"
    | _ => throwError "shared-step kernel replay skipped {name}"
  -- Lean skips partial compiler bodies; a safe proof depending on one still fails replay.
  logInfo m!"IMAGE_MAP_SHARED_STEP_KERNEL_REPLAY safe_constants={targets.size} replayed={targets.size - partialBodies.size} skipped_partial={partialBodies} runtime_correspondence=UNPROVED"
