-- Copyright 2026 Andrew Yates | Apache-2.0
-- Separate decoder-boundary audit: does not widen the pure formal root.
import Lean
import Lean.Replay
import TrustIrEval.DecodeEnumAdmission
import TrustIrEval.DecodeEnumOmission
import TrustIrEval.DecodeEnumGraph
import TrustIrEval.DecodeEnumPlan
import TrustIrEval.DecodeEnumCodec
import TrustIrEval.DecodeEnumPrefix
import TrustIrEval.DecodeEnumImage
import TrustIrEval.DecodeArrayQueryOrigins
import TrustIrEval.DecodeLayoutDeterminism
import TrustIrEval.DecodeArrayLanes
import TrustIrEval.DecodePlanKinds
import TrustIrEval.DecodeArrayIdentity
import TrustIrEval.DecodeSiblingGeometry
import TrustIrEval.DecodeFieldSteps
import TrustIrEval.DecodeFieldCoherence
import TrustIrEval.DecodeFieldBindings
import TrustIrEval.Run

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owners := #[`TrustIrEval.EnumAdmission, `TrustIrEval.DecodeEnumAdmission, `TrustIrEval.DecodeEnumOmission, `TrustIrEval.DecodeEnumGraph, `TrustIrEval.DecodeEnumPlan, `TrustIrEval.DecodeEnumCodec, `TrustIrEval.DecodeEnumPrefix, `TrustIrEval.DecodeEnumImage, `TrustIrEval.DecodeArrayQueryOrigins, `TrustIrEval.DecodeLayoutDeterminism, `TrustIrEval.DecodeArrayLanes, `TrustIrEval.DecodePlanKinds, `TrustIrEval.DecodeArrayIdentity, `TrustIrEval.DecodeSiblingGeometry, `TrustIrEval.DecodeFieldSteps, `TrustIrEval.DecodeFieldCoherence, `TrustIrEval.DecodeFieldBindings, `TrustIrEval.Run]
  let mut targets : HashMap Name ConstantInfo := {}
  let mut roots : Array Name := #[]
  let mut compiledHelpers := 0
  for (name, info) in env.constants.map₁.toList do
    if let some index := env.getModuleIdxFor? name then
      if owners.contains env.header.moduleNames[index.toNat]! then
        if info.isPartial then
          throwError "wire-enum-admission: partial boundary declaration {name}"
        -- As in the standing math replay, unsafe compiler staging artifacts
        -- are not logical constants. The kernel rejects any safe declaration
        -- that tries to use them; none is inherited into the replay base.
        if info.isUnsafe then
          compiledHelpers := compiledHelpers + 1
          continue
        if let .axiomInfo _ := info then
          throwError "wire-enum-admission: new boundary axiom {name}"
        targets := targets.insert name info
        roots := roots.push name
  if roots.isEmpty then throwError "wire-enum-admission: empty boundary audit"
  let collect : CollectAxioms.M Unit := roots.forM CollectAxioms.collect
  let (_, collected) := (collect.run env).run {}
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for ax in collected.axioms do
    unless allowed.contains ax do
      throwError "wire-enum-admission: forbidden axiom {ax}"
  -- Only imported dependencies form the base. None of the boundary module's
  -- own declarations may be inherited instead of rechecked by the kernel.
  let base ← liftIO <| importModules #[
    { module := `TrustIrEval.DecodeRecordKeys }, { module := `TrustIr.Proofs.SourceLayoutArrayOrigin }, { module := `TrustIr.Proofs.SourceLayoutDeterminism }, { module := `TrustIr.Proofs.SourcePlanKinds }, { module := `TrustIr.Proofs.SourceArrayIdentity }, { module := `TrustIr.Proofs.SourceSiblingGeometry },
    { module := `TrustIr.DecodedEntry }, { module := `TrustIrEval.Observation }] {} 0
  for name in roots do
    if base.contains name then throwError "wire-enum-admission: replay target already inherited {name}"
  let replayed ← liftIO <| Environment.replay targets base
  for name in roots do
    unless replayed.contains name do throwError "wire-enum-admission: kernel omitted {name}"
  logInfo m!"WIRE_ENUM_ADMISSION_REPLAY_PASS safe={targets.size} axioms={collected.axioms.size} partial=0 compiler-helpers={compiledHelpers}"
