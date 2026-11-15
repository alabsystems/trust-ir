-- Copyright 2026 Andrew Yates | Apache-2.0
-- Separate decoder-boundary audit: does not widen the pure formal root.
import Lean
import Lean.Replay
import TrustIrEval.DecodeRecordKeys

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `TrustIrEval.DecodeRecordKeys
  let mut targets : HashMap Name ConstantInfo := {}
  let mut roots : Array Name := #[]
  let mut compiledHelpers := 0
  for (name, info) in env.constants.map₁.toList do
    if let some index := env.getModuleIdxFor? name then
      if env.header.moduleNames[index.toNat]! == owner then
        if info.isPartial then
          throwError "wire-record-keys: partial boundary declaration {name}"
        -- As in the standing math replay, unsafe compiler staging artifacts
        -- are not logical constants. The kernel rejects any safe declaration
        -- that tries to use them; none is inherited into the replay base.
        if info.isUnsafe then
          compiledHelpers := compiledHelpers + 1
          continue
        if let .axiomInfo _ := info then
          throwError "wire-record-keys: new boundary axiom {name}"
        targets := targets.insert name info
        roots := roots.push name
  if roots.isEmpty then throwError "wire-record-keys: empty boundary audit"
  let collect : CollectAxioms.M Unit := roots.forM CollectAxioms.collect
  let (_, collected) := (collect.run env).run {}
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for ax in collected.axioms do
    unless allowed.contains ax do
      throwError "wire-record-keys: forbidden axiom {ax}"
  -- Only imported dependencies form the base. None of the boundary module's
  -- own declarations may be inherited instead of rechecked by the kernel.
  let base ← liftIO <| importModules #[
    { module := `TrustIrEval.Decode }, { module := `TrustIr.Proofs.SourceInhabitSound }] {} 0
  for name in roots do
    if base.contains name then throwError "wire-record-keys: replay target already inherited {name}"
  let replayed ← liftIO <| Environment.replay targets base
  for name in roots do
    unless replayed.contains name do throwError "wire-record-keys: kernel omitted {name}"
  logInfo m!"WIRE_RECORD_KEYS_REPLAY_PASS safe={targets.size} axioms={collected.axioms.size} partial=0 compiler-helpers={compiledHelpers}"
