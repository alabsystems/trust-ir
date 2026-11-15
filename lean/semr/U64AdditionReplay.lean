/- Copyright 2026 Andrew Yates. Apache-2.0.
   Fresh SAME-kernel replay of only the newly introduced subject/proof declarations.
   The unchanged canonical SemR/MiniRust base is imported, never re-proved here. -/
import Lean
import U64AdditionAudit

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut targets : Std.HashMap Name ConstantInfo := {}
  let mut theorems := 0
  for (name, ci) in env.constants.map₁.toList do
    if ci.isUnsafe then continue
    if let some idx := env.getModuleIdxFor? name then
      let m := env.header.moduleNames[idx.toNat]!
      -- Lean generates lazy equation helpers of imported definitions while
      -- elaborating a new module. Module-index attribution alone would call
      -- unchanged SemR.constVal.eq_* a new scalar declaration. Replay exactly
      -- this source's public/private namespaces; the canonical base supplies
      -- its own generated equation helpers through normal kernel lookup.
      if (m == `U64Addition || m == `U64AdditionAudit) &&
          ((`SemRU64Addition).isPrefixOf name || (`SemRU64AdditionAudit).isPrefixOf name ||
            name.toString.startsWith "_private.U64Addition.0.SemRU64Addition.") then
        if let .axiomInfo _ := ci then
          throwError "new scalar subject declares an axiom: {name}"
        if let .thmInfo _ := ci then theorems := theorems + 1
        targets := targets.insert name ci
  if targets.isEmpty || theorems < 14 then
    throwError "empty/incomplete scalar replay: {targets.size} declarations, {theorems} theorems"
  let base ← liftIO <| importModules #[{ module := `SemRMiniRust }] {} 0
  -- Close over genuine source-environment dependencies missing from the fresh
  -- imported base, including Lean's lazy generated equation helpers. Never
  -- inject guessed constants or new axioms, and do not treat names as proofs.
  let mut pending := targets.toArray.map Prod.fst
  let mut visited : Std.HashSet Name := {}
  let mut budget := 100000
  while !pending.isEmpty do
    if budget == 0 then throwError "scalar replay dependency bound"
    budget := budget - 1
    let name := pending.back!
    pending := pending.pop
    if visited.contains name then continue
    visited := visited.insert name
    let some ci := env.find? name | throwError "missing original declaration {name}"
    let deps := match ci with
      | .thmInfo v => v.type.getUsedConstants ++ v.value.getUsedConstants
      | .defnInfo v => v.type.getUsedConstants ++ v.value.getUsedConstants
      | .opaqueInfo v => v.type.getUsedConstants ++ v.value.getUsedConstants
      | _ => ci.type.getUsedConstants
    for dep in deps do
      if (base.find? dep).isSome then continue
      let some value := env.find? dep | throwError "missing actual source dependency {dep}"
      if value.isUnsafe then throwError "unsafe scalar dependency {dep}"
      if let .axiomInfo _ := value then throwError "new scalar dependency axiom {dep}"
      targets := targets.insert dep value
      pending := pending.push dep
  let checked ← liftIO <| Environment.replay targets base
  for (name, _) in targets do
    -- replay returns Environment.ofKernelEnv; its API explicitly forbids
    -- leaking this temporary wrapper into elaborator async lookup. New checked
    -- declarations live in the kernel map₂, so inspect that actual kernel map.
    unless (checked.toKernelEnv.find? name).isSome do
      throwError "scalar replay skipped {name}"
  let key := `SemRU64Addition.original_return
  let some (.thmInfo original) := targets[key]? | throwError "required actual return theorem missing"
  let bad := targets.insert key (.thmInfo { original with value := mkConst ``True.intro })
  let rejected ← liftIO do
    try
      let _ ← Environment.replay bad base
      pure false
    catch _ => pure true
  unless rejected do throwError "kernel accepted a replaced original-return proof"
  logInfo m!"SEMR_U64_REPLAY declarations={targets.size} theorems={theorems} missing=0 new-axioms=0 wrong-term-refused=1; unchanged SemR/MiniRust imported; SAME Lean kernel, not a new independent checker"
