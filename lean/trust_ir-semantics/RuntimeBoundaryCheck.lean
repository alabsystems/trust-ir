-- Copyright 2026 Andrew Yates | Apache-2.0
-- Metadata checks only; no runtime correspondence or proof-promotion verdict.
import Lean
import TrustIrRuntime
import TrustIrEval.ImageMapStepBinding

run_cmd TrustIrEval.ImageMapStepBinding.checkSourceBodies

open Lean Elab Command

private def telescopeArity : Expr → Nat
  | .forallE _ _ body _ => telescopeArity body + 1
  | _ => 0

private def field {α : Type} [FromJson α] (value : Json) (name : String) : CommandElabM α :=
  match value.getObjValAs? α name with
  | .ok result => pure result
  | .error error => throwError "runtime boundary field {name}: {error}"

run_cmd do
  let text ← IO.FS.readFile "runtime-boundary.json"
  let document ← match Json.parse text with
    | .ok value => pure value
    | .error error => throwError "runtime boundary JSON: {error}"
  let rows : Array Json ← field document "interfaces"
  unless rows.size == 15 do throwError "runtime interface census differs"
  let env ← getEnv
  let constants := env.constants.toList
  let find (text : String) := constants.filter (fun pair => pair.1.toString == text)
  for row in rows do
    let logical : String ← field row "logical_full_name"
    let runtime : String ← field row "runtime_full_name"
    let symbol : String ← field row "symbol"
    let abi : Json ← field row "abi"
    let arity : Nat ← field abi "arity"
    let logicalRows := find logical
    let runtimeRows := find runtime
    unless logicalRows.length == 1 && runtimeRows.length == 1 do
      throwError "ABI identity is absent or ambiguous: {logical} / {runtime}"
    let logicalName := logicalRows.head!.1
    let logicalInfo := logicalRows.head!.2
    let runtimeInfo := runtimeRows.head!.2
    if logicalInfo.isUnsafe || !runtimeInfo.isUnsafe then
      throwError "ABI logical/runtime safety changed: {logical} / {runtime}"
    unless logicalName.mangle == symbol && telescopeArity logicalInfo.type == arity do
      throwError "ABI mangling/arity differs: {logical} / {symbol} / {arity}"
    unless logicalInfo.type == runtimeInfo.type do
      throwError "ABI provider type differs: {logical} / {runtime}"
  logInfo "RUNTIME_ABI_DECLARATION_TYPES_PASS interfaces=15 correspondence=UNPROVED"
