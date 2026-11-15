-- Copyright 2026 Andrew Yates | Apache-2.0
import TrustIrRuntime
import TrustIrEval.Run
import TrustIr.Proofs.GenericCoroProps

/-! Test-only connection from cold decoded module graphs to the actual
    expansion factory. This reports computations; it issues no certificate. -/

open TrustIr Lean

namespace TrustIrEval.CoroPrefixFactory

def errorJson (message : String) : Json :=
  Json.mkObj [("error", Json.str message)]

def auditPair (request : Json) : Except String Json := do
  let sourceJson ← request.getObjVal? "source"
  let targetJson ← request.getObjVal? "target"
  let selected ← (← request.getObjVal? "selected").getNat?
  let source ← (TrustIrEval.module sourceJson).mapError (fun error => reprStr error)
  let target ← (TrustIrEval.module targetJson).mapError (fun error => reprStr error)
  let sourceFunction ← match source.functions.find? (fun function => function.id.index == selected) with
    | some function => pure function
    | none => throw "source selected function is absent"
  let targetFunction ← match target.functions.find? (fun function => function.id.index == selected) with
    | some function => pure function
    | none => throw "target selected function is absent"
  let sourceBlocks ← sourceFunction.blocks.mapError (fun error => reprStr error)
  let targetBlocks ← targetFunction.blocks.mapError (fun error => reprStr error)
  let header ← (evalFunctionOf source sourceFunction sourceBlocks).mapError (fun error => reprStr error)
  let manualTarget ← (evalFunctionOf target targetFunction targetBlocks).mapError (fun error => reprStr error)
  let (signatures, direct) := localTypeHeadersOf source
  match GenericCoro.functionsOfExpansion direct (fun id => (trustIrArrayGet? signatures id.index)) header sourceBlocks with
  | .error error => pure (Json.mkObj [("status", Json.str "source_error"), ("error", Json.str (reprStr error))])
  | .ok (.capacity _ _) => pure (Json.mkObj [("status", Json.str "capacity")])
  | .ok (.expanded actualSource actualTarget triple) =>
    let names := GenericCoro.Names.ofTriple triple
    let ids := sourceBlocks.map Prod.fst ++ targetBlocks.map Prod.fst
    let targetCfg := GenericCoro.cfgOf targetBlocks
    let equal := reprStr actualTarget.body == reprStr manualTarget.body &&
      actualTarget.callingConv == manualTarget.callingConv &&
      actualTarget.entryBlock == manualTarget.entryBlock &&
      ids.all (fun id => reprStr (actualTarget.cfg id) == reprStr (targetCfg id))
    let metadata := match actualSource.localTypes, actualTarget.localTypes, manualTarget.localTypes with
      | some sourceTypes, some targetTypes, some manualTypes =>
        (GenericCoro.graphValueIds sourceBlocks).all (fun id =>
          reprStr (sourceTypes id) == reprStr (targetTypes id)) &&
        (GenericCoro.graphValueIds sourceBlocks ++ GenericCoro.graphValueIds targetBlocks ++
          [names.index, names.pointer, names.state]).all (fun id =>
          reprStr (targetTypes id) == reprStr (manualTypes id)) &&
        reprStr (targetTypes names.index) == reprStr (some Ty.I64) &&
        reprStr (targetTypes names.pointer) == reprStr (some Ty.Ptr) &&
        reprStr (targetTypes names.state) == reprStr (some Ty.I64)
      | _, _, _ => false
    pure (Json.mkObj [
      ("status", Json.str "expanded"),
      ("actual_target_ast_equal", Json.bool equal),
      ("original_and_generated_metadata", Json.bool metadata),
      ("names", toJson [names.index.index, names.pointer.index, names.state.index])])

def audit (request : Json) : Except String Json := do
  let pairs ← (← request.getObjVal? "pairs").getArr?
  let results ← pairs.toList.mapM auditPair
  pure (Json.arr results.toArray)

end TrustIrEval.CoroPrefixFactory

def main (args : List String) : IO UInt32 := do
  match args with
  | [path] =>
    let text ← IO.FS.readFile path
    match Json.parse text >>= TrustIrEval.CoroPrefixFactory.audit with
    | .ok result => IO.println result.compress; pure 0
    | .error error => IO.eprintln error; pure 1
  | _ => IO.eprintln "usage: CoroPrefixFactory.lean request.json"; pure 2
