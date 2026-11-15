-- Copyright 2026 Andrew Yates | Apache-2.0
import TrustIrRuntime
import TrustIrEval.Run
import TrustIr.Proofs.GenericCoroModuleFactory

/-! Test-only execution of the actual decoded-module producer. The target
    batch consumes its emitted AST directly; no manual expansion, second
    planner, or reconstructed evaluator-function table supplies that target. -/

open TrustIr Lean

namespace TrustIrEval.CoroModuleFactory
open GenericCoro GenericCoro.ModuleFactory GenericCoroAllBlocksPlanner

private def headerView (function : Function) : Json :=
  Json.mkObj [
    ("id", toJson function.id.index), ("name", Json.str function.name),
    ("type", toJson function.ty.index), ("entry", toJson function.entry.index),
    ("declaration", Json.bool function.isDeclaration),
    ("calling_convention", Json.str (reprStr function.callingConvention))]

private def functionView (function : Function) : Json :=
  Json.mkObj [
    ("id", toJson function.id.index),
    ("header", headerView function),
    ("body", Json.str (reprStr function.blocks))]

private def functionViews (functions : List Function) : Json :=
  Json.arr (functions.map functionView).toArray

private def suspends (functions : List Function) : Nat :=
  functions.foldl (fun total function => total + match function.blocks with
    | .ok rows => suspendCount rows
    | .error _ => 0) 0

private def rejection (problem : Problem) : Json :=
  match problem with
  | .decode function error => Json.mkObj [
      ("kind", Json.str "decode"), ("function", toJson function.index),
      ("error", Json.str (reprStr error))]
  | .inference function error => Json.mkObj [
      ("kind", Json.str "inference"), ("function", toJson function.index),
      ("error", Json.str (reprStr error))]
  | .capacity function _ _ => Json.mkObj [
      ("kind", Json.str "capacity"), ("function", toJson function.index)]

private def runProduced (fuel callDepth : Nat) (strategy : PanicStrategy) (batch : Batch) : Json :=
  -- The single call to transform is the only source of the target module.
  match GenericCoro.ModuleFactory.transform batch.module with
  | .rejected original problem => Json.mkObj [
      ("status", Json.str "rejected"),
      ("problem", rejection problem),
      ("original_functions", functionViews original.functions),
      ("source_functions", functionViews batch.module.functions)]
  | .ready target =>
      let targetBatch := { batch with module := target }
      Json.mkObj [
        ("status", Json.str "ready"),
        ("source_functions", functionViews batch.module.functions),
        ("target_functions", functionViews target.functions),
        ("headers_equal", Json.bool
          ((Json.arr (batch.module.functions.map headerView).toArray).compress ==
            (Json.arr (target.functions.map headerView).toArray).compress)),
        ("source_suspend_count", toJson (suspends batch.module.functions)),
        ("target_suspend_count", toJson (suspends target.functions)),
        ("source_runs", runBatch fuel callDepth strategy batch),
        ("target_runs", runBatch fuel callDepth strategy targetBatch)]

def audit (requestJson : Json) : Except String Json := do
  let decoded ← (TrustIrEval.request requestJson).mapError (fun error => reprStr error)
  pure (Json.arr (decoded.batches.map
    (runProduced decoded.fuel decoded.callDepth decoded.strategy)).toArray)

end TrustIrEval.CoroModuleFactory

def main (args : List String) : IO UInt32 := do
  match args with
  | [path] =>
    let text ← IO.FS.readFile path
    match Json.parse text >>= TrustIrEval.CoroModuleFactory.audit with
    | .ok response => IO.println response.compress; pure 0
    | .error error => IO.eprintln error; pure 1
  | _ => IO.eprintln "usage: CoroModuleFactory.lean request.json"; pure 2
