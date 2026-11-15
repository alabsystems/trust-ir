-- Copyright 2026 Andrew Yates | Apache-2.0
import TrustIrRuntime
import TrustIrEval.Run
import TrustIr.Proofs.GenericCoroAllBlocksFactory

/-! Test-only observations of the actual all-block factory. No evaluator
    refinement, certificate, or native authority is issued by this tool. -/

open TrustIr Lean

namespace TrustIrEval.CoroAllBlocksFactory
open GenericCoro GenericCoroAllBlocksPlanner

private def message (status error : String) : Json :=
  Json.mkObj [("status", Json.str status), ("error", Json.str error)]

/-- Construct only the decoded original header. Inference belongs to the
    actual factory and must not be preempted by the observer. -/
private def headerOf (m : Module) (f : Function) (blocks : Rows) : Except String EvalFunction := do
  let signature ← match (trustIrArrayGet? m.funcTys.toArray f.ty.index) with
    | some signature => pure signature
    | none => throw "selected function signature is absent"
  pure { body := { paramTys := signature.params, returnTys := signature.returns, abi := signature.abi, isVararg := signature.isVararg }
         cfg := GenericCoro.cfgOf blocks
         entryBlock := f.entry
         callingConv := f.callingConvention }

private def sameHeader (actual manual : EvalFunction) : Bool :=
  reprStr actual.body == reprStr manual.body &&
  actual.callingConv == manual.callingConv && actual.entryBlock == manual.entryBlock

private def namesIds (trace : Trace) : List ValueId :=
  trustIrListBind trace (fun (_, names) => [names.index, names.pointer, names.state])

private def traceJson (trace : Trace) : Json :=
  Json.arr (trace.map (fun (block, names) => Json.mkObj [
    ("block", toJson block.index),
    ("names", toJson [names.index.index, names.pointer.index, names.state.index])])).toArray

private def tableSame (left right : Option LocalTypeTable) (ids : List ValueId) : Bool :=
  match left, right with
  | some left, some right => ids.all (fun id => reprStr (left id) == reprStr (right id))
  | _, _ => false

private def comparePair (actualSource actualTarget manual : EvalFunction)
    (sourceRows expectedRows manualRows : Rows) (trace : Trace) : Json := Id.run do
  let ids := graphValueIds sourceRows ++ graphValueIds expectedRows ++
    graphValueIds manualRows ++ namesIds trace
  let labels := sourceRows.map Prod.fst ++ expectedRows.map Prod.fst ++ manualRows.map Prod.fst
  let header := sameHeader actualTarget manual
  let cfg := labels.all (fun id => reprStr (actualTarget.cfg id) == reprStr (manual.cfg id))
  -- A CFG closure does not retain duplicate raw rows. Compare the literal
  -- emitted rows too, and separately anchor their lookup to actualTarget.
  let rows := reprStr expectedRows == reprStr manualRows
  let anchored := labels.all (fun id =>
    reprStr (actualTarget.cfg id) == reprStr (GenericCoro.cfgOf expectedRows id))
  let preserved := tableSame actualSource.localTypes actualTarget.localTypes (graphValueIds sourceRows)
  let manualMetadata := tableSame actualTarget.localTypes manual.localTypes ids
  let generated := match actualTarget.localTypes with
    | none => false
    | some table => trace.all (fun (_, names) =>
      reprStr (table names.index) == reprStr (some Ty.I64) &&
      reprStr (table names.pointer) == reprStr (some Ty.Ptr) &&
      reprStr (table names.state) == reprStr (some Ty.I64))
  return Json.mkObj [
    ("actual_target_ast_equal", Json.bool (header && cfg && rows && anchored)),
    ("header_equal", Json.bool header), ("cfg_equal", Json.bool cfg),
    ("literal_rows_equal", Json.bool rows), ("factory_cfg_matches_rows", Json.bool anchored),
    ("original_metadata_preserved", Json.bool preserved),
    ("manual_metadata_equal", Json.bool manualMetadata),
    ("generated_metadata_typed", Json.bool generated),
    ("checked_value_ids", toJson (ids.map (·.index))),
    ("trace", traceJson trace)]

private def outcomeName {domain : Nat} {rows : Rows}
    (outcome : Except SemError (GenericCoro.AllBlocks.Expansion domain rows)) : String :=
  match outcome with
  | .error _ => "source_error"
  | .ok (.unchanged _) => "unchanged"
  | .ok (.capacity _ _) => "capacity"
  | .ok (.expanded _ _) => "expanded"

trustIrDecodeCompilerCommand {
private def auditPairCore (request : Json) : Except String Json := do
  let sourceJson ← request.getObjVal? "source"
  let targetJson ← request.getObjVal? "target"
  let selected ← (← request.getObjVal? "selected").getNat?
  let source ← (TrustIrEval.module sourceJson).mapError (fun e => reprStr e)
  let target ← (TrustIrEval.module targetJson).mapError (fun e => reprStr e)
  let sourceFunction ← match source.functions.find? (fun f => f.id.index == selected) with
    | some f => pure f | none => throw "source selected function is absent"
  let targetFunction ← match target.functions.find? (fun f => f.id.index == selected) with
    | some f => pure f | none => throw "target selected function is absent"
  let sourceRows ← sourceFunction.blocks.mapError (fun e => reprStr e)
  let targetRows ← targetFunction.blocks.mapError (fun e => reprStr e)
  let header ← headerOf source sourceFunction sourceRows
  let manualHeader ← headerOf target targetFunction targetRows
  let (signatures, direct) := localTypeHeadersOf source
  let indirect := fun id => (trustIrArrayGet? signatures id.index)
  let actual := GenericCoro.AllBlocks.functions direct indirect header sourceRows
  -- A small-domain probe exercises the real capacity branch separately; it
  -- never substitutes for the production u32-domain result above.
  let capacityProbe := match request.getObjVal? "probe_domain" >>= Json.getNat? with
    | .ok domain => Json.mkObj [("domain", toJson domain),
        ("status", Json.str (outcomeName
          (GenericCoro.AllBlocks.functionsWithDomain domain direct indirect header sourceRows)))]
    | .error _ => Json.null
  match actual with
  | .error error => pure (Json.mkObj [("status", Json.str "source_error"),
      ("error", Json.str (reprStr error)), ("capacity_probe", capacityProbe)])
  | .ok (.capacity _ _) => pure (Json.mkObj [("status", Json.str "capacity"),
      ("domain", toJson GenericCoroFreshIds.u32Domain), ("capacity_probe", capacityProbe)])
  | .ok result =>
    let (actualSource, actualTarget, rows, trace, status) := match result with
      | .unchanged source => (source, source, sourceRows, [], "unchanged")
      | .expanded source target =>
        let planned := planAllBlocks sourceRows
        (source, target, planned.rows, planned.trace, "expanded")
      | .capacity source _ => (source, source, [], [], "capacity")
    match evalFunctionOf target targetFunction targetRows with
    | .error error => pure (Json.mkObj [("status", Json.str status),
        ("actual_target_ast_equal", Json.bool false),
        ("manual_metadata_error", Json.str (reprStr error)),
        ("header_equal", Json.bool (sameHeader actualTarget manualHeader)),
        ("trace", traceJson trace), ("capacity_probe", capacityProbe)])
    | .ok manual =>
      let comparisons := comparePair actualSource actualTarget manual sourceRows rows targetRows trace
      let .obj fields := comparisons | throw "internal comparison object"
      pure (Json.mkObj ([("status", Json.str status), ("capacity_probe", capacityProbe)] ++
        fields.fold (fun pairs key value => (key, value) :: pairs) []))
} {
private def auditPairCore (request : Json) : Except String Json := do
  let sourceJson ← request.getObjVal? "source"
  let targetJson ← request.getObjVal? "target"
  let selected ← (← request.getObjVal? "selected").getNat?
  let source ← (TrustIrEval.module sourceJson).mapError (fun e => reprStr e)
  let target ← (TrustIrEval.module targetJson).mapError (fun e => reprStr e)
  let sourceFunction ← match source.functions.find? (fun f => f.id.index == selected) with
    | some f => pure f | none => throw "source selected function is absent"
  let targetFunction ← match target.functions.find? (fun f => f.id.index == selected) with
    | some f => pure f | none => throw "target selected function is absent"
  let sourceRows ← sourceFunction.blocks.mapError (fun e => reprStr e)
  let targetRows ← targetFunction.blocks.mapError (fun e => reprStr e)
  let header ← headerOf source sourceFunction sourceRows
  let manualHeader ← headerOf target targetFunction targetRows
  let (signatures, direct) := localTypeHeadersOf source
  let indirect := fun id => (trustIrArrayGet? signatures id.index)
  let actual := GenericCoro.AllBlocks.functions direct indirect header sourceRows
  -- A small-domain probe exercises the real capacity branch separately; it
  -- never substitutes for the production u32-domain result above.
  let capacityProbe := match request.getObjVal? "probe_domain" >>= Json.getNat? with
    | .ok domain => Json.mkObj [("domain", toJson domain),
        ("status", Json.str (outcomeName
          (GenericCoro.AllBlocks.functionsWithDomain domain direct indirect header sourceRows)))]
    | .error _ => Json.null
  match actual with
  | .error error => pure (Json.mkObj [("status", Json.str "source_error"),
      ("error", Json.str (reprStr error)), ("capacity_probe", capacityProbe)])
  | .ok (.capacity _ _) => pure (Json.mkObj [("status", Json.str "capacity"),
      ("domain", toJson GenericCoroFreshIds.u32Domain), ("capacity_probe", capacityProbe)])
  | .ok result =>
    let (actualSource, actualTarget, rows, trace, status) := match result with
      | .unchanged source => (source, source, sourceRows, [], "unchanged")
      | .expanded source target =>
        let planned := planAllBlocks sourceRows
        (source, target, planned.rows, planned.trace, "expanded")
      | .capacity source _ => (source, source, [], [], "capacity")
    match evalFunctionOf target targetFunction targetRows with
    | .error error => pure (Json.mkObj [("status", Json.str status),
        ("actual_target_ast_equal", Json.bool false),
        ("manual_metadata_error", Json.str (reprStr error)),
        ("header_equal", Json.bool (sameHeader actualTarget manualHeader)),
        ("trace", traceJson trace), ("capacity_probe", capacityProbe)])
    | .ok manual =>
      let comparisons := comparePair actualSource actualTarget manual sourceRows rows targetRows trace
      let .obj fields := comparisons | throw "internal comparison object"
      pure (Json.mkObj ([("status", Json.str status), ("capacity_probe", capacityProbe)] ++
        fields.foldl (fun pairs key value => (key, value) :: pairs) []))
}

def audit (request : Json) : Except String Json := do
  let pairs ← (← request.getObjVal? "pairs").getArr?
  let answers := pairs.toList.map (fun pair => match auditPairCore pair with
    | .ok result => result
    | .error error => message "decode_error" error)
  pure (Json.arr answers.toArray)

end TrustIrEval.CoroAllBlocksFactory

def main (args : List String) : IO UInt32 := do
  match args with
  | [path] =>
    let text ← IO.FS.readFile path
    match Json.parse text >>= TrustIrEval.CoroAllBlocksFactory.audit with
    | .ok result => IO.println result.compress; pure 0
    | .error error => IO.eprintln error; pure 1
  | _ => IO.eprintln "usage: CoroAllBlocksFactory.lean request.json"; pure 2
