-- Copyright 2026 Andrew Yates
-- Licensed under the Apache License, Version 2.0

import TrustIrRuntime
import TrustIrEval.Run

open Lean (Json)
open TrustIr TrustIrEval

private def require (label : String) (condition : Bool) : IO Unit :=
  unless condition do throw (IO.userError label)

private def exact (label : String) (actual : Json) (expected : String) : IO Unit := do
  let expected ← match Json.parse expected with
    | .ok value => pure value
    | .error error => throw (IO.userError error)
  require label (actual == expected)

private def decimal (value : Json) : Except String Nat := do
  let text ← value.getStr?
  match text.toNat? with
  | some value => pure value
  | none => throw "invalid decimal observation"

private def edge (measures : Array (String × Nat)) (value : Json) (kind : String) :
    Except String (Nat × Nat) := do
  let index ← value.getNat?
  match (trustIrArrayGet? measures index) with
  | some (actual, count) =>
    if actual == kind then pure (index, count) else throw "observation edge kind mismatch"
  | none => throw "observation edge is not backward"

/-- Independent wire-level integer-array reader. Lengths are checked bottom-up;
    a huge uniform's logical extent is never enumerated. -/
private def graphData (observation : Json) : Except String (Array Json × Array (String × Nat) × Nat × Nat) := do
  let graph ← observation.getObjVal? "graph"
  let version ← (← graph.getObjVal? "version").getNat?
  if version != 2 then throw "unsupported graph version"
  let nodes ← (← graph.getObjVal? "nodes").getArr?
  let mut measures := #[]
  for node in nodes do
    let kind ← (← node.getArrVal? 0).getStr?
    let measure ← match kind with
      | "int" => pure ("value", 0)
      | "nil" => pure ("list", 0)
      | "cons" => do
        let _ ← edge measures (← node.getArrVal? 1) "value"
        let (_, count) ← edge measures (← node.getArrVal? 2) "list"
        pure ("list", count + 1)
      | "empty" => pure ("tree", 0)
      | "uniform" => do
        let count ← decimal (← node.getArrVal? 1)
        let _ ← edge measures (← node.getArrVal? 2) "value"
        pure ("tree", count)
      | "dense" => do
        let (_, count) ← edge measures (← node.getArrVal? 1) "list"
        pure ("tree", count)
      | "concat" => do
        let (_, left) ← edge measures (← node.getArrVal? 1) "tree"
        let (_, right) ← edge measures (← node.getArrVal? 2) "tree"
        pure ("tree", left + right)
      | "array" => do
        let count ← decimal (← node.getArrVal? 1)
        let (_, actual) ← edge measures (← node.getArrVal? 2) "tree"
        if actual != count then throw "array extent mismatch"
        pure ("value", 0)
      | _ => throw "unexpected node in integer-array control"
    measures := measures.push measure
  let root ← (← (← graph.getObjVal? "roots").getArrVal? 0).getNat?
  let node ← match (trustIrArrayGet? nodes root) with
    | some node => pure node
    | none => throw "missing graph root"
  if (← (← node.getArrVal? 0).getStr?) != "array" then throw "root is not an array"
  let count ← decimal (← node.getArrVal? 1)
  let tree ← (← node.getArrVal? 2).getNat?
  pure (nodes, measures, tree, count)

private def graphIntAt (observation : Json) (index : Nat) : Except String (Option Nat) := do
  let (nodes, measures, tree, count) ← graphData observation
  if index ≥ count then return none
  let mut current := tree
  let mut offset := index
  for _ in List.range (nodes.size + 1) do
    let node ← match (trustIrArrayGet? nodes current) with
      | some node => pure node
      | none => throw "invalid node"
    match (← (← node.getArrVal? 0).getStr?) with
    | "uniform" =>
      current ← (← node.getArrVal? 2).getNat?
    | "dense" => current ← (← node.getArrVal? 1).getNat?
    | "concat" =>
      let (left, count) ← edge measures (← node.getArrVal? 1) "tree"
      if offset < count then current := left
      else
        current ← (← node.getArrVal? 2).getNat?
        offset := offset - count
    | "cons" =>
      if offset == 0 then current ← (← node.getArrVal? 1).getNat?
      else
        current ← (← node.getArrVal? 2).getNat?
        offset := offset - 1
    | "int" => return some (← decimal (← node.getArrVal? 2))
    | _ => throw "unexpected node while reading an in-bounds element"
  throw "observation traversal did not descend"

private def readIs (actual : Except String (Option Nat)) (expected : Option Nat) : Bool :=
  match actual with
  | .ok value => value == expected
  | .error _ => false

private def swapRootChildren (observation : Json) : Except String Json := do
  let (nodes, _, tree, _) ← graphData observation
  let node ← match (trustIrArrayGet? nodes tree) with
    | some node => pure node
    | none => throw "missing root tree"
  if (← (← node.getArrVal? 0).getStr?) != "concat" then throw "root is not a concat"
  let swapped := Json.arr #[.str "concat", (← node.getArrVal? 2), (← node.getArrVal? 1)]
  let graph ← observation.getObjVal? "graph"
  let roots ← graph.getObjVal? "roots"
  pure (Json.mkObj [("graph", Json.mkObj [("version", .num 2),
    ("nodes", .arr (nodes.set! tree swapped)), ("roots", roots)])])

def main : IO Unit := do
  let count := 2 ^ 64 - 1
  let uniform := Value.array (CompactArray.Packed.uniform count (.int 64 7))
  exact "uniform logical count is metadata, not expanded elements" (Observation.renderGraphSpec [uniform])
    "{\"graph\":{\"version\":2,\"nodes\":[[\"int\",64,\"7\"],[\"uniform\",\"18446744073709551615\",0],[\"array\",\"18446744073709551615\",1]],\"roots\":[2]}}"
  exact "duplicate roots share their normalized node descriptions"
    (Observation.renderGraphSpec [uniform, uniform])
    "{\"graph\":{\"version\":2,\"nodes\":[[\"int\",64,\"7\"],[\"uniform\",\"18446744073709551615\",0],[\"array\",\"18446744073709551615\",1]],\"roots\":[2,2]}}"
  let empty := Value.array (CompactArray.Packed.uniform 0 (.undef .I64))
  exact "empty uniform observations never inspect the unused payload" (Observation.renderGraphSpec [empty])
    "{\"graph\":{\"version\":2,\"nodes\":[[\"empty\"],[\"array\",\"0\",0]],\"roots\":[1]}}"
  exact "integer observations retain canonical residue at their lane width"
    (Observation.renderGraphSpec [.int 8 (-1)])
    "{\"graph\":{\"version\":2,\"nodes\":[[\"int\",8,\"255\"]],\"roots\":[0]}}"
  exact "pointer observation retains the established nullness policy"
    (Observation.renderGraphSpec [.ptr 0 none, .nullPtr])
    "{\"graph\":{\"version\":2,\"nodes\":[[\"ptr\",false],[\"ptr\",true]],\"roots\":[0,1]}}"
  let updated ← match setElement uniform (count - 1) (.int 64 9) with
    | some value => pure value
    | none => throw (IO.userError "in-bounds persistent update failed")
  require "updated huge value has a compact serialized observation"
    ((Observation.renderGraphSpec [updated]).compress.length < 20000)
  let source := ((List.range 65).map (fun n => Value.int 64 (Int.ofNat n))).toArray
  let dense := Value.array (CompactArray.Packed.ofArray source)
  for index in List.range 66 do
    let expected := if index < 65 then some index else none
    require s!"dense wire observation at {index}"
      (readIs (graphIntAt (Observation.renderGraphSpec [dense]) index) expected)
  for index in [0, 1, count / 2, count - 2, count - 1, count] do
    let expected := if index < count then some (if index == count - 1 then 9 else 7) else none
    require s!"updated huge wire observation at {index}"
      (readIs (graphIntAt (Observation.renderGraphSpec [updated]) index) expected)
  let wrong ← match swapRootChildren (Observation.renderGraphSpec [updated]) with
    | .ok graph => pure graph
    | .error error => throw (IO.userError error)
  require "swapped graph loses the actual final-index replacement"
    (!(readIs (graphIntAt wrong (count - 1)) (some 9)))
  require "swapped graph remains valid and exposes the wrong value"
    (readIs (graphIntAt wrong (count - 1)) (some 7))
  let malformed ← match Json.parse
      "{\"graph\":{\"version\":2,\"nodes\":[[\"int\",64,\"7\"],[\"uniform\",\"1\",0],[\"array\",\"2\",1]],\"roots\":[2]}}" with
    | .ok graph => pure graph
    | .error error => throw (IO.userError error)
  require "mismatched declared extents refuse" (match graphData malformed with
    | .error _ => true
    | .ok _ => false)
  IO.println "Compact value-graph specification controls passed"
