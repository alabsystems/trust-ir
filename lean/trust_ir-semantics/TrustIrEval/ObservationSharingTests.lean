-- Copyright 2026 Andrew Yates
-- Licensed under the Apache License, Version 2.0

import TrustIrRuntime
import TrustIrEval.Observation

open Lean (Json)
open TrustIr TrustIrEval

private def require (label : String) (condition : Bool) : IO Unit :=
  unless condition do throw (IO.userError label)

private def orError {α : Type} (value : Option α) (message : String) : Except String α :=
  match value with | some value => .ok value | none => .error message

private def orIO {α : Type} (value : Option α) (message : String) : IO α :=
  match value with | some value => pure value | none => throw (IO.userError message)

/-- Both edges are the very same child, not separately reconstructed trees. -/
private def sharedTree : (depth : Nat) → CompactArray.Tree Value (2 ^ depth)
  | 0 => .uniform 1 (.int 32 7)
  | depth + 1 =>
    have positive : 0 < 2 ^ depth := Nat.pow_pos (by decide)
    have lower : 2 ^ (depth + 1) / 2 = 2 ^ depth := by rw [Nat.pow_succ]; omega
    have upper : 2 ^ (depth + 1) - 2 ^ (depth + 1) / 2 = 2 ^ depth := by
      rw [Nat.pow_succ]; omega
    let child := sharedTree depth
    .split (by rw [Nat.pow_succ]; omega) (lower.symm ▸ child) (upper.symm ▸ child)

private def sharedValue : Nat → Value
  | 0 => .int 32 7
  | depth + 1 => let child := sharedValue depth; .aggregate [child, child]

private def packed (depth : Nat) : CompactArray.Packed Value := ⟨2 ^ depth, sharedTree depth⟩

/-- Independent expected wire for an unchanged shared tree, built in O(depth)
    from the protocol alone, without visiting the source tree. -/
private def expectedTree (depth : Nat) : Json := Id.run do
  let mut nodes : Array Json := #[.arr #[.str "int", .num 32, .str "7"],
    .arr #[.str "uniform", .str "1", .num 0]]
  let mut previous := 1
  for _ in List.range depth do
    let next := nodes.size
    nodes := nodes.push (.arr #[.str "concat", .num previous, .num previous])
    previous := next
  let root := nodes.size
  nodes := nodes.push (.arr #[.str "array", .str (toString (2 ^ depth)), .num previous])
  return Json.mkObj [("graph", Json.mkObj [("version", .num 2),
    ("nodes", .arr nodes), ("roots", .arr #[.num root])])]

/-- Bounded independent indexed reader for the integer array controls. It
    derives subtree lengths from backward wire edges, never source identities. -/
private def integerAt (wire : Json) (slot index : Nat) : Except String (Option Nat) := do
  let graph ← wire.getObjVal? "graph"
  let nodes ← (← graph.getObjVal? "nodes").getArr?
  let mut lengths : Array Nat := #[]
  for node in nodes do
    let kind ← (← node.getArrVal? 0).getStr?
    let count ← match kind with
      | "uniform" => pure (← (← node.getArrVal? 1).getStr?).toNat!
      | "cons" => pure ((lengths[(← (← node.getArrVal? 2).getNat?)]?).getD 0 + 1)
      | "dense" => pure ((lengths[(← (← node.getArrVal? 1).getNat?)]?).getD 0)
      | "concat" => pure ((lengths[(← (← node.getArrVal? 1).getNat?)]?).getD 0 +
          (lengths[(← (← node.getArrVal? 2).getNat?)]?).getD 0)
      | _ => pure 0
    lengths := lengths.push count
  let root ← (← (← graph.getObjVal? "roots").getArrVal? slot).getNat?
  let root ← orError ((trustIrArrayGet? nodes root)) "missing root"
  let count := (← (← root.getArrVal? 1).getStr?).toNat!
  if index ≥ count then return none
  let mut current ← (← root.getArrVal? 2).getNat?
  let mut offset := index
  for _ in List.range (nodes.size + 1) do
    let node ← orError ((trustIrArrayGet? nodes current)) "missing node"
    match (← (← node.getArrVal? 0).getStr?) with
    | "uniform" => current ← (← node.getArrVal? 2).getNat?
    | "concat" =>
      let left ← (← node.getArrVal? 1).getNat?
      let count := (lengths[left]?).getD 0
      if offset < count then current := left
      else
        current ← (← node.getArrVal? 2).getNat?
        offset := offset - count
    | "dense" => current ← (← node.getArrVal? 1).getNat?
    | "cons" =>
      if offset == 0 then current ← (← node.getArrVal? 1).getNat?
      else
        current ← (← node.getArrVal? 2).getNat?
        offset := offset - 1
    | "int" => return some (← (← node.getArrVal? 2).getStr?).toNat!
    | _ => throw "unexpected node"
  throw "wire path did not descend"

private def readIs (value : Except String (Option Nat)) (expected : Option Nat) : Bool :=
  match value with | .ok value => value == expected | .error _ => false

private def mixed : List Value :=
  let tail := [.int 128 (-1), .float (0.0 / 0.0), .float (-0.0), .bool true]
  let fields := [("λ", .int 8 255), ("x", .aggregate tail)]
  [.aggregate [], .record [], .nullPtr, .ptr 0 none, .uninit,
    .aggregate tail, .vector tail, .sequence tail, .set tail,
    .record fields, .record (("prefix", .bool false) :: fields),
    .closure ⟨4⟩ tail, .typedClosure ⟨5⟩ ⟨4⟩ tail, .fnDef ⟨6⟩ ⟨7⟩,
    .fatPtr 0 none (.int 64 9), .fatPtr 17 none (.ptr 99 none),
    .partial [none], .undef .U32, .frame 0 tail,
    .array (CompactArray.Packed.uniform 0 (.int 32 99)),
    .array (CompactArray.Packed.ofArray ((List.range 65).map (fun n => .int 32 n)).toArray)]

private unsafe def corpus : IO Unit := do
  let original := packed 63
  let updated ← orIO (original.set? (original.size - 1) (.int 32 99)) "update failed"
  let value := sharedValue 80
  for values in [[.array original, .array updated, .array original],
      [value, value], mixed] do
    let (wire, stats) := Observation.renderGraphWithStats values
    IO.println (Json.mkObj [("observation", wire), ("visits", .num stats.visits),
      ("hits", .num stats.hits), ("treeVisits", .num stats.treeVisits)]).compress

unsafe def main (args : List String) : IO Unit := do
  if args.contains "--corpus" then return ← corpus
  -- This bounded case comes first so cache-disabled controls never reach the
  -- enormous cases. A wrong implementation fails by a counter, not exhaustion.
  let depth := 12
  let input := [Value.array (packed depth)]
  let (wire, stats) := Observation.renderGraphWithStats input
  require "shared tree inputs must be inspected once" (stats.treeVisits ≤ depth + 1)
  require "shared tree aliases must hit the source cache" (stats.hits ≥ depth)
  require "bounded tree must match pure specification" (wire == Observation.renderGraphSpec input)
  require "bounded tree must match independent expected wire" (wire == expectedTree depth)
  for depth in List.range 11 do
    let value := sharedValue depth
    let values := [value, value]
    let (wire, stats) := Observation.renderGraphWithStats values
    require "shared values must be inspected once" (stats.valueVisits ≤ depth + 1)
    require "shared values must match pure specification" (wire == Observation.renderGraphSpec values)
    require "runtime wrapper must use the same wire" (Observation.renderGraph values == wire)
  require "mixed source domains must retain exact observations"
    ((Observation.renderGraphWithStats mixed).1 == Observation.renderGraphSpec mixed)
  if args.contains "--bounded" then
    IO.println "Bounded physical input-sharing controls passed"
    return
  let large := packed 63
  let (wire, stats) := Observation.renderGraphWithStats [.array large]
  require "huge shared tree must retain exact full wire" (wire == expectedTree 63)
  require "huge shared tree must visit only physical nodes" (stats.treeVisits ≤ 64)
  let updated ← orIO (large.set? (large.size - 1) (.int 32 99)) "update failed"
  let values := [Value.array large, .array updated, .array large]
  let (wire, stats) := Observation.renderGraphWithStats values
  require "overlapping roots must share one cache" (stats.treeVisits ≤ 128)
  require "compiled runtime wrapper must retain whole-batch caching" (Observation.renderGraph values == wire)
  for slot in [0, 1, 2] do
    for index in [0, large.size / 2, large.size - 1] do
      let expected := if slot == 1 && index == large.size - 1 then 99 else 7
      require "late update and original roots must remain distinct"
        (readIs (integerAt wire slot index) (some expected))
    require "end index must be absent" (readIs (integerAt wire slot large.size) none)
  let value := sharedValue 80
  let (wire, stats) := Observation.renderGraphWithStats [value, value]
  require "nested value DAG must remain physical" (stats.valueVisits ≤ 81 && stats.visits ≤ 328)
  let nodeCount := (((wire.getObjVal? "graph").bind (·.getObjVal? "nodes")
    |>.bind Json.getArr?).toOption.map Array.size).getD 10000
  require "nested DAG output must stay compact" (nodeCount ≤ 328)
  IO.println "Physical input-sharing runtime checks passed"
