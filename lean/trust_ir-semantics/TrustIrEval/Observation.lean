-- Copyright 2026 Andrew Yates
-- Licensed under the Apache License, Version 2.0

import TrustIr.State.ValueMap
import TrustIr.Semantics.FloatFormat

namespace TrustIrEval.Observation

open Lean (Json)
open TrustIr

-- Select only the native map API supplied by the two admitted compiler pins.
macro "trustIrObservationCompilerCommand " "{" legacyCommand:command "}" "{" modernCommand:command "}" : command => do
  if Lean.versionString == "4.8.0" then pure legacyCommand
  else if Lean.versionString == "4.30.0-rc2" then pure modernCommand
  else Lean.Macro.throwError "unsupported compiler for Observation map API"

trustIrObservationCompilerCommand {
/-- Canonical output interning is independent of source sharing. -/
structure GraphState where
  nodes : Array Json := #[]
  canonical : Lean.HashMap String Nat := Lean.mkHashMap
} {
/-- Canonical output interning is independent of source sharing. -/
structure GraphState where
  nodes : Array Json := #[]
  canonical : Std.HashMap String Nat := Std.HashMap.emptyWithCapacity
}

private def tag (name : String) (fields : List Json := []) : Json :=
  .arr ((Json.str name :: fields).toArray)

private def ref (index : Nat) : Json := .num index

trustIrObservationCompilerCommand {
private def intern (node : Json) : StateM GraphState Nat := do
  let state ← get
  let key := node.compress
  match state.canonical.find? key with
  | some index => pure index
  | none =>
    let index := state.nodes.size
    set ({ nodes := state.nodes.push node, canonical := state.canonical.insert key index } : GraphState)
    pure index
} {
private def intern (node : Json) : StateM GraphState Nat := do
  let state ← get
  let key := node.compress
  match state.canonical.get? key with
  | some index => pure index
  | none =>
    let index := state.nodes.size
    set ({ nodes := state.nodes.push node, canonical := state.canonical.insert key index } : GraphState)
    pure index
}

/-- Typed retained source objects. The wrappers are not identity keys: the
    runtime cache keys the original object inside each wrapper. -/
private inductive Input where
  | value (value : Value)
  | values (values : List Value)
  | fields (fields : List (String × Value))
  | tree {size : Nat} (tree : CompactArray.Tree Value size) (offset count : Nat)
  | leaf {size : Nat} (leaf : CompactArray.Leaf Value size) (offset count : Nat)
  | repeat {size : Nat} (tree : CompactArray.Tree Value size) (copies : Nat)
  | concat (first later : Input)

/-- One shared wire vocabulary for both traversals. Primitive metadata is
    already JSON; source edges are evaluated in their original order. -/
private structure Shape where
  name : String
  fields : List (Sum Json Input) := []
  alias : Option Input := none

private def literal (value : Json) : Sum Json Input := .inl value
private def child (input : Input) : Sum Json Input := .inr input

private def view : Input → Shape
  | .value (.int width value) =>
    ⟨"int", [literal (ref width), literal (.str (toString ((value % ((2 : Int) ^ width)).toNat)))], none⟩
  | .value (.float value) =>
    let bits := if value.isNaN then "nan" else
      match encodeBits .binary64 value with
      | some bits => toString bits
      | none => "unencodable"
    ⟨"float", [literal (.str bits)], none⟩
  | .value (.bool value) => ⟨"bool", [literal (.bool value)], none⟩
  | .value (.ptr _ _) => ⟨"ptr", [literal (.bool false)], none⟩
  | .value .nullPtr => ⟨"ptr", [literal (.bool true)], none⟩
  | .value (.fatPtr address _ metadata) =>
    ⟨"fatptr", [child (.value (if address == 0 then .nullPtr else .ptr address none)),
      child (.value metadata)], none⟩
  | .value (.array values) =>
    ⟨"array", [literal (.str (toString values.size)), child (.tree values.tree 0 values.size)], none⟩
  | .value (.aggregate values) => ⟨"aggregate", [child (.values values)], none⟩
  | .value (.vector values) => ⟨"vector", [child (.values values)], none⟩
  | .value (.sequence values) => ⟨"sequence", [child (.values values)], none⟩
  | .value (.set values) => ⟨"set", [child (.values values)], none⟩
  | .value (.record fields) => ⟨"record", [child (.fields fields)], none⟩
  | .value (.closure func captures) | .value (.typedClosure _ func captures) =>
    ⟨"closure", [literal (ref func.index), child (.values captures)], none⟩
  | .value (.fnDef signature func) =>
    ⟨"function", [literal (ref signature.index), literal (ref func.index)], none⟩
  | .value (.frame _ slots) => ⟨"frame", [literal (ref slots.length)], none⟩
  | .value (.partial _) | .value (.undef _) => ⟨"poison", [], none⟩
  | .value .uninit => ⟨"uninit", [], none⟩
  | .values [] | .fields [] => ⟨"nil", [], none⟩
  | .values (head :: tail) =>
    ⟨"cons", [child (.value head), child (.values tail)], none⟩
  | .fields ((name, value) :: tail) =>
    ⟨"field", [literal (.str name), child (.value value), child (.fields tail)], none⟩
  | .tree (size := size) tree offset count =>
    let count := min count (size - offset)
    if count == 0 then ⟨"empty", [], none⟩ else
    match tree with
    | .uniform _ value => ⟨"uniform", [literal (.str (toString count)), child (.value value)], none⟩
    | .dense _ values => ⟨"dense", [child (.leaf values offset count)], none⟩
    | .split (size := size) _ left right =>
      let before := min count (size / 2 - offset)
      if before == 0 then { name := "empty", alias := some (.tree right (offset - size / 2) count) }
      else if before == count then { name := "empty", alias := some (.tree left offset count) }
      else ⟨"concat", [child (.tree left offset before),
        child (.tree right (offset + before - size / 2) (count - before))], none⟩
    | .periodic (period := period) unit _ phase _ =>
      let start := (phase + offset) % period
      let before := min count (period - start)
      let remaining := count - before
      let copies := remaining / period
      let tail := remaining % period
      let first := Input.tree unit start before
      if remaining == 0 then { name := "empty", alias := some first }
      else if copies == 0 then ⟨"concat", [child first, child (.tree unit 0 tail)], none⟩
      else if tail == 0 then ⟨"concat", [child first, child (.repeat unit copies)], none⟩
      else ⟨"concat", [child first, child (.concat (.repeat unit copies) (.tree unit 0 tail))], none⟩
  | .leaf (size := size) leaf offset count =>
    let count := min count (size - offset)
    if count == 0 then ⟨"nil", [], none⟩ else
    match leaf with
    | .nil => ⟨"nil", [], none⟩
    | .cons head tail =>
      if offset > 0 then { name := "nil", alias := some (.leaf tail (offset - 1) count) }
      else ⟨"cons", [child (.value head), child (.leaf tail 0 (count - 1))], none⟩
  | .repeat (size := size) tree copies =>
    if copies == 0 || size == 0 then ⟨"empty", [], none⟩
    else if copies == 1 then { name := "empty", alias := some (.tree tree 0 size) }
    else ⟨"repeat", [child (.tree tree 0 size), literal (.str (toString copies))], none⟩
  | .concat first later => ⟨"concat", [child first, child later], none⟩

private partial def specNode (input : Input) : StateM GraphState Nat := do
  let shape := view input
  if let some target := shape.alias then specNode target else do
    let fields ← shape.fields.mapM fun field => match field with
      | .inl value => pure value
      | .inr input => ref <$> specNode input
    intern (tag shape.name fields)

private def finish (roots : List Nat) (state : GraphState) : Json :=
  Json.mkObj [("graph", Json.mkObj [("version", .num 2), ("nodes", .arr state.nodes),
    ("roots", .arr (roots.map ref).toArray)])]

/-- Pure canonical serializer; deliberately does not inspect physical identity.
    This remains the specification and the finite differential control. -/
def renderGraphSpec (values : List Value) : Json :=
  let (roots, state) := (values.mapM (fun value => specNode (.value value))).run {}
  finish roots state

/-- Diagnostic counters, not observation budgets or proof evidence. Misses count
    source objects whose shape is inspected; hits skip the entire subtree. -/
structure MemoStats where
  visits : Nat := 0
  hits : Nat := 0
  treeVisits : Nat := 0
  valueVisits : Nat := 0
  deriving Repr

private abbrev MemoKey := (Nat × Nat × USize) × Nat × Nat

trustIrObservationCompilerCommand {
private structure RuntimeState where
  graph : GraphState := {}
  -- Keeping the complete typed input alive prevents address reuse while a key
  -- is present. Domains and dependent extents are part of the exact key.
  memo : Lean.HashMap MemoKey (Nat × Input) := Lean.mkHashMap
  stats : MemoStats := {}
} {
private structure RuntimeState where
  graph : GraphState := {}
  -- Keeping the complete typed input alive prevents address reuse while a key
  -- is present. Domains and dependent extents are part of the exact key.
  memo : Std.HashMap MemoKey (Nat × Input) := Std.HashMap.emptyWithCapacity
  stats : MemoStats := {}
}

private unsafe def inputKey (input : Input) : MemoKey :=
  let address := ptrAddrUnsafe input
  match input with
  | .value value => ((0, 0, ptrAddrUnsafe value), 0, 0)
  | .values values => ((1, 0, ptrAddrUnsafe values), 0, 0)
  | .fields fields => ((2, 0, ptrAddrUnsafe fields), 0, 0)
  | .tree (size := size) tree offset count => ((3, size, ptrAddrUnsafe tree), offset, min count (size - offset))
  | .leaf (size := size) leaf offset count => ((4, size, ptrAddrUnsafe leaf), offset, min count (size - offset))
  | .repeat (size := size) tree copies => ((5, size, ptrAddrUnsafe tree), 0, copies)
  | .concat _ _ => ((6, 0, address), 0, 0)

trustIrObservationCompilerCommand {
private unsafe def runtimeNode (input : Input) : StateM RuntimeState Nat := do
  let key := inputKey input
  let state ← get
  match state.memo.find? key with
  | some (index, _) =>
    modify fun state => { state with stats := { state.stats with hits := state.stats.hits + 1 } }
    return index
  | none => pure ()
  -- Lookup precedes decomposition, allocation of child wrappers, and descent.
  modify fun state => { state with stats := { state.stats with
    visits := state.stats.visits + 1
    treeVisits := state.stats.treeVisits + (if key.1.1 == 3 then 1 else 0)
    valueVisits := state.stats.valueVisits + (if key.1.1 == 0 then 1 else 0) } }
  let shape := view input
  let index ← match shape.alias with
    | some target => runtimeNode target
    | none => do
      let fields ← shape.fields.mapM fun field => match field with
        | .inl value => pure value
        | .inr input => ref <$> runtimeNode input
      let state ← get
      let (index, graph) := (intern (tag shape.name fields)).run state.graph
      set { state with graph }
      pure index
  modify fun state => { state with memo := state.memo.insert key (index, input) }
  return index
} {
private unsafe def runtimeNode (input : Input) : StateM RuntimeState Nat := do
  let key := inputKey input
  let state ← get
  match state.memo.get? key with
  | some (index, _) =>
    modify fun state => { state with stats := { state.stats with hits := state.stats.hits + 1 } }
    return index
  | none => pure ()
  -- Lookup precedes decomposition, allocation of child wrappers, and descent.
  modify fun state => { state with stats := { state.stats with
    visits := state.stats.visits + 1
    treeVisits := state.stats.treeVisits + (if key.1.1 == 3 then 1 else 0)
    valueVisits := state.stats.valueVisits + (if key.1.1 == 0 then 1 else 0) } }
  let shape := view input
  let index ← match shape.alias with
    | some target => runtimeNode target
    | none => do
      let fields ← shape.fields.mapM fun field => match field with
        | .inl value => pure value
        | .inr input => ref <$> runtimeNode input
      let state ← get
      let (index, graph) := (intern (tag shape.name fields)).run state.graph
      set { state with graph }
      pure index
  modify fun state => { state with memo := state.memo.insert key (index, input) }
  return index
}

/-- Native-only diagnostic entry. Its unsafe boundary is pointer identity;
    cache entries retain their sources, and the cache dies after this batch.
    This is executable reference machinery, never kernel proof authority. -/
unsafe def renderGraphWithStats (values : List Value) : Json × MemoStats :=
  let (roots, state) := (values.mapM (fun value => runtimeNode (.value value))).run {}
  (finish roots state.graph, state.stats)

private unsafe def renderGraphNative (values : List Value) : Json :=
  (renderGraphWithStats values).1

/-- Compiled traversal uses operation-local retained physical-identity caches.
    The logical definition is the pure specification. The native replacement
    is qualified by executable controls, not a kernel proof of pointer caching. -/
@[implemented_by renderGraphNative]
def renderGraph (values : List Value) : Json := renderGraphSpec values

end TrustIrEval.Observation
