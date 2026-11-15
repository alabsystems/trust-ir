-- Copyright 2026 Andrew Yates | Apache-2.0
-- Runtime implementation and representation; correspondence is UNPROVED.
import TrustIr.State.ValueMap

namespace TrustIr.ValueDepthRuntime

/-- Counters describe traversal, not admission limits or proof authority. -/

private inductive Input where
  | value (value : Value)
  | values (values : List Value)
  | fields (fields : List (String × Value))
  | tree {size : Nat} (tree : CompactArray.Tree Value size) (offset count : Nat)
  | leaf {size : Nat} (leaf : CompactArray.Leaf Value size) (offset count : Nat)

private structure Shape where
  base : Nat
  children : List Input := []

private def view : Input → Shape
  | .value (.array values) => ⟨1, [.tree values.tree 0 values.size]⟩
  | .value (.aggregate values) | .value (.vector values) | .value (.frame _ values)
  | .value (.set values) | .value (.sequence values) | .value (.closure _ values)
  | .value (.typedClosure _ _ values) => ⟨1, [.values values]⟩
  | .value (.record fields) => ⟨1, [.fields fields]⟩
  | .value (.fatPtr _ _ metadata) => ⟨1, [.value metadata]⟩
  | .value _ => ⟨1, []⟩
  | .values [] | .fields [] => ⟨0, []⟩
  | .values (head :: tail) => ⟨0, [.value head, .values tail]⟩
  | .fields ((_, value) :: tail) => ⟨0, [.value value, .fields tail]⟩
  | .tree (size := size) tree offset count =>
    let count := min count (size - offset)
    if count == 0 then ⟨0, []⟩ else
    match tree with
    | .uniform _ value => ⟨0, [.value value]⟩
    | .dense _ values => ⟨0, [.leaf values offset count]⟩
    | .split (size := size) _ left right =>
      let before := min count (size / 2 - offset)
      ⟨0, [.tree left offset before, .tree right (offset + before - size / 2) (count - before)]⟩
    | .periodic (period := period) unit _ phase _ =>
      let start := (phase + offset) % period
      let before := min count (period - start)
      ⟨0, [.tree unit start before, .tree unit 0 (min period (count - before))]⟩
  | .leaf (size := size) leaf offset count =>
    let count := min count (size - offset)
    if count == 0 then ⟨0, []⟩ else
    match leaf with
    | .nil => ⟨0, []⟩
    | .cons value rest =>
      if offset == 0 then ⟨0, [.value value, .leaf rest 0 (count - 1)]⟩
      else ⟨0, [.leaf rest (offset - 1) count]⟩

private abbrev Key := (Nat × Nat × USize) × Nat × Nat
private structure Cache where
  -- Retention prevents address reuse. Extents and domains distinguish all
  -- dependent carriers; the cache belongs to exactly one depth operation.
  memo : trustIrHashMap Key (Nat × Input) := ∅
  stats : Stats := {}

private unsafe def key : Input → Key
  | .value value => ((0, 0, ptrAddrUnsafe value), 0, 0)
  | .values values => ((1, 0, ptrAddrUnsafe values), 0, 0)
  | .fields fields => ((2, 0, ptrAddrUnsafe fields), 0, 0)
  | .tree (size := size) tree offset count => ((3, size, ptrAddrUnsafe tree), offset, min count (size - offset))
  | .leaf (size := size) leaf offset count => ((4, size, ptrAddrUnsafe leaf), offset, min count (size - offset))

private unsafe def visit (input : Input) : StateM Cache Nat := do
  let identity := key input
  let state ← get
  if let some (depth, _) := trustIrHashMapFind? state.memo identity then
    modify fun state => { state with stats := { state.stats with hits := state.stats.hits + 1 } }
    return depth
  modify fun state => { state with stats := { state.stats with visits := state.stats.visits + 1 } }
  let shape := view input
  let mut largest := 0
  for child in shape.children do largest := max largest (← visit child)
  let depth := shape.base + largest
  modify fun state => { state with memo := state.memo.insert identity (depth, input) }
  return depth

unsafe def depthWithStats (value : Value) : Nat × Stats :=
  let (depth, state) := (visit (.value value)).run {}
  (depth, state.stats)

private unsafe def run (input : Input) : Nat := ((visit input).run {}).1
@[export l_TrustIr_Value_depth]
unsafe def valueDepth (value : Value) : Nat := run (.value value)
@[export l_TrustIr_valueListDepth]
unsafe def listDepth (values : List Value) : Nat := run (.values values)
@[export l_TrustIr_valueFieldDepth]
unsafe def fieldDepth (fields : List (String × Value)) : Nat := run (.fields fields)
@[export l_TrustIr_arrayTreeDepth]
unsafe def treeDepth {size : Nat} (tree : CompactArray.Tree Value size) : Nat := run (.tree tree 0 size)
@[export l_TrustIr_arrayLeafDepth]
unsafe def leafDepth {size : Nat} (leaf : CompactArray.Leaf Value size) : Nat := run (.leaf leaf 0 size)

end TrustIr.ValueDepthRuntime
