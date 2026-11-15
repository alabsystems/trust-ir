-- Copyright 2026 Andrew Yates | Apache-2.0
-- Runtime implementation and representation; correspondence is UNPROVED.
import TrustIr.State.CompactArray

namespace TrustIr.CompactArray.StoredCheckRuntime

private inductive Input (α : Type) where
  | tree {size : Nat} (tree : Tree α size)
  | leaf {size : Nat} (leaf : Leaf α size)
private abbrev NodeKey := Nat × Nat × USize
private abbrev Key := NodeKey × Nat × Nat
private structure Cache (α ε : Type) where
  memo : trustIrHashMap Key (Except ε Unit × Input α) := ∅
  stats : Stats := {}
private def extent {α : Type} : Input α → Nat
  | .tree (size := size) _ => size
  | .leaf (size := size) _ => size

private unsafe def key {α : Type} : Input α → NodeKey
  | .tree (size := size) tree => (0, size, ptrAddrUnsafe tree)
  | .leaf (size := size) leaf => (1, size, ptrAddrUnsafe leaf)

private unsafe def visit {α ε : Type} (check : α → Except ε Unit) (input : Input α) (offset count : Nat) :
    StateM (Cache α ε) (Except ε Unit) := do
  let count := min count (extent input - offset)
  if count == 0 then return .ok ()
  let identity := (key input, offset, count)
  let state ← get
  if let some (result, _) := trustIrHashMapFind? state.memo identity then
    modify fun state => { state with stats := { state.stats with hits := state.stats.hits + 1 } }
    return result
  modify fun state => { state with stats := { state.stats with visits := state.stats.visits + 1 } }
  let result ← match input with
    | .tree (.uniform _ value) => do
      modify fun state => { state with stats := { state.stats with payloads := state.stats.payloads + 1 } }
      pure (check value)
    | .tree (.dense _ values) => visit check (.leaf values) offset count
    | .tree (.split (size := size) _ left right) => do
      let before := min count (size / 2 - offset)
      match ← visit check (.tree left) offset before with
      | .error error => pure (.error error)
      | .ok () => visit check (.tree right) (offset + before - size / 2) (count - before)
    | .tree (.periodic (period := period) unit _ phase _) => do
      let start := (phase + offset) % period
      let before := min count (period - start)
      match ← visit check (.tree unit) start before with
      | .error error => pure (.error error)
      | .ok () => visit check (.tree unit) 0 (min period (count - before))
    | .leaf .nil => pure (.ok ())
    | .leaf (.cons head tail) => do
      if offset > 0 then visit check (.leaf tail) (offset - 1) count else do
        modify fun state => { state with stats := { state.stats with payloads := state.stats.payloads + 1 } }
        match check head with
        | .error error => pure (.error error)
        | .ok () => visit check (.leaf tail) 0 (count - 1)
  modify fun state => { state with memo := state.memo.insert identity (result, input) }
  return result

/-- One fixed callback and retained input arena per complete operation. Cached
    errors are actual callback errors; an empty uniform never checks payload. -/
unsafe def treeWithStats {α ε : Type} (check : α → Except ε Unit) {size : Nat}
    (tree : Tree α size) : Except ε Unit × Stats :=
  let (result, state) := (visit check (.tree tree) 0 size).run {}
  (result, state.stats)
@[export l_TrustIr_CompactArray_Tree_checkStored]
unsafe def tree {α ε : Type} (check : α → Except ε Unit) {size : Nat}
    (tree : Tree α size) : Except ε Unit := (treeWithStats check tree).1
@[export l_TrustIr_CompactArray_Leaf_checkStored]
unsafe def leaf {α ε : Type} (check : α → Except ε Unit) {size : Nat}
    (leaf : Leaf α size) : Except ε Unit := ((visit check (.leaf leaf) 0 size).run {}).1
/-- One fixed callback and retained input arena per bounded operation. Exact
    offset and clipped count are part of each memo key. Empty windows inspect
    no payload, and callback errors retain left-to-right precedence. -/
unsafe def rangeWithStats {α ε : Type} (check : α → Except ε Unit) {size : Nat}
    (tree : Tree α size) (offset count : Nat) : Except ε Unit × Stats :=
  let (result, state) := (visit check (.tree tree) offset count).run {}
  (result, state.stats)
@[export l_TrustIr_CompactArray_Tree_checkRange]
unsafe def range {α ε : Type} (check : α → Except ε Unit) {size : Nat}
    (tree : Tree α size) (offset count : Nat) : Except ε Unit :=
  (rangeWithStats check tree offset count).1
@[export l_TrustIr_CompactArray_Leaf_checkRange]
unsafe def leafRange {α ε : Type} (check : α → Except ε Unit) {size : Nat}
    (leaf : Leaf α size) (offset count : Nat) : Except ε Unit :=
  ((visit check (.leaf leaf) offset count).run {}).1

end TrustIr.CompactArray.StoredCheckRuntime
