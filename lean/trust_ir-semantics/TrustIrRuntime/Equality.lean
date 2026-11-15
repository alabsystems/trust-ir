-- Copyright 2026 Andrew Yates | Apache-2.0
-- Runtime implementation and representation; correspondence is UNPROVED.
import TrustIr.State.CompactArray

namespace TrustIr.CompactArray

private structure CyclicWindow (α : Type) where
  size : Nat
  positive : 0 < size
  tree : Tree α size
  phase : Nat

private def normalizeCyclic {α : Type} {size : Nat} (tree : Tree α size)
    (positive : 0 < size) (phase count : Nat) : CyclicWindow α :=
  let phase := phase % size
  let original : CyclicWindow α := ⟨size, positive, tree, phase⟩
  if count = 0 then original else
  match tree with
  | .uniform _ value => ⟨1, by decide, .uniform 1 value, 0⟩
  | .dense _ _ => original
  | .split (size := size) large left right =>
    if phase + count ≤ size / 2 then
      normalizeCyclic left (by omega) phase count
    else if size / 2 ≤ phase ∧ phase + count ≤ size then
      normalizeCyclic right (by omega) (phase - size / 2) count
    else original
  | .periodic (period := period) unit innerPositive innerPhase size =>
    if size % period = 0 ∨ phase + count ≤ size then
      normalizeCyclic unit innerPositive ((innerPhase + phase) % period) count
    else original

private def shiftCyclic {α : Type} (window : CyclicWindow α) (offset : Nat) : CyclicWindow α :=
  ⟨window.size, window.positive, window.tree, (window.phase + offset) % window.size⟩

private def cyclicRead {α : Type} (window : CyclicWindow α) (index : Nat) : Option α :=
  window.tree.get? ((window.phase + index) % window.size)


namespace EqualityRuntime

private abbrev NodeKey := Nat × Nat × USize × Nat
private abbrev Key := Nat × NodeKey × NodeKey
private structure Entry (α β ε : Type) where
  result : Except ε Bool
  left : CyclicWindow α
  right : CyclicWindow β
private structure Cache (α β ε : Type) where
  memo : trustIrHashMap Key (Entry α β ε) := ∅
  stats : Stats := {}

private unsafe def key {α : Type} (window : CyclicWindow α) : NodeKey :=
  let address := ptrAddrUnsafe window.tree
  match window.tree with
  | .uniform _ value => (0, 1, ptrAddrUnsafe value, 0)
  | _ => (1, window.size, address, window.phase)

private unsafe def visit {α β ε : Type} (eq : α → β → Except ε Bool)
    (left : CyclicWindow α) (right : CyclicWindow β) (count : Nat) :
    StateM (Cache α β ε) (Except ε Bool) := do
  if count == 0 then return .ok true
  let left := normalizeCyclic left.tree left.positive left.phase count
  let right := normalizeCyclic right.tree right.positive right.phase count
  let identity := (count, key left, key right)
  let state ← get
  if let some entry := trustIrHashMapFind? state.memo identity then
    modify fun state => { state with stats := { state.stats with hits := state.stats.hits + 1 } }
    return entry.result
  modify fun state => { state with stats := { state.stats with visits := state.stats.visits + 1 } }
  let result ← match left.tree, right.tree with
    | .uniform _ a, .uniform _ b => pure (eq a b)
    | _, _ => do
      let joint := Nat.lcm left.size right.size
      if joint < count then visit eq left right joint
      else if count == 1 then
        match cyclicRead left 0, cyclicRead right 0 with
        | some a, some b => pure (eq a b)
        | _, _ => pure (.ok false)
      else
        match ← visit eq left right (count / 2) with
        | .ok true => visit eq (shiftCyclic left (count / 2)) (shiftCyclic right (count / 2)) (count - count / 2)
        | result => pure result
  modify fun state => { state with memo := state.memo.insert identity { result, left, right } }
  return result

/-- A fixed comparator and retained typed source arena per complete operation.
    Phase and full logical count are keys. Alias identity never supplies truth. -/
unsafe def treeWithStats {α β ε : Type} (eq : α → β → Except ε Bool) {size : Nat}
    (left : Tree α size) (right : Tree β size) : Except ε Bool × Stats :=
  if zero : size = 0 then (.ok true, {}) else
    let (result, state) := (visit eq ⟨size, by omega, left, 0⟩ ⟨size, by omega, right, 0⟩ size).run {}
    (result, state.stats)
@[export l_TrustIr_CompactArray_Tree_eqByM]
unsafe def tree {α β ε : Type} (eq : α → β → Except ε Bool) {size : Nat}
    (left : Tree α size) (right : Tree β size) : Except ε Bool :=
  (treeWithStats eq left right).1

end EqualityRuntime

end TrustIr.CompactArray
