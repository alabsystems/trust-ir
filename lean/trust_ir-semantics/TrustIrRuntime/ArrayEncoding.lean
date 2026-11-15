-- Copyright 2026 Andrew Yates | Apache-2.0
-- Runtime implementation and representation; correspondence is UNPROVED.
import TrustIr.Semantics.Monad
import TrustIr.State.ByteImageTraversal
import TrustIr.State.ArrayEncodingStats

namespace TrustIr.AggregateMemory.ArrayEncodingRuntime

private inductive Input where
  | tree {size : Nat} (tree : CompactArray.Tree Value size)
  | leaf {size : Nat} (leaf : CompactArray.Leaf Value size)
private abbrev NodeKey := Nat × Nat × USize
private abbrev Key := NodeKey × Nat × Nat
private structure Entry where
  result : Except SemError ByteImage
  input : Input
private structure Cache where
  memo : trustIrHashMap Key Entry := ∅
  stats : Stats := {}
private def extent : Input → Nat
  | .tree (size := size) _ => size
  | .leaf (size := size) _ => size
private unsafe def key : Input → NodeKey
  | .tree (size := size) tree => (0, size, ptrAddrUnsafe tree)
  | .leaf (size := size) leaf => (1, size, ptrAddrUnsafe leaf)

private unsafe def visit (encode : Value → Except SemError ByteImage) (input : Input) (offset count : Nat) :
    StateM Cache (Except SemError ByteImage) := do
  let count := min count (extent input - offset)
  if count == 0 then return .ok ByteImage.empty
  let identity := (key input, offset, count)
  if let some entry := trustIrHashMapFind? (← getThe Cache).memo identity then
    modify fun cache => { cache with stats := { cache.stats with hits := cache.stats.hits + 1 } }
    return entry.result
  modify fun cache => { cache with stats := { cache.stats with visits := cache.stats.visits + 1 } }
  let result ← match input with
    | .tree (.uniform _ value) => pure ((encode value).map (fun unit => unit.tile count))
    | .tree (.dense _ values) => visit encode (.leaf values) offset count
    | .tree (.split (size := size) _ left right) => do
      let before := min count (size / 2 - offset)
      match ← visit encode (.tree left) offset before with
      | .error error => pure (.error error)
      | .ok first => do
        pure ((← visit encode (.tree right) (offset + before - size / 2) (count - before)).map first.append)
    | .tree (.periodic (period := period) unit _ phase _) => do
      let start := (phase + offset) % period
      let before := min count (period - start)
      let remaining := count - before
      let copies := remaining / period
      match ← visit encode (.tree unit) start before with
      | .error error => pure (.error error)
      | .ok first =>
        let middle ← if copies == 0 then pure (.ok ByteImage.empty) else visit encode (.tree unit) 0 period
        match middle with
        | .error error => pure (.error error)
        | .ok middle => do
          pure ((← visit encode (.tree unit) 0 (remaining % period)).map
            (fun last => first.append ((middle.tile copies).append last)))
    | .leaf .nil => pure (.ok ByteImage.empty)
    | .leaf (.cons head tail) =>
      if offset > 0 then visit encode (.leaf tail) (offset - 1) count else
      match encode head with
      | .error error => pure (.error error)
      | .ok first => do pure ((← visit encode (.leaf tail) 0 (count - 1)).map first.append)

  modify fun cache => { cache with memo := cache.memo.insert identity { result, input } }
  return result

/-- Encoding retains only bytes computed by the actual leaf callback. No
    producer-time typed image is substituted for aliased memory contents. -/
unsafe def encodeTreeWithStats (encode : Value → Except SemError ByteImage) {size : Nat}
    (tree : CompactArray.Tree Value size) : Except SemError ByteImage × Stats :=
  let (result, cache) := (visit encode (.tree tree) 0 size).run {}
  (result, cache.stats)
@[export l___private_TrustIr_Semantics_AggregateImages_0__TrustIr_AggregateMemory_encodeArrayImage]
unsafe def encodeTree (encode : Value → Except SemError ByteImage) {size : Nat}
    (tree : CompactArray.Tree Value size) : Except SemError ByteImage :=
  (encodeTreeWithStats encode tree).1

end TrustIr.AggregateMemory.ArrayEncodingRuntime
