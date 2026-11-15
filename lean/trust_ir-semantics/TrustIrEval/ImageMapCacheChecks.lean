-- Copyright 2026 Andrew Yates | Apache-2.0
-- Functional counters in the actual StateM cache; no correspondence proof grade.
import TrustIr.State.ByteImage

namespace TrustIrEval.ImageMapCacheChecks
open TrustIr TrustIr.ByteImage

private def counterKey : MapCacheKey := (0, 0)
private def runs (cache : MapCache) : Nat :=
  match cache.find? counterKey with
  | none => 0
  | some entry => entry.mapped.size

private def countedMiss (mapped : Tree 1) (_ : Unit) : StateM MapCache (Tree 1) := fun cache =>
  let entry : MapCacheEntry := { original := ByteImage.empty, mapped := ByteImage.fill (runs cache + 1) none }
  (mapped, cache.insert counterKey entry)

def checkMapCacheThunks : IO Unit := do
  let tree : Tree 1 := .fill 1 (some 7)
  let mapped : Tree 1 := .fill 1 (some 9)
  let identity : MapCacheKey := (1, 0)
  let empty : MapCache := Lean.mkHashMap
  let cache := empty.insert identity { original := ⟨1, tree⟩, mapped := ⟨1, mapped⟩ }
  let hit := tree.mapCacheStep identity (countedMiss mapped) cache
  unless hit.1.get 0 == some 9 && runs hit.2 == 0 do
    throw (IO.userError "cache hit ran the miss callback or returned wrong bytes")
  let miss := tree.mapCacheStep identity (countedMiss mapped) empty
  unless miss.1.get 0 == some 9 && runs miss.2 == 1 do
    throw (IO.userError "cache miss did not retain exactly one callback run")
  match miss.2.find? identity with
  | none => throw (IO.userError "cache miss did not insert its result")
  | some entry =>
    unless entry.original.tree.get 0 == some 7 && entry.mapped.tree.get 0 == some 9 do
      throw (IO.userError "cache insertion lost the original or mapped image")
  let twice := fun (_ : Unit) cache =>
    let (_, after) := countedMiss mapped () cache
    countedMiss mapped () after
  let doubleRun := tree.mapCacheStep identity twice empty
  unless doubleRun.1.get 0 == some 9 && runs doubleRun.2 == 2 do
    throw (IO.userError "double-run calibration did not preserve both counter updates")
  IO.println "IMAGE_MAP_CACHE_THUNK_PASS hit_runs=0 miss_runs=1 double_run_control=2 correspondence=UNPROVED"

end TrustIrEval.ImageMapCacheChecks
