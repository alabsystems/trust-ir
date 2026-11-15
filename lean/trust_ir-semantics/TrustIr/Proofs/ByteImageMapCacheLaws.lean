-- Copyright 2026 Andrew Yates | Apache-2.0
import TrustIr.Proofs.ByteImageMapCache.Legacy.Lookup
import TrustIr.State.ByteImageMapCache
namespace TrustIr.ByteImage.MapCacheLaws

/-- Exactly actual empty plus insert, all capacities, keys and payloads. -/
inductive Reachable : MapCache → Prop where
  | empty (capacity : Nat) : Reachable (trustIrMapCacheEmptyWithCapacity capacity)
  | insert {before : MapCache} (key : MapCacheKey) (entry : MapCacheEntry) :
      Reachable before → Reachable (before.insert key entry)

theorem reachable_empty : Reachable (∅ : MapCache) := by
  exact Reachable.empty 8

trustIrLegacyMapCacheDecl
private theorem legacy_reachable (cache : MapCache) (reachable : Reachable cache) :
    TrustIr.ByteImage.MapCacheProof.Legacy.MapCacheReachable cache := by
  induction reachable with
  | empty capacity => exact .empty capacity
  | insert key entry reachable ih => exact .insert key entry ih

theorem find_empty_capacity (capacity : Nat) (query : MapCacheKey) :
    trustIrHashMapFind? (trustIrMapCacheEmptyWithCapacity capacity : MapCache) query = none := by
  trustIrCompilerProof {
    change Lean.HashMapImp.find? (Lean.mkHashMapImp capacity) query = none
    rw [TrustIr.ByteImage.MapCacheProof.Legacy.actual_find]
    exact TrustIr.ByteImage.MapCacheProof.Legacy.read_empty_buckets _
      (Nat.isPowerOfTwo_nextPowerOfTwo _) query
  } {
    exact Std.HashMap.get?_emptyWithCapacity
  }

theorem find_empty (query : MapCacheKey) :
    trustIrHashMapFind? (∅ : MapCache) query = none := by
  exact find_empty_capacity 8 query

/-- Actual library insertion, with the canonical library invariant derived
    from the exact operation-local reachable protocol; no insert-law premise. -/
theorem find_insert (cache : MapCache) (reachable : Reachable cache)
    (key query : MapCacheKey) (entry : MapCacheEntry) :
    trustIrHashMapFind? (cache.insert key entry) query =
      if key == query then some entry else trustIrHashMapFind? cache query := by
  trustIrCompilerProof {
    exact TrustIr.ByteImage.MapCacheProof.Legacy.reachable_insert_find cache
      (legacy_reachable cache reachable) key query entry
  } {
    exact Std.HashMap.get?_insert
  }
end TrustIr.ByteImage.MapCacheLaws
