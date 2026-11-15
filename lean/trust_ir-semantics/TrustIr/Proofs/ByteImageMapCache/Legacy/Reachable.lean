-- Copyright 2026 Andrew Yates | Apache-2.0
import TrustIr.ByteImageMapCacheCompat
import TrustIr.Proofs.ByteImageMapCache.Legacy.Move
namespace TrustIr.ByteImage.MapCacheProof.Legacy
open Lean
universe u v
variable {α : Type u} {β : Type v}

trustIrLegacyMapCacheDecl
theorem entriesAbsent_empty [BEq α] [Hashable α] (entries : AssocList α β)
    (count : Nat) (power : count.isPowerOfTwo) :
    EntriesAbsent entries
      (⟨Array.mkArray count AssocList.nil, by simpa using power⟩ : HashMapBucket α β) := by
  induction entries with
  | nil => trivial
  | cons key value tail ih => exact ⟨read_empty_buckets count power key, ih⟩

trustIrLegacyMapCacheDecl
/-- Actual resize derives its concrete loop invariant from actual fresh empty
    target buckets and the source routing/uniqueness invariant. -/
theorem expand_rawInvariant [BEq α] [LawfulBEq α] [Hashable α]
    (source : HashMapBucket α β) (size : Nat) (valid : RawInvariant source) :
    RawInvariant (HashMapImp.expand size source).buckets := by
  unfold HashMapImp.expand
  apply moveEntries_rawInvariant source _ 0 valid
  · exact rawInvariant_empty (source.val.size * 2)
      (Nat.mul2_isPowerOfTwo_of_isPowerOfTwo source.property)
  · intro index _
    exact entriesAbsent_empty (source.val.get index) (source.val.size * 2)
      (Nat.mul2_isPowerOfTwo_of_isPowerOfTwo source.property)

-- Exact unfolded private-index insertion, for proof reduction only. This is
-- tied to the actual library definition by rfl; runtime still calls actualinsert.
trustIrLegacyMapCacheDecl
def insertReference [BEq α] [Hashable α] (source : HashMapImp α β) (key : α) (value : β) :
    HashMapImp α β × Bool :=
  let buckets := source.buckets
  let selected := bucketIndex (hash key) buckets.property
  let bucket := buckets.val.get ⟨selected.val.toNat, selected.property⟩
  if bucket.contains key then
    (⟨source.size, buckets.update selected.val (bucket.replace key value) selected.property⟩, true)
  else
    let size := source.size + 1
    let updated := buckets.update selected.val (.cons key value bucket) selected.property
    if size * 4 / 3 ≤ buckets.val.size then (⟨size, updated⟩, false)
    else (HashMapImp.expand size updated, false)

trustIrLegacyMapCacheDecl
theorem actual_insert_reference [BEq α] [Hashable α]
    (source : HashMapImp α β) (key : α) (value : β) :
    HashMapImp.insert source key value = insertReference source key value := by
  cases source
  rfl

trustIrLegacyMapCacheDecl
/-- Actual insert's replacement, direct-add and expand branches, with arbitrary
    capacity/load count, key, payload and source satisfying concrete invariants. -/
theorem insert_rawInvariant [BEq α] [LawfulBEq α] [Hashable α]
    (source : HashMapImp α β) (key : α) (value : β)
    (valid : RawInvariant source.buckets) :
    RawInvariant (HashMapImp.insert source key value).1.buckets := by
  cases source with
  | mk size buckets =>
    rw [actual_insert_reference]
    unfold insertReference
    dsimp only
    split
    · exact rawInvariant_replace buckets key value valid
    · rename_i absent
      split
      · exact rawInvariant_reinsert_fresh buckets key value valid (Bool.of_not_eq_true absent)
      · apply expand_rawInvariant
        exact rawInvariant_reinsert_fresh buckets key value valid (Bool.of_not_eq_true absent)

trustIrLegacyMapCacheDecl
/-- Initial operation-local cache capacity is arbitrary; after any finite
    number of actual inserts the concrete invariant still holds. The protocol
    exactly matches runtime MapCache (empty/insert), not generic WellFormed. -/
theorem reachable_rawInvariant [BEq α] [LawfulBEq α] [Hashable α]
    (map : HashMap α β) (reachable : MapCacheReachable map) :
    RawInvariant map.val.buckets := by
  induction reachable with
  | empty capacity =>
    apply rawInvariant_empty
    apply Nat.isPowerOfTwo_nextPowerOfTwo
  | @insert before key value reachable ih =>
    cases before with
    | mk raw wellFormed =>
      have preserved := insert_rawInvariant raw key value ih
      cases result : HashMapImp.insert raw key value with
      | mk after replaced =>
        simp only [result] at preserved
        simpa only [HashMap.insert, result] using preserved
end TrustIr.ByteImage.MapCacheProof.Legacy
