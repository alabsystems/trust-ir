-- Copyright 2026 Andrew Yates | Apache-2.0
import TrustIr.ByteImageMapCacheCompat
import TrustIr.Proofs.ByteImageMapCache.Legacy.Reinsert
namespace TrustIr.ByteImage.MapCacheProof.Legacy
open Lean
universe u v
variable {α : Type u} {β : Type v}

trustIrLegacyMapCacheDecl
/-- Every actual source bucket is duplicate-free, including buckets not selected
    by an arbitrary fixed query. This follows from universal RawInvariant. -/
theorem rawInvariant_bucket_unique [Hashable α]
    (buckets : HashMapBucket α β) (valid : RawInvariant buckets)
    (index : Fin buckets.val.size) :
    UniqueBucket (buckets.val.get index) := by
  cases contents : buckets.val.get index with
  | nil => trivial
  | cons key value tail =>
    by_cases selected : index.val = (pick buckets key).val
    · have indices : index = pick buckets key := Fin.ext selected
      have unique := queryShape_selected_unique key buckets.val.data
        (pick buckets key) (valid key)
      rw [← indices] at unique
      change UniqueBucket (buckets.val.get index) at unique
      rw [contents] at unique
      exact unique
    · have absent := queryShape_other_absent key buckets.val.data
        (pick buckets key) index (valid key) selected
      change NoKey key (buckets.val.get index) at absent
      rw [contents] at absent
      exact False.elim (absent.1 rfl)

trustIrLegacyMapCacheDecl
/-- A key found in any actual bucket must be routed there by the actual index
    function (including its fallback). No abstract hashing law is supplied. -/
theorem rawInvariant_found_location [BEq α] [LawfulBEq α] [Hashable α]
    (buckets : HashMapBucket α β) (valid : RawInvariant buckets)
    (index : Fin buckets.val.size) (query : α) (value : β)
    (found : (buckets.val.get index).find? query = some value) :
    index.val = (pick buckets query).val := by
  by_cases same : index.val = (pick buckets query).val
  · exact same
  · have absent := queryShape_other_absent query buckets.val.data
      (pick buckets query) index (valid query) same
    have missing := (noKey_iff_find_none query _).mp absent
    change (buckets.val.get index).find? query = none at missing
    rw [found] at missing
    cases missing

trustIrLegacyMapCacheDecl
/-- Thus distinct source buckets cannot both contain a query; this is the
    cross-bucket disjointness needed by the destructive source-clearing loop. -/
theorem rawInvariant_distinct_bucket_absent [BEq α] [LawfulBEq α] [Hashable α]
    (buckets : HashMapBucket α β) (valid : RawInvariant buckets)
    (first second : Fin buckets.val.size) (query : α) (value : β)
    (found : (buckets.val.get first).find? query = some value)
    (different : second.val ≠ first.val) :
    NoKey query (buckets.val.get second) := by
  have location := rawInvariant_found_location buckets valid first query value found
  exact queryShape_other_absent query buckets.val.data (pick buckets query) second
    (valid query) (by rw [← location]; exact different)
end TrustIr.ByteImage.MapCacheProof.Legacy
