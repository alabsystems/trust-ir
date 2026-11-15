-- Copyright 2026 Andrew Yates | Apache-2.0
import TrustIr.ByteImageMapCacheCompat
import TrustIr.Proofs.ByteImageMapCache.Legacy.Reachable
namespace TrustIr.ByteImage.MapCacheProof.Legacy
open Lean
universe u v
variable {α : Type u} {β : Type v}

trustIrLegacyMapCacheDecl
theorem find_replace_other [BEq α] [LawfulBEq α]
    (entries : AssocList α β) (key query : α) (value : β) (different : key ≠ query) :
    (entries.replace key value).find? query = entries.find? query := by
  induction entries with
  | nil => rfl
  | cons head payload tail ih =>
    by_cases same : head = key
    · subst head
      simp [AssocList.replace, AssocList.find?, beq_false_of_ne different]
    · have comparison : (head == key) = false := by simp [same]
      simp only [AssocList.replace, comparison]
      by_cases atQuery : head = query
      · subst head
        simp [AssocList.find?]
      · simp [AssocList.find?, beq_false_of_ne atQuery, ih]

trustIrLegacyMapCacheDecl
theorem find_replace_present [BEq α] [LawfulBEq α]
    (entries : AssocList α β) (key : α) (value : β)
    (present : entries.contains key = true) :
    (entries.replace key value).find? key = some value := by
  induction entries with
  | nil => cases present
  | cons head payload tail ih =>
    cases comparison : head == key with
    | false =>
      simp only [AssocList.contains, comparison] at present
      simp only [AssocList.replace, AssocList.find?, comparison]
      exact ih present
    | true =>
      simp [AssocList.replace, AssocList.find?, comparison]

trustIrLegacyMapCacheDecl
theorem read_replace_selected [BEq α] [LawfulBEq α] [Hashable α]
    (buckets : HashMapBucket α β) (key query : α) (value : β)
    (present : (buckets.val.get (pick buckets key)).contains key = true) :
    read (buckets.update (bucketIndex (hash key) buckets.property).val
      ((buckets.val.get (pick buckets key)).replace key value)
      (bucketIndex (hash key) buckets.property).property) query =
      if key == query then some value else read buckets query := by
  rw [read_update]
  change (if (pick buckets key).val = (pick buckets query).val then
    ((buckets.val.get (pick buckets key)).replace key value).find? query
    else read buckets query) = _
  by_cases sameKey : key = query
  · subst query
    simpa using find_replace_present (buckets.val.get (pick buckets key)) key value present
  · by_cases sameIndex : (pick buckets key).val = (pick buckets query).val
    · have indices : pick buckets key = pick buckets query := Fin.ext sameIndex
      simp [sameIndex, sameKey, find_replace_other _ key query value sameKey, indices, read]
    · simp [sameIndex, sameKey]

trustIrLegacyMapCacheDecl
/-- The actual legacy lookup-after-insert equation. Resize correctness is
    supplied by the derived concrete bucket invariant, never a postulated law. -/
theorem actual_insert_find [BEq α] [LawfulBEq α] [Hashable α]
    (source : HashMapImp α β) (key query : α) (value : β)
    (valid : RawInvariant source.buckets) :
    (HashMapImp.insert source key value).1.find? query =
      if key == query then some value else source.find? query := by
  cases source with
  | mk size buckets =>
    rw [actual_insert_reference]
    unfold insertReference
    dsimp only
    split
    · rename_i present
      simpa only [actual_find] using read_replace_selected buckets key query value present
    · rename_i missing
      split
      · simpa only [actual_find] using read_reinsert buckets key query value
      · change (HashMapImp.expand (size + 1) (HashMapImp.reinsertAux hash buckets key value)).find? query =
          if key == query then some value else read buckets query
        rw [expand_read _ _ query (rawInvariant_reinsert_fresh buckets key value valid (Bool.of_not_eq_true missing))]
        exact read_reinsert buckets key query value

trustIrLegacyMapCacheDecl
/-- Every actual empty/insert-only cache has the ordinary insert equation after
    any number of prior inserts, any initial capacity, and all keys/payloads. -/
theorem reachable_insert_find [BEq α] [LawfulBEq α] [Hashable α]
    (map : HashMap α β) (reachable : MapCacheReachable map)
    (key query : α) (value : β) :
    (map.insert key value).find? query =
      if key == query then some value else map.find? query := by
  cases map with
  | mk raw wellFormed =>
    have law := actual_insert_find raw key query value
      (reachable_rawInvariant ⟨raw, wellFormed⟩ reachable)
    cases result : HashMapImp.insert raw key value with
    | mk after replaced =>
      simp only [result] at law
      simpa only [HashMap.insert, HashMap.find?, result] using law
end TrustIr.ByteImage.MapCacheProof.Legacy
