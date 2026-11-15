-- Copyright 2026 Andrew Yates | Apache-2.0
import TrustIr.ByteImageMapCacheCompat
import TrustIr.Proofs.ByteImageMapCache.Legacy.ResizeLoop
namespace TrustIr.ByteImage.MapCacheProof.Legacy
open Lean
universe u v
variable {α : Type u} {β : Type v}

trustIrLegacyMapCacheDecl
theorem rowsAbsent_replicate_nil (query : α) (count : Nat) :
    RowsAbsent query (List.replicate count (AssocList.nil : AssocList α β)) := by
  induction count with
  | zero => trivial
  | succ count ih => exact ⟨True.intro, ih⟩

trustIrLegacyMapCacheDecl
theorem queryShape_replicate_nil (query : α) (count index : Nat)
    (inside : index < count) :
    QueryShape query (List.replicate count (AssocList.nil : AssocList α β)) index := by
  induction count generalizing index with
  | zero => exact False.elim (Nat.not_lt_zero _ inside)
  | succ count ih =>
    cases index with
    | zero => exact ⟨True.intro, rowsAbsent_replicate_nil query count⟩
    | succ index => exact ⟨True.intro, ih index (Nat.lt_of_succ_lt_succ inside)⟩

trustIrLegacyMapCacheDecl
/-- Concrete routing/uniqueness of actual empty bucket arrays, all capacities. -/
theorem rawInvariant_empty [Hashable α] (count : Nat) (power : count.isPowerOfTwo) :
    RawInvariant (⟨Array.mkArray count AssocList.nil, by simpa using power⟩ : HashMapBucket α β) := by
  intro query
  let buckets : HashMapBucket α β :=
    ⟨Array.mkArray count AssocList.nil, by simpa using power⟩
  change QueryShape query (List.replicate count AssocList.nil) (pick buckets query).val
  apply queryShape_replicate_nil
  simpa only [buckets, Array.size_mkArray] using (pick buckets query).isLt

trustIrLegacyMapCacheDecl
/-- Actual replacement preserves every absent key because it changes payloads
    only. LawfulBEq is the actual concrete key comparison law, not insert law. -/
theorem noKey_replace [BEq α] [LawfulBEq α] (entries : AssocList α β)
    (query key : α) (value : β) (absent : NoKey query entries) :
    NoKey query (entries.replace key value) := by
  induction entries with
  | nil => trivial
  | cons head payload tail ih =>
    cases comparison : head == key with
    | false =>
      simp only [AssocList.replace, comparison]
      change head ≠ query ∧ NoKey query (tail.replace key value)
      exact ⟨absent.1, ih absent.2⟩
    | true =>
      simp only [AssocList.replace, comparison]
      have same : head = key := (beq_iff_eq head key).mp comparison
      change key ≠ query ∧ NoKey query tail
      exact ⟨by rw [← same]; exact absent.1, absent.2⟩

trustIrLegacyMapCacheDecl
/-- Actual replace cannot manufacture duplicate keys. -/
theorem unique_replace [BEq α] [LawfulBEq α] (entries : AssocList α β)
    (key : α) (value : β) (unique : UniqueBucket entries) :
    UniqueBucket (entries.replace key value) := by
  induction entries with
  | nil => trivial
  | cons head payload tail ih =>
    cases comparison : head == key with
    | false =>
      simp only [AssocList.replace, comparison]
      change NoKey head (tail.replace key value) ∧ UniqueBucket (tail.replace key value)
      exact ⟨noKey_replace tail head key value unique.1, ih unique.2⟩
    | true =>
      simp only [AssocList.replace, comparison]
      have same : head = key := (beq_iff_eq head key).mp comparison
      change NoKey key tail ∧ UniqueBucket tail
      exact ⟨by rw [← same]; exact unique.1, unique.2⟩

trustIrLegacyMapCacheDecl
/-- Exact operation-local reachable maps: empty plus actual insert, with no
    restriction on keys, values, counts, capacities or resize frequency. This
    is not a claim about arbitrary publicly constructible HashMapImp values. -/
inductive MapCacheReachable [BEq α] [Hashable α] : HashMap α β → Prop where
  | empty (capacity : Nat) : MapCacheReachable (mkHashMap capacity)
  | insert {before : HashMap α β} (key : α) (value : β) :
      MapCacheReachable before → MapCacheReachable (before.insert key value)

-- Actual insertion and resize invariant preservation are proved in the
-- downstream Move, Reachable and Lookup modules. No insertion law is assumed.
end TrustIr.ByteImage.MapCacheProof.Legacy
