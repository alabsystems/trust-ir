-- Copyright 2026 Andrew Yates | Apache-2.0
import TrustIr.ByteImageMapCacheCompat
import TrustIr.Proofs.ByteImageMapCache.Legacy.SourceRouting
namespace TrustIr.ByteImage.MapCacheProof.Legacy
open Lean
universe u v
variable {α : Type u} {β : Type v}

trustIrLegacyMapCacheDecl
def KeysAll (property : α → Prop) : AssocList α β → Prop
  | .nil => True
  | .cons key _ tail => property key ∧ KeysAll property tail

trustIrLegacyMapCacheDecl
theorem keysAll_of_find [BEq α] [LawfulBEq α]
    (entries : AssocList α β) (property : α → Prop)
    (every : ∀ query value, entries.find? query = some value → property query) :
    KeysAll property entries := by
  induction entries with
  | nil => trivial
  | cons head payload tail ih =>
    constructor
    · apply every head payload
      simp [AssocList.find?]
    · apply ih
      intro query value found
      cases comparison : head == query with
      | false =>
        apply every query value
        simp only [AssocList.find?, comparison]
        exact found
      | true =>
        apply every query payload
        simp only [AssocList.find?, comparison]

trustIrLegacyMapCacheDecl
theorem source_buckets_disjoint [BEq α] [LawfulBEq α] [Hashable α]
    (source : HashMapBucket α β) (valid : RawInvariant source)
    (processed pending : Fin source.val.size) (different : processed.val ≠ pending.val) :
    KeysAll (fun query => NoKey query (source.val.get processed)) (source.val.get pending) := by
  apply keysAll_of_find
  intro query value found
  exact rawInvariant_distinct_bucket_absent source valid pending processed query value found different

trustIrLegacyMapCacheDecl
theorem entriesAbsent_after_fold [BEq α] [LawfulBEq α] [Hashable α]
    (processed pending : AssocList α β) (target : HashMapBucket α β)
    (apart : KeysAll (fun query => NoKey query processed) pending)
    (absent : EntriesAbsent pending target) :
    EntriesAbsent pending (processed.foldl (HashMapImp.reinsertAux hash) target) := by
  induction pending with
  | nil => trivial
  | cons query value tail ih =>
    exact ⟨by rw [read_fold_absent processed target query apart.1]; exact absent.1,
      ih apart.2 absent.2⟩

-- Actual moveEntries uses Fin/Nat source clearing, not USize truncation. This
-- distinction preserves arbitrary logical capacities, including huge arrays.
trustIrLegacyMapCacheDecl
def clearBucket (source : HashMapBucket α β) (index : Fin source.val.size) : HashMapBucket α β :=
  ⟨source.val.set index AssocList.nil, by simpa only [Array.size_set] using source.property⟩

trustIrLegacyMapCacheDecl
theorem pick_clear_value [Hashable α] (source : HashMapBucket α β)
    (index : Fin source.val.size) (query : α) :
    (pick (clearBucket source index) query).val = (pick source query).val := by
  simp only [pick, bucketIndex_value, clearBucket, Array.size_set]

trustIrLegacyMapCacheDecl
theorem rawInvariant_clear [Hashable α] (source : HashMapBucket α β)
    (index : Fin source.val.size) (valid : RawInvariant source) :
    RawInvariant (clearBucket source index) := by
  intro query
  change QueryShape query (source.val.data.set index.val AssocList.nil)
    (pick (clearBucket source index) query).val
  rw [pick_clear_value]
  apply queryShape_set query source.val.data (pick source query).val index.val AssocList.nil (valid query)
  split <;> trivial

trustIrLegacyMapCacheDecl
theorem clear_get_other (source : HashMapBucket α β) (index : Fin source.val.size)
    (query : Fin (clearBucket source index).val.size) (different : index.val ≠ query.val) :
    (clearBucket source index).val.get query =
      source.val.get ⟨query.val, by simpa only [clearBucket, Array.size_set] using query.isLt⟩ := by
  change (source.val.set index AssocList.nil).get query = _
  rw [array_get_set]
  simp only [different, if_false]

-- Concrete loop invariant: no unprocessed actual source key is in target.
trustIrLegacyMapCacheDecl
def PendingAbsent [BEq α] [Hashable α] (source : HashMapBucket α β)
    (start : Nat) (target : HashMapBucket α β) : Prop :=
  ∀ index : Fin source.val.size, start ≤ index.val →
    EntriesAbsent (source.val.get index) target

trustIrLegacyMapCacheDecl
theorem pending_step [BEq α] [LawfulBEq α] [Hashable α]
    (source : HashMapBucket α β) (index : Fin source.val.size)
    (target : HashMapBucket α β) (sourceValid : RawInvariant source)
    (pending : PendingAbsent source index.val target) :
    PendingAbsent (clearBucket source index) (index.val + 1)
      ((source.val.get index).foldl (HashMapImp.reinsertAux hash) target) := by
  intro query later
  have different : index.val ≠ query.val := by omega
  rw [clear_get_other source index query different]
  let original : Fin source.val.size :=
    ⟨query.val, by simpa only [clearBucket, Array.size_set] using query.isLt⟩
  exact entriesAbsent_after_fold (source.val.get index) (source.val.get original) target
    (source_buckets_disjoint source sourceValid index original different)
    (pending original (by
      change index.val ≤ query.val
      exact Nat.le_trans (Nat.le_succ _) later))

trustIrLegacyMapCacheDecl
/-- Actual source.set(nil), foldl(reinsertAux), increment loop. All source and
    target capacities/keys/payloads are unrestricted by this invariant proof. -/
theorem moveEntries_rawInvariant [BEq α] [LawfulBEq α] [Hashable α]
    (source : HashMapBucket α β) (target : HashMapBucket α β) (start : Nat)
    (sourceValid : RawInvariant source) (targetValid : RawInvariant target)
    (pending : PendingAbsent source start target) :
    RawInvariant (HashMapImp.moveEntries start source.val target) := by
  rw [HashMapImp.moveEntries]
  split
  · rename_i inside
    let index : Fin source.val.size := ⟨start, inside⟩
    have nextValid := rawInvariant_fold_reinsert (source.val.get index) target targetValid
      (rawInvariant_bucket_unique source sourceValid index) (pending index (Nat.le_refl _))
    exact moveEntries_rawInvariant (clearBucket source index)
      ((source.val.get index).foldl (HashMapImp.reinsertAux hash) target) (start + 1)
      (rawInvariant_clear source index sourceValid) nextValid
      (pending_step source index target sourceValid pending)
  · exact targetValid
termination_by source.val.size - start
decreasing_by
  simp_wf
  simp only [clearBucket, Array.size_set]
  omega
end TrustIr.ByteImage.MapCacheProof.Legacy
