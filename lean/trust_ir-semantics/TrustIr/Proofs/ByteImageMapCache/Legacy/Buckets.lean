-- Copyright 2026 Andrew Yates | Apache-2.0
import TrustIr.ByteImageMapCacheCompat
-- No production imports/definitions/instances are changed.
import Lean
import Init.Data.Array.Lemmas
namespace TrustIr.ByteImage.MapCacheProof.Legacy
open Lean
universe u v
variable {α : Type u} {β : Type v}

-- The 4.8 distribution has no List.Nodup/Perm library. Define the needed
-- structural invariant explicitly rather than importing nonexistent laws.
trustIrLegacyMapCacheDecl
def NoKey (query : α) : AssocList α β → Prop
  | .nil => True
  | .cons key _ tail => key ≠ query ∧ NoKey query tail

trustIrLegacyMapCacheDecl
def UniqueBucket : AssocList α β → Prop
  | .nil => True
  | .cons key _ tail => NoKey key tail ∧ UniqueBucket tail

trustIrLegacyMapCacheDecl
def Records : AssocList α β → List (α × β)
  | .nil => []
  | .cons key value tail => (key, value) :: Records tail

trustIrLegacyMapCacheDecl
/-- Exact logical reference implementation of the private library mkIdx.
    Same bitmask, bounds branch and zero fallback; native extern not assumed. -/
def bucketIndex {size : Nat} (hashValue : UInt64) (power : size.isPowerOfTwo) :
    { index : USize // index.toNat < size } :=
  let index := hashValue.toUSize &&& (size.toUSize - 1)
  if inside : index.toNat < size then ⟨index, inside⟩
  else ⟨0, by
    simp [USize.toNat, OfNat.ofNat, USize.ofNat, Fin.ofNat']
    apply Nat.pos_of_isPowerOfTwo power⟩

-- The selected numeric value is independent of its power-of-two proof.
-- This removes dependent proof transport from actual bucket update arithmetic.
trustIrLegacyMapCacheDecl
theorem bucketIndex_value {size : Nat} (hashValue : UInt64) (power : size.isPowerOfTwo) :
    (bucketIndex hashValue power).val =
      let index := hashValue.toUSize &&& (size.toUSize - 1)
      if index.toNat < size then index else 0 := by
  unfold bucketIndex
  dsimp only
  split <;> rfl

trustIrLegacyMapCacheDecl
def pick [Hashable α] (buckets : HashMapBucket α β) (key : α) : Fin buckets.val.size :=
  let selected := bucketIndex (hash key) buckets.property
  ⟨selected.val.toNat, selected.property⟩

trustIrLegacyMapCacheDecl
def read [BEq α] [Hashable α] (buckets : HashMapBucket α β) (query : α) : Option β :=
  AssocList.find? query (buckets.val.get (pick buckets query))

trustIrLegacyMapCacheDecl
/-- Definitional bridge binds the reference index to actual private mkIdx. -/
theorem actual_find [BEq α] [Hashable α] (size : Nat)
    (buckets : HashMapBucket α β) (query : α) :
    HashMapImp.find? ⟨size, buckets⟩ query = read buckets query := rfl

trustIrLegacyMapCacheDecl
theorem actual_reinsert [Hashable α] (buckets : HashMapBucket α β)
    (key : α) (value : β) :
    HashMapImp.reinsertAux hash buckets key value =
      buckets.update (bucketIndex (hash key) buckets.property).val
        (.cons key value (buckets.val.get (pick buckets key)))
        (bucketIndex (hash key) buckets.property).property := rfl

trustIrLegacyMapCacheDecl
theorem pick_update_value [Hashable α] (buckets : HashMapBucket α β)
    (index : USize) (entry : AssocList α β) (inside : index.toNat < buckets.val.size)
    (query : α) :
    (pick (buckets.update index entry inside) query).val = (pick buckets query).val := by
  simp only [pick, bucketIndex_value, HashMapBucket.update, Array.uset, Array.size_set]

trustIrLegacyMapCacheDecl
theorem array_get_set (array : Array β) (index : Fin array.size) (value : β)
    (query : Fin (array.set index value).size) :
    (array.set index value).get query =
      if index.val = query.val then value else
        array.get ⟨query.val, by simpa only [Array.size_set] using query.isLt⟩ := by
  exact Array.getElem_set array index value query.val query.isLt

trustIrLegacyMapCacheDecl
/-- Exact update lookup for every query and every power-of-two capacity. -/
theorem read_update [BEq α] [Hashable α] (buckets : HashMapBucket α β)
    (index : USize) (entry : AssocList α β) (inside : index.toNat < buckets.val.size)
    (query : α) :
    read (buckets.update index entry inside) query =
      if index.toNat = (pick buckets query).val then AssocList.find? query entry
      else read buckets query := by
  -- Keep Array.get visible until the proved get-after-set equation fires.
  -- Simplifying read/Array.get too early hides this exact library interface.
  change AssocList.find? query
      ((buckets.val.set ⟨index.toNat, inside⟩ entry).get
        (pick (buckets.update index entry inside) query)) =
    if index.toNat = (pick buckets query).val then AssocList.find? query entry
    else AssocList.find? query (buckets.val.get (pick buckets query))
  rw [array_get_set]
  split
  · rename_i same
    have originalSame : index.toNat = (pick buckets query).val :=
      same.trans (pick_update_value buckets index entry inside query)
    simp [originalSame]
  · rename_i different
    have originalDifferent : index.toNat ≠ (pick buckets query).val := by
      intro equal
      apply different
      exact equal.trans (pick_update_value buckets index entry inside query).symm
    rw [if_neg originalDifferent]
    congr 1
    apply congrArg (fun selected : Fin buckets.val.size => buckets.val.get selected)
    apply Fin.ext
    exact pick_update_value buckets index entry inside query

trustIrLegacyMapCacheDecl
theorem cons_find [BEq α] (key query : α) (value : β) (tail : AssocList α β) :
    AssocList.find? query (.cons key value tail) =
      if key == query then some value else AssocList.find? query tail := by
  cases comparison : key == query <;> simp [AssocList.find?, comparison]

trustIrLegacyMapCacheDecl
/-- Actual reinsertAux semantics, without a bucket uniqueness assumption. -/
theorem read_reinsert [BEq α] [LawfulBEq α] [Hashable α]
    (buckets : HashMapBucket α β) (key query : α) (value : β) :
    read (HashMapImp.reinsertAux hash buckets key value) query =
      if key == query then some value else read buckets query := by
  rw [actual_reinsert, read_update]
  change (if (pick buckets key).val = (pick buckets query).val then
      AssocList.find? query (.cons key value (buckets.val.get (pick buckets key)))
      else read buckets query) = _
  by_cases equalKey : key = query
  · subst query
    simp [cons_find]
  · by_cases sameIndex : (pick buckets key).val = (pick buckets query).val
    · have indices : pick buckets key = pick buckets query := Fin.ext sameIndex
      simp [sameIndex, equalKey, cons_find, indices, read]
    · simp [sameIndex, equalKey]

trustIrLegacyMapCacheDecl
theorem read_reinsert_same [BEq α] [LawfulBEq α] [Hashable α]
    (buckets : HashMapBucket α β) (key : α) (value : β) :
    read (HashMapImp.reinsertAux hash buckets key value) key = some value := by
  rw [read_reinsert]
  simp

trustIrLegacyMapCacheDecl
theorem read_reinsert_other [BEq α] [LawfulBEq α] [Hashable α]
    (buckets : HashMapBucket α β) (key query : α) (value : β) (different : key ≠ query) :
    read (HashMapImp.reinsertAux hash buckets key value) query = read buckets query := by
  rw [read_reinsert]
  simp [different]

trustIrLegacyMapCacheDecl
/-- This is the actual scalar update performed by reinsert, not an assumed law. -/
def overwrite [BEq α] (query : α) (previous : Option β) (key : α) (value : β) : Option β :=
  if key == query then some value else previous

trustIrLegacyMapCacheDecl
/-- Exact actual AssocList.foldl rehash semantics, including collision order. -/
theorem read_fold_reinsert [BEq α] [LawfulBEq α] [Hashable α]
    (entries : AssocList α β) (target : HashMapBucket α β) (query : α) :
    read (entries.foldl (HashMapImp.reinsertAux hash) target) query =
      entries.foldl (overwrite query) (read target query) := by
  induction entries generalizing target with
  | nil => rfl
  | cons key value tail ih =>
    change read (tail.foldl (HashMapImp.reinsertAux hash)
      (HashMapImp.reinsertAux hash target key value)) query =
      tail.foldl (overwrite query) (overwrite query (read target query) key value)
    rw [ih, read_reinsert]
    rfl

trustIrLegacyMapCacheDecl
theorem read_fold_absent [BEq α] [LawfulBEq α] [Hashable α]
    (entries : AssocList α β) (target : HashMapBucket α β) (query : α)
    (absent : NoKey query entries) :
    read (entries.foldl (HashMapImp.reinsertAux hash) target) query = read target query := by
  induction entries generalizing target with
  | nil => rfl
  | cons key value tail ih =>
    change read (tail.foldl (HashMapImp.reinsertAux hash)
      (HashMapImp.reinsertAux hash target key value)) query = _
    rw [ih _ absent.2, read_reinsert_other _ _ _ _ absent.1]

trustIrLegacyMapCacheDecl
/-- With uniqueness derived elsewhere, reinsertion order is irrelevant to lookup.
    This discharges the single-source-bucket part of actual resize. -/
theorem read_fold_unique [BEq α] [LawfulBEq α] [Hashable α]
    (entries : AssocList α β) (target : HashMapBucket α β) (query : α)
    (unique : UniqueBucket entries) :
    read (entries.foldl (HashMapImp.reinsertAux hash) target) query =
      match AssocList.find? query entries with
      | some value => some value
      | none => read target query := by
  induction entries generalizing target with
  | nil => rfl
  | cons key value tail ih =>
    change read (tail.foldl (HashMapImp.reinsertAux hash)
      (HashMapImp.reinsertAux hash target key value)) query = _
    by_cases same : key = query
    · subst query
      rw [read_fold_absent _ _ _ unique.1, read_reinsert_same]
      simp [AssocList.find?]
    · rw [ih _ unique.2, read_reinsert_other _ _ _ _ same]
      simp [AssocList.find?, beq_false_of_ne same]

trustIrLegacyMapCacheDecl
/-- Literal query interpretation of the actual source-clearing resize loop.
    No client callback or insert-preservation premise is supplied. -/
def overwriteBuckets [BEq α] (i : Nat) (source : Array (AssocList α β))
    (query : α) (previous : Option β) : Option β :=
  if inside : i < source.size then
    let index : Fin source.size := ⟨i, inside⟩
    let entries := source.get index
    let source := source.set index AssocList.nil
    overwriteBuckets (i + 1) source query (entries.foldl (overwrite query) previous)
  else previous
termination_by source.size - i
decreasing_by simp_wf; decreasing_trivial_pre_omega

trustIrLegacyMapCacheDecl
/-- Actual moveEntries lookup equals the complete query replay for ALL raw
    bucket arrays, even malformed/duplicate ones; no transparency shortcut. -/
theorem read_moveEntries [BEq α] [LawfulBEq α] [Hashable α]
    (i : Nat) (source : Array (AssocList α β))
    (target : HashMapBucket α β) (query : α) :
    read (HashMapImp.moveEntries i source target) query =
      overwriteBuckets i source query (read target query) := by
  rw [HashMapImp.moveEntries, overwriteBuckets]
  split
  · rw [read_moveEntries, read_fold_reinsert]
  · rfl
termination_by source.size - i
decreasing_by simp_wf; decreasing_trivial_pre_omega

trustIrLegacyMapCacheDecl
/-- Real bucket replacement semantics, including misses and existing duplicates. -/
theorem find_replace [BEq α] [LawfulBEq α]
    (entries : AssocList α β) (key query : α) (value : β) :
    AssocList.find? query (AssocList.replace key value entries) =
      if key == query then
        if AssocList.contains key entries then some value else none
      else AssocList.find? query entries := by
  induction entries with
  | nil => simp [AssocList.replace, AssocList.find?, AssocList.contains]
  | cons head payload tail ih =>
    by_cases headKey : head = key
    · subst head
      by_cases keyQuery : key = query
      · subst query
        simp [AssocList.replace, AssocList.find?, AssocList.contains]
      · simp [AssocList.replace, AssocList.find?, AssocList.contains, beq_false_of_ne keyQuery]
    · by_cases headQuery : head = query
      · subst query
        have keyHead : key ≠ head := Ne.symm headKey
        simp [AssocList.replace, AssocList.find?, AssocList.contains, beq_false_of_ne headKey, beq_false_of_ne keyHead]
      · simpa [AssocList.replace, AssocList.find?, AssocList.contains, beq_false_of_ne headKey, beq_false_of_ne headQuery] using ih


-- Lookup after insertion is proved for the actual empty/insert cache protocol
-- by the downstream reachable-map and lookup modules.
end TrustIr.ByteImage.MapCacheProof.Legacy
