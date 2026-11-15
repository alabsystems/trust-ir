-- Copyright 2026 Andrew Yates | Apache-2.0
import TrustIr.ByteImageMapCacheCompat
import TrustIr.Proofs.ByteImageMapCache.Legacy.Empty
namespace TrustIr.ByteImage.MapCacheProof.Legacy
open Lean
universe u v
variable {α : Type u} {β : Type v}

trustIrLegacyMapCacheDecl
theorem rowsAbsent_set (query : α) (rows : List (AssocList α β))
    (index : Nat) (replacement : AssocList α β)
    (old : RowsAbsent query rows) (fresh : NoKey query replacement) :
    RowsAbsent query (rows.set index replacement) := by
  induction rows generalizing index with
  | nil => trivial
  | cons head tail ih =>
    cases index with
    | zero => exact ⟨fresh, old.2⟩
    | succ index => exact ⟨old.1, ih index old.2⟩

trustIrLegacyMapCacheDecl
/-- Updating the selected bucket needs uniqueness; updating any other bucket
    needs query absence. These are concrete structural properties of entries. -/
theorem queryShape_set (query : α) (rows : List (AssocList α β))
    (selected index : Nat) (replacement : AssocList α β)
    (old : QueryShape query rows selected)
    (fresh : if index = selected then UniqueBucket replacement else NoKey query replacement) :
    QueryShape query (rows.set index replacement) selected := by
  induction rows generalizing selected index with
  | nil => exact False.elim old
  | cons head tail ih =>
    cases selected with
    | zero =>
      cases index with
      | zero => exact ⟨by simpa using fresh, old.2⟩
      | succ index =>
        exact ⟨old.1, rowsAbsent_set query tail index replacement old.2 (by simpa using fresh)⟩
    | succ selected =>
      cases index with
      | zero => exact ⟨by simpa using fresh, old.2⟩
      | succ index =>
        exact ⟨old.1, ih selected index old.2 (by simpa using fresh)⟩

trustIrLegacyMapCacheDecl
/-- Binds the structural lemma to the actual HashMapBucket.update operation,
    including all legal USize indices and power-of-two capacities. -/
theorem rawInvariant_update [Hashable α] (buckets : HashMapBucket α β)
    (index : USize) (replacement : AssocList α β)
    (inside : index.toNat < buckets.val.size) (old : RawInvariant buckets)
    (fresh : ∀ query, if index.toNat = (pick buckets query).val
      then UniqueBucket replacement else NoKey query replacement) :
    RawInvariant (buckets.update index replacement inside) := by
  intro query
  change QueryShape query (buckets.val.data.set index.toNat replacement)
    (pick (buckets.update index replacement inside) query).val
  rw [pick_update_value]
  exact queryShape_set query buckets.val.data (pick buckets query).val index.toNat
    replacement (old query) (fresh query)

trustIrLegacyMapCacheDecl
/-- Empty duplicate-free buckets are selected by actual lookup, all indices. -/
theorem queryShape_selected_unique (query : α) (rows : List (AssocList α β))
    (selected : Fin rows.length) (shape : QueryShape query rows selected.val) :
    UniqueBucket (rows.get selected) := by
  induction rows with
  | nil => exact False.elim shape
  | cons head tail ih =>
    cases selected with
    | mk selected inside =>
      cases selected with
      | zero => exact shape.1
      | succ selected => exact ih ⟨selected, Nat.lt_of_succ_lt_succ inside⟩ shape.2

trustIrLegacyMapCacheDecl
theorem rowsAbsent_get (query : α) (rows : List (AssocList α β))
    (index : Fin rows.length) (absent : RowsAbsent query rows) :
    NoKey query (rows.get index) := by
  induction rows with
  | nil => exact False.elim (Nat.not_lt_zero _ index.isLt)
  | cons head tail ih =>
    cases index with
    | mk index inside =>
      cases index with
      | zero => exact absent.1
      | succ index => exact ih ⟨index, Nat.lt_of_succ_lt_succ inside⟩ absent.2

trustIrLegacyMapCacheDecl
/-- This is the exact routing exclusion needed when an insertion updates a
    bucket different from the current query's selected bucket. -/
theorem queryShape_other_absent (query : α) (rows : List (AssocList α β))
    (selected index : Fin rows.length) (shape : QueryShape query rows selected.val)
    (different : index.val ≠ selected.val) : NoKey query (rows.get index) := by
  induction rows with
  | nil => exact False.elim shape
  | cons head tail ih =>
    cases selected with
    | mk selected selectedInside =>
      cases index with
      | mk index indexInside =>
        cases selected with
        | zero =>
          cases index with
          | zero => exact False.elim (different rfl)
          | succ index =>
            exact rowsAbsent_get query tail ⟨index, Nat.lt_of_succ_lt_succ indexInside⟩ shape.2
        | succ selected =>
          cases index with
          | zero => exact shape.1
          | succ index =>
            exact ih ⟨selected, Nat.lt_of_succ_lt_succ selectedInside⟩
              ⟨index, Nat.lt_of_succ_lt_succ indexInside⟩ shape.2
              (fun equal => different (congrArg Nat.succ equal))

trustIrLegacyMapCacheDecl
theorem noKey_iff_contains_false [BEq α] [LawfulBEq α]
    (query : α) (entries : AssocList α β) :
    NoKey query entries ↔ entries.contains query = false := by
  induction entries with
  | nil => exact ⟨fun _ => rfl, fun _ => True.intro⟩
  | cons key value tail ih =>
    cases comparison : key == query with
    | false =>
      have different : key ≠ query := ne_of_beq_false comparison
      change (key ≠ query ∧ NoKey query tail) ↔ _
      simp only [AssocList.contains, comparison]
      constructor
      · intro absent; exact ih.mp absent.2
      · intro absent; exact ⟨different, ih.mpr absent⟩
    | true =>
      have same : key = query := eq_of_beq comparison
      constructor
      · intro absent
        exact False.elim (absent.1 same)
      · intro impossible
        simp only [AssocList.contains, comparison] at impossible
        cases impossible

trustIrLegacyMapCacheDecl
/-- Concrete absent-key insertion into its actual selected bucket preserves
    routing/uniqueness before the optional resize. No lookup law is assumed. -/
theorem rawInvariant_reinsert_fresh [BEq α] [LawfulBEq α] [Hashable α]
    (buckets : HashMapBucket α β) (key : α) (value : β)
    (old : RawInvariant buckets)
    (freshKey : (buckets.val.get (pick buckets key)).contains key = false) :
    RawInvariant (HashMapImp.reinsertAux hash buckets key value) := by
  rw [actual_reinsert]
  apply rawInvariant_update _ _ _ _ old
  intro query
  have unique : UniqueBucket (buckets.val.get (pick buckets key)) :=
    queryShape_selected_unique key buckets.val.data (pick buckets key) (old key)
  have absentKey : NoKey key (buckets.val.get (pick buckets key)) :=
    (noKey_iff_contains_false key _).mpr freshKey
  change (if (pick buckets key).val = (pick buckets query).val
    then UniqueBucket (.cons key value (buckets.val.get (pick buckets key)))
    else NoKey query (.cons key value (buckets.val.get (pick buckets key))))
  split
  · exact ⟨absentKey, unique⟩
  · rename_i different
    have keyDifferent : key ≠ query := by
      intro equal
      subst query
      exact different rfl
    exact ⟨keyDifferent, queryShape_other_absent query buckets.val.data
      (pick buckets query) (pick buckets key) (old query) different⟩

trustIrLegacyMapCacheDecl
/-- Concrete actual replacement update preserves routing/uniqueness. This
    includes replacing at every possible hash collision and every capacity. -/
theorem rawInvariant_replace [BEq α] [LawfulBEq α] [Hashable α]
    (buckets : HashMapBucket α β) (key : α) (value : β)
    (old : RawInvariant buckets) :
    RawInvariant (buckets.update
      (bucketIndex (hash key) buckets.property).val
      ((buckets.val.get (pick buckets key)).replace key value)
      (bucketIndex (hash key) buckets.property).property) := by
  apply rawInvariant_update _ _ _ _ old
  intro query
  change (if (pick buckets key).val = (pick buckets query).val
    then UniqueBucket ((buckets.val.get (pick buckets key)).replace key value)
    else NoKey query ((buckets.val.get (pick buckets key)).replace key value))
  split
  · exact unique_replace _ key value
      (queryShape_selected_unique key buckets.val.data (pick buckets key) (old key))
  · rename_i different
    exact noKey_replace _ query key value
      (queryShape_other_absent query buckets.val.data
        (pick buckets query) (pick buckets key) (old query) different)
end TrustIr.ByteImage.MapCacheProof.Legacy
