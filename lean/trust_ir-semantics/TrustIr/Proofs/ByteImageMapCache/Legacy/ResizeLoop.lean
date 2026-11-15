-- Copyright 2026 Andrew Yates | Apache-2.0
import TrustIr.ByteImageMapCacheCompat
import TrustIr.Proofs.ByteImageMapCache.Legacy.Buckets
namespace TrustIr.ByteImage.MapCacheProof.Legacy
open Lean
universe u v
variable {α : Type u} {β : Type v}

trustIrLegacyMapCacheDecl
theorem drop_set_consumed {γ : Type u} (rows : List γ) (index : Nat) (replacement : γ) :
    (rows.set index replacement).drop (index + 1) = rows.drop (index + 1) := by
  induction rows generalizing index with
  | nil => cases index <;> rfl
  | cons head tail ih =>
    cases index with
    | zero => rfl
    | succ index => exact ih index

trustIrLegacyMapCacheDecl
theorem drop_at_inside {γ : Type u} (rows : List γ) (index : Nat)
    (inside : index < rows.length) :
    rows.drop index = rows.get ⟨index, inside⟩ :: rows.drop (index + 1) := by
  induction rows generalizing index with
  | nil => exact False.elim (Nat.not_lt_zero _ inside)
  | cons head tail ih =>
    cases index with
    | zero => rfl
    | succ index =>
      exact ih index (Nat.lt_of_succ_lt_succ inside)

trustIrLegacyMapCacheDecl
theorem drop_past_end {γ : Type u} (rows : List γ) (index : Nat)
    (done : rows.length ≤ index) : rows.drop index = [] := by
  induction rows generalizing index with
  | nil => cases index <;> rfl
  | cons head tail ih =>
    cases index with
    | zero => exact False.elim (Nat.not_succ_le_zero _ done)
    | succ index => exact ih index (Nat.le_of_succ_le_succ done)

trustIrLegacyMapCacheDecl
/-- Exact ordered bucket query replay; no HashMap invariant supplied. -/
def overwriteRows [BEq α] : List (AssocList α β) → α → Option β → Option β
  | [], _, previous => previous
  | entries :: tail, query, previous =>
    overwriteRows tail query (entries.foldl (overwrite query) previous)

trustIrLegacyMapCacheDecl
/-- The actual source.set(nil) update does not alter the unprocessed suffix. -/
theorem overwriteBuckets_suffix [BEq α]
    (i : Nat) (source : Array (AssocList α β)) (query : α) (previous : Option β) :
    overwriteBuckets i source query previous =
      overwriteRows (source.data.drop i) query previous := by
  rw [overwriteBuckets]
  split
  · rename_i inside
    rw [overwriteBuckets_suffix]
    change overwriteRows ((source.data.set i AssocList.nil).drop (i + 1)) query
        ((source.get ⟨i, inside⟩).foldl (overwrite query) previous) = _
    rw [drop_set_consumed, drop_at_inside source.data i inside]
    rfl
  · rename_i done
    rw [drop_past_end source.data i (Nat.le_of_not_lt done)]
    rfl
termination_by source.size - i
decreasing_by simp_wf; decreasing_trivial_pre_omega

trustIrLegacyMapCacheDecl
/-- Complete actual moveEntries lookup through all remaining original buckets.
    This is an unconditional implementation theorem, not an insert-law premise. -/
theorem moveEntries_read_rows [BEq α] [LawfulBEq α] [Hashable α]
    (i : Nat) (source : Array (AssocList α β))
    (target : HashMapBucket α β) (query : α) :
    read (HashMapImp.moveEntries i source target) query =
      overwriteRows (source.data.drop i) query (read target query) := by
  rw [read_moveEntries, overwriteBuckets_suffix]

trustIrLegacyMapCacheDecl
/-- Query-specific absence in a sequence of buckets. -/
def RowsAbsent (query : α) : List (AssocList α β) → Prop
  | [] => True
  | entries :: tail => NoKey query entries ∧ RowsAbsent query tail

trustIrLegacyMapCacheDecl
theorem fold_overwrite_absent [BEq α] [LawfulBEq α]
    (entries : AssocList α β) (query : α) (previous : Option β)
    (absent : NoKey query entries) :
    entries.foldl (overwrite query) previous = previous := by
  induction entries generalizing previous with
  | nil => rfl
  | cons key value tail ih =>
    change tail.foldl (overwrite query) (overwrite query previous key value) = previous
    rw [ih _ absent.2]
    simp [overwrite, absent.1]

trustIrLegacyMapCacheDecl
theorem fold_overwrite_unique [BEq α] [LawfulBEq α]
    (entries : AssocList α β) (query : α) (previous : Option β)
    (unique : UniqueBucket entries) :
    entries.foldl (overwrite query) previous =
      match AssocList.find? query entries with
      | some value => some value
      | none => previous := by
  induction entries generalizing previous with
  | nil => rfl
  | cons key value tail ih =>
    change tail.foldl (overwrite query) (overwrite query previous key value) = _
    by_cases same : key = query
    · subst query
      rw [fold_overwrite_absent _ _ _ unique.1]
      simp [overwrite, AssocList.find?]
    · rw [ih _ unique.2]
      simp [overwrite, AssocList.find?, beq_false_of_ne same]

trustIrLegacyMapCacheDecl
theorem overwriteRows_absent [BEq α] [LawfulBEq α]
    (rows : List (AssocList α β)) (query : α) (previous : Option β)
    (absent : RowsAbsent query rows) : overwriteRows rows query previous = previous := by
  induction rows generalizing previous with
  | nil => rfl
  | cons entries tail ih =>
    change overwriteRows tail query (entries.foldl (overwrite query) previous) = previous
    rw [fold_overwrite_absent _ _ _ absent.1, ih _ absent.2]

trustIrLegacyMapCacheDecl
/-- The selected bucket alone may contain this query; selected contents unique.
    This is a structural description, not a callback/lookup-law assumption. -/
def QueryShape (query : α) : List (AssocList α β) → Nat → Prop
  | [], _ => False
  | entries :: tail, 0 => UniqueBucket entries ∧ RowsAbsent query tail
  | entries :: tail, index + 1 => NoKey query entries ∧ QueryShape query tail index

trustIrLegacyMapCacheDecl
theorem overwriteRows_shape [BEq α] [LawfulBEq α]
    (rows : List (AssocList α β)) (query : α) (previous : Option β)
    (index : Fin rows.length) (shape : QueryShape query rows index.val) :
    overwriteRows rows query previous =
      match AssocList.find? query (rows.get index) with
      | some value => some value
      | none => previous := by
  induction rows generalizing previous with
  | nil => exact False.elim shape
  | cons entries tail ih =>
    cases index with
    | mk index inside =>
      cases index with
      | zero =>
        change overwriteRows tail query (entries.foldl (overwrite query) previous) = _
        rw [overwriteRows_absent _ _ _ shape.2, fold_overwrite_unique _ _ _ shape.1]
        rfl
      | succ index =>
        change overwriteRows tail query (entries.foldl (overwrite query) previous) = _
        rw [fold_overwrite_absent _ _ _ shape.1]
        exact ih previous ⟨index, Nat.lt_of_succ_lt_succ inside⟩ shape.2

trustIrLegacyMapCacheDecl
/-- Key routing + per-bucket uniqueness in query form for arbitrary capacities.
    It is intended to be derived from empty/insert/actual-resize transitions. -/
def RawInvariant [Hashable α] (buckets : HashMapBucket α β) : Prop :=
  ∀ query, QueryShape query buckets.val.data (pick buckets query).val

trustIrLegacyMapCacheDecl
theorem get_replicate {γ : Type u} (n : Nat) (value : γ)
    (index : Fin (List.replicate n value).length) :
    (List.replicate n value).get index = value := by
  induction n with
  | zero => exact False.elim (Nat.not_lt_zero _ index.isLt)
  | succ n ih =>
    cases index with
    | mk index inside =>
      cases index with
      | zero => rfl
      | succ index => exact ih ⟨index, Nat.lt_of_succ_lt_succ inside⟩

trustIrLegacyMapCacheDecl
theorem read_empty_buckets [BEq α] [Hashable α] (n : Nat) (power : n.isPowerOfTwo)
    (query : α) : read (⟨Array.mkArray n AssocList.nil, by simpa using power⟩ : HashMapBucket α β) query = none := by
  unfold read
  rw [show (Array.mkArray n (AssocList.nil : AssocList α β)).get
      (pick (⟨Array.mkArray n AssocList.nil, by simpa using power⟩ : HashMapBucket α β) query) = AssocList.nil from
    get_replicate n AssocList.nil _]
  rfl

trustIrLegacyMapCacheDecl
/-- Actual expand preserves every query once the concrete bucket routing and
    uniqueness invariant is established; no inserted-law premise. -/
theorem expand_read [BEq α] [LawfulBEq α] [Hashable α]
    (buckets : HashMapBucket α β) (size : Nat) (query : α)
    (valid : RawInvariant buckets) :
    (HashMapImp.expand size buckets).find? query = read buckets query := by
  unfold HashMapImp.expand
  rw [actual_find, moveEntries_read_rows]
  rw [read_empty_buckets (buckets.val.size * 2)
    (Nat.mul2_isPowerOfTwo_of_isPowerOfTwo buckets.property) query]
  change overwriteRows buckets.val.data query none = read buckets query
  rw [overwriteRows_shape _ _ _ (pick buckets query) (valid query)]
  change (match read buckets query with | some value => some value | none => none) = read buckets query
  cases read buckets query <;> rfl
end TrustIr.ByteImage.MapCacheProof.Legacy
