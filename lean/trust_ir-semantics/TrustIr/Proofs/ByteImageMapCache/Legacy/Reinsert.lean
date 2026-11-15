-- Copyright 2026 Andrew Yates | Apache-2.0
import TrustIr.ByteImageMapCacheCompat
-- from the resize input's routing/global uniqueness, not an assumed insert law.
import TrustIr.Proofs.ByteImageMapCache.Legacy.BucketUpdate
namespace TrustIr.ByteImage.MapCacheProof.Legacy
open Lean
universe u v
variable {α : Type u} {β : Type v}

trustIrLegacyMapCacheDecl
theorem noKey_iff_find_none [BEq α] [LawfulBEq α]
    (query : α) (entries : AssocList α β) :
    NoKey query entries ↔ entries.find? query = none := by
  induction entries with
  | nil => exact ⟨fun _ => rfl, fun _ => True.intro⟩
  | cons key value tail ih =>
    cases comparison : key == query with
    | false =>
      have different : key ≠ query := ne_of_beq_false comparison
      change (key ≠ query ∧ NoKey query tail) ↔ _
      simp only [AssocList.find?, comparison]
      constructor
      · intro absent; exact ih.mp absent.2
      · intro absent; exact ⟨different, ih.mpr absent⟩
    | true =>
      have same : key = query := eq_of_beq comparison
      constructor
      · intro absent
        exact False.elim (absent.1 same)
      · intro impossible
        simp only [AssocList.find?, comparison] at impossible

-- Every unprocessed source key is absent from the concrete accumulated target.
trustIrLegacyMapCacheDecl
def EntriesAbsent [BEq α] [Hashable α] : AssocList α β → HashMapBucket α β → Prop
  | .nil, _ => True
  | .cons key _ tail, target => read target key = none ∧ EntriesAbsent tail target

trustIrLegacyMapCacheDecl
/-- Prepending a distinct processed key preserves absence of every pending
    key, by the already derived actual read_reinsert_other equation. -/
theorem entriesAbsent_reinsert [BEq α] [LawfulBEq α] [Hashable α]
    (entries : AssocList α β) (target : HashMapBucket α β)
    (key : α) (value : β) (different : NoKey key entries)
    (absent : EntriesAbsent entries target) :
    EntriesAbsent entries (HashMapImp.reinsertAux hash target key value) := by
  induction entries with
  | nil => trivial
  | cons head payload tail ih =>
    change read (HashMapImp.reinsertAux hash target key value) head = none ∧ _
    exact ⟨by rw [read_reinsert_other target key head value (Ne.symm different.1)];
              exact absent.1,
      ih different.2 absent.2⟩

trustIrLegacyMapCacheDecl
/-- The actual foldl reinsertAux used by expand preserves routing and
    uniqueness for all bucket capacities. No capacity or key bound is added. -/
theorem rawInvariant_fold_reinsert [BEq α] [LawfulBEq α] [Hashable α]
    (entries : AssocList α β) (target : HashMapBucket α β)
    (valid : RawInvariant target) (unique : UniqueBucket entries)
    (absent : EntriesAbsent entries target) :
    RawInvariant (entries.foldl (HashMapImp.reinsertAux hash) target) := by
  induction entries generalizing target with
  | nil => exact valid
  | cons key value tail ih =>
    change RawInvariant (tail.foldl (HashMapImp.reinsertAux hash)
      (HashMapImp.reinsertAux hash target key value))
    have noKey : NoKey key (target.val.get (pick target key)) :=
      (noKey_iff_find_none key _).mpr absent.1
    have missing : (target.val.get (pick target key)).contains key = false :=
      (noKey_iff_contains_false key _).mp noKey
    exact ih (HashMapImp.reinsertAux hash target key value)
      (rawInvariant_reinsert_fresh target key value valid missing) unique.2
      (entriesAbsent_reinsert tail target key value unique.1 absent.2)
end TrustIr.ByteImage.MapCacheProof.Legacy
