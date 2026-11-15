-- Copyright 2026 Andrew Yates | Apache-2.0
import TrustIr.Semantics.NatIndexStorage

namespace TrustIr

/-- Compressed executable storage with the exact original key-bound and
    binary-view depth certificates. The logical tree is a computed view, not
    a second stored copy. Normal inference never constructs that view. -/
structure NatIndex (α : Type) where
  storage : NatIndexStorage α
  keyBound : Nat
  outsideBound : ∀ key, keyBound ≤ key → storage.find key = none
  depthValue : Nat
  depthCorrect : NatIndexStorage.DepthCertificate storage depthValue

namespace NatIndex
variable {α : Type}

def tree (index : NatIndex α) : NatIndexTree α := index.storage.toTree

def empty : NatIndex α :=
  ⟨.empty, 0, fun _ _ => rfl, 0, .empty⟩

/-- Preserve any original logical tree and any valid (possibly loose) bound.
    Normal inference starts from `empty`; this adapter establishes that the
    representation change does not narrow the public tree domain. -/
def ofTree (source : NatIndexTree α) (keyBound : Nat)
    (outside : ∀ key, keyBound ≤ key → source.find key = none) : NatIndex α :=
  { storage := NatIndexStorage.ofTree source
    keyBound := keyBound
    outsideBound := by
      intro key bound
      rw [← NatIndexStorage.toTree_find, NatIndexStorage.toTree_ofTree]
      exact outside key bound
    depthValue := source.depth
    depthCorrect := by
      have certificate := NatIndexStorage.depth_certificate (NatIndexStorage.ofTree source)
      rw [NatIndexStorage.toTree_ofTree] at certificate
      exact certificate }

theorem tree_ofTree (source : NatIndexTree α) (keyBound : Nat)
    (outside : ∀ key, keyBound ≤ key → source.find key = none) :
    (ofTree source keyBound outside).tree = source :=
  NatIndexStorage.toTree_ofTree source

def find? (index : NatIndex α) (key : Nat) : Option α := index.storage.find key

def contains (index : NatIndex α) (key : Nat) : Bool := (index.find? key).isSome

def insert (index : NatIndex α) (key : Nat) (entry : α) : NatIndex α :=
  { storage := index.storage.insert key entry
    keyBound := max index.keyBound (key + 1)
    outsideBound := by
      intro query bound
      rw [NatIndexStorage.find_insert]
      have neq : query ≠ key := by
        have higher := Nat.le_trans (Nat.le_max_right index.keyBound (key + 1)) bound
        omega
      rw [if_neg neq]
      exact index.outsideBound query (Nat.le_trans (Nat.le_max_left _ _) bound)
    depthValue := max index.depthValue (NatIndexTree.keyDepthFast key)
    depthCorrect := by
      have certificate := NatIndexStorage.depth_certificate (index.storage.insert key entry)
      have exactDepth : (index.storage.insert key entry).toTree.depth =
          max index.depthValue (NatIndexTree.keyDepthFast key) := by
        rw [NatIndexStorage.toTree_insert, NatIndexTree.depth_insert_eq,
          index.depthCorrect.eq_view, NatIndexTree.keyDepthFast_eq]
      rw [exactDepth] at certificate
      exact certificate }

def depth (index : NatIndex α) : Nat := index.depthValue

theorem depth_eq_tree (index : NatIndex α) : index.depth = index.tree.depth := index.depthCorrect.eq_view.symm

theorem tree_find (index : NatIndex α) (key : Nat) : index.tree.find key = index.find? key :=
  NatIndexStorage.toTree_find index.storage key

theorem tree_outsideBound (index : NatIndex α) (key : Nat) (bound : index.keyBound ≤ key) :
    index.tree.find key = none := by
  rw [tree_find]
  exact index.outsideBound key bound

theorem find?_empty (key : Nat) : (empty : NatIndex α).find? key = none := rfl

theorem find?_insert (index : NatIndex α) (key query : Nat) (entry : α) :
    (index.insert key entry).find? query =
      if query = key then some entry else index.find? query :=
  NatIndexStorage.find_insert _ _ _ _

theorem find?_insert_same (index : NatIndex α) (key : Nat) (entry : α) :
    (index.insert key entry).find? key = some entry := by
  simp [find?_insert]

theorem find?_insert_ne (index : NatIndex α) (key query : Nat) (entry : α)
    (different : query ≠ key) :
    (index.insert key entry).find? query = index.find? query := by
  simp only [find?_insert, if_neg different]

theorem find?_insert_commute (index : NatIndex α) (first second query : Nat)
    (left right : α) (different : first ≠ second) :
    ((index.insert first left).insert second right).find? query =
      ((index.insert second right).insert first left).find? query := by
  simp only [find?_insert]
  by_cases atFirst : query = first <;> by_cases atSecond : query = second <;>
    simp_all

end NatIndex
end TrustIr
