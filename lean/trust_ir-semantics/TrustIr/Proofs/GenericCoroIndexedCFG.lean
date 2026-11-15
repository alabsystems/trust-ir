-- Copyright 2026 Andrew Yates | Apache-2.0
import TrustIr.PreparedCFG
import TrustIr.Proofs.GenericCoroProps

namespace TrustIr.GenericCoro.IndexedCFG

theorem insertFirst_find (index : NatIndex BasicBlock) (key query : Nat) (block : BasicBlock) :
    (insertFirst index key block).find? query =
      (index.find? query).orElse (fun _ => if query = key then some block else none) := by
  by_cases same : query = key
  · subst query
    cases found : index.find? key <;> simp only [insertFirst, found, NatIndex.find?_insert_same,
      Option.orElse, if_pos rfl, if_true]
  · cases found : index.find? key <;>
      simp only [insertFirst, found, NatIndex.find?_insert, if_neg same]
    all_goals cases index.find? query <;> rfl

/-- Existing seed entries have priority; otherwise the first source row at
    the queried identifier wins. This is the actual builder lookup law. -/
theorem prepareFrom_lookup (blocks : List (BlockId × BasicBlock))
    (index : NatIndex BasicBlock) (query : BlockId) :
    (prepareFrom blocks index).find? query.index =
      (index.find? query.index).orElse (fun _ => cfgOf blocks query) := by
  trustIrCompilerProof {
    induction blocks generalizing index with
    | nil =>
      simp only [prepareFrom, cfgOf, List.find?, Option.map]
      cases index.find? query.index <;> rfl
    | cons row rest ih =>
      rcases row with ⟨id, block⟩
      rw [prepareFrom, ih, insertFirst_find]
      by_cases same : query.index = id.index
      · have ids : id = query := by
          cases id
          cases query
          simp only [] at same
          exact congrArg BlockId.mk same.symm
        subst id
        simp only [cfgOf, List.find?, beq_self_eq_true, if_true, Option.map, if_pos rfl]
        cases index.find? query.index <;> rfl
      · have different : (id == query) = false := by
          apply (beq_eq_false_iff_ne id query).mpr
          intro equal
          subst id
          exact same rfl
        simp only [cfgOf, List.find?, different, Bool.false_eq_true, if_false, Option.map,
          if_neg same]
        cases index.find? query.index <;> rfl
  } {
    induction blocks generalizing index with
    | nil =>
      simp only [prepareFrom, cfgOf, List.find?, Option.map]
      cases index.find? query.index <;> rfl
    | cons row rest ih =>
      rcases row with ⟨id, block⟩
      rw [prepareFrom, ih, insertFirst_find]
      by_cases same : query.index = id.index
      · have ids : id = query := by
          cases id
          cases query
          simp only [] at same
          exact congrArg BlockId.mk same.symm
        subst id
        simp only [cfgOf, List.find?, beq_self_eq_true, if_true, Option.map, if_pos rfl]
        cases index.find? query.index <;> rfl
      · have different : (id == query) = false := by
          apply beq_eq_false_iff_ne.mpr
          intro equal
          subst id
          exact same rfl
        simp only [cfgOf, List.find?, different, Bool.false_eq_true, if_false, Option.map,
          if_neg same]
        cases index.find? query.index <;> rfl
  }

theorem prepare_lookup (blocks : List (BlockId × BasicBlock)) (query : BlockId) :
    (prepare blocks).find? query.index = cfgOf blocks query := by
  simp only [prepare, prepareFrom_lookup, NatIndex.find?_empty, Option.orElse]

/-- A successful prepared lookup is the actual first matching original row,
    with no matching key hidden in its preceding rows. No sorted/unique-id
    assumption or index-to-list conversion is involved. -/
theorem prepare_first_row (blocks : List (BlockId × BasicBlock)) (query : BlockId)
    (block : BasicBlock) (found : (prepare blocks).find? query.index = some block) :
    ∃ before id after,
      blocks = before ++ (id, block) :: after ∧ (id == query) = true ∧
      (∀ row ∈ before, (row.1 == query) = false) := by
  apply cfgOf_decompose blocks query block
  exact (prepare_lookup blocks query).symm.trans found

theorem indexedCFG_index (blocks : List (BlockId × BasicBlock)) :
    (indexedCFG blocks).index = prepare blocks := rfl

theorem indexedCFG_lookup (blocks : List (BlockId × BasicBlock)) (query : BlockId) :
    (indexedCFG blocks).cfg query = cfgOf blocks query :=
  prepare_lookup blocks query

theorem indexedCFG_eq_cfgOf (blocks : List (BlockId × BasicBlock)) :
    (indexedCFG blocks).cfg = cfgOf blocks :=
  funext (indexedCFG_lookup blocks)

namespace Controls

def first : BasicBlock := { params := [(⟨0⟩, .I32)], body := [], terminator := .Return [⟨0⟩] }
def shadowed : BasicBlock := { params := [], body := [], terminator := .Unreachable }
def high : BasicBlock := { params := [], body := [.Const .I64 (.int 9)], terminator := .Return [] }
def rows : List (BlockId × BasicBlock) :=
  [(⟨9⟩, first), (⟨2^128⟩, high), (⟨9⟩, shadowed), (⟨0⟩, shadowed)]

theorem duplicate_first_row_wins : (indexedCFG rows).cfg ⟨9⟩ = some first := rfl

theorem arbitrary_high_key_is_retained : (indexedCFG rows).cfg ⟨2^128⟩ = some high := rfl

theorem neighboring_high_key_is_missing : (indexedCFG rows).cfg ⟨2^128 + 1⟩ = none := rfl

theorem zero_key_is_retained : (indexedCFG rows).cfg ⟨0⟩ = some shadowed := rfl

theorem empty_graph_is_missing : (indexedCFG []).cfg ⟨2^128⟩ = none := rfl

end Controls
end TrustIr.GenericCoro.IndexedCFG
