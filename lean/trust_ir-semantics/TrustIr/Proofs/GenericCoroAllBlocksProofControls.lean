-- Copyright 2026 Andrew Yates | Apache-2.0
import TrustIr.Proofs.GenericCoroAllBlocksCorrect
import TrustIr.Proofs.GenericCoroAllBlocksControls

namespace TrustIr.GenericCoro.AllBlocks.ProofControls
open Controls

private theorem equivalent_of_expanded_tag (blocks : GenericCoroAllBlocksPlanner.Rows)
    (result : Except SemError (Expansion GenericCoroFreshIds.u32Domain blocks))
    (correct : FactoryCorrect (fun _ => none) (fun _ => none) header blocks result)
    (expanded : outputTag result = 3) :
    ∃ source target, result = .ok (.expanded source target) ∧
      RunCallEquivalent source target ∧ CallEquivalent source target := by
  cases result with
  | error error => cases expanded
  | ok result =>
    cases result with
    | unchanged source => cases expanded
    | capacity source certificate => cases expanded
    | expanded source target =>
      obtain ⟨_, _, _, _, _, _, _, _, _, _, calls, entryCalls⟩ := correct
      exact ⟨source, target, rfl, calls, entryCalls⟩

private theorem correct_at_result (blocks : GenericCoroAllBlocksPlanner.Rows)
    (result : Except SemError (Expansion GenericCoroFreshIds.u32Domain blocks))
    (actual : functions (fun _ => none) (fun _ => none) header blocks = result) :
    FactoryCorrect (fun _ => none) (fun _ => none) header blocks result :=
  actual ▸ functions_correct (fun _ => none) (fun _ => none) header blocks

/-- Inhabited applications of the complete call theorem. The entry branches
    to the first suspend; the other row is also lowered and inferred. Duplicate
    labels here are raw ordered-model controls, with no validator-admission
    claim. No result, caller state, callback or successful prefix is assumed. -/
theorem actual_graph_call_equivalence (duplicate : Bool) :
    ∃ source target,
      functions (fun _ => none) (fun _ => none) header (graph duplicate) = .ok (.expanded source target) ∧
      RunCallEquivalent source target ∧ CallEquivalent source target := by
  have tag : outputTag (functions (fun _ => none) (fun _ => none) header (graph duplicate)) = 3 := by
    cases duplicate <;> rfl
  generalize actual : functions (fun _ => none) (fun _ => none) header (graph duplicate) = result at tag ⊢
  exact equivalent_of_expanded_tag (graph duplicate) result
    (correct_at_result (graph duplicate) result actual) tag

theorem nonentry_br_graph_has_complete_call_equivalence :
    ∃ source target,
      functions (fun _ => none) (fun _ => none) header (graph false) = .ok (.expanded source target) ∧
      RunCallEquivalent source target ∧ CallEquivalent source target :=
  actual_graph_call_equivalence false

theorem duplicate_occurrences_have_complete_call_equivalence :
    ∃ source target,
      functions (fun _ => none) (fun _ => none) header (graph true) = .ok (.expanded source target) ∧
      RunCallEquivalent source target ∧ CallEquivalent source target :=
  actual_graph_call_equivalence true

end TrustIr.GenericCoro.AllBlocks.ProofControls
