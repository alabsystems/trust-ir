-- Copyright 2026 Andrew Yates | Apache-2.0
import TrustIr.Proofs.GenericCoroAllBlocksFactory
import TrustIr.Proofs.GenericCoroAllBlocksSimulation

namespace TrustIr.GenericCoro.AllBlocks
open Prefix GenericCoroAllBlocksPlanner

/-- Source-aware outcomes of the actual all-row factory. Metadata errors are
    exactly source errors. Capacity is carried by the outcome's genuine
    NoSchedule certificate for three distinct fresh u32 names per original
    suspend occurrence. Expanded functions use both actual inference tables,
    have no remaining suspend terminators, and expose complete call equality.
    This is a finite function-graph transform in the Lean evaluator model;
    it does not assert instruction-cost equality or native compiler admission. -/
def FactoryCorrect (direct : FuncId → Option FuncTyDef) (indirect : FuncTyTable)
    (header : EvalFunction) (blocks : Rows) : Except SemError (Expansion GenericCoroFreshIds.u32Domain blocks) → Prop
  | .error error =>
    inferLocalTypesWithEvidence direct indirect (graphParams blocks) (graphNodes blocks) = .error error
  | .ok (.unchanged source) =>
    ∃ inferred,
      inferLocalTypesWithEvidence direct indirect (graphParams blocks) (graphNodes blocks) = .ok inferred ∧
      source = withInferredGraph header blocks inferred ∧
      blocks.any (fun row => isSuspend row.2.terminator) = false
  | .ok (.capacity source _) =>
    ∃ inferred,
      inferLocalTypesWithEvidence direct indirect (graphParams blocks) (graphNodes blocks) = .ok inferred ∧
      source = withInferredGraph header blocks inferred
  | .ok (.expanded source target) =>
    ∃ sourceInferred targetInferred,
      inferLocalTypesWithEvidence direct indirect (graphParams blocks) (graphNodes blocks) = .ok sourceInferred ∧
      inferLocalTypesWithEvidence direct indirect (graphParams (planAllBlocks blocks).rows)
        (graphNodes (planAllBlocks blocks).rows) = .ok targetInferred ∧
      source = withInferredGraph header blocks sourceInferred ∧
      target = withInferredGraph header (planAllBlocks blocks).rows targetInferred ∧
      Ready (planAllBlocks blocks) ∧ suspendCount (planAllBlocks blocks).rows = 0 ∧
      (∀ id ∈ graphValueIds blocks, sourceInferred.table id = targetInferred.table id) ∧
      AllBlocksInference.TraceTyped targetInferred.table (planAllBlocks blocks).trace ∧
      RunCallEquivalent source target ∧ CallEquivalent source target

/-- Total correctness of the production u32 factory for every finite ordered
    row list and every header. There is no entry-block shape, block uniqueness,
    successful-prefix, no-call, caller-freshness or valid-pointer premise.
    Recursive and mutually recursive calls, all PCs, both strategies and zero
    budgets are covered by the actual paired evaluator/resource induction. -/
theorem functions_correct (direct : FuncId → Option FuncTyDef) (indirect : FuncTyTable)
    (header : EvalFunction) (blocks : Rows) :
    FactoryCorrect direct indirect header blocks (functions direct indirect header blocks) := by
  trustIrCompilerProof {
    cases sourceRun : inferLocalTypesWithEvidence direct indirect (graphParams blocks) (graphNodes blocks) with
    | error error =>
      have actual := functions_source_error GenericCoroFreshIds.u32Domain direct indirect header blocks error sourceRun
      change FactoryCorrect direct indirect header blocks (functionsWithDomain _ _ _ _ _)
      rw [actual]
      exact sourceRun
    | ok inferred =>
      cases changed : blocks.any (fun row => isSuspend row.2.terminator) with
      | false =>
        have actual := functions_without_suspends GenericCoroFreshIds.u32Domain direct indirect header blocks
          inferred sourceRun changed
        change FactoryCorrect direct indirect header blocks (functionsWithDomain _ _ _ _ _)
        rw [actual]
        exact ⟨inferred, sourceRun, rfl, changed⟩
      | true =>
        cases outcome : (lowerRows GenericCoroFreshIds.u32Domain blocks).completion with
        | ready =>
          have ready : Ready (planAllBlocks blocks) := by simp only [Ready, planAllBlocks, outcome]
          obtain ⟨targetInferred, actual, targetRun, preserved, typed⟩ :=
            functions_expanded_of_ready direct indirect header blocks inferred sourceRun changed ready
          rw [actual]
          have calls : RunCallEquivalent (withInferredGraph header blocks inferred)
              (withInferredGraph header (planAllBlocks blocks).rows targetInferred) := by
            rw [withInferredGraph_eq, withInferredGraph_eq]
            exact AllBlocksSimulation.lowerRows_runCallEquivalent header blocks ready inferred.table
              targetInferred.table preserved typed
          exact ⟨inferred, targetInferred, sourceRun, targetRun, rfl, rfl, ready,
            (lowerRows_ready GenericCoroFreshIds.u32Domain blocks ready).suspendCount_target_zero,
            preserved, typed, calls, callEquivalent_of_runCallEquivalent _ _ calls⟩
        | capacity delta short covers full =>
          simp only [functions, functionsWithDomain, sourceRun, Bind.bind, Except.bind,
            changed, Bool.not_true, Bool.false_eq_true, if_false, outcome, Pure.pure, Except.pure]
          split <;> simp_all only [Completion.noConfusion]
          exact ⟨inferred, sourceRun, rfl⟩
  } {
    cases sourceRun : inferLocalTypesWithEvidence direct indirect (graphParams blocks) (graphNodes blocks) with
    | error error =>
      have actual := functions_source_error GenericCoroFreshIds.u32Domain direct indirect header blocks error sourceRun
      change FactoryCorrect direct indirect header blocks (functionsWithDomain _ _ _ _ _)
      rw [actual]
      exact sourceRun
    | ok inferred =>
      cases changed : blocks.any (fun row => isSuspend row.2.terminator) with
      | false =>
        have actual := functions_without_suspends GenericCoroFreshIds.u32Domain direct indirect header blocks
          inferred sourceRun changed
        change FactoryCorrect direct indirect header blocks (functionsWithDomain _ _ _ _ _)
        rw [actual]
        exact ⟨inferred, sourceRun, rfl, changed⟩
      | true =>
        cases outcome : (lowerRows GenericCoroFreshIds.u32Domain blocks).completion with
        | ready =>
          have ready : Ready (planAllBlocks blocks) := by simp only [Ready, planAllBlocks, outcome]
          obtain ⟨targetInferred, actual, targetRun, preserved, typed⟩ :=
            functions_expanded_of_ready direct indirect header blocks inferred sourceRun changed ready
          rw [actual]
          have calls : RunCallEquivalent (withInferredGraph header blocks inferred)
              (withInferredGraph header (planAllBlocks blocks).rows targetInferred) := by
            rw [withInferredGraph_eq, withInferredGraph_eq]
            exact AllBlocksSimulation.lowerRows_runCallEquivalent header blocks ready inferred.table
              targetInferred.table preserved typed
          exact ⟨inferred, targetInferred, sourceRun, targetRun, rfl, rfl, ready,
            (lowerRows_ready GenericCoroFreshIds.u32Domain blocks ready).suspendCount_target_zero,
            preserved, typed, calls, callEquivalent_of_runCallEquivalent _ _ calls⟩
        | capacity delta short covers full =>
          simp only [functions, functionsWithDomain, sourceRun, Bind.bind, Except.bind,
            changed, Bool.not_true, Bool.false_eq_true, if_false, outcome, Pure.pure, Except.pure]
          split <;> simp_all only [Completion.noConfusion]
          all_goals first | exact ⟨inferred, sourceRun, rfl⟩ | cases outcome
  }

end TrustIr.GenericCoro.AllBlocks
