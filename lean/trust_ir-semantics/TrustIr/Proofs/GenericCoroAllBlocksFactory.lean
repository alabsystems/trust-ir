-- Copyright 2026 Andrew Yates | Apache-2.0
import TrustIr.Proofs.GenericCoroAllBlocksPlanner
import TrustIr.Proofs.GenericCoroIndexedCFG
import TrustIr.Proofs.GenericCoroRowInference
import TrustIr.Proofs.GenericCoroAllBlocksInference

namespace TrustIr.GenericCoro.AllBlocks
open GenericCoroAllBlocksPlanner GenericCoroFreshIds GenericCoroFreshCursor

/-- Capacity is about the complete canonical three-name-per-suspend
    schedule, across every original row occurrence. It is not evaluator fuel. -/
def NoSchedule (domain : Nat) (blocks : Rows) : Prop :=
  ∀ candidates : List Nat, candidates.length = 3 * suspendCount blocks →
    Distinct candidates → (∀ key ∈ candidates, key < domain) →
    (∀ key ∈ candidates, key ∉ graphReservations blocks) → False

/-- Keep the prepared data carrier until its cached query closure has been
    installed in the function. Both lexical tables use actual inference. -/
def withInferredGraph (header : EvalFunction) (blocks : Rows)
    (inferred : LocalTypeInference) : EvalFunction :=
  let prepared := IndexedCFG.indexedCFG blocks
  { header with cfg := prepared.cfg, localTypes := some inferred.table }

theorem withInferredGraph_eq (header : EvalFunction) (blocks : Rows)
    (inferred : LocalTypeInference) :
    withInferredGraph header blocks inferred =
      { header with cfg := cfgOf blocks, localTypes := some inferred.table } := by
  simp only [withInferredGraph, IndexedCFG.indexedCFG_eq_cfgOf]

/-- A graph with no suspend needs no identifier allocation or target walk.
    Expanded results contain only the two executable functions; allocator
    indexes and diagnostic history are not retained in the success value. -/
inductive Expansion (domain : Nat) (blocks : Rows) where
  | unchanged (source : EvalFunction)
  | capacity (source : EvalFunction) (certificate : NoSchedule domain blocks)
  | expanded (source target : EvalFunction)

/-- Authoritative source inference comes first. The changed branch prepares
    one fresh-name cursor, traverses every row, and runs target inference once.
    Metadata failures are ordinary errors; no synthetic table is installed. -/
def functionsWithDomain (domain : Nat) (direct : FuncId → Option FuncTyDef)
    (indirect : FuncTyTable) (header : EvalFunction) (blocks : Rows) :
    Except SemError (Expansion domain blocks) := do
  let sourceInferred ← inferLocalTypesWithEvidence direct indirect (graphParams blocks) (graphNodes blocks)
  let source := withInferredGraph header blocks sourceInferred
  if !(blocks.any (fun row => isSuspend row.2.terminator)) then
    return .unchanged source
  let planned := lowerRows domain blocks
  match outcome : planned.completion with
  | .capacity delta short covers full =>
    have certificate : NoSchedule domain blocks := by
      have actual := lowerRows_capacity_excludes_schedule domain blocks
      have completion : (lowerRows domain blocks).completion =
          .capacity delta short covers full := outcome
      simp only [completion] at actual
      exact actual
    return .capacity source certificate
  | .ready =>
    let targetInferred ← inferLocalTypesWithEvidence direct indirect
      (graphParams planned.rows) (graphNodes planned.rows)
    return .expanded source (withInferredGraph header planned.rows targetInferred)

/-- The production identifier domain is the actual wire u32 domain. -/
def functions (direct : FuncId → Option FuncTyDef) (indirect : FuncTyTable)
    (header : EvalFunction) (blocks : Rows) : Except SemError (Expansion u32Domain blocks) :=
  functionsWithDomain u32Domain direct indirect header blocks

/-- The initial inference error is preserved before either index allocation
    or any target inference, independently of graph shape and runtime state. -/
theorem functions_source_error (domain : Nat) (direct : FuncId → Option FuncTyDef)
    (indirect : FuncTyTable) (header : EvalFunction) (blocks : Rows) (error : SemError)
    (source : inferLocalTypesWithEvidence direct indirect (graphParams blocks) (graphNodes blocks) =
      .error error) : functionsWithDomain domain direct indirect header blocks = .error error := by
  simp only [functionsWithDomain, source, Bind.bind, Except.bind]

/-- This branch reuses the already-authoritative source table and CFG;
    it cannot spend a fresh identifier or refuse on identifier capacity. -/
theorem functions_without_suspends (domain : Nat) (direct : FuncId → Option FuncTyDef)
    (indirect : FuncTyTable) (header : EvalFunction) (blocks : Rows) (inferred : LocalTypeInference)
    (source : inferLocalTypesWithEvidence direct indirect (graphParams blocks) (graphNodes blocks) =
      .ok inferred)
    (none : blocks.any (fun row => isSuspend row.2.terminator) = false) :
    functionsWithDomain domain direct indirect header blocks =
      .ok (.unchanged (withInferredGraph header blocks inferred)) := by
  simp only [functionsWithDomain, source, Bind.bind, Except.bind, none,
    Bool.not_false, if_true, Pure.pure, Except.pure]

/-- The changed production branch installs the actual inferred target table.
    A ready planner cannot turn successful source inference into an error.
    All source identifiers and all generated triples have their derived types. -/
theorem functions_expanded_of_ready (direct : FuncId → Option FuncTyDef)
    (indirect : FuncTyTable) (header : EvalFunction) (blocks : Rows)
    (inferred : LocalTypeInference)
    (source : inferLocalTypesWithEvidence direct indirect (graphParams blocks) (graphNodes blocks) =
      .ok inferred)
    (changed : blocks.any (fun row => isSuspend row.2.terminator) = true)
    (ready : Ready (planAllBlocks blocks)) :
    ∃ targetInferred,
      functions direct indirect header blocks =
        .ok (.expanded (withInferredGraph header blocks inferred)
          (withInferredGraph header (planAllBlocks blocks).rows targetInferred)) ∧
      inferLocalTypesWithEvidence direct indirect (graphParams (planAllBlocks blocks).rows)
        (graphNodes (planAllBlocks blocks).rows) = .ok targetInferred ∧
      (∀ id ∈ graphValueIds blocks, inferred.table id = targetInferred.table id) ∧
      AllBlocksInference.TraceTyped targetInferred.table (planAllBlocks blocks).trace := by
  trustIrCompilerProof {
    obtain ⟨targetInferred, targetRun, preserved, typed⟩ :=
      AllBlocksInference.lowerRows_inference direct indirect blocks inferred source ready
    have completion : (lowerRows u32Domain blocks).completion = .ready := by
      cases outcome : (lowerRows u32Domain blocks).completion with
      | ready => rfl
      | capacity delta short covers full =>
        simp only [Ready, planAllBlocks, outcome] at ready
    refine ⟨targetInferred, ?_, targetRun, preserved, typed⟩
    simp only [functions, functionsWithDomain, source, Bind.bind, Except.bind,
      changed, Bool.not_true, Bool.false_eq_true, if_false, completion,
      planAllBlocks, Pure.pure, Except.pure] at targetRun ⊢
    split <;> simp_all only [Completion.noConfusion, targetRun, Bind.bind, Except.bind, Pure.pure, Except.pure]
  } {
    obtain ⟨targetInferred, targetRun, preserved, typed⟩ :=
      AllBlocksInference.lowerRows_inference direct indirect blocks inferred source ready
    have completion : (lowerRows u32Domain blocks).completion = .ready := by
      cases outcome : (lowerRows u32Domain blocks).completion with
      | ready => rfl
      | capacity delta short covers full =>
        simp only [Ready, planAllBlocks, outcome] at ready
    refine ⟨targetInferred, ?_, targetRun, preserved, typed⟩
    simp only [functions, functionsWithDomain, source, Bind.bind, Except.bind,
      changed, Bool.not_true, Bool.false_eq_true, if_false, completion,
      planAllBlocks, Pure.pure, Except.pure] at targetRun ⊢
    split <;> simp_all only [Completion.noConfusion, targetRun, Bind.bind, Except.bind, Pure.pure, Except.pure] <;> cases completion
  }

/-- Once source inference succeeds, the production factory always returns an
    executable pair, an unchanged source, or a genuine capacity certificate.
    No caller-supplied target-inference premise is required. -/
theorem functions_defined (direct : FuncId → Option FuncTyDef) (indirect : FuncTyTable)
    (header : EvalFunction) (blocks : Rows) (inferred : LocalTypeInference)
    (source : inferLocalTypesWithEvidence direct indirect (graphParams blocks) (graphNodes blocks) =
      .ok inferred) :
    ∃ result, functions direct indirect header blocks = .ok result := by
  trustIrCompilerProof {
    cases changed : blocks.any (fun row => isSuspend row.2.terminator) with
    | false => exact ⟨_, functions_without_suspends u32Domain direct indirect header blocks inferred source changed⟩
    | true =>
      cases outcome : (lowerRows u32Domain blocks).completion with
      | ready =>
        have ready : Ready (planAllBlocks blocks) := by
          simp only [Ready, planAllBlocks, outcome]
        obtain ⟨targetInferred, actual, _⟩ :=
          functions_expanded_of_ready direct indirect header blocks inferred source changed ready
        exact ⟨_, actual⟩
      | capacity delta short covers full =>
        simp only [functions, functionsWithDomain, source, Bind.bind, Except.bind,
          changed, Bool.not_true, Bool.false_eq_true, if_false, outcome, Pure.pure, Except.pure]
        split <;> simp_all only [Completion.noConfusion]
        exact ⟨_, rfl⟩
  } {
    cases changed : blocks.any (fun row => isSuspend row.2.terminator) with
    | false => exact ⟨_, functions_without_suspends u32Domain direct indirect header blocks inferred source changed⟩
    | true =>
      cases outcome : (lowerRows u32Domain blocks).completion with
      | ready =>
        have ready : Ready (planAllBlocks blocks) := by
          simp only [Ready, planAllBlocks, outcome]
        obtain ⟨targetInferred, actual, _⟩ :=
          functions_expanded_of_ready direct indirect header blocks inferred source changed ready
        exact ⟨_, actual⟩
      | capacity delta short covers full =>
        simp only [functions, functionsWithDomain, source, Bind.bind, Except.bind,
          changed, Bool.not_true, Bool.false_eq_true, if_false, outcome, Pure.pure, Except.pure]
        split <;> simp_all only [Completion.noConfusion]
        all_goals first | exact ⟨_, rfl⟩ | cases outcome
  }

end TrustIr.GenericCoro.AllBlocks

#trustIrAxiomsExact TrustIr.GenericCoro.AllBlocks.Expansion == []
#trustIrAxiomsExact TrustIr.GenericCoro.AllBlocks.Expansion.capacity == []
#trustIrAxiomsExact TrustIr.GenericCoro.AllBlocks.Expansion.capacity.inj == []
#trustIrAxiomsExact TrustIr.GenericCoro.AllBlocks.Expansion.capacity.injEq == [propext]
#trustIrAxiomsExact TrustIr.GenericCoro.AllBlocks.Expansion.capacity.sizeOf_spec == []
#trustIrAxiomsExact TrustIr.GenericCoro.AllBlocks.Expansion.casesOn == []
#trustIrAxiomsExact TrustIr.GenericCoro.AllBlocks.Expansion.expanded == []
#trustIrAxiomsExact TrustIr.GenericCoro.AllBlocks.Expansion.expanded.inj == []
#trustIrAxiomsExact TrustIr.GenericCoro.AllBlocks.Expansion.expanded.injEq == [propext]
#trustIrAxiomsExact TrustIr.GenericCoro.AllBlocks.Expansion.expanded.sizeOf_spec == []
#trustIrAxiomsExact TrustIr.GenericCoro.AllBlocks.Expansion.noConfusion == []
#trustIrAxiomsExact TrustIr.GenericCoro.AllBlocks.Expansion.noConfusionType == []
#trustIrAxiomsExact TrustIr.GenericCoro.AllBlocks.Expansion.rec == []
#trustIrAxiomsExact TrustIr.GenericCoro.AllBlocks.Expansion.recOn == []
#trustIrAxiomsExact TrustIr.GenericCoro.AllBlocks.Expansion.unchanged == []
#trustIrAxiomsExact TrustIr.GenericCoro.AllBlocks.Expansion.unchanged.inj == []
#trustIrAxiomsExact TrustIr.GenericCoro.AllBlocks.Expansion.unchanged.injEq == [propext]
#trustIrAxiomsExact TrustIr.GenericCoro.AllBlocks.Expansion.unchanged.sizeOf_spec == []
