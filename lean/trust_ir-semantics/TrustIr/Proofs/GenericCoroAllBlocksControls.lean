-- Copyright 2026 Andrew Yates | Apache-2.0
import TrustIr.Proofs.GenericCoroAllBlocksFactory

namespace TrustIr.GenericCoro.AllBlocks.Controls
open GenericCoroAllBlocksPlanner GenericCoroFreshIds

def header : EvalFunction := {
  body := {paramTys := [.Ptr, .I32], returnTys := [.I32]}
  cfg := fun _ => none
  entryBlock := ⟨0⟩ }

def entry : BasicBlock := {
  params := [(⟨0⟩, .Ptr), (⟨1⟩, .I32)]
  body := []
  terminator := .Br ⟨1⟩ [] }

def first : BasicBlock := {
  params := []
  body := [.Copy .I32 ⟨1⟩]
  bodyResultDests := [[⟨5⟩], [⟨2⟩], [⟨3⟩]]
  terminator := .CoroSuspend ⟨0⟩ 0 17 ⟨5⟩ }

def second : BasicBlock := {
  params := [], body := [], terminator := .CoroSuspend ⟨0⟩ 1 19 ⟨5⟩ }

/-- The entry is a branch; both non-entry row occurrences require lowering.
    The first normalization drops two unused raw rows, but their ids must
    remain unavailable to the second allocation and absent from both tables. -/
def graph (duplicate : Bool := false) : Rows :=
  [(⟨0⟩, entry), (⟨1⟩, first), (⟨if duplicate then 1 else 2⟩, second)]

theorem actual_plan_uses_two_distinct_triples :
    traceObservation (planAllBlocks (graph false)).trace =
      [(1, [4, 6, 7]), (2, [8, 9, 10])] := rfl

def outputTag {domain : Nat} {blocks : Rows} : Except SemError (Expansion domain blocks) → Nat
  | .error _ => 0
  | .ok (.unchanged _) => 1
  | .ok (.capacity _ _) => 2
  | .ok (.expanded _ _) => 3

theorem actual_factory_expands_nonentry_graph :
    outputTag (functions (fun _ => none) (fun _ => none) header (graph false)) = 3 := rfl

theorem actual_factory_installs_both_expanded_blocks :
    match functions (fun _ => none) (fun _ => none) header (graph false) with
    | .ok (.expanded source target) =>
      source.cfg ⟨0⟩ = some entry ∧ target.cfg ⟨0⟩ = some entry ∧
      target.cfg ⟨1⟩ = some (expandedEntry ⟨⟨4⟩, ⟨6⟩, ⟨7⟩⟩ first) ∧
      target.cfg ⟨2⟩ = some (expandedEntry ⟨⟨8⟩, ⟨9⟩, ⟨10⟩⟩ second)
    | _ => False := ⟨rfl, rfl, rfl, rfl⟩

theorem actual_factory_keeps_dropped_raw_ids_undeclared :
    match functions (fun _ => none) (fun _ => none) header (graph false) with
    | .ok (.expanded source target) =>
      source.localTypes.bind (fun table => table ⟨2⟩) = none ∧
      source.localTypes.bind (fun table => table ⟨3⟩) = none ∧
      target.localTypes.bind (fun table => table ⟨2⟩) = none ∧
      target.localTypes.bind (fun table => table ⟨3⟩) = none
    | _ => False := ⟨rfl, rfl, rfl, rfl⟩

theorem actual_factory_infers_all_generated_types :
    match functions (fun _ => none) (fun _ => none) header (graph false) with
    | .ok (.expanded _ target) =>
      ([4, 6, 7, 8, 9, 10].map (fun key =>
        target.localTypes.bind (fun table => table ⟨key⟩))) =
          [some .I64, some .Ptr, some .I64, some .I64, some .Ptr, some .I64]
    | _ => False := rfl

theorem actual_factory_duplicate_labels_keep_first_match :
    match functions (fun _ => none) (fun _ => none) header (graph true) with
    | .ok (.expanded _ target) =>
      target.cfg ⟨1⟩ = some (expandedEntry ⟨⟨4⟩, ⟨6⟩, ⟨7⟩⟩ first) ∧
      target.localTypes.bind (fun table => table ⟨10⟩) = some .I64
    | _ => False := ⟨rfl, rfl⟩

theorem actual_partial_capacity_is_reported :
    outputTag (functionsWithDomain 10 (fun _ => none) (fun _ => none) header (graph false)) = 2 := rfl

theorem empty_graph_needs_no_identifier_capacity :
    outputTag (functionsWithDomain 0 (fun _ => none) (fun _ => none) header []) = 1 := rfl

def cyclicGraph : Rows := [(⟨0⟩, {
  params := [(⟨0⟩, .Ptr), (⟨1⟩, .I32)]
  body := [.Borrow ⟨5⟩]
  bodyResultDests := [[⟨5⟩]]
  terminator := .CoroSuspend ⟨0⟩ 0 17 ⟨1⟩ })]

theorem actual_source_error_precedes_capacity :
    functionsWithDomain 0 (fun _ => none) (fun _ => none) header cyclicGraph =
      .error (.typeError "SSA types: cyclic borrow declarations") := rfl

/-- An inhabited application of the generic factory theorem, rather than
    only an independently reduced list of target metadata observations. -/
theorem actual_graph_instantiates_factory_inference :
    ∃ sourceInferred targetInferred,
      inferLocalTypesWithEvidence (fun _ => none) (fun _ => none)
        (graphParams (graph false)) (graphNodes (graph false)) = .ok sourceInferred ∧
      functions (fun _ => none) (fun _ => none) header (graph false) =
        .ok (.expanded (withInferredGraph header (graph false) sourceInferred)
          (withInferredGraph header (planAllBlocks (graph false)).rows targetInferred)) ∧
      (∀ id ∈ graphValueIds (graph false), sourceInferred.table id = targetInferred.table id) ∧
      AllBlocksInference.TraceTyped targetInferred.table (planAllBlocks (graph false)).trace := by
  have actual : ∃ inferred, inferLocalTypesWithEvidence (fun _ => none) (fun _ => none)
      (graphParams (graph false)) (graphNodes (graph false)) = .ok inferred := ⟨_, rfl⟩
  obtain ⟨sourceInferred, sourceRun⟩ := actual
  obtain ⟨targetInferred, factoryRun, _, preserved, typed⟩ :=
    functions_expanded_of_ready (fun _ => none) (fun _ => none) header (graph false)
      sourceInferred sourceRun rfl True.intro
  exact ⟨sourceInferred, targetInferred, sourceRun, factoryRun, preserved, typed⟩

end TrustIr.GenericCoro.AllBlocks.Controls
