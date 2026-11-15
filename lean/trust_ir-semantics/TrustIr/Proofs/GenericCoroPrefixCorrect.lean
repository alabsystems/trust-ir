-- Copyright 2026 Andrew Yates | Apache-2.0
import TrustIr.Proofs.GenericCoroPrefixGraphEffect
import TrustIr.Proofs.GenericCoroPrefixCallBoundary

namespace TrustIr.GenericCoro
open LocalTypeInference Prefix

/-- The actual selected graph can contain arbitrary body instructions before
    its suspend. Its direct, indirect and sequential callbacks may recurse
    through the changed global function table. -/
theorem expandedGraph_prefix_runCallEquivalent (header : EvalFunction)
    (blocks : List (BlockId × BasicBlock)) (names : GraphNames blocks)
    (sourceTypes targetTypes : LocalTypeTable)
    (params : List (ValueId × Ty)) (bodyPrefix : List Inst)
    (bodyDests : List (List ValueId)) (termDests : List ValueId)
    (frame value : ValueId) (slot : Nat) (next : Int)
    (found : cfgOf blocks header.entryBlock = some {
      params := params, body := bodyPrefix, bodyResultDests := bodyDests,
      terminator := .CoroSuspend frame slot next value, terminatorResultDests := termDests })
    (indexType : targetTypes (Names.ofTriple names).index = some .I64)
    (pointerType : targetTypes (Names.ofTriple names).pointer = some .Ptr)
    (stateType : targetTypes (Names.ofTriple names).state = some .I64)
    (preserved : ∀ id ∈ graphValueIds blocks, sourceTypes id = targetTypes id) :
    RunCallEquivalent {header with cfg := cfgOf blocks, localTypes := some sourceTypes}
      {header with
        cfg := cfgOf (expandedGraph (Names.ofTriple names) blocks header.entryBlock),
        localTypes := some targetTypes} := by
  let source : EvalFunction := {header with cfg := cfgOf blocks, localTypes := some sourceTypes}
  let target : EvalFunction := {header with
    cfg := cfgOf (expandedGraph (Names.ofTriple names) blocks header.entryBlock),
    localTypes := some targetTypes}
  apply runCallEquivalent_of_selectedEffects source target rfl
  intro ctx selected fuel
  apply (evaluator_simulation ctx selected source target rfl rfl ?_ fuel).2
  intro sourceRecurse targetRecurse effects
  exact expandedGraph_prefix_layer_effect sourceRecurse targetRecurse ctx
    (withFunction ctx selected source).functions (withFunction ctx selected target).functions
    (headerAgreement_withFunction ctx selected source target rfl rfl) effects
    header blocks names sourceTypes targetTypes params bodyPrefix bodyDests termDests frame value slot next
    found indexType pointerType stateType preserved

theorem expandedGraph_prefix_callEquivalent (header : EvalFunction)
    (blocks : List (BlockId × BasicBlock)) (names : GraphNames blocks)
    (sourceTypes targetTypes : LocalTypeTable)
    (params : List (ValueId × Ty)) (bodyPrefix : List Inst)
    (bodyDests : List (List ValueId)) (termDests : List ValueId)
    (frame value : ValueId) (slot : Nat) (next : Int)
    (found : cfgOf blocks header.entryBlock = some {
      params := params, body := bodyPrefix, bodyResultDests := bodyDests,
      terminator := .CoroSuspend frame slot next value, terminatorResultDests := termDests })
    (indexType : targetTypes (Names.ofTriple names).index = some .I64)
    (pointerType : targetTypes (Names.ofTriple names).pointer = some .Ptr)
    (stateType : targetTypes (Names.ofTriple names).state = some .I64)
    (preserved : ∀ id ∈ graphValueIds blocks, sourceTypes id = targetTypes id) :
    CallEquivalent {header with cfg := cfgOf blocks, localTypes := some sourceTypes}
      {header with
        cfg := cfgOf (expandedGraph (Names.ofTriple names) blocks header.entryBlock),
        localTypes := some targetTypes} :=
  callEquivalent_of_runCallEquivalent _ _
    (expandedGraph_prefix_runCallEquivalent header blocks names sourceTypes targetTypes params bodyPrefix
      bodyDests termDests frame value slot next found indexType pointerType stateType preserved)

/-- Total source-aware expansion of a selected entry with any finite body.
    The complete source graph derives both declaration tables and all three
    unused u32 identifiers. Metadata errors and certified identifier capacity
    remain explicit outcomes. The expanded branch exposes the actual shared
    Call helper and complete caller-state equality for every resource budget,
    argument list, caller context and panic strategy. Other blocks are kept;
    this theorem does not describe a pass lowering every suspend block. -/
theorem functionsOfExpansion_prefix_correct (direct : FuncId → Option FuncTyDef) (indirect : FuncTyTable)
    (header : EvalFunction) (blocks : List (BlockId × BasicBlock))
    (params : List (ValueId × Ty)) (bodyPrefix : List Inst)
    (bodyDests : List (List ValueId)) (termDests : List ValueId)
    (frame value : ValueId) (slot : Nat) (next : Int)
    (found : cfgOf blocks header.entryBlock = some {
      params := params, body := bodyPrefix, bodyResultDests := bodyDests,
      terminator := .CoroSuspend frame slot next value, terminatorResultDests := termDests }) :
    ExpansionCorrect direct indirect header blocks
      (functionsOfExpansion direct indirect header blocks) := by
  cases sourceRun : inferLocalTypesWithEvidence direct indirect (graphParams blocks) (graphNodes blocks) with
  | error error =>
    simp only [functionsOfExpansion, functionOfGraphWithEvidence, sourceRun, Bind.bind,
      Pure.pure, Except.bind, Except.pure, ExpansionCorrect,
      functionOfGraph, inferLocalTypes, inferLocalTypesWithWork]
  | ok inferred =>
    have sourceBuilt := functionOfGraph_of_inference direct indirect header blocks inferred sourceRun
    cases allocation : GenericCoroFreshIds.u32Names (graphReservations blocks) with
    | capacity certificate =>
      simp only [functionsOfExpansion, functionOfGraphWithEvidence, sourceRun, allocation,
        Bind.bind, Pure.pure, Except.bind, Except.pure, ExpansionCorrect]
      refine ⟨sourceBuilt, ?_⟩
      intro available
      obtain ⟨names⟩ := available
      exact GenericCoroFreshIds.capacity_excludes_triple certificate names
    | ready names =>
      obtain ⟨targetInferred, targetRun, indexType, pointerType, stateType, preserved⟩ :=
        expandedGraph_prefix_inference direct indirect blocks header.entryBlock params bodyPrefix bodyDests termDests
          frame value slot next names inferred found sourceRun
      have targetBuilt := functionOfGraph_of_inference direct indirect header
        (expandedGraph (Names.ofTriple names) blocks header.entryBlock) targetInferred targetRun
      simp only [functionsOfExpansion, functionOfGraphWithEvidence, sourceRun, allocation,
        targetBuilt, Bind.bind, Pure.pure, Except.bind, Except.pure, ExpansionCorrect]
      exact ⟨sourceBuilt, True.intro,
        expandedGraph_prefix_runCallEquivalent header blocks names inferred.table targetInferred.table
          params bodyPrefix bodyDests termDests frame value slot next found indexType pointerType stateType preserved,
        expandedGraph_prefix_callEquivalent header blocks names inferred.table targetInferred.table
          params bodyPrefix bodyDests termDests frame value slot next found indexType pointerType stateType preserved⟩

end TrustIr.GenericCoro
