-- Copyright 2026 Andrew Yates | Apache-2.0
import TrustIr.Proofs.GenericCoroProps

namespace TrustIr.GenericCoro
open LocalTypeInference

/-- Normalize precisely the destination rows executed by the source bodyPrefix,
    then append generated rows. Neither excess trailing rows nor omitted rows
    may shift an appended instruction onto an unrelated source destination. -/
theorem bodyInsts_normalized_append (bodyPrefix suffix : List Inst)
    (prefixDests suffixDests : List (List ValueId)) :
    bodyInstsWithResultDests (bodyPrefix ++ suffix)
      ((bodyInstsWithResultDests bodyPrefix prefixDests).map Prod.snd ++ suffixDests) =
      bodyInstsWithResultDests bodyPrefix prefixDests ++ bodyInstsWithResultDests suffix suffixDests := by
  induction bodyPrefix generalizing prefixDests with
  | nil => rfl
  | cons inst rest ih =>
    cases prefixDests with
    | nil =>
      simpa only [List.cons_append, bodyInstsWithResultDests, List.map_cons] using
        congrArg (List.cons (inst, [])) (ih [])
    | cons dest restDests =>
      simpa only [List.cons_append, bodyInstsWithResultDests, List.map_cons] using
        congrArg (List.cons (inst, dest)) (ih restDests)

theorem graphNodes_prefix_sourceEntry (before after : List (BlockId × BasicBlock)) (id : BlockId)
    (params : List (ValueId × Ty)) (bodyPrefix : List Inst)
    (bodyDests : List (List ValueId)) (termDests : List ValueId)
    (frame value : ValueId) (slot : Nat) (next : Int) :
    graphNodes (before ++ (id, {
      params := params
      body := bodyPrefix
      bodyResultDests := bodyDests
      terminator := .CoroSuspend frame slot next value
      terminatorResultDests := termDests }) :: after) =
      (graphNodes before ++ bodyInstsWithResultDests bodyPrefix bodyDests) ++
        (.CoroSuspend frame slot next value, termDests) :: graphNodes after := by
  rw [graphNodes_append, graphNodes_cons]
  simp only [List.append_assoc, List.cons_append, List.nil_append]

theorem graphNodes_prefix_expandedEntry (names : Names)
    (before after : List (BlockId × BasicBlock)) (id : BlockId)
    (params : List (ValueId × Ty)) (bodyPrefix : List Inst)
    (bodyDests : List (List ValueId)) (termDests : List ValueId)
    (frame value : ValueId) (slot : Nat) (next : Int) :
    graphNodes (before ++ (id, expandedEntry names {
      params := params
      body := bodyPrefix
      bodyResultDests := bodyDests
      terminator := .CoroSuspend frame slot next value
      terminatorResultDests := termDests }) :: after) =
      ((graphNodes before ++ bodyInstsWithResultDests bodyPrefix bodyDests) ++
        [(.Const .I64 (.int slot), [names.index]),
         (.GEP .I64 frame [names.index] false, [names.pointer]),
         (.Const .I64 (.int next), [names.state]),
         (.Store .I64 names.pointer names.state false none, []), (.Return [value], [])]) ++
        graphNodes after := by
  rw [graphNodes_append, graphNodes_cons]
  simp only [expandedEntry, bodyInsts_normalized_append, bodyInstsWithResultDests,
    List.append_assoc, List.cons_append, List.nil_append]

theorem expandedGraph_prefix_inference (direct : FuncId → Option FuncTyDef) (indirect : FuncTyTable)
    (blocks : List (BlockId × BasicBlock)) (entry : BlockId)
    (params : List (ValueId × Ty)) (bodyPrefix : List Inst) (bodyDests : List (List ValueId)) (termDests : List ValueId)
    (frame value : ValueId) (slot : Nat) (next : Int) (names : GraphNames blocks)
    (inferred : LocalTypeInference)
    (found : cfgOf blocks entry = some {
      params := params
      body := bodyPrefix
      bodyResultDests := bodyDests
      terminator := .CoroSuspend frame slot next value
      terminatorResultDests := termDests })
    (run : inferLocalTypesWithEvidence direct indirect (graphParams blocks) (graphNodes blocks) =
      .ok inferred) :
    ∃ targetInferred,
      inferLocalTypesWithEvidence direct indirect
        (graphParams (expandedGraph (Names.ofTriple names) blocks entry))
        (graphNodes (expandedGraph (Names.ofTriple names) blocks entry)) = .ok targetInferred ∧
      targetInferred.table (Names.ofTriple names).index = some .I64 ∧
      targetInferred.table (Names.ofTriple names).pointer = some .Ptr ∧
      targetInferred.table (Names.ofTriple names).state = some .I64 ∧
      (∀ id ∈ graphValueIds blocks, inferred.table id = targetInferred.table id) := by
  obtain ⟨before, selectedId, after, decomposition, selected, noMatch⟩ :=
    cfgOf_decompose blocks entry _ found
  have sourceNodes : graphNodes blocks =
      (graphNodes before ++ bodyInstsWithResultDests bodyPrefix bodyDests) ++ (.CoroSuspend frame slot next value, termDests) :: graphNodes after := by
    rw [decomposition]
    exact graphNodes_prefix_sourceEntry before after selectedId params bodyPrefix bodyDests termDests frame value slot next
  have termMember : (.CoroSuspend frame slot next value, termDests) ∈ graphNodes blocks := by
    rw [sourceNodes]
    exact trustIrListMemAppendRight _ ((trustIrListMemConsSelf _ _))
  have census := infer_success_census direct indirect (graphParams blocks) (graphNodes blocks)
    (.CoroSuspend frame slot next value, termDests) [] termMember rfl inferred run
  have termEmpty : termDests = [] := by
    cases termDests with
    | nil => rfl
    | cons head rest => simp only [List.length_nil, List.length_cons] at census <;> omega
  subst termDests
  have free := GraphNames.unused blocks names
  have firstAvoid := graph_input_avoids direct indirect blocks names.first free.1
  have secondAvoid := graph_input_avoids direct indirect blocks names.second free.2.1
  have thirdAvoid := graph_input_avoids direct indirect blocks names.third free.2.2
  rw [sourceNodes] at firstAvoid secondAvoid thirdAvoid
  have sourceRun := run
  rw [sourceNodes] at sourceRun
  have baseRun : inferLocalTypesWithEvidence direct indirect (graphParams blocks)
      ((graphNodes before ++ bodyInstsWithResultDests bodyPrefix bodyDests) ++ graphNodes after) = .ok inferred :=
    (infer_insert_empty direct indirect (graphParams blocks) ((graphNodes before ++ bodyInstsWithResultDests bodyPrefix bodyDests)) (graphNodes after)
      (.CoroSuspend frame slot next value) rfl).symm.trans sourceRun
  obtain ⟨targetInferred, targetRows, indexType, pointerType, stateType, preserved⟩ :=
    infer_insert_three direct indirect (graphParams blocks) ((graphNodes before ++ bodyInstsWithResultDests bodyPrefix bodyDests)) (graphNodes after)
      names.first names.second names.third .I64 .Ptr .I64
      (.Const .I64 (.int slot)) (.GEP .I64 frame [⟨names.first⟩] false) (.Const .I64 (.int next))
      rfl rfl rfl names.firstSecond names.firstThird names.secondThird
      firstAvoid.removeNode secondAvoid.removeNode thirdAvoid.removeNode inferred baseRun
  let temps := Names.ofTriple names
  let beforeReturn := (graphNodes before ++ bodyInstsWithResultDests bodyPrefix bodyDests) ++
    [(.Const .I64 (.int slot), [temps.index]),
      (.GEP .I64 frame [temps.index] false, [temps.pointer]),
      (.Const .I64 (.int next), [temps.state])]
  have nonvoidRun : inferLocalTypesWithEvidence direct indirect (graphParams blocks)
      (beforeReturn ++ graphNodes after) = .ok targetInferred := by
    simpa only [beforeReturn, temps, Names.ofTriple, List.append_assoc,
      List.cons_append, List.nil_append] using targetRows
  have removeStore := infer_insert_empty direct indirect (graphParams blocks) beforeReturn
    ((.Return [value], []) :: graphNodes after) (.Store .I64 temps.pointer temps.state false none) rfl
  have removeReturn := infer_insert_empty direct indirect (graphParams blocks) beforeReturn
    (graphNodes after) (.Return [value]) rfl
  refine ⟨targetInferred, ?_, indexType, pointerType, stateType, ?_⟩
  · have targetGraph : expandedGraph temps blocks entry = before ++
        (selectedId, expandedEntry temps {
          params := params
          body := bodyPrefix
          bodyResultDests := bodyDests
          terminator := .CoroSuspend frame slot next value
          terminatorResultDests := [] }) :: after := by
      unfold expandedGraph
      rw [decomposition]
      exact expandFirstEntry_at temps entry selectedId _ before after selected noMatch
    have targetParams : graphParams (expandedGraph temps blocks entry) = graphParams blocks :=
      graphParams_expandFirstEntry temps entry blocks
    change inferLocalTypesWithEvidence direct indirect
      (graphParams (expandedGraph temps blocks entry)) (graphNodes (expandedGraph temps blocks entry)) = _
    rw [targetParams, targetGraph, graphNodes_prefix_expandedEntry]
    simpa only [beforeReturn, List.append_assoc, List.cons_append, List.nil_append] using
      (removeStore.trans removeReturn).trans nonvoidRun
  · intro id member
    have original_ne (fresh : Nat) (unused : ValueId.mk fresh ∉ graphValueIds blocks) : id.index ≠ fresh := by
      intro same
      have idEq : id = ⟨fresh⟩ := by cases id; cases same; rfl
      apply unused
      rw [← idEq]
      exact member
    exact preserved id (original_ne names.first free.1) (original_ne names.second free.2.1)
      (original_ne names.third free.2.2)


end TrustIr.GenericCoro
