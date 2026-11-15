-- Copyright 2026 Andrew Yates | Apache-2.0
import TrustIr.Proofs.GenericCoroPrefixInference

namespace TrustIr.GenericCoro.RowInference
open LocalTypeInference

/-- Replacing this exact row occurrence retains all parameter rows, including
    earlier rows whose block identifier happens to be the same. -/
theorem graphParams_expandedRow (names : Names) (before after : List (BlockId × BasicBlock))
    (id : BlockId) (block : BasicBlock) :
    graphParams (before ++ (id, expandedEntry names block) :: after) =
      graphParams (before ++ (id, block) :: after) := by
  simp only [graphParams, trustIrCoroListLemma List.append_bind List.flatMap_append, trustIrCoroListLemma List.cons_bind List.flatMap_cons, trustIrCoroListLemma List.nil_bind List.flatMap_nil,
    expandedEntry_params]

/-- Actual metadata inference for an explicit row occurrence, rather than a
    first CFG lookup. Every source row participates in the authoritative fold.
    Only the selected terminator shape and actual source inference success are
    premises; names reserve the complete current graph, including unused raw
    destination rows. No prefix, frame, runtime or block-id uniqueness guard is
    introduced. This is a local inference step, not an all-block pass theorem. -/
theorem expandedRow_inference_except_generated (direct : FuncId → Option FuncTyDef) (indirect : FuncTyTable)
    (before after : List (BlockId × BasicBlock)) (selectedId : BlockId) (block : BasicBlock)
    (frame value : ValueId) (slot : Nat) (next : Int)
    (suspend : block.terminator = .CoroSuspend frame slot next value)
    (names : GraphNames (before ++ (selectedId, block) :: after))
    (inferred : LocalTypeInference)
    (run : inferLocalTypesWithEvidence direct indirect
      (graphParams (before ++ (selectedId, block) :: after))
      (graphNodes (before ++ (selectedId, block) :: after)) = .ok inferred) :
    ∃ targetInferred,
      inferLocalTypesWithEvidence direct indirect
        (graphParams (before ++ (selectedId, expandedEntry (Names.ofTriple names) block) :: after))
        (graphNodes (before ++ (selectedId, expandedEntry (Names.ofTriple names) block) :: after)) =
          .ok targetInferred ∧
      targetInferred.table (Names.ofTriple names).index = some .I64 ∧
      targetInferred.table (Names.ofTriple names).pointer = some .Ptr ∧
      targetInferred.table (Names.ofTriple names).state = some .I64 ∧
      (∀ id, id ≠ (Names.ofTriple names).index →
        id ≠ (Names.ofTriple names).pointer → id ≠ (Names.ofTriple names).state →
        inferred.table id = targetInferred.table id) := by
  cases block with
  | mk params bodyPrefix bodyDests term termDests =>
    cases suspend
    let sourceBlock : BasicBlock := {
      params := params, body := bodyPrefix, bodyResultDests := bodyDests,
      terminator := .CoroSuspend frame slot next value, terminatorResultDests := termDests }
    let blocks := before ++ (selectedId, sourceBlock) :: after
    have sourceNodes : graphNodes blocks =
        (graphNodes before ++ bodyInstsWithResultDests bodyPrefix bodyDests) ++ (.CoroSuspend frame slot next value, termDests) :: graphNodes after := by
      exact graphNodes_prefix_sourceEntry before after selectedId params bodyPrefix bodyDests termDests frame value slot next
    have termMember : (.CoroSuspend frame slot next value, termDests) ∈ graphNodes blocks := by
      rw [sourceNodes]
      exact trustIrListMemAppendRight _ ((trustIrListMemConsSelf _ _))
    have census := infer_success_census direct indirect (graphParams blocks) (graphNodes blocks)
      (.CoroSuspend frame slot next value, termDests) [] termMember rfl inferred run
    have termEmpty : termDests = [] := by
      trustIrCompilerProof {
        cases termDests with
        | nil => rfl
        | cons head rest => simp only [List.length_nil, List.length_cons] at census
      } {
        cases termDests with
        | nil => rfl
        | cons head rest =>
          simp only [List.length_nil, List.length_cons] at census
          omega
      }
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
    · have targetParams :
          graphParams (before ++ (selectedId, expandedEntry temps sourceBlock) :: after) = graphParams blocks :=
        graphParams_expandedRow temps before after selectedId sourceBlock
      change inferLocalTypesWithEvidence direct indirect
        (graphParams (before ++ (selectedId, expandedEntry temps sourceBlock) :: after))
        (graphNodes (before ++ (selectedId, expandedEntry temps sourceBlock) :: after)) = _
      rw [targetParams]
      change inferLocalTypesWithEvidence direct indirect (graphParams blocks)
        (graphNodes (before ++ (selectedId, expandedEntry temps {
          params := params, body := bodyPrefix, bodyResultDests := bodyDests,
          terminator := .CoroSuspend frame slot next value, terminatorResultDests := [] }) :: after)) = _
      rw [graphNodes_prefix_expandedEntry]
      simpa only [beforeReturn, List.append_assoc, List.cons_append, List.nil_append] using
        (removeStore.trans removeReturn).trans nonvoidRun
    · intro id indexDifferent pointerDifferent stateDifferent
      have index_ne (key : Nat) (different : id ≠ ⟨key⟩) : id.index ≠ key := by
        intro same
        apply different
        cases id
        cases same
        rfl
      exact preserved id (index_ne names.first indexDifferent)
        (index_ne names.second pointerDifferent) (index_ne names.third stateDifferent)

/-- The original graph-support interface is retained verbatim as a corollary. -/
theorem expandedRow_prefix_inference (direct : FuncId → Option FuncTyDef) (indirect : FuncTyTable)
    (before after : List (BlockId × BasicBlock)) (selectedId : BlockId) (block : BasicBlock)
    (frame value : ValueId) (slot : Nat) (next : Int)
    (suspend : block.terminator = .CoroSuspend frame slot next value)
    (names : GraphNames (before ++ (selectedId, block) :: after))
    (inferred : LocalTypeInference)
    (run : inferLocalTypesWithEvidence direct indirect
      (graphParams (before ++ (selectedId, block) :: after))
      (graphNodes (before ++ (selectedId, block) :: after)) = .ok inferred) :
    ∃ targetInferred,
      inferLocalTypesWithEvidence direct indirect
        (graphParams (before ++ (selectedId, expandedEntry (Names.ofTriple names) block) :: after))
        (graphNodes (before ++ (selectedId, expandedEntry (Names.ofTriple names) block) :: after)) =
          .ok targetInferred ∧
      targetInferred.table (Names.ofTriple names).index = some .I64 ∧
      targetInferred.table (Names.ofTriple names).pointer = some .Ptr ∧
      targetInferred.table (Names.ofTriple names).state = some .I64 ∧
      (∀ id ∈ graphValueIds (before ++ (selectedId, block) :: after),
        inferred.table id = targetInferred.table id) := by
  obtain ⟨targetInferred, targetRun, indexType, pointerType, stateType, preserved⟩ :=
    expandedRow_inference_except_generated direct indirect before after selectedId block
      frame value slot next suspend names inferred run
  refine ⟨targetInferred, targetRun, indexType, pointerType, stateType, ?_⟩
  intro id member
  have different := GraphNames.different_original (before ++ (selectedId, block) :: after) names id member
  exact preserved id different.1 different.2.1 different.2.2

private theorem graph_append_mem (before after : List (BlockId × BasicBlock)) (id : ValueId) :
    id ∈ graphValueIds (before ++ after) ↔ id ∈ graphValueIds before ∨ id ∈ graphValueIds after := by
  simp only [graphValueIds, graphParams, graphNodes_append, trustIrCoroListLemma List.append_bind List.flatMap_append, List.map_append,
    mem_append_iff']
  simp only [or_assoc, or_left_comm, or_comm]

private theorem join_append {α : Type} (left right : List (List α)) :
    trustIrCoroFlatten (left ++ right) = trustIrCoroFlatten left ++ trustIrCoroFlatten right := by
  induction left with
  | nil => rfl
  | cons head rest ih => simp only [List.cons_append, trustIrCoroListLemma List.join_cons List.flatten_cons, ih, List.append_assoc]

private theorem raw_dest_mem (rows : List (Inst × List ValueId)) (id : ValueId)
    (member : id ∈ trustIrCoroFlatten (rows.map Prod.snd)) :
    id ∈ trustIrListBind rows (fun row => row.2 ++ operandIds row.1) := by
  induction rows with
  | nil => cases member
  | cons row rest ih =>
    simp only [List.map_cons, trustIrCoroListLemma List.join_cons List.flatten_cons] at member
    rcases mem_append_iff'.mp member with first | later
    · rw [trustIrCoroListLemma List.cons_bind List.flatMap_cons]
      exact trustIrListMemAppendLeft _ (trustIrListMemAppendLeft _ first)
    · rw [trustIrCoroListLemma List.cons_bind List.flatMap_cons]
      exact trustIrListMemAppendRight _ (ih later)

private theorem singleton_support (names : Names) (label : BlockId)
    (params : List (ValueId × Ty)) (body : List Inst) (dests : List (List ValueId))
    (termDests : List ValueId) (frame value : ValueId) (slot : Nat) (next : Int) (id : ValueId)
    (member : id ∈ graphValueIds [(label, expandedEntry names {
      params := params, body := body, bodyResultDests := dests,
      terminator := .CoroSuspend frame slot next value, terminatorResultDests := termDests })]) :
    id ∈ graphValueIds [(label, {
      params := params, body := body, bodyResultDests := dests,
      terminator := .CoroSuspend frame slot next value, terminatorResultDests := termDests })] ++
      [names.index, names.pointer, names.state] := by
  have const_ids (ty : Ty) (constant : Constant) : operandIds (.Const ty constant) = [] := rfl
  have gep_ids (ty : Ty) (pointer : ValueId) (indices : List ValueId) (inbounds : Bool) :
      operandIds (.GEP ty pointer indices inbounds) = pointer :: indices := rfl
  have store_ids (ty : Ty) (pointer value : ValueId) (vol : Bool) (align : Option Nat) :
      operandIds (.Store ty pointer value vol align) = [pointer, value] := rfl
  have return_ids (values : List ValueId) : operandIds (.Return values) = values := rfl
  have suspend_ids : operandIds (.CoroSuspend frame slot next value) = [frame, value] := rfl
  simp only [graphValueIds, graphParams, graphNodes, trustIrCoroListLemma List.cons_bind List.flatMap_cons, trustIrCoroListLemma List.nil_bind List.flatMap_nil,
    List.map_append, List.map_cons, List.map_nil, List.append_nil,
    expandedEntry, bodyInsts_normalized_append, bodyInstsWithResultDests,
    trustIrCoroListLemma List.append_bind List.flatMap_append, const_ids, gep_ids, store_ids, return_ids, suspend_ids, join_append, trustIrCoroListLemma List.join_cons List.flatten_cons, trustIrCoroListLemma List.join_nil List.flatten_nil,
    mem_append_iff', List.mem_cons, List.not_mem_nil, or_false] at member ⊢
  have h := member
  repeat' first
    | solve | simp_all
    | solve
      | have node := raw_dest_mem (bodyInstsWithResultDests body dests) id h
        simp_all
    | rcases h with h | h


private theorem entry_valueIds_supported (names : Names) (label : BlockId)
    (block : BasicBlock) (id : ValueId)
    (member : id ∈ graphValueIds [(label, expandedEntry names block)]) :
    id ∈ graphValueIds [(label, block)] ++ [names.index, names.pointer, names.state] := by
  cases block with
  | mk params body dests term termDests =>
    cases term
    case CoroSuspend frame slot next value =>
      exact singleton_support names label params body dests termDests frame value slot next id member
    all_goals exact trustIrListMemAppendLeft _ member

/-- Every syntactic target identifier is already in the complete source graph
    or is one of the three generated identifiers. This includes raw destination
    rows and every operand, requires no inference or freshness premise, and
    applies to an explicit occurrence even with earlier duplicate block ids. -/
theorem expandedRow_valueIds_supported (names : Names) (before after : List (BlockId × BasicBlock))
    (label : BlockId) (block : BasicBlock) (id : ValueId)
    (member : id ∈ graphValueIds (before ++ (label, expandedEntry names block) :: after)) :
    id ∈ graphValueIds (before ++ (label, block) :: after) ++
      [names.index, names.pointer, names.state] := by
  rcases (graph_append_mem before _ id).mp member with earlier | later
  · apply trustIrListMemAppendLeft _
    exact (graph_append_mem before _ id).mpr (.inl earlier)
  · have later' : id ∈ graphValueIds ([(label, expandedEntry names block)] ++ after) := later
    rcases (graph_append_mem _ after id).mp later' with selected | following
    · rcases mem_append_iff'.mp (entry_valueIds_supported names label block id selected) with old | new
      · apply trustIrListMemAppendLeft _
        apply (graph_append_mem before _ id).mpr
        right
        exact (graph_append_mem [(label, block)] after id).mpr (.inl old)
      · exact trustIrListMemAppendRight _ new
    · apply trustIrListMemAppendLeft _
      apply (graph_append_mem before _ id).mpr
      right
      exact (graph_append_mem [(label, block)] after id).mpr (.inr following)

namespace Controls

/-- A raw metadata graph: the selected second occurrence is shadowed in CFG
    lookup. This witnesses the fold lemma, not Rust module validation. -/
def earlier : BasicBlock := { params := [], body := [], terminator := .Return [] }

def selected : BasicBlock := {
  params := [(⟨0⟩, .Ptr), (⟨1⟩, .I32)]
  body := [.Copy .I32 ⟨1⟩]
  bodyResultDests := [[⟨5⟩], [⟨2⟩], [⟨3⟩]]
  terminator := .CoroSuspend ⟨0⟩ 0 17 ⟨5⟩ }

def beforeRows : List (BlockId × BasicBlock) := [(⟨40⟩, earlier)]

def sourceGraph : List (BlockId × BasicBlock) := beforeRows ++ [(⟨40⟩, selected)]

def names : GraphNames sourceGraph := {
  first := 4, second := 6, third := 7
  firstBound := by decide
  secondBound := by decide
  thirdBound := by decide
  firstUnused := by decide
  secondUnused := by decide
  thirdUnused := by decide
  firstSecond := by decide
  firstThird := by decide
  secondThird := by decide }

def targetGraph : List (BlockId × BasicBlock) :=
  beforeRows ++ [(⟨40⟩, expandedEntry (Names.ofTriple names) selected)]

theorem first_lookup_still_selects_earlier_duplicate :
    cfgOf sourceGraph ⟨40⟩ = some earlier := rfl

theorem unused_raw_rows_reserve_the_actual_first_holes :
    GenericCoroFreshIds.observable (GenericCoroFreshIds.u32Names (graphReservations sourceGraph)) =
      some [4, 6, 7] := rfl

theorem actual_source_inference_succeeds :
    ∃ inferred, inferLocalTypesWithEvidence (fun _ => none) (fun _ => none)
      (graphParams sourceGraph) (graphNodes sourceGraph) = .ok inferred := ⟨_, rfl⟩

theorem unused_raw_rows_are_not_declarations :
    (inferLocalTypesWithEvidence (fun _ => none) (fun _ => none)
      (graphParams sourceGraph) (graphNodes sourceGraph)).map
        (fun inferred => [inferred.table ⟨2⟩, inferred.table ⟨3⟩, inferred.table ⟨5⟩]) =
      .ok [none, none, some .I32] := rfl

theorem actual_expanded_metadata_has_three_new_types :
    (inferLocalTypesWithEvidence (fun _ => none) (fun _ => none)
      (graphParams targetGraph) (graphNodes targetGraph)).map
        (fun inferred => [inferred.table ⟨4⟩, inferred.table ⟨6⟩, inferred.table ⟨7⟩]) =
      .ok [some .I64, some .Ptr, some .I64] := rfl

/-- An inhabited application of the row theorem to that actual inference run.
    No first-lookup equality is supplied: it selects the other occurrence. -/
theorem actual_shadowed_row_retains_full_inference_contract :
    ∃ sourceInferred targetInferred,
      inferLocalTypesWithEvidence (fun _ => none) (fun _ => none)
        (graphParams sourceGraph) (graphNodes sourceGraph) = .ok sourceInferred ∧
      inferLocalTypesWithEvidence (fun _ => none) (fun _ => none)
        (graphParams targetGraph) (graphNodes targetGraph) = .ok targetInferred ∧
      targetInferred.table ⟨4⟩ = some .I64 ∧
      targetInferred.table ⟨6⟩ = some .Ptr ∧
      targetInferred.table ⟨7⟩ = some .I64 ∧
      (∀ id ∈ graphValueIds sourceGraph, sourceInferred.table id = targetInferred.table id) := by
  obtain ⟨sourceInferred, sourceRun⟩ := actual_source_inference_succeeds
  obtain ⟨targetInferred, targetRun, indexType, pointerType, stateType, preserved⟩ :=
    expandedRow_prefix_inference (fun _ => none) (fun _ => none) beforeRows [] ⟨40⟩ selected
      ⟨0⟩ ⟨5⟩ 0 17 rfl names sourceInferred sourceRun
  exact ⟨sourceInferred, targetInferred, sourceRun, targetRun,
    indexType, pointerType, stateType, preserved⟩

end Controls

namespace FollowUpControls

def laterBlock : BasicBlock := {
  params := [], body := [], terminator := .CoroSuspend ⟨0⟩ 0 19 ⟨5⟩ }

def currentGraph : List (BlockId × BasicBlock) :=
  Controls.targetGraph ++ [(⟨41⟩, laterBlock)]

def laterNames : GraphNames currentGraph := {
  first := 8, second := 9, third := 10
  firstBound := by decide
  secondBound := by decide
  thirdBound := by decide
  firstUnused := by decide
  secondUnused := by decide
  thirdUnused := by decide
  firstSecond := by decide
  firstThird := by decide
  secondThird := by decide }

def laterTarget : List (BlockId × BasicBlock) :=
  Controls.targetGraph ++ [(⟨41⟩, expandedEntry (Names.ofTriple laterNames) laterBlock)]

/-- Normalizing the earlier row really dropped the unused raw2/3 rows, so
    the old graph-membership corollary cannot directly cover these identifiers. -/
theorem earlier_raw_tails_are_no_longer_in_current_graph :
    (⟨2⟩ : ValueId) ∉ graphValueIds currentGraph ∧
      (⟨3⟩ : ValueId) ∉ graphValueIds currentGraph := by decide

/-- The stronger primitive preserves those absent original identifiers at the
    next actual rewrite, while the complete metadata inference succeeds. -/
theorem later_rewrite_keeps_dropped_raw_ids_none :
    ∃ sourceInferred targetInferred,
      inferLocalTypesWithEvidence (fun _ => none) (fun _ => none)
        (graphParams currentGraph) (graphNodes currentGraph) = .ok sourceInferred ∧
      inferLocalTypesWithEvidence (fun _ => none) (fun _ => none)
        (graphParams laterTarget) (graphNodes laterTarget) = .ok targetInferred ∧
      sourceInferred.table ⟨2⟩ = none ∧ sourceInferred.table ⟨3⟩ = none ∧
      targetInferred.table ⟨2⟩ = none ∧ targetInferred.table ⟨3⟩ = none := by
  have sourceExists : ∃ inferred, inferLocalTypesWithEvidence (fun _ => none) (fun _ => none)
      (graphParams currentGraph) (graphNodes currentGraph) = .ok inferred := ⟨_, rfl⟩
  obtain ⟨sourceInferred, sourceRun⟩ := sourceExists
  obtain ⟨targetInferred, targetRun, _, _, _, preserved⟩ :=
    expandedRow_inference_except_generated (fun _ => none) (fun _ => none)
      Controls.targetGraph [] ⟨41⟩ laterBlock ⟨0⟩ ⟨5⟩ 0 19 rfl laterNames sourceInferred sourceRun
  have twoQuery :
      (inferLocalTypesWithEvidence (fun _ => none) (fun _ => none)
        (graphParams currentGraph) (graphNodes currentGraph)).map (fun inferred => inferred.table ⟨2⟩) =
      .ok none := rfl
  have threeQuery :
      (inferLocalTypesWithEvidence (fun _ => none) (fun _ => none)
        (graphParams currentGraph) (graphNodes currentGraph)).map (fun inferred => inferred.table ⟨3⟩) =
      .ok none := rfl
  rw [sourceRun] at twoQuery threeQuery
  have twoNone : sourceInferred.table ⟨2⟩ = none := Except.ok.inj twoQuery
  have threeNone : sourceInferred.table ⟨3⟩ = none := Except.ok.inj threeQuery
  exact ⟨sourceInferred, targetInferred, sourceRun, targetRun, twoNone, threeNone,
    (preserved ⟨2⟩ (by decide) (by decide) (by decide)).symm.trans twoNone,
    (preserved ⟨3⟩ (by decide) (by decide) (by decide)).symm.trans threeNone⟩

theorem later_target_identifiers_have_supported_origin (id : ValueId)
    (member : id ∈ graphValueIds laterTarget) :
    id ∈ graphValueIds currentGraph ++ [⟨8⟩, ⟨9⟩, ⟨10⟩] :=
  expandedRow_valueIds_supported (Names.ofTriple laterNames) Controls.targetGraph [] ⟨41⟩ laterBlock id member

end FollowUpControls

end TrustIr.GenericCoro.RowInference
