-- Copyright 2026 Andrew Yates | Apache-2.0
import TrustIr.Proofs.GenericCoroAllBlocksPlanner
import TrustIr.Proofs.GenericCoroRowInference

namespace TrustIr.GenericCoro.AllBlocksInference
open GenericCoroAllBlocksPlanner GenericCoroFreshIds GenericCoroFreshCursor

/-- All syntactic identifiers in the intermediate graph are covered by the
    original reservation census or the cursor's accumulated history. -/
def Supported {used : List Nat} (cursor : Cursor u32Domain used) (blocks : Rows) : Prop :=
  ∀ id ∈ graphValueIds blocks, id.index ∈ cursor.reserved ++ used

private theorem of_index_member (ids : List ValueId) (key : Nat)
    (member : key ∈ ids.map ValueId.index) : ValueId.mk key ∈ ids := by
  induction ids with
  | nil => cases member
  | cons id ids ih =>
    rcases List.mem_cons.mp member with same | later
    · cases id
      cases same
      exact (trustIrListMemConsSelf _ _)
    · exact List.mem_cons_of_mem _ (ih later)

/-- Rebase the already-selected triple to the current graph. This is proof
    transport only; it does not run another allocator or rebuild an index. -/
def graphNames {used : List Nat} (cursor : Cursor u32Domain used) (blocks : Rows)
    (supported : Supported cursor blocks) (names : Triple u32Domain (cursor.reserved ++ used)) :
    GraphNames blocks :=
  { names with
    firstUnused := fun member => names.firstUnused
      (supported ⟨names.first⟩ (of_index_member _ _ member))
    secondUnused := fun member => names.secondUnused
      (supported ⟨names.second⟩ (of_index_member _ _ member))
    thirdUnused := fun member => names.thirdUnused
      (supported ⟨names.third⟩ (of_index_member _ _ member)) }

private theorem history_member {used : List Nat} (before middle : Cursor u32Domain used)
    (names : Triple u32Domain (before.reserved ++ used))
    (history : middle.reserved = [names.third, names.second, names.first] ++ before.reserved)
    (key : Nat) (member : key ∈ before.reserved ++ used) : key ∈ middle.reserved ++ used := by
  rw [history, List.append_assoc]
  exact trustIrListMemAppendRight _ member

private theorem generated_member {used : List Nat} (before middle : Cursor u32Domain used)
    (names : Triple u32Domain (before.reserved ++ used))
    (history : middle.reserved = [names.third, names.second, names.first] ++ before.reserved)
    (id : ValueId) (member : id ∈ [(Names.ofTriple names).index,
      (Names.ofTriple names).pointer, (Names.ofTriple names).state]) :
    id.index ∈ middle.reserved ++ used := by
  rw [history]
  apply trustIrListMemAppendLeft _
  apply trustIrListMemAppendLeft _
  simp only [Names.ofTriple, List.mem_cons, List.not_mem_nil, or_false] at member ⊢
  rcases member with same | same | same <;> cases same <;> simp only [or_true, true_or, eq_self]

private theorem protected_ne {used : List Nat} (cursor : Cursor u32Domain used)
    (fresh : Nat) (unused : fresh ∉ cursor.reserved ++ used) (id : ValueId)
    (member : id.index ∈ cursor.reserved ++ used) : id ≠ ⟨fresh⟩ := by
  intro same
  cases same
  exact unused member

private theorem suspend_shape (block : BasicBlock) (suspend : isSuspend block.terminator = true) :
    ∃ frame slot next value, block.terminator = .CoroSuspend frame slot next value := by
  cases shape : block.terminator <;> simp only [shape, isSuspend, Bool.false_eq_true] at suspend
  exact ⟨_, _, _, _, rfl⟩

/-- The final actual table records every generated triple, including triples
    generated for shadowed duplicate block occurrences. -/
def TraceTyped (table : LocalTypeTable) (trace : Trace) : Prop :=
  ∀ row ∈ trace, table row.2.index = some .I64 ∧
    table row.2.pointer = some .Ptr ∧ table row.2.state = some .I64

-- Reconstruct the original canonical nil eliminator only where the compiler
-- no longer generates it. The actual nil branch below calls this exact name.
run_cmd do
  if Lean.versionString == "4.8.0" then pure ()
  else if Lean.versionString == "4.30.0-rc2" then
    let originalName := Lean.mkIdent
      (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "Plans") "inference") "match_1")
    Lean.Elab.Command.elabCommand (← `(command|
      def $originalName:ident (x : TrustIr.BlockId × TrustIr.GenericCoro.Names)
          (motive : x ∈ ([] : TrustIr.GenericCoroAllBlocksPlanner.Trace) → Prop)
          (member : x ∈ ([] : TrustIr.GenericCoroAllBlocksPlanner.Trace)) : motive member := by
        cases member))
  else throwError "unsupported compiler for original inference matcher"

/-- Inference follows the actual occurrence plan. Intermediate inference
    witnesses are erased: the executable factory still infers its target once.
    The protected domain includes earlier generated identifiers as well as all
    original raw identifiers, even when normalization removed their last use. -/
theorem Plans.inference {used : List Nat} {before after : Cursor u32Domain used}
    {source target : Rows} {trace : Trace} (plan : Plans before after source target trace)
    (direct : FuncId → Option FuncTyDef) (indirect : FuncTyTable)
    (doneRows : Rows) (inferred : LocalTypeInference)
    (run : inferLocalTypesWithEvidence direct indirect (graphParams (doneRows ++ source))
      (graphNodes (doneRows ++ source)) = .ok inferred)
    (supported : Supported before (doneRows ++ source)) :
    ∃ finalInferred,
      inferLocalTypesWithEvidence direct indirect (graphParams (doneRows ++ target))
        (graphNodes (doneRows ++ target)) = .ok finalInferred ∧
      (∀ id, id.index ∈ before.reserved ++ used → inferred.table id = finalInferred.table id) ∧
      TraceTyped finalInferred.table trace := by
  induction plan generalizing doneRows inferred with
  | nil state =>
    trustIrCompilerProof {
      exact ⟨inferred, run, (fun _ _ => rfl), fun _ member => nomatch member⟩
    } {
      exact ⟨inferred, run, (fun _ _ => rfl), fun row member =>
        Plans.inference.match_1 row
          (fun _ => inferred.table row.2.index = some .I64 ∧
            inferred.table row.2.pointer = some .Ptr ∧
            inferred.table row.2.state = some .I64) member⟩
    }
  | keep before after id block notSuspend source target trace rest ih =>
    obtain ⟨finalInferred, finalRun, preserved, typed⟩ := ih (doneRows ++ [(id, block)]) inferred
      (by simpa only [List.append_assoc, List.singleton_append] using run)
      (by simpa only [List.append_assoc, List.singleton_append] using supported)
    exact ⟨finalInferred,
      by simpa only [List.append_assoc, List.singleton_append] using finalRun, preserved, typed⟩
  | expand before middle after id block suspend names history source target trace rest ih =>
    obtain ⟨frame, slot, next, value, shape⟩ := suspend_shape block suspend
    let currentNames := graphNames before (doneRows ++ (id, block) :: source) supported names
    obtain ⟨stepInferred, stepRun, indexType, pointerType, stateType, stepPreserved⟩ :=
      RowInference.expandedRow_inference_except_generated direct indirect doneRows source id block
        frame value slot next shape currentNames inferred run
    have namesEq : Names.ofTriple currentNames = Names.ofTriple names := rfl
    rw [namesEq] at stepRun stepPreserved indexType pointerType stateType
    have stepSupport : Supported middle (doneRows ++ (id, expandedEntry (Names.ofTriple names) block) :: source) := by
      intro key member
      have included := RowInference.expandedRow_valueIds_supported (Names.ofTriple names)
        doneRows source id block key member
      rcases mem_append_iff'.mp included with old | generated
      · exact history_member before middle names history key.index (supported key old)
      · exact generated_member before middle names history key generated
    obtain ⟨finalInferred, finalRun, preserved, typed⟩ := ih
      (doneRows ++ [(id, expandedEntry (Names.ofTriple names) block)]) stepInferred
      (by simpa only [List.append_assoc, List.singleton_append] using stepRun)
      (by simpa only [List.append_assoc, List.singleton_append] using stepSupport)
    refine ⟨finalInferred,
      by simpa only [List.append_assoc, List.singleton_append] using finalRun, ?_, ?_⟩
    · intro key member
      exact (stepPreserved key (protected_ne before _ names.firstUnused key member)
        (protected_ne before _ names.secondUnused key member)
        (protected_ne before _ names.thirdUnused key member)).trans
          (preserved key (history_member before middle names history key.index member))
    · intro row member
      rcases List.mem_cons.mp member with same | later
      · cases same
        have retained (key : ValueId) (member : key ∈ [(Names.ofTriple names).index,
            (Names.ofTriple names).pointer, (Names.ofTriple names).state]) :=
          preserved key (generated_member before middle names history key member)
        exact ⟨(retained _ (by simp only [List.mem_cons, true_or, eq_self])).symm.trans indexType,
          (retained _ (by simp only [List.mem_cons, true_or, or_true, eq_self])).symm.trans pointerType,
          (retained _ (by simp only [List.mem_cons, true_or, or_true, eq_self])).symm.trans stateType⟩
      · exact typed row later

/-- A ready production-u32 plan cannot introduce a target inference failure
    after actual source inference succeeds. Every original syntactic identifier
    retains its table association and every generated triple has its real type. -/
theorem lowerRows_inference (direct : FuncId → Option FuncTyDef) (indirect : FuncTyTable)
    (blocks : Rows) (inferred : LocalTypeInference)
    (run : inferLocalTypesWithEvidence direct indirect (graphParams blocks) (graphNodes blocks) =
      .ok inferred) (ready : Ready (planAllBlocks blocks)) :
    ∃ finalInferred,
      inferLocalTypesWithEvidence direct indirect (graphParams (planAllBlocks blocks).rows)
        (graphNodes (planAllBlocks blocks).rows) = .ok finalInferred ∧
      (∀ id ∈ graphValueIds blocks, inferred.table id = finalInferred.table id) ∧
      TraceTyped finalInferred.table (planAllBlocks blocks).trace := by
  have supported : Supported (prepare u32Domain (graphReservations blocks)) ([] ++ blocks) := by
    intro id member
    exact mem_map_of_mem ValueId.index (graphValueIds blocks) id member
  obtain ⟨finalInferred, finalRun, preserved, typed⟩ :=
    Plans.inference (lowerRows_ready u32Domain blocks ready) direct indirect [] inferred run supported
  refine ⟨finalInferred, finalRun, ?_, typed⟩
  intro id member
  exact preserved id (mem_map_of_mem ValueId.index (graphValueIds blocks) id member)

end TrustIr.GenericCoro.AllBlocksInference

#trustIrAxiomsExact TrustIr.GenericCoro.AllBlocksInference.Plans.inference.match_1 == []
