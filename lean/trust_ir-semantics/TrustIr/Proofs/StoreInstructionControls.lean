-- Copyright 2026 Andrew Yates | Apache-2.0
import TrustIr.Proofs.StoreInstructionExecution
import TrustIr.Proofs.AggregateLoadExecution

/- Enable kernel reduction through the imported mutual compiler equations.
The metadata is local to these proofs; no executable definition is replaced. -/
run_cmd do
  if Lean.versionString == "4.30.0-rc2" then
    let env ← Lean.getEnv
    let mut registered := 0
    for (n, _) in env.constants.map₁.toList do
      if n.toString.endsWith "TrustIr.SourceLayout.compileTy.eq_def" ||
         n.toString.endsWith "TrustIr.SourceLayout.compileTypes.eq_def" then
        Lean.Elab.Command.elabCommand (← `(command| attribute [local cbv_eval] $(Lean.mkIdent n):ident))
        registered := registered + 1
    unless registered == 2 do
      Lean.throwError "expected the two original layout compiler equations"
  else if Lean.versionString != "4.8.0" then
    Lean.throwError "unsupported compiler for layout equation reduction"

namespace TrustIr.StoreInstructionControls

private def root : Ty := .Tuple [.U8,.U8]
private def service (model : ByteModel) : AggregateMemory.Service := AggregateMemory.prepare { model } [root]
private def context (model : ByteModel) : EvalContext :=
  { EvalContext.empty with byteModel := model, memoryService := some (service model) }
private def other : ByteModel → ByteModel | .le32 => .le64 | .le64 => .le32
private def wrongContext (model : ByteModel) : EvalContext :=
  { context model with memoryService := some (service (other model)) }
private def allocation : Allocation :=
  { id := ⟨7⟩,base := 100,size := 8,requested := 8,alive := true,origin := .rustStack }
private def pointer : Value := .ptr 100 (some ⟨7⟩)
private def held : Value := .aggregate [.uninit,.int 8 9]
private def initial (value : Value) : MachineState :=
  { MachineState.empty with
    locals := (ValueMap.empty.set ⟨0⟩ pointer).set ⟨1⟩ value
    nextValueId := 40
    memory := ({ Memory.empty with allocations := [allocation],nextAddr := 108,nextAllocId := 8 }).recordUnwritten ⟨7⟩ 100 [(0,8)] }
private def afterStore (model : ByteModel) : MachineState :=
  match Sem.run (stepInstWithContext (context model) (.Store root ⟨0⟩ ⟨1⟩ false none)) (initial held) with
  | .ok (_,state) => state
  | .error _ => initial held

private theorem ran (model : ByteModel) :
    Sem.run (stepInstWithContext (context model) (.Store root ⟨0⟩ ⟨1⟩ false none)) (initial held) =
      .ok (.value none,afterStore model) := by
  trustIrCompilerProof {
    cases model <;> rfl
  } {
    cases model <;> trustIrReduce
  }

theorem descriptor_selector_uses_actual_service (model : ByteModel) :
    (context model).memoryServiceFor root = some (service model) := rfl

theorem canonical_selector_keeps_scalar_path (model : ByteModel) :
    (wrongContext model).memoryServiceFor .U8 = none := rfl

theorem actual_store_node_executes (model : ByteModel) :
    Sem.run (stepInstWithContext (context model) (.Store root ⟨0⟩ ⟨1⟩ false none)) (initial held) =
      .ok (.value none,afterStore model) := ran model

theorem store_node_does_not_publish_ssa_temporaries (model : ByteModel) :
    (afterStore model).locals = (initial held).locals ∧ (afterStore model).nextValueId = 40 := by
  trustIrCompilerProof {
    cases model <;> exact ⟨rfl,rfl⟩
  } {
    cases model <;> exact ⟨by trustIrReduce,by trustIrReduce⟩
  }

theorem store_node_publishes_selected_unwritten_image (model : ByteModel) :
    ((afterStore model).memory.bytes 101,(afterStore model).memory.isUnwritten ⟨7⟩ 100,
      (afterStore model).memory.isUnwritten ⟨7⟩ 101) = (some 9,true,false) := by
  trustIrCompilerProof {
    cases model <;> rfl
  } {
    cases model <;> trustIrReduce
  }

theorem missing_pointer_lookup_precedes_other_refusals :
    Sem.run (stepInstWithContext (wrongContext .le64) (.Store root ⟨0⟩ ⟨1⟩ true (some 0)))
      { initial (.partial [none,none]) with locals := ValueMap.empty } =
      .error (.typeError s!"undefined SSA value: {repr (ValueId.mk 0)}") := rfl

theorem missing_value_lookup_is_not_a_missing_pointer :
    Sem.run (stepInstWithContext (context .le64) (.Store root ⟨0⟩ ⟨1⟩ false none))
      { initial held with locals := ValueMap.empty.set ⟨0⟩ pointer } =
      .error (.typeError s!"undefined SSA value: {repr (ValueId.mk 1)}") := rfl

theorem canonical_store_ignores_wrong_target_descriptor (model : ByteModel) :
    (Sem.run (stepInstWithContext (wrongContext model) (.Store .U8 ⟨0⟩ ⟨1⟩ false none)) (initial (.int 8 9))).map
      (fun result => (result.1,result.2.memory.bytes 100,result.2.nextValueId)) = .ok (.value none,some 9,40) := by
  trustIrCompilerProof {
    cases model <;> rfl
  } {
    cases model <;> trustIrReduce
  }

theorem descriptor_store_keeps_target_refusal (model : ByteModel) :
    Sem.run (stepInstWithContext (wrongContext model) (.Store root ⟨0⟩ ⟨1⟩ false none)) (initial held) =
      .error (.typeError "memory: source layout target does not match evaluator target") := by
  trustIrCompilerProof {
    cases model <;> rfl
  } {
    cases model <;> trustIrReduce
  }

theorem missing_descriptor_has_no_fabricated_layout :
    Sem.run (stepInstWithContext EvalContext.empty (.Store root ⟨0⟩ ⟨1⟩ false none)) (initial held) =
      .error (.unsupported .layout "type has no complete scalar/vector byte layout") := rfl

theorem instruction_alignment_is_forwarded :
    Sem.run (stepInstWithContext (context .le64) (.Store root ⟨0⟩ ⟨1⟩ false (some 0))) (initial held) =
      .error (.typeError "Store: alignment must be a nonzero u64 power of two") := by
  trustIrCompilerProof {
    exact rfl
  } {
    exact by trustIrReduce
  }

private def nullState : MachineState :=
  { initial (.partial [none,none]) with locals := (ValueMap.empty.set ⟨0⟩ .nullPtr).set ⟨1⟩ (.partial [none,none]) }

theorem descriptor_strict_poison_precedes_pointer_check :
    Sem.run (stepInstWithContext (context .le64) (.Store root ⟨0⟩ ⟨1⟩ true none)) nullState =
      .error (.ub "Store: strict store of poison or unwritten aggregate lane") := rfl

theorem canonical_pointer_check_precedes_strict_poison :
    Sem.run (stepInstWithContext (context .le64) (.Store .U8 ⟨0⟩ ⟨1⟩ true none)) nullState =
      .error (.ub "Store: null pointer dereference") := rfl

theorem identical_operand_ids_are_read_from_original_state (model : ByteModel) :
    (Sem.run (stepInstWithContext (context model) (.Store .Ptr ⟨0⟩ ⟨0⟩ false (some 1))) (initial held)).map Prod.fst =
      .ok (.value none) := by
  trustIrCompilerProof {
    cases model <;> rfl
  } {
    cases model <;> trustIrReduce
  }

theorem descriptor_store_then_load_publishes_only_the_load (model : ByteModel) :
    (Sem.run (do
      let _ ← stepInstWithContext (context model) (.Store root ⟨0⟩ ⟨1⟩ false none)
      stepInstWithContext (context model) (.Load root ⟨0⟩ false none)) (initial held)).map
      (fun result => (result.1,result.2.lookupValue ⟨40⟩,result.2.nextValueId)) =
      .ok (.value (some ⟨40⟩),some held,41) := by
  trustIrCompilerProof {
    cases model <;> rfl
  } {
    let selectedPlan : AggregateMemory.Plan := .fields root ⟨2,1⟩
      [(0,.leaf .U8 ⟨1,1⟩),(1,.leaf .U8 ⟨1,1⟩)]
    have query : (service model).query root = .ok selectedPlan := by
      cases model <;> trustIrReduce
    let originalBytes := ByteImage.fill 2 none
    let firstBytes := (originalBytes.slice 0 0).append
      ((ByteImage.fill 1 none).append (originalBytes.slice 1 1))
    let produced : AggregateMemory.Image :=
      { bytes := (firstBytes.slice 0 1).append ((ByteImage.ofList [some 9]).append (firstBytes.slice 2 0))
        unwritten := [(0,1)] }
    have encoded : AggregateMemory.encode model none selectedPlan held true = .ok produced := by
      dsimp only [produced,selectedPlan,firstBytes,originalBytes]
      cases model <;> trustIrReduce
    have execution : model = (service model).model ∧ afterStore model =
        { initial held with memory := ((initial held).memory.writeImage 100 produced.bytes).recordUnwritten ⟨7⟩ 100 produced.unwritten } := by
      obtain ⟨_,actualPointer,actualValue,actualPlan,actualAlign,address,identity,image,pointerFound,valueFound,
        _clean,target,actualQuery,_aligned,pointerShape,_access,accepted,_extent,frame⟩ :=
        stepStore_descriptor_success_steps (context model) root ⟨0⟩ ⟨1⟩ false none (service model)
          (descriptor_selector_uses_actual_service model) (initial held) (afterStore model) (.value none) (ran model)
      change some pointer = some actualPointer at pointerFound
      change some held = some actualValue at valueFound
      cases pointerFound
      cases valueFound
      rw [query] at actualQuery
      cases actualQuery
      cases pointerShape
      change AggregateMemory.encode model none selectedPlan held true = .ok image at accepted
      have same : image = produced := Except.ok.inj (accepted.symm.trans encoded)
      subst image
      exact ⟨target,frame⟩
    have accessed : Sem.run (Sem.checkedAccess "Load" 100 ⟨7⟩ 2 1 model)
        (afterStore model) = .ok (100,afterStore model) := by
      rw [execution.2]
      dsimp only [produced,selectedPlan,firstBytes,originalBytes]
      cases model <;> trustIrReduce
    have decoded : AggregateMemory.loadImageResult model none root false (afterStore model).memory ⟨7⟩ 100 selectedPlan
        ((afterStore model).memory.readImage 100 2) = .ok held := by
      rw [execution.2]
      let finalMemory := ((initial held).memory.writeImage 100 produced.bytes).recordUnwritten ⟨7⟩ 100 produced.unwritten
      let snapshot := finalMemory.readImage 100 2
      change AggregateMemory.loadImageResult model none root false finalMemory ⟨7⟩ 100 selectedPlan snapshot = .ok held
      have missing : AggregateMemory.firstMissing snapshot = some 0 := by
        dsimp only [snapshot,finalMemory,produced,firstBytes,originalBytes]
        trustIrReduce
      have coverage : AggregateMemory.covered selectedPlan snapshot = .ok (some 0) := by
        dsimp only [selectedPlan,snapshot,finalMemory,produced,firstBytes,originalBytes]
        trustIrReduce
      have explanation : AggregateMemory.covered selectedPlan
          (AggregateMemory.explainedLoadImage finalMemory ⟨7⟩ 100 snapshot) = .ok none := by
        dsimp only [selectedPlan,snapshot,finalMemory,produced,firstBytes,originalBytes]
        trustIrReduce
      have read : AggregateMemory.decodeUnwritten model none finalMemory selectedPlan snapshot = .ok held := by
        dsimp only [selectedPlan,snapshot,finalMemory,produced,firstBytes,originalBytes]
        trustIrReduce
        simp only [decodeValueAt,decodeTypedAtModel,decodeImageAt,decodeImageAtModel,
          decodeValueAtModel,decodeValue,Memory.resolveDecoded,Except.bind]
        all_goals cases model <;> trustIrReduce
      have noPartial : isPartialLoadTyFor model root = false := by cases model <;> rfl
      simp only [AggregateMemory.loadImageResult,missing,Option.isNone,noPartial,
        Bool.not_false,Bool.true_and,Bool.false_eq_true,ite_false,coverage,Except.bind,explanation]
      exact read
    have loaded : Sem.run (selectedLoadAction (context model) root pointer false none)
        (afterStore model) = .ok (held,afterStore model) := by
      change Sem.run (AggregateMemory.loadValue (service model) none root pointer false none model)
        (afterStore model) = .ok (held,afterStore model)
      exact AggregateMemory.loadValue_of_checks (service model) none root false none model (afterStore model)
        selectedPlan 1 100 ⟨7⟩ held execution.1 query rfl accessed decoded
    have lookup : (afterStore model).lookupValue ⟨0⟩ = some pointer := by
      unfold MachineState.lookupValue
      rw [(store_node_does_not_publish_ssa_temporaries model).1]
      rfl
    have fresh : (afterStore model).nextValueId = 40 := (store_node_does_not_publish_ssa_temporaries model).2
    have loadRun : Sem.run (stepInstWithContext (context model) (.Load root ⟨0⟩ false none))
        (afterStore model) = .ok (.value (some ⟨(afterStore model).nextValueId⟩),
          { afterStore model with
            locals := (afterStore model).locals.set ⟨(afterStore model).nextValueId⟩ held
            nextValueId := (afterStore model).nextValueId + 1 }) :=
      (stepLoad_success_iff (context model) root ⟨0⟩ false none _ _ _).mpr
        ⟨pointer,held,lookup,loaded,rfl,rfl⟩
    rw [Sem.run_bind,ran model]
    simp only [Except.bind,loadRun,Except.map,MachineState.lookupValue,fresh,ValueMap.set]
    rfl
  }

theorem canonical_store_then_load_publishes_only_the_load (model : ByteModel) :
    (Sem.run (do
      let _ ← stepInstWithContext (wrongContext model) (.Store .U8 ⟨0⟩ ⟨1⟩ false none)
      stepInstWithContext (wrongContext model) (.Load .U8 ⟨0⟩ false none)) (initial (.int 8 9))).map
      (fun result => (result.1,result.2.lookupValue ⟨40⟩,result.2.nextValueId)) =
      .ok (.value (some ⟨40⟩),some (.int 8 9),41) := by
  trustIrCompilerProof {
    cases model <;> rfl
  } {
    cases model <;> trustIrReduce
  }

end TrustIr.StoreInstructionControls
