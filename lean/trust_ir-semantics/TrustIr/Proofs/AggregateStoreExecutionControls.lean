-- Copyright 2026 Andrew Yates | Apache-2.0
import TrustIr.Proofs.AggregateStoreExecution
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

namespace TrustIr.AggregateMemory.StoreExecutionControls
open SourceLayout

private def service (model : ByteModel) : Service := prepare { model } [.U8,.Tuple [.U8,.U8]]
private def allocation : Allocation :=
  { id := ⟨7⟩,base := 100,size := 8,requested := 8,alive := true,origin := .rustStack }
private def initial : MachineState :=
  { MachineState.empty with
    nextValueId := 40
    memory := ({ Memory.empty with allocations := [allocation],nextAddr := 108,nextAllocId := 8 }).recordUnwritten ⟨7⟩ 100 [(0,8)] }
private def pointer : Value := .ptr 100 (some ⟨7⟩)
private def scalarAfter (model : ByteModel) : MachineState :=
  match Sem.run (storeValue (service model) none .U8 pointer (.int 8 9) false none model) initial with
  | .ok (_,state) => state
  | .error _ => initial

private theorem scalarRan (model : ByteModel) :
    Sem.run (storeValue (service model) none .U8 pointer (.int 8 9) false none model) initial = .ok ((),scalarAfter model) := by
  trustIrCompilerProof {
    cases model <;> rfl
  } {
    cases model <;> trustIrReduce
  }

theorem actual_scalar_store_executes (model : ByteModel) :
    Sem.run (storeValue (service model) none .U8 pointer (.int 8 9) false none model) initial = .ok ((),scalarAfter model) :=
  scalarRan model

theorem actual_scalar_store_writes_byte (model : ByteModel) : (scalarAfter model).memory.bytes 100 = some 9 := by
  trustIrCompilerProof {
    cases model <;> rfl
  } {
    cases model <;> trustIrReduce
  }

theorem actual_scalar_store_clears_exact_window (model : ByteModel) :
    ((scalarAfter model).memory.isUnwritten ⟨7⟩ 100,(scalarAfter model).memory.isUnwritten ⟨7⟩ 101) = (false,true) := by
  trustIrCompilerProof {
    cases model <;> rfl
  } {
    cases model <;> trustIrReduce
  }

theorem scalar_store_retains_private_state (model : ByteModel) :
    (scalarAfter model).locals = initial.locals ∧ (scalarAfter model).nextValueId = 40 := by
  trustIrCompilerProof {
    cases model <;> exact ⟨rfl,rfl⟩
  } {
    cases model <;> exact ⟨by trustIrReduce,by trustIrReduce⟩
  }

theorem partial_transport_is_not_ordinary_encoding (model : ByteModel) :
    (Sem.run (storeValue (service model) none .U8 pointer (.partial [none]) false none model) initial).map
      (fun result => (result.2.memory.bytes 100,result.2.memory.isUnwritten ⟨7⟩ 100,result.2.memory.isUnwritten ⟨7⟩ 101)) =
      .ok (none,false,true) := by
  trustIrCompilerProof {
    cases model <;> rfl
  } {
    cases model <;> trustIrReduce
  }

theorem typed_poison_transport_has_no_new_records (model : ByteModel) :
    (Sem.run (storeValue (service model) none .U8 pointer (.undef .U8) false none model) initial).map
      (fun result => (result.2.memory.bytes 100,result.2.memory.isUnwritten ⟨7⟩ 100,result.2.memory.isUnwritten ⟨7⟩ 101)) =
      .ok (none,false,true) := by
  trustIrCompilerProof {
    cases model <;> rfl
  } {
    cases model <;> trustIrReduce
  }

theorem wrong_poison_type_refuses :
    Sem.run (storeValue (service .le64) none .U8 pointer (.undef .U16) false none .le64) initial =
      .error (.typeError "Store: poison source type does not match store type") := by
  trustIrCompilerProof {
    exact rfl
  } {
    exact by trustIrReduce
  }

theorem strict_poison_refuses_before_target_and_pointer :
    Sem.run (storeValue (service .le64) none .U8 .nullPtr (.partial [none]) true none .le32) initial =
      .error (.ub "Store: strict store of poison or unwritten aggregate lane") := by
  trustIrCompilerProof {
    exact rfl
  } {
    exact by trustIrReduce
  }

theorem source_target_mismatch_refuses :
    Sem.run (storeValue (service .le64) none .U8 pointer (.int 8 9) false none .le32) initial =
      .error (.typeError "memory: source layout target does not match evaluator target") := by
  trustIrCompilerProof {
    exact rfl
  } {
    exact by trustIrReduce
  }

theorem alignment_refusal_precedes_pointer :
    Sem.run (storeValue (service .le64) none .U8 .nullPtr (.int 8 9) false (some 0) .le64) initial =
      .error (.typeError "Store: alignment must be a nonzero u64 power of two") := by
  trustIrCompilerProof {
    exact rfl
  } {
    exact by trustIrReduce
  }

theorem null_pointer_refuses :
    Sem.run (storeValue (service .le64) none .U8 .nullPtr (.int 8 9) false none .le64) initial =
      .error (.ub "Store: null pointer dereference") := by
  trustIrCompilerProof {
    exact rfl
  } {
    exact by trustIrReduce
  }

theorem dead_allocation_refuses :
    Sem.run (storeValue (service .le64) none .U8 pointer (.int 8 9) false none .le64)
      { initial with memory := { initial.memory with allocations := [{ allocation with alive := false }] } } =
      .error (.ub "Store: use after dealloc") := by
  trustIrCompilerProof {
    exact rfl
  } {
    exact by trustIrReduce
  }

theorem access_refusal_precedes_bad_carrier :
    Sem.run (storeValue (service .le64) none .U8 (.ptr 108 (some ⟨7⟩)) (.bool true) false none .le64) initial =
      .error (.ub "Store: access is out of bounds") := by
  trustIrCompilerProof {
    exact rfl
  } {
    exact by trustIrReduce
  }

theorem target32_refusal_precedes_allocation :
    Sem.run (storeValue (service .le32) none .U8 (.ptr 4294967296 (some ⟨7⟩)) (.int 8 9) false none .le32) initial =
      .error (.ub "Store: access is outside the target address space") := by
  trustIrCompilerProof {
    exact rfl
  } {
    exact by trustIrReduce
  }

theorem partial_image_extent_refuses :
    Sem.run (storeValue (service .le64) none .U8 pointer (.partial [none,none]) false none .le64) initial =
      .error (.typeError "Store: image byte count does not match source layout") := by
  trustIrCompilerProof {
    exact rfl
  } {
    exact by trustIrReduce
  }

theorem actual_unwritten_tuple_publication (model : ByteModel) :
    (Sem.run (storeValue (service model) none (.Tuple [.U8,.U8]) pointer
      (.aggregate [.uninit,.int 8 9]) false none model) initial).map
      (fun result => (result.2.memory.bytes 101,result.2.memory.isUnwritten ⟨7⟩ 100,
        result.2.memory.isUnwritten ⟨7⟩ 101,result.2.memory.isUnwritten ⟨7⟩ 102)) = .ok (some 9,true,false,true) := by
  trustIrCompilerProof {
    cases model <;> rfl
  } {
    cases model <;> trustIrReduce
  }

theorem strict_nested_unwritten_refuses :
    Sem.run (storeValue (service .le64) none (.Tuple [.U8,.U8]) pointer
      (.aggregate [.uninit,.int 8 9]) true none .le64) initial =
      .error (.ub "Store: strict store of poison or unwritten aggregate lane") := by
  trustIrCompilerProof {
    exact rfl
  } {
    exact by trustIrReduce
  }

theorem whole_unwritten_store_registers_a_new_lane :
    (Sem.run (storeValue (service .le64) none .U8 pointer .uninit false none .le64) initial).map
      (fun result => (result.2.memory.bytes 100,result.2.memory.unwritten.length)) = .ok (none,2) := by
  trustIrCompilerProof {
    exact rfl
  } {
    exact by trustIrReduce
  }

theorem actual_scalar_store_then_load (model : ByteModel) :
    (Sem.run (do
      storeValue (service model) none .U8 pointer (.int 8 9) false none model
      loadValue (service model) none .U8 pointer false none model) initial).map Prod.fst = .ok (.int 8 9) := by
  trustIrCompilerProof {
    cases model <;> rfl
  } {
    cases model <;> trustIrReduce
  }

theorem actual_unwritten_tuple_store_then_load (model : ByteModel) :
    (Sem.run (do
      storeValue (service model) none (.Tuple [.U8,.U8]) pointer (.aggregate [.uninit,.int 8 9]) false none model
      loadValue (service model) none (.Tuple [.U8,.U8]) pointer false none model) initial).map Prod.fst =
      .ok (.aggregate [.uninit,.int 8 9]) := by
  trustIrCompilerProof {
    cases model <;> rfl
  } {
    let rootTy : Ty := .Tuple [.U8,.U8]
    let heldInput : Value := .aggregate [.uninit,.int 8 9]
    let after : MachineState :=
      match Sem.run (storeValue (service model) none rootTy pointer heldInput false none model) initial with
      | .ok (_,state) => state
      | .error _ => initial
    have ran : Sem.run (storeValue (service model) none rootTy pointer heldInput false none model) initial =
        .ok ((),after) := by
      dsimp only [after,rootTy,heldInput]
      cases model <;> trustIrReduce
    let selectedPlan : AggregateMemory.Plan := .fields rootTy ⟨2,1⟩
      [(0,.leaf .U8 ⟨1,1⟩),(1,.leaf .U8 ⟨1,1⟩)]
    have query : (service model).query rootTy = .ok selectedPlan := by
      cases model <;> trustIrReduce
    let originalBytes := ByteImage.fill 2 none
    let firstBytes := (originalBytes.slice 0 0).append
      ((ByteImage.fill 1 none).append (originalBytes.slice 1 1))
    let produced : AggregateMemory.Image :=
      { bytes := (firstBytes.slice 0 1).append ((ByteImage.ofList [some 9]).append (firstBytes.slice 2 0))
        unwritten := [(0,1)] }
    have encoded : AggregateMemory.encode model none selectedPlan heldInput true = .ok produced := by
      dsimp only [produced,selectedPlan,firstBytes,originalBytes,rootTy,heldInput]
      cases model <;> trustIrReduce
    have execution : model = (service model).model ∧ after =
        { initial with memory := ((initial).memory.writeImage 100 produced.bytes).recordUnwritten ⟨7⟩ 100 produced.unwritten } := by
      obtain ⟨_clean,actualPlan,actualAlign,address,identity,image,target,actualQuery,_aligned,
        pointerShape,_access,accepted,_extent,frame⟩ :=
        storeValue_success_steps (service model) none rootTy pointer heldInput false none model initial after ran
      rw [query] at actualQuery
      cases actualQuery
      cases pointerShape
      change AggregateMemory.encode model none selectedPlan heldInput true = .ok image at accepted
      have same : image = produced := Except.ok.inj (accepted.symm.trans encoded)
      subst image
      exact ⟨target,frame⟩
    have accessed : Sem.run (Sem.checkedAccess "Load" 100 ⟨7⟩ 2 1 model)
        after = .ok (100,after) := by
      rw [execution.2]
      dsimp only [produced,selectedPlan,firstBytes,originalBytes,rootTy,heldInput]
      cases model <;> trustIrReduce
    have decoded : AggregateMemory.loadImageResult model none rootTy false after.memory ⟨7⟩ 100 selectedPlan
        (after.memory.readImage 100 2) = .ok heldInput := by
      rw [execution.2]
      let finalMemory := ((initial).memory.writeImage 100 produced.bytes).recordUnwritten ⟨7⟩ 100 produced.unwritten
      let snapshot := finalMemory.readImage 100 2
      change AggregateMemory.loadImageResult model none rootTy false finalMemory ⟨7⟩ 100 selectedPlan snapshot = .ok heldInput
      have missing : AggregateMemory.firstMissing snapshot = some 0 := by
        dsimp only [snapshot,finalMemory,produced,firstBytes,originalBytes]
        trustIrReduce
      have coverage : AggregateMemory.covered selectedPlan snapshot = .ok (some 0) := by
        dsimp only [selectedPlan,snapshot,finalMemory,produced,firstBytes,originalBytes,rootTy,heldInput]
        trustIrReduce
      have explanation : AggregateMemory.covered selectedPlan
          (AggregateMemory.explainedLoadImage finalMemory ⟨7⟩ 100 snapshot) = .ok none := by
        dsimp only [selectedPlan,snapshot,finalMemory,produced,firstBytes,originalBytes,rootTy,heldInput]
        trustIrReduce
      have read : AggregateMemory.decodeUnwritten model none finalMemory selectedPlan snapshot = .ok heldInput := by
        dsimp only [selectedPlan,snapshot,finalMemory,produced,firstBytes,originalBytes,rootTy,heldInput]
        trustIrReduce
        simp only [decodeValueAt,decodeTypedAtModel,decodeImageAt,decodeImageAtModel,
          decodeValueAtModel,decodeValue,Memory.resolveDecoded,Except.bind]
        all_goals cases model <;> trustIrReduce
      have noPartial : isPartialLoadTyFor model rootTy = false := by cases model <;> rfl
      simp only [AggregateMemory.loadImageResult,missing,Option.isNone,noPartial,
        Bool.not_false,Bool.true_and,Bool.false_eq_true,ite_false,coverage,Except.bind,explanation]
      exact read
    have loaded : Sem.run (loadValue (service model) none rootTy pointer false none model)
        after = .ok (heldInput,after) := by
      exact loadValue_of_checks (service model) none rootTy false none model after
        selectedPlan 1 100 ⟨7⟩ heldInput execution.1 query rfl accessed decoded
    change (Sem.run (do
      storeValue (service model) none rootTy pointer heldInput false none model
      loadValue (service model) none rootTy pointer false none model) initial).map Prod.fst = .ok heldInput
    rw [Sem.run_bind,ran]
    simp only [Except.bind,loaded,Except.map]
  }

theorem absent_transport_does_not_authorize_strict_load (model : ByteModel) :
    (Sem.run (do
      storeValue (service model) none .U8 pointer (.partial [none]) false none model
      loadValue (service model) none .U8 pointer true none model) initial).map Prod.fst =
      .error (.ub "Load: reading uninitialized covered memory") := by
  trustIrCompilerProof {
    cases model <;> rfl
  } {
    cases model <;> trustIrReduce
  }

end TrustIr.AggregateMemory.StoreExecutionControls
