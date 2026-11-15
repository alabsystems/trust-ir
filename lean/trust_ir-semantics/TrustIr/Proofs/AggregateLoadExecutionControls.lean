-- Copyright 2026 Andrew Yates | Apache-2.0
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

namespace TrustIr.AggregateLoadExecutionControls

private def root : Ty := .Tuple [.U8,.U32]
private def plan : AggregateMemory.Plan := .fields root { size := 8,alignment := 4 }
  [(0,.leaf .U8 { size := 1,alignment := 1 }),(4,.leaf .U32 { size := 4,alignment := 4 })]
private def service (model : ByteModel) : AggregateMemory.Service := AggregateMemory.prepare { model } [root]
private def context (model : ByteModel) : EvalContext :=
  { EvalContext.empty with byteModel := model,memoryService := some (service model) }
private def complete : ByteImage := ByteImage.ofList [some 11,some 0,some 0,some 0,some 9,some 0,some 0,some 0]
private def padded : ByteImage := ByteImage.ofList [some 11,none,none,none,some 9,some 0,some 0,some 0]
private def unwritten : ByteImage := ByteImage.ofList [none,none,none,none,some 9,some 0,some 0,some 0]
private def initializedValue : Value := .aggregate [.int 8 11,.int 32 9]
private def unwrittenValue : Value := .aggregate [.uninit,.int 32 9]
private def memory (image : ByteImage) : Memory :=
  ({ Memory.empty with
    allocations := [{ id := ⟨7⟩,base := 100,size := 8,requested := 8,alive := true,origin := .rustStack }]
    nextAddr := 108
    nextAllocId := 8 }).writeImage 100 image
private def explainedMemory : Memory := (memory unwritten).recordUnwritten ⟨7⟩ 100 [(0,1)]
private def state (image : ByteImage) : MachineState :=
  { MachineState.empty with memory := memory image,locals := ValueMap.empty.set ⟨0⟩ (.ptr 100 (some ⟨7⟩)),nextValueId := 40 }

theorem plan_is_actual_source_query (model : ByteModel) : (service model).query root = .ok plan := by
  trustIrCompilerProof {
    cases model <;> rfl
  } {
    cases model <;> trustIrReduce
  }

theorem complete_image_selects_ordinary_decode (model : ByteModel) :
    AggregateMemory.loadImageResult model none root false (memory complete) ⟨7⟩ 100 plan complete = .ok initializedValue := by
  trustIrCompilerProof {
    cases model <;> rfl
  } {
    cases model <;> trustIrReduce
  }

theorem missing_padding_is_not_partial_poison (model : ByteModel) :
    AggregateMemory.loadImageResult model none root false (memory padded) ⟨7⟩ 100 plan padded = .ok initializedValue := by
  trustIrCompilerProof {
    cases model <;> rfl
  } {
    cases model <;> trustIrReduce
  }

theorem padding_path_checks_only_covered_bytes :
    (AggregateMemory.firstMissing padded,AggregateMemory.covered plan padded) = (some 1,.ok none) := by
  trustIrCompilerProof {
    exact rfl
  } {
    exact by trustIrReduce
  }

theorem explained_fields_decode_original_unwritten_value (model : ByteModel) :
    AggregateMemory.loadImageResult model none root false explainedMemory ⟨7⟩ 100 plan unwritten = .ok unwrittenValue := by
  trustIrCompilerProof {
    cases model <;> rfl
  } {
    cases model <;> trustIrReduce
  }

theorem temporary_zeros_do_not_replace_original_image :
    (unwritten.get 0,(AggregateMemory.explainedLoadImage explainedMemory ⟨7⟩ 100 unwritten).get 0) = (none,some 0) := by
  trustIrCompilerProof {
    exact rfl
  } {
    exact by trustIrReduce
  }

theorem temporary_zeros_are_not_a_loaded_zero_value (model : ByteModel) :
    AggregateMemory.loadImageResult model none root false explainedMemory ⟨7⟩ 100 plan unwritten ≠
      .ok (.aggregate [.int 8 0,.int 32 9]) := by
  trustIrCompilerProof {
    cases model <;> intro bad <;> cases bad
  } {
    intro bad
    rw [explained_fields_decode_original_unwritten_value model] at bad
    cases bad
  }

theorem wrong_allocation_cannot_explain_a_hole (model : ByteModel) :
    AggregateMemory.loadImageResult model none root false ((memory unwritten).recordUnwritten ⟨8⟩ 100 [(0,1)])
      ⟨7⟩ 100 plan unwritten = .error (.ub "Load: reading uninitialized covered memory") := by
  trustIrCompilerProof {
    cases model <;> rfl
  } {
    cases model <;> trustIrReduce
  }

theorem padding_record_cannot_explain_a_field (model : ByteModel) :
    AggregateMemory.loadImageResult model none root false ((memory unwritten).recordUnwritten ⟨7⟩ 100 [(1,2)])
      ⟨7⟩ 100 plan unwritten = .error (.ub "Load: reading uninitialized covered memory") := by
  trustIrCompilerProof {
    cases model <;> rfl
  } {
    cases model <;> trustIrReduce
  }

theorem adjacent_record_does_not_cover_the_load (model : ByteModel) :
    AggregateMemory.loadImageResult model none root false ((memory unwritten).recordUnwritten ⟨7⟩ 108 [(0,1)])
      ⟨7⟩ 100 plan unwritten = .error (.ub "Load: reading uninitialized covered memory") := by
  trustIrCompilerProof {
    cases model <;> rfl
  } {
    cases model <;> trustIrReduce
  }

theorem partial_scalar_transport_is_a_distinct_branch (model : ByteModel) :
    AggregateMemory.loadImageResult model none .U8 false Memory.empty ⟨7⟩ 100
      (.leaf .U8 { size := 1,alignment := 1 }) (ByteImage.ofList [none]) = .ok (.partial [none]) := by
  trustIrCompilerProof {
    cases model <;> rfl
  } {
    cases model <;> trustIrReduce
  }

theorem strict_scalar_does_not_take_partial_transport (model : ByteModel) :
    AggregateMemory.loadImageResult model none .U8 true Memory.empty ⟨7⟩ 100
      (.leaf .U8 { size := 1,alignment := 1 }) (ByteImage.ofList [none]) =
      .error (.ub "Load: reading uninitialized covered memory") := by
  trustIrCompilerProof {
    cases model <;> rfl
  } {
    cases model <;> trustIrReduce
  }

theorem original_node_reads_padded_image (model : ByteModel) :
    (Sem.run (stepInstWithContext (context model) (.Load root ⟨0⟩ false none)) (state padded)).map
      (fun pair => (pair.1,pair.2.lookupValue ⟨40⟩,pair.2.nextValueId)) =
      .ok (.value (some ⟨40⟩),some initializedValue,41) := by
  trustIrCompilerProof {
    cases model <;> rfl
  } {
    cases model <;> trustIrReduce
  }

theorem original_node_reads_unwritten_image (model : ByteModel) :
    (Sem.run (stepInstWithContext (context model) (.Load root ⟨0⟩ false none))
      { state unwritten with memory := explainedMemory }).map
      (fun pair => (pair.1,pair.2.lookupValue ⟨40⟩,pair.2.nextValueId,pair.2.memory.bytes 100)) =
      .ok (.value (some ⟨40⟩),some unwrittenValue,41,none) := by
  trustIrCompilerProof {
    cases model <;> rfl
  } {
    cases model <;> trustIrReduce
  }

end TrustIr.AggregateLoadExecutionControls
