-- Copyright 2026 Andrew Yates | Apache-2.0
import TrustIr.Proofs.LoadInstructionExecution

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

namespace TrustIr.LoadInstructionControls

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
private def initial (bytes : List (Option UInt8)) : MachineState :=
  { MachineState.empty with
    locals := ValueMap.empty.set ⟨0⟩ pointer
    nextValueId := 40
    memory := ({ Memory.empty with allocations := [allocation],nextAddr := 108,nextAllocId := 8 }).writeImage
      100 (ByteImage.ofList bytes) }
private def unwritten : MachineState :=
  { initial [none,some 9] with memory := (initial [none,some 9]).memory.recordUnwritten ⟨7⟩ 100 [(0,1)] }
private def observation (result : InstrResult × MachineState) :=
  (result.1,result.2.lookupValue ⟨40⟩,result.2.nextValueId)

theorem descriptor_load_publishes_actual_value_once (model : ByteModel) :
    (Sem.run (stepInstWithContext (context model) (.Load root ⟨0⟩ false none)) (initial [some 11,some 9])).map observation =
      .ok (.value (some ⟨40⟩),some (.aggregate [.int 8 11,.int 8 9]),41) := by
  trustIrCompilerProof {
    cases model <;> rfl
  } {
    cases model <;> trustIrReduce
  }

theorem scalar_load_keeps_canonical_path (model : ByteModel) :
    (Sem.run (stepInstWithContext (wrongContext model) (.Load .U8 ⟨0⟩ false none)) (initial [some 11,some 9])).map observation =
      .ok (.value (some ⟨40⟩),some (.int 8 11),41) := by
  trustIrCompilerProof {
    cases model <;> rfl
  } {
    cases model <;> trustIrReduce
  }

theorem scalar_partial_load_publishes_poison (model : ByteModel) :
    (Sem.run (stepInstWithContext (context model) (.Load .U8 ⟨0⟩ false none)) (initial [none,some 9])).map observation =
      .ok (.value (some ⟨40⟩),some (.partial [none]),41) := by
  trustIrCompilerProof {
    cases model <;> rfl
  } {
    cases model <;> trustIrReduce
  }

theorem scalar_strict_load_refuses_uninitialized (model : ByteModel) :
    Sem.run (stepInstWithContext (context model) (.Load .U8 ⟨0⟩ true none)) (initial [none,some 9]) =
      .error (.ub "Load: reading uninitialized memory") := by
  trustIrCompilerProof {
    cases model <;> rfl
  } {
    cases model <;> trustIrReduce
  }

theorem descriptor_unexplained_hole_is_not_padding (model : ByteModel) :
    Sem.run (stepInstWithContext (context model) (.Load root ⟨0⟩ false none)) (initial [none,some 9]) =
      .error (.ub "Load: reading uninitialized covered memory") := by
  trustIrCompilerProof {
    cases model <;> rfl
  } {
    cases model <;> trustIrReduce
  }

theorem descriptor_unwritten_load_uses_original_metadata (model : ByteModel) :
    (Sem.run (stepInstWithContext (context model) (.Load root ⟨0⟩ false none)) unwritten).map observation =
      .ok (.value (some ⟨40⟩),some (.aggregate [.uninit,.int 8 9]),41) := by
  trustIrCompilerProof {
    cases model <;> rfl
  } {
    cases model <;> trustIrReduce
  }

theorem strict_descriptor_preserves_explicit_unwritten_policy (model : ByteModel) :
    (Sem.run (stepInstWithContext (context model) (.Load root ⟨0⟩ true none)) unwritten).map observation =
      .ok (.value (some ⟨40⟩),some (.aggregate [.uninit,.int 8 9]),41) := by
  trustIrCompilerProof {
    cases model <;> rfl
  } {
    cases model <;> trustIrReduce
  }

theorem unwritten_read_does_not_consume_metadata (model : ByteModel) :
    (Sem.run (stepInstWithContext (context model) (.Load root ⟨0⟩ false none)) unwritten).map
      (fun pair => (pair.2.memory.isUnwritten ⟨7⟩ 100,pair.2.memory.bytes 100,pair.2.memory.bytes 101)) =
      .ok (true,none,some 9) := by
  trustIrCompilerProof {
    cases model <;> rfl
  } {
    cases model <;> trustIrReduce
  }

theorem missing_operand_precedes_target_refusal :
    Sem.run (stepInstWithContext (wrongContext .le64) (.Load root ⟨1⟩ false (some 0))) (initial [some 11,some 9]) =
      .error (.typeError s!"undefined SSA value: {repr (ValueId.mk 1)}") := rfl

theorem descriptor_target_precedes_null_pointer (model : ByteModel) :
    Sem.run (stepInstWithContext (wrongContext model) (.Load root ⟨0⟩ false none))
      { initial [some 11,some 9] with locals := ValueMap.empty.set ⟨0⟩ .nullPtr } =
      .error (.typeError "memory: source layout target does not match evaluator target") := by
  trustIrCompilerProof {
    cases model <;> rfl
  } {
    cases model <;> trustIrReduce
  }

theorem scalar_null_pointer_precedes_bad_alignment (model : ByteModel) :
    Sem.run (stepInstWithContext (context model) (.Load .U8 ⟨0⟩ false (some 0)))
      { initial [some 11,some 9] with locals := ValueMap.empty.set ⟨0⟩ .nullPtr } =
      .error (.ub "Load: null pointer dereference") := by
  trustIrCompilerProof {
    cases model <;> rfl
  } {
    cases model <;> trustIrReduce
  }

theorem descriptor_alignment_is_forwarded (model : ByteModel) :
    Sem.run (stepInstWithContext (context model) (.Load root ⟨0⟩ false (some 0))) (initial [some 11,some 9]) =
      .error (.typeError "Load: alignment must be a nonzero u64 power of two") := by
  trustIrCompilerProof {
    cases model <;> rfl
  } {
    cases model <;> trustIrReduce
  }

theorem missing_service_does_not_fabricate_layout :
    Sem.run (stepInstWithContext EvalContext.empty (.Load root ⟨0⟩ false none)) (initial [some 11,some 9]) =
      .error (.unsupported .layout "Load: type has no byte size") := rfl

/-- Without a global freshness invariant, bindFresh can overwrite an existing
    local. The universal publication law intentionally does not claim otherwise. -/
theorem colliding_next_id_still_looks_up_before_publication (model : ByteModel) :
    (Sem.run (stepInstWithContext (context model) (.Load .U8 ⟨0⟩ false none))
      { initial [some 11,some 9] with nextValueId := 0 }).map
      (fun pair => (pair.1,pair.2.lookupValue ⟨0⟩,pair.2.nextValueId)) =
      .ok (.value (some ⟨0⟩),some (.int 8 11),1) := by
  trustIrCompilerProof {
    cases model <;> rfl
  } {
    cases model <;> trustIrReduce
  }

end TrustIr.LoadInstructionControls
