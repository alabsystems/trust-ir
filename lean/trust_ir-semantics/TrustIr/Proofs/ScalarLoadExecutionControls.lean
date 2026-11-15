-- Copyright 2026 Andrew Yates | Apache-2.0
import TrustIr.Proofs.ScalarLoadExecution

namespace TrustIr.ScalarLoadExecutionControls

private def context (model : ByteModel) (order : FunctionAddressOrder := none) : EvalContext :=
  { EvalContext.empty with byteModel := model,functionOrder := order }
private def pointer : Value := .ptr 104 (some ⟨7⟩)
private def initial (bytes : List (Option UInt8)) : MachineState :=
  { MachineState.empty with
    locals := ValueMap.empty.set ⟨0⟩ pointer
    nextValueId := 40
    memory := ({ Memory.empty with
      allocations := [{ id := ⟨7⟩,base := 104,size := 16,requested := 16,alive := true,origin := .rustStack }]
      nextAddr := 120
      nextAllocId := 8 }).writeImage 104 (ByteImage.ofList bytes) }
private def observation (result : InstrResult × MachineState) :=
  (result.1,result.2.lookupValue ⟨40⟩,result.2.nextValueId)
private def word : List (Option UInt8) := [some 1,some 0,some 0,some 0,some 2,some 0,some 0,some 0]
private def code : List (Option UInt8) := [some 1,some 0,some 0,some 0,some 0,some 0,some 0,some 0]
private def half : List (Option UInt8) := [some 1,some 0,some 0,some 0,none,none,none,none]
private def refusal : Memory → List UInt8 → Except SemError Value :=
  fun _ _ => .error (.typeError "probe decoder refused initialized bytes")

theorem target32_reads_exactly_four_usize_bytes :
    (Sem.run (stepInstWithContext (context .le32) (.Load .Usize ⟨0⟩ false none)) (initial word)).map observation =
      .ok (.value (some ⟨40⟩),some (.int 32 1),41) := rfl

theorem target64_reads_all_eight_usize_bytes :
    (Sem.run (stepInstWithContext (context .le64) (.Load .Usize ⟨0⟩ false none)) (initial word)).map observation =
      .ok (.value (some ⟨40⟩),some (.int 64 8589934593),41) := rfl

theorem target32_ignores_unread_high_half :
    (Sem.run (stepInstWithContext (context .le32) (.Load .Usize ⟨0⟩ false none)) (initial half)).map observation =
      .ok (.value (some ⟨40⟩),some (.int 32 1),41) := rfl

theorem target64_transports_the_actual_partial_image :
    (Sem.run (stepInstWithContext (context .le64) (.Load .Usize ⟨0⟩ false none)) (initial half)).map observation =
      .ok (.value (some ⟨40⟩),some (.partial half),41) := rfl

theorem pointer_decode_recovers_original_memory_provenance (model : ByteModel) :
    (Sem.run (stepInstWithContext (context model) (.Load .Ptr ⟨0⟩ false none))
      (initial [some 104,some 0,some 0,some 0,some 0,some 0,some 0,some 0])).map observation =
      .ok (.value (some ⟨40⟩),some pointer,41) := by
  trustIrCompilerProof {
    cases model <;> rfl
  } {
    cases model <;> trustIrReduce
  }

theorem function_decode_uses_source_order (model : ByteModel) :
    (Sem.run (stepInstWithContext (context model (some [⟨42⟩,⟨7⟩])) (.Load (.Func ⟨0⟩) ⟨0⟩ false none)) (initial code)).map observation =
      .ok (.value (some ⟨40⟩),some (.fnDef ⟨0⟩ ⟨42⟩),41) := by
  cases model <;> rfl

theorem changed_function_order_changes_actual_loaded_identity (model : ByteModel) :
    (Sem.run (stepInstWithContext (context model (some [⟨99⟩,⟨42⟩])) (.Load (.Func ⟨0⟩) ⟨0⟩ false none)) (initial code)).map observation =
      .ok (.value (some ⟨40⟩),some (.fnDef ⟨0⟩ ⟨99⟩),41) := by
  cases model <;> rfl

theorem initialized_function_without_table_is_refused (model : ByteModel) :
    Sem.run (stepInstWithContext (context model) (.Load (.Func ⟨0⟩) ⟨0⟩ false none)) (initial code) =
      .error (.unsupported .layout "function pointer Load requires a source function table") := by
  cases model <;> rfl

theorem null_function_does_not_require_a_table (model : ByteModel) :
    (Sem.run (stepInstWithContext (context model) (.Load (.Func ⟨0⟩) ⟨0⟩ false none))
      (initial [some 0,some 0,some 0,some 0,some 0,some 0,some 0,some 0])).map observation =
      .ok (.value (some ⟨40⟩),some .nullPtr,41) := by
  cases model <;> rfl

theorem initialized_invalid_char_is_refused (model : ByteModel) :
    Sem.run (stepInstWithContext (context model) (.Load .Char ⟨0⟩ false none))
      (initial [some 0,some 216,some 0,some 0]) =
      .error (.ub "memory decode: invalid Unicode scalar value") := by
  cases model <;> rfl

theorem partial_char_keeps_the_partial_transport_path (model : ByteModel) :
    (Sem.run (stepInstWithContext (context model) (.Load .Char ⟨0⟩ false none))
      (initial [none,some 216,some 0,some 0])).map observation =
      .ok (.value (some ⟨40⟩),some (.partial [none,some 216,some 0,some 0]),41) := by
  cases model <;> rfl

theorem initialized_bytes_retain_the_actual_decoder_refusal (model : ByteModel) :
    Sem.run (semLoadValueUsing refusal .U8 pointer false none model) (initial [some 1]) =
      .error (.typeError "probe decoder refused initialized bytes") := by
  cases model <;> rfl

theorem partial_transport_does_not_assume_decoder_success (model : ByteModel) :
    Sem.run (semLoadValueUsing refusal .U8 pointer false none model) (initial [none]) =
      .ok (.partial [none],initial [none]) := by
  cases model <;> rfl

end TrustIr.ScalarLoadExecutionControls
