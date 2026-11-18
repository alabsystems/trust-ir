-- Copyright 2026 Andrew Yates | Apache-2.0
import TrustIr.Proofs.ContextualAllocation
import TrustIr.Semantics.AggregateAccess

namespace TrustIr.ContextualAllocation.Checks

private def unitResult : ValueId × MachineState := result MachineState.empty 0 1

/-- Even an empty source value has a real allocation and provenance. -/
theorem empty_value_allocates :
    Sem.run (semAlloca .Unit none (some 1)) MachineState.empty = .ok unitResult := rfl

theorem empty_value_record :
    unitResult.2.memory.lookup ⟨0⟩ =
      some { id := ⟨0⟩, base := 1024, size := 0, requested := 0, alive := true, origin := .rustStack } := rfl

theorem empty_value_pointer :
    unitResult.2.lookupValue unitResult.1 = some (.ptr 1024 (some ⟨0⟩)) := rfl

theorem successive_empty_values_are_distinct :
    (Sem.run (do
      let first ← semAlloca .Unit none (some 1)
      let second ← semAlloca .Unit none (some 1)
      let a ← Sem.lookupValue first
      let b ← Sem.lookupValue second
      pure (a, b)) MachineState.empty).map Prod.fst =
        .ok (.ptr 1024 (some ⟨0⟩), .ptr 1025 (some ⟨1⟩)) := rfl

theorem layout_error_precedes_bad_alignment (before : MachineState) (error : SemError) :
    Sem.run (semAllocaUsing (fun _ => .error error) unknownIntegerOperand .Unit
      none (some 0) .le64) before = .error error := rfl

theorem empty_value_zero_alignment_refuses (before : MachineState) :
    Sem.run (semAlloca .Unit none (some 0)) before =
      .error (.typeError "Alloca: alignment must be a nonzero u64 power of two") := rfl

private def exhaustedIdentity : MachineState :=
  { MachineState.empty with memory := { Memory.empty with nextAllocId := word64Max } }

theorem empty_value_exhausted_identity_refuses :
    Sem.run (semAlloca .Unit none (some 1)) exhaustedIdentity =
      .error (.ub "allocation identifier increment overflows u64") := rfl

private def exhaustedAddress : MachineState :=
  { MachineState.empty with memory := { Memory.empty with nextAddr := word64Max } }

theorem empty_value_exhausted_address_refuses :
    Sem.run (semAlloca .Unit none (some 1)) exhaustedAddress =
      .error (.outOfMemory "allocation next-address increment exceeds u64") := rfl

private def occupiedResult : MachineState :=
  { MachineState.empty with locals := ValueMap.empty.set ⟨0⟩ (.bool true) }

/-- Publishing at the next SSA id is not unconditional SSA freshness. -/
theorem occupied_result_slot_is_overwritten :
    (result occupiedResult 0 1).2.lookupValue ⟨0⟩ =
      some (.ptr 1024 (some ⟨0⟩)) := rfl

private def target32Limit : MachineState :=
  { MachineState.empty with memory := { Memory.empty with nextAddr := ByteModel.le32.addressLimit } }

theorem empty_value_target32_limit_refuses :
    Sem.run (semAlloca .Unit none (some 1) .le32) target32Limit =
      .error (.outOfMemory "allocation exceeds the target address space") := rfl

theorem empty_value_same_address_fits_target64 :
    Sem.run (semAlloca .Unit none (some 1) .le64) target32Limit =
      .ok (result target32Limit 0 1) := rfl

/-- The no-count theorem does not erase a real dynamic-count operand. -/
theorem missing_count_precedes_layout (error : SemError) :
    Sem.run (semAllocaUsing (fun _ => .error error) unknownIntegerOperand .Unit
      (some ⟨8⟩) (some 0) .le64) MachineState.empty =
      .error (.typeError s!"undefined SSA value: {repr (⟨8⟩ : ValueId)}") := rfl

private def nominalSource : SourceLayout.Environment :=
    { hasTargetInfo := true
      closures := [{ func := ⟨0⟩, captures := [] }]
      closureLayouts := [{ closure := ⟨0⟩, size := 0, align := 1, captureOffsets := [] }] }

private def nominalService : AggregateMemory.Service :=
  AggregateMemory.prepare nominalSource
    [.Closure ⟨0⟩]

/-- The same table is valid for its original source shape question, so the
execution refusal below cannot pass because of unrelated malformed metadata. -/
theorem nominal_table_has_valid_shape :
    ((SourceLayout.prepare nominalSource).query .shape (.Closure ⟨0⟩)).map
      (fun row => (row.1.size, row.1.align)) = .ok (0, some 1) := by
  trustIrCompilerProof { rfl } { trustIrReduce }

/-- Pin the exact unsupported-Closure error of the existing execution mode. -/
theorem nominal_table_exact_execution_refusal :
    AggregateMemory.layoutQuery nominalService .le64 (.Closure ⟨0⟩) =
      .error (.unsupported .layout
        s!"memory: {repr (SourceLayout.Error.unsupported (.Closure ⟨0⟩))}") := by
  trustIrCompilerProof { rfl } { trustIrReduce }

/-- A real canonical prepared nominal table is still outside the direct
closure execution-layout slice. This control must remain a refusal until a
separate storage-layout/codec contract is established, not be retagged Unit. -/
theorem nominal_table_does_not_create_execution_layout :
    (AggregateMemory.layoutQuery nominalService .le64 (.Closure ⟨0⟩)).isOk = false := by
  trustIrCompilerProof { rfl } { trustIrReduce }

/-- A false observation retained for independent kernel rejection controls. -/
def WrongEmptyPointer : Prop :=
  unitResult.2.lookupValue unitResult.1 = some (.ptr 1024 none)

def WrongEmptyNoAllocation : Prop := unitResult.2.memory.allocations = []

def WrongPreservedOccupiedSlot : Prop :=
  (result occupiedResult 0 1).2.lookupValue ⟨0⟩ = some (.bool true)

end TrustIr.ContextualAllocation.Checks
