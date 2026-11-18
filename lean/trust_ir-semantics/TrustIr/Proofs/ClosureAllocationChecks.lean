-- Copyright 2026 Andrew Yates | Apache-2.0
import TrustIr.Proofs.ContextualAllocationChecks
import TrustIr.Semantics.Eval

namespace TrustIr.ContextualAllocation.ClosureChecks

private def source (captures : List Ty) (size alignment : Nat) (offsets : List Nat) :
    SourceLayout.Environment :=
  { hasTargetInfo := true
    closures := [{ func := ⟨0⟩, captures }]
    closureLayouts := [{ closure := ⟨0⟩, size, align := alignment, captureOffsets := offsets }] }

private def emptySource := source [] 0 1 []
private def wordSource := source [.U64] 8 8 [0]

/-- Both the value source and the private prepared memory service use these
actual finite source rows. This fixture grants no function/body/ABI validity. -/
private def context (rows : SourceLayout.Environment) : EvalContext :=
  { EvalContext.empty with
    valueSource := FunctionItemPresence.prepare { closures := rows.closures }
    memoryService := some (AggregateMemory.prepare rows [.Closure ⟨0⟩]) }

private def emptyAfter := (result MachineState.empty 0 1).2

/-- The actual production instruction dispatcher now allocates nominal
storage, retaining the real zero-byte record, pointer and owned permission. -/
theorem actual_empty_nominal_alloca :
    Sem.run (stepInstWithContext (context emptySource)
      (.Alloca (.Closure ⟨0⟩) none (some 1))) MachineState.empty =
      .ok (.value (some ⟨0⟩), emptyAfter) := by
  trustIrCompilerProof { rfl } { trustIrReduce }

theorem actual_word_nominal_alloca :
    Sem.run (stepInstWithContext (context wordSource)
      (.Alloca (.Closure ⟨0⟩) none none)) MachineState.empty =
      .ok (.value (some ⟨0⟩), (result MachineState.empty 8 8).2) := by
  trustIrCompilerProof { rfl } { trustIrReduce }

theorem actual_empty_nominal_record :
    emptyAfter.memory.lookup ⟨0⟩ =
      some { id := ⟨0⟩, base := 1024, size := 0, requested := 0, alive := true, origin := .rustStack } := rfl

theorem actual_empty_nominal_pointer :
    emptyAfter.lookupValue ⟨0⟩ = some (.ptr 1024 (some ⟨0⟩)) := rfl

theorem original_execution_layout_stays_refused :
    (context emptySource).memoryLayout (.Closure ⟨0⟩) =
      .error (.unsupported .layout
        s!"memory: {repr (SourceLayout.Error.unsupported (.Closure ⟨0⟩))}") := by
  trustIrCompilerProof { rfl } { trustIrReduce }

theorem allocated_nominal_load_stays_refused :
    Sem.run (AggregateMemory.loadValue
      (AggregateMemory.prepare emptySource [.Closure ⟨0⟩]) none
      (.Closure ⟨0⟩) (.ptr 1024 (some ⟨0⟩)) false (some 1)) emptyAfter =
      .error (.unsupported .layout
        s!"memory: {repr (SourceLayout.Error.unsupported (.Closure ⟨0⟩))}") := by
  trustIrCompilerProof { rfl } { trustIrReduce }

/-- Even an empty byte footprint cannot supply a logical/code identity. -/
theorem allocated_nominal_store_stays_refused (target : FuncId) :
    Sem.run (AggregateMemory.storeValue
      (AggregateMemory.prepare emptySource [.Closure ⟨0⟩]) none
      (.Closure ⟨0⟩) (.ptr 1024 (some ⟨0⟩)) (.typedClosure ⟨0⟩ target [])
      false (some 1)) emptyAfter =
      .error (.unsupported .layout
        s!"memory: {repr (SourceLayout.Error.unsupported (.Closure ⟨0⟩))}") := by
  trustIrCompilerProof { rfl } { trustIrReduce }

theorem heap_nominal_route_stays_refused :
    Sem.run (stepInstWithContext (context emptySource)
      (.HeapAlloc (.Closure ⟨0⟩) none (some 1) .RustHeap)) MachineState.empty =
      .error (.unsupported .layout
        s!"memory: {repr (SourceLayout.Error.unsupported (.Closure ⟨0⟩))}") := by
  trustIrCompilerProof { rfl } { trustIrReduce }

theorem missing_nominal_source_refuses :
    (context {}).allocationLayout (.Closure ⟨0⟩) =
      .error (.typeError s!"memory layout: {repr (SourceLayout.Error.missingClosure 0)}") := by
  trustIrCompilerProof { rfl } { trustIrReduce }

theorem absent_target_metadata_refuses :
    (context { emptySource with hasTargetInfo := false }).allocationLayout (.Closure ⟨0⟩) =
      .error (.typeError s!"memory layout: {repr (SourceLayout.Error.missingTarget "closure")}") := by
  trustIrCompilerProof { rfl } { trustIrReduce }

theorem misaligned_capture_descriptor_refuses :
    (context (source [.U64] 8 8 [1])).allocationLayout (.Closure ⟨0⟩) =
      .error (.typeError s!"memory layout: {repr (SourceLayout.Error.incoherent "closure" 0)}") := by
  trustIrCompilerProof { rfl } { trustIrReduce }

theorem missing_capture_offset_refuses :
    (context (source [.U64] 8 8 [])).allocationLayout (.Closure ⟨0⟩) =
      .error (.typeError s!"memory layout: {repr (SourceLayout.Error.incoherent "closure" 0)}") := by
  trustIrCompilerProof { rfl } { trustIrReduce }

theorem source_target_mismatch_refuses :
    (context { emptySource with model := .le32 }).allocationLayout (.Closure ⟨0⟩) =
      .error (.typeError "memory: source layout target does not match evaluator target") := by
  trustIrCompilerProof { rfl } { trustIrReduce }

theorem actual_nominal_zero_alignment_refuses :
    Sem.run (stepInstWithContext (context emptySource)
      (.Alloca (.Closure ⟨0⟩) none (some 0))) MachineState.empty =
      .error (.typeError "Alloca: alignment must be a nonzero u64 power of two") := by
  trustIrCompilerProof { rfl } { trustIrReduce }

/-- Dynamic operand retrieval still occurs before asking for source layout. -/
theorem actual_missing_count_precedes_bad_source :
    Sem.run (stepInstWithContext (context {})
      (.Alloca (.Closure ⟨0⟩) (some ⟨8⟩) (some 0))) MachineState.empty =
      .error (.typeError s!"undefined SSA value: {repr (⟨8⟩ : ValueId)}") := rfl

private def countedContext (rows : SourceLayout.Environment) (declared : Ty) : EvalContext :=
  { context rows with
    localTypes := some (fun id => if id == (⟨7⟩ : ValueId) then some declared else none) }

private def countState (value : Value) : MachineState :=
  { MachineState.empty with
    locals := ValueMap.empty.set ⟨7⟩ value
    nextValueId := 8 }

theorem actual_typed_count_one_succeeds :
    Sem.run (stepInstWithContext (countedContext wordSource .U64)
      (.Alloca (.Closure ⟨0⟩) (some ⟨7⟩) none)) (countState (.int 64 1)) =
      .ok (.value (some ⟨8⟩), (result (countState (.int 64 1)) 8 8).2) := by
  trustIrCompilerProof { rfl } { trustIrReduce }

/-- The same carrier is refused when its original SSA declaration differs. -/
theorem actual_wrong_count_declaration_refuses :
    Sem.run (stepInstWithContext (countedContext wordSource .U8)
      (.Alloca (.Closure ⟨0⟩) (some ⟨7⟩) none)) (countState (.int 64 1)) =
      .error (.typeError "typed integer: carrier width mismatch") := by
  trustIrCompilerProof { rfl } { trustIrReduce }

theorem actual_zero_nominal_wide_count_refuses :
    Sem.run (stepInstWithContext (countedContext emptySource .U128)
      (.Alloca (.Closure ⟨0⟩) (some ⟨7⟩) none))
      (countState (.int 128 (Int.ofNat word64Limit))) =
      .error (.ub "Alloca: integer operand exceeds u64") := by
  trustIrCompilerProof { rfl } { trustIrReduce }

theorem actual_nominal_size_multiplication_overflow_refuses :
    Sem.run (stepInstWithContext (countedContext wordSource .U64)
      (.Alloca (.Closure ⟨0⟩) (some ⟨7⟩) none))
      (countState (.int 64 (Int.ofNat word64Max))) =
      .error (.ub "Alloca: byte size multiplication overflows u64") := by
  trustIrCompilerProof { rfl } { trustIrReduce }

theorem actual_nominal_alignment_overflow_refuses :
    Sem.run (stepInstWithContext (context emptySource)
      (.Alloca (.Closure ⟨0⟩) none (some word64Limit))) MachineState.empty =
      .error (.typeError "Alloca: alignment must be a nonzero u64 power of two") := by
  trustIrCompilerProof { rfl } { trustIrReduce }

/-- A valid nominal-zero table cannot supply nominal one's storage layout. -/
theorem wrong_nominal_cannot_borrow_valid_source_layout :
    (context wordSource).allocationLayout (.Closure ⟨1⟩) =
      .error (.typeError s!"memory layout: {repr (SourceLayout.Error.missingClosure 1)}") := by
  trustIrCompilerProof { rfl } { trustIrReduce }

theorem duplicate_nominal_descriptor_refuses :
    (context { emptySource with closureLayouts := emptySource.closureLayouts ++ emptySource.closureLayouts }).allocationLayout (.Closure ⟨0⟩) =
      .error (.typeError s!"memory layout: {repr (SourceLayout.Error.incoherent "closure" 0)}") := by
  trustIrCompilerProof { rfl } { trustIrReduce }

def WrongNominalPointer : Prop := emptyAfter.lookupValue ⟨0⟩ = some (.ptr 1024 none)

def WrongNominalLayoutPermission : Prop :=
  (context emptySource).memoryLayout (.Closure ⟨0⟩) = .ok ⟨0, 1⟩

end TrustIr.ContextualAllocation.ClosureChecks
