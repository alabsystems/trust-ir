-- Copyright 2026 Andrew Yates | Apache-2.0
import TrustIr.Proofs.OriginalClosureMemoryReadback
import TrustIr.DecodedEntry

namespace TrustIr.OriginalClosureMemory.ReadbackChecks
open TrustIrEval

private def signature (params returns : List Ty) : FuncTyDef :=
  {params, returns, isVararg := false}
private def function (id ty : Nat) (params : List (ValueId × Ty))
    (body : List Inst) (results : List (List ValueId)) (returns : List ValueId) : Function :=
  {id := ⟨id⟩, name := "closure-readback-source", ty := ⟨ty⟩, entry := ⟨0⟩,
   isDeclaration := false, blocks := .ok [(⟨0⟩,
     {params, body, bodyResultDests := results, terminator := .Return returns})]}

private def captured (ty : Ty) : Module :=
  {hasTargetInfo := true
   functions := [function 7 1 [(⟨0⟩,ty)] [] [] [⟨0⟩],
     function 8 2 [(⟨0⟩,.Ptr)]
       [.Load (.Closure ⟨0⟩) ⟨0⟩ false none, .CallIndirect ⟨1⟩ ⟨0⟩ [] .C]
       [[⟨1⟩],[⟨2⟩]] [⟨2⟩],
     function 9 3 [(⟨0⟩,ty)] [.MakeClosure ⟨0⟩ ⟨7⟩ [⟨0⟩],
       .Alloca (.Closure ⟨0⟩) none none, .Store (.Closure ⟨0⟩) ⟨2⟩ ⟨1⟩ false none,
       .Call ⟨8⟩ [⟨2⟩]] [[⟨1⟩],[⟨2⟩],[],[⟨3⟩]] [⟨3⟩]]
   funcTys := [signature [] [ty],signature [ty] [ty],signature [.Ptr] [ty],signature [ty] [ty]]
   closureTys := [{func := ⟨0⟩,captures := [ty]}]
   closureLayouts := [{closure := ⟨0⟩,size := 16,align := 8,captureOffsets := [8]}]
   globals := [],enums := [],structs := [],types := []}

private def allocated : MachineState :=
  let (_,memory) := Memory.empty.alloc 16 8 0 .rustStack
  {MachineState.empty with memory}
private def pointer : Value := .ptr 1024 (some ⟨0⟩)
private def integerInput : Value := .typedClosure ⟨0⟩ ⟨7⟩ [.int 64 18446744073709551658]
private def pointerInput : Value := .typedClosure ⟨0⟩ ⟨7⟩ [.ptr 1032 (some ⟨99⟩)]
/-- Retain the actual production state, not a guessed compact image. Each
success control below proves the error/default branch is unreachable. -/
private def stored (source : Module) (value : Value) : MachineState :=
  match Sem.run (storeValue (prepare source .le64 []) none ⟨0⟩ pointer value) allocated with
  | .ok (_,after) => after
  | .error _ => allocated
private def integerState := stored (captured .U64) integerInput
private def pointerState := stored (captured .Ptr) pointerInput

private theorem query64 :
    (AggregateMemory.prepare (layoutSourceOf (captured .U64) .le64) []).query .U64 =
      .ok (.leaf .U64 ⟨8,8⟩) := by
  trustIrCompilerProof {rfl} {trustIrReduce}
private theorem queryPtr :
    (AggregateMemory.prepare (layoutSourceOf (captured .Ptr) .le64) []).query .Ptr =
      .ok (.leaf .Ptr ⟨8,8⟩) := by
  trustIrCompilerProof {rfl} {trustIrReduce}

private theorem integerAdmitted :
    CaptureReadbackInputs (captured .U64) .le64 [] none integerState.memory ⟨0⟩
      [.int 64 18446744073709551658] := by
  intro nominal actual position ty input plan typeRow inputRow queried
  change some {func := ⟨0⟩,captures := [.U64]} = some nominal at actual
  cases actual
  cases position with
  | zero =>
    cases typeRow
    cases inputRow
    rw [query64] at queried
    cases queried
    exact .scalar (.integer .U64 ⟨8,8⟩ 64 _ rfl rfl rfl)
  | succ n => cases n <;> cases typeRow

private theorem pointerAdmitted :
    CaptureReadbackInputs (captured .Ptr) .le64 [] none pointerState.memory ⟨0⟩
      [.ptr 1032 (some ⟨99⟩)] := by
  intro nominal actual position ty input plan typeRow inputRow queried
  change some {func := ⟨0⟩,captures := [.Ptr]} = some nominal at actual
  cases actual
  cases position with
  | zero =>
    cases typeRow
    cases inputRow
    rw [queryPtr] at queried
    cases queried
    exact .scalar (.pointer .Ptr ⟨8,8⟩ 1032 (some ⟨99⟩) rfl (by decide) rfl)
  | succ n => cases n <;> cases typeRow

private theorem leafQueries64 : CaptureLeafQueries (captured .U64) .le64 [] ⟨0⟩ := by
  intro nominal actual ty present plan queried
  change some {func := ⟨0⟩,captures := [.U64]} = some nominal at actual
  cases actual
  have same : ty = .U64 := by
    rcases List.mem_cons.mp present with same | absent
    · exact same
    · cases absent
  subst ty
  rw [query64] at queried
  cases queried
  exact ⟨.U64,⟨8,8⟩,rfl⟩
private theorem leafQueriesPtr : CaptureLeafQueries (captured .Ptr) .le64 [] ⟨0⟩ := by
  intro nominal actual ty present plan queried
  change some {func := ⟨0⟩,captures := [.Ptr]} = some nominal at actual
  cases actual
  have same : ty = .Ptr := by
    rcases List.mem_cons.mp present with same | absent
    · exact same
    · cases absent
  subst ty
  rw [queryPtr] at queried
  cases queried
  exact ⟨.Ptr,⟨8,8⟩,rfl⟩

theorem actual_noncanonical_integer_store :
    Sem.run (storeValue (prepare (captured .U64) .le64 []) none ⟨0⟩ pointer integerInput)
      allocated = .ok ((),integerState) := by
  trustIrCompilerProof {rfl} {trustIrReduce}

theorem actual_noncanonical_integer_load :
    Sem.run (loadValue (prepare (captured .U64) .le64 []) none ⟨0⟩ pointer) integerState =
      .ok (.typedClosure ⟨0⟩ ⟨7⟩ [.int 64 42],integerState) := by
  trustIrCompilerProof {rfl} {trustIrReduce}

/-- Apply the general execution theorem to an actual noncanonical raw input;
the conclusion retains the original checked Binding and canonical residue. -/
theorem general_law_derives_integer_readback :
    ∃ binding : ClosureStorage.Binding (captured .U64) ⟨0⟩,
      ValueReadback (captured .U64) ⟨0⟩ binding .le64 integerState.memory integerInput
        (.typedClosure ⟨0⟩ ⟨7⟩ [.int 64 42]) := by
  obtain ⟨binding,output,loaded,related⟩ := prepared_store_load_readback (captured .U64) .le64 [] none
    ⟨0⟩ ⟨0⟩ ⟨7⟩ [.int 64 18446744073709551658] pointer false none allocated integerState
    integerAdmitted leafQueries64 actual_noncanonical_integer_store
  rw [actual_noncanonical_integer_load] at loaded
  cases loaded
  exact ⟨binding,related⟩

theorem actual_pointer_store :
    Sem.run (storeValue (prepare (captured .Ptr) .le64 []) none ⟨0⟩ pointer pointerInput)
      allocated = .ok ((),pointerState) := by
  trustIrCompilerProof {rfl} {trustIrReduce}

theorem actual_pointer_load_uses_receiving_provenance :
    Sem.run (loadValue (prepare (captured .Ptr) .le64 []) none ⟨0⟩ pointer) pointerState =
      .ok (.typedClosure ⟨0⟩ ⟨7⟩ [.ptr 1032 (some ⟨0⟩)],pointerState) := by
  trustIrCompilerProof {rfl} {trustIrReduce}

theorem general_law_derives_receiving_pointer_readback :
    ∃ binding : ClosureStorage.Binding (captured .Ptr) ⟨0⟩,
      ValueReadback (captured .Ptr) ⟨0⟩ binding .le64 pointerState.memory pointerInput
        (.typedClosure ⟨0⟩ ⟨7⟩ [.ptr 1032 (some ⟨0⟩)]) := by
  obtain ⟨binding,output,loaded,related⟩ := prepared_store_load_readback (captured .Ptr) .le64 [] none
    ⟨0⟩ ⟨0⟩ ⟨7⟩ [.ptr 1032 (some ⟨99⟩)] pointer false none allocated pointerState
    pointerAdmitted leafQueriesPtr actual_pointer_store
  rw [actual_pointer_load_uses_receiving_provenance] at loaded
  cases loaded
  exact ⟨binding,related⟩

theorem padding_remains_unwritten : integerState.memory.bytes 1024 = none := by
  trustIrCompilerProof {rfl} {trustIrReduce}

theorem padding_change_does_not_change_capture :
    let changed := {integerState with memory := integerState.memory.writeImage 1024 (.ofList [some 77])}
    (Sem.run (loadValue (prepare (captured .U64) .le64 []) none ⟨0⟩ pointer) changed).map Prod.fst =
      .ok (.typedClosure ⟨0⟩ ⟨7⟩ [.int 64 42]) := by
  trustIrCompilerProof {rfl} {trustIrReduce}

theorem covered_byte_change_changes_capture :
    let changed := {integerState with memory := integerState.memory.writeImage 1032 (.ofList [some 41])}
    (Sem.run (loadValue (prepare (captured .U64) .le64 []) none ⟨0⟩ pointer) changed).map Prod.fst =
      .ok (.typedClosure ⟨0⟩ ⟨7⟩ [.int 64 41]) := by
  trustIrCompilerProof {rfl} {trustIrReduce}

theorem real_allocation_lifetimes_and_frontiers_preserved :
    ∃ binding : ClosureStorage.Binding (captured .U64) ⟨0⟩,
      ∃ address allocation, pointer = .ptr address (some allocation) ∧
        integerState.memory.allocations = allocated.memory.allocations ∧
        integerState.memory.nextAddr = allocated.memory.nextAddr ∧
        integerState.memory.nextAllocId = allocated.memory.nextAllocId ∧
        ∀ query, query < address ∨ address + binding.shape.size ≤ query →
          integerState.memory.bytes query = allocated.memory.bytes query := by
  obtain ⟨binding,_nominal,_target,address,allocation,pointed,allocs,nextAddr,nextId,outside⟩ :=
    prepared_store_memory_locality (captured .U64) .le64 [] none ⟨0⟩ ⟨0⟩ ⟨7⟩
      [.int 64 18446744073709551658] pointer false none allocated integerState actual_noncanonical_integer_store
  exact ⟨binding,address,allocation,pointed,allocs,nextAddr,nextId,outside⟩

/-- Original public conversion caller remains connected through real borrowed
pointer, direct callee Load and indirect target invocation. -/
theorem public_borrowed_callee_uses_padded_capture :
    (match runDecodedModule (captured .U64) 16 [] 32 .abort ⟨9⟩ [.int 64 42] with
      | .evaluated run => run.map Prod.fst
      | _ => .error (.typeError "control did not evaluate")) = .ok [.int 64 42] := by
  trustIrCompilerProof {rfl} {trustIrReduce}

private def empty : Module :=
  {captured .U64 with
   functions := [function 7 0 [] [.Const .U64 (.int 37)] [[⟨0⟩]] [⟨0⟩],
     function 8 1 [(⟨0⟩,.Ptr)]
       [.Load (.Closure ⟨0⟩) ⟨0⟩ false (some 1),.CallIndirect ⟨1⟩ ⟨0⟩ [] .C]
       [[⟨1⟩],[⟨2⟩]] [⟨2⟩],
     function 9 0 [] [.MakeClosure ⟨0⟩ ⟨7⟩ [],.Alloca (.Closure ⟨0⟩) none (some 1),
       .Store (.Closure ⟨0⟩) ⟨1⟩ ⟨0⟩ false (some 1),.Call ⟨8⟩ [⟨1⟩]]
       [[⟨0⟩],[⟨1⟩],[],[⟨2⟩]] [⟨2⟩]]
   funcTys := [signature [] [.U64],signature [.Ptr] [.U64]]
   closureTys := [{func := ⟨0⟩,captures := []}]
   closureLayouts := [{closure := ⟨0⟩,size := 0,align := 1,captureOffsets := []}]}

private theorem emptyAdmitted :
    CaptureReadbackInputs empty .le64 [] none allocated.memory ⟨0⟩ [] := by
  intro nominal actual position ty input plan typeRow
  change some {func := ⟨0⟩,captures := []} = some nominal at actual
  cases actual
  cases position <;> cases typeRow
private theorem emptyLeaves : CaptureLeafQueries empty .le64 [] ⟨0⟩ := by
  intro nominal actual ty present
  change some {func := ⟨0⟩,captures := []} = some nominal at actual
  cases actual
  cases present

theorem actual_zero_store_retains_live_allocation_and_entire_state :
    Sem.run (storeValue (prepare empty .le64 []) none ⟨0⟩ pointer (.typedClosure ⟨0⟩ ⟨7⟩ []))
      allocated = .ok ((),allocated) := by
  trustIrCompilerProof {rfl} {trustIrReduce}

theorem general_law_derives_actual_zero_byte_readback :
    ∃ (binding : ClosureStorage.Binding empty ⟨0⟩) (output : Value),
      Sem.run (loadValue (prepare empty .le64 []) none ⟨0⟩ pointer) allocated = .ok (output,allocated) ∧
      ValueReadback empty ⟨0⟩ binding .le64 allocated.memory (.typedClosure ⟨0⟩ ⟨7⟩ []) output :=
  prepared_store_load_readback empty .le64 [] none ⟨0⟩ ⟨0⟩ ⟨7⟩ [] pointer false none allocated allocated
    emptyAdmitted emptyLeaves actual_zero_store_retains_live_allocation_and_entire_state

theorem public_borrowed_empty_closure_still_calls_real_target :
    (match runDecodedModule empty 16 [] 32 .abort ⟨9⟩ [] with
      | .evaluated run => run.map Prod.fst
      | _ => .error (.typeError "control did not evaluate")) = .ok [.int 64 37] := by
  trustIrCompilerProof {rfl} {trustIrReduce}

/-- False targets for independent fresh-kernel hostile substitutions. -/
def WrongRawIntegerEquality : Prop :=
    (Sem.run (loadValue (prepare (captured .U64) .le64 []) none ⟨0⟩ pointer) integerState).map Prod.fst = .ok integerInput
def WrongRetainedProvenance : Prop :=
    (Sem.run (loadValue (prepare (captured .Ptr) .le64 []) none ⟨0⟩ pointer) pointerState).map Prod.fst = .ok pointerInput
def WrongCoveredByteInvariant : Prop :=
    let changed := {integerState with memory := integerState.memory.writeImage 1032 (.ofList [some 41])}
    (Sem.run (loadValue (prepare (captured .U64) .le64 []) none ⟨0⟩ pointer) changed).map Prod.fst =
      .ok (.typedClosure ⟨0⟩ ⟨7⟩ [.int 64 42])

end TrustIr.OriginalClosureMemory.ReadbackChecks
