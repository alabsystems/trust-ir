-- Copyright 2026 Andrew Yates | Apache-2.0
import TrustIr.DecodedEntry

namespace TrustIr.OriginalClosureMemory.Checks
open TrustIrEval

private def signature (params returns : List Ty) : FuncTyDef :=
  {params, returns, isVararg := false}

private def function (id ty : Nat) (params : List (ValueId × Ty))
    (body : List Inst) (results : List (List ValueId)) (returns : List ValueId) : Function :=
  {id := ⟨id⟩, name := "original-closure-memory", ty := ⟨ty⟩, entry := ⟨0⟩,
   isDeclaration := false, blocks := .ok [(⟨0⟩,
     {params, body, bodyResultDests := results, terminator := .Return returns})]}

private def scalarTarget (id value : Nat) : Function :=
  function id 0 [] [.Const .U64 (.int value)] [[⟨0⟩]] [⟨0⟩]

private def borrower : Function :=
  function 8 1 [(⟨0⟩, .Ptr)]
    [.Load (.Closure ⟨0⟩) ⟨0⟩ false (some 1), .CallIndirect ⟨1⟩ ⟨0⟩ [] .C]
    [[⟨1⟩], [⟨2⟩]] [⟨2⟩]

private def caller : Function :=
  function 9 0 []
    [.MakeClosure ⟨0⟩ ⟨7⟩ [], .Alloca (.Closure ⟨0⟩) none (some 1),
     .Store (.Closure ⟨0⟩) ⟨1⟩ ⟨0⟩ false (some 1), .Call ⟨8⟩ [⟨1⟩]]
    [[⟨0⟩], [⟨1⟩], [], [⟨2⟩]] [⟨2⟩]

private def registerEntry : Function :=
  function 11 2 [(⟨0⟩, .Closure ⟨0⟩)] [.CallIndirect ⟨0⟩ ⟨0⟩ [] .C] [[⟨1⟩]] [⟨1⟩]

private def parameterStore : Function :=
  function 12 2 [(⟨0⟩, .Closure ⟨0⟩)]
    [.Alloca (.Closure ⟨0⟩) none (some 1), .Store (.Closure ⟨0⟩) ⟨1⟩ ⟨0⟩ false (some 1),
     .Const .U64 (.int 0)] [[⟨1⟩], [], [⟨2⟩]] [⟨2⟩]

private def returnedStore : Function :=
  function 14 2 [(⟨0⟩, .Closure ⟨0⟩)]
    [.Call ⟨13⟩ [⟨0⟩], .Alloca (.Closure ⟨0⟩) none (some 1),
     .Store (.Closure ⟨0⟩) ⟨2⟩ ⟨1⟩ false (some 1), .Const .U64 (.int 0)]
    [[⟨1⟩], [⟨2⟩], [], [⟨3⟩]] [⟨3⟩]

private def original : Module :=
  {hasTargetInfo := true
   functions := [scalarTarget 7 37, borrower, caller, scalarTarget 10 99, registerEntry,
     parameterStore, function 13 3 [(⟨0⟩, .Closure ⟨0⟩)] [] [] [⟨0⟩], returnedStore]
   funcTys := [signature [] [.U64], signature [.Ptr] [.U64],
     signature [.Closure ⟨0⟩] [.U64], signature [.Closure ⟨0⟩] [.Closure ⟨0⟩]]
   closureTys := [{func := ⟨0⟩, captures := []}]
   closureLayouts := [{closure := ⟨0⟩, size := 0, align := 1, captureOffsets := []}]
   globals := [], enums := [], structs := [], types := []}

private def runValues (source : Module) (entry : Nat) (args : List Value := []) :
    Except SemError (List Value) :=
  match runDecodedModule source 16 [] 32 .abort ⟨entry⟩ args with
  | .evaluated result => result.map Prod.fst
  | _ => .error (.typeError "control did not reach actual evaluation")

/-- The actual public conversion/entry caller: the closure's real pointer
crosses a direct call, the callee loads it, then calls its original target. -/
theorem actual_borrowed_empty_closure_calls_original_target :
    runValues original 9 = .ok [.int 64 37] := by
  trustIrCompilerProof { rfl } { trustIrReduce }

/-- Constructor uniformity is a storage profile, not a restriction silently
applied to arbitrary imported register values. Target 10 has the same complete
physical signature but is not the module's storage constructor target 7. -/
theorem imported_same_nominal_value_keeps_its_actual_register_target :
    runValues original 11 [.typedClosure ⟨0⟩ ⟨10⟩ []] = .ok [.int 64 99] := by
  trustIrCompilerProof { rfl } { trustIrReduce }

theorem imported_parameter_cannot_be_relabelled_by_zero_byte_store :
    runValues original 12 [.typedClosure ⟨0⟩ ⟨10⟩ []] =
      .error (.typeError "closure Store nominal, target or capture count mismatch") := by
  trustIrCompilerProof { rfl } { trustIrReduce }

theorem returned_same_nominal_value_cannot_be_relabelled_by_storage :
    runValues original 14 [.typedClosure ⟨0⟩ ⟨10⟩ []] =
      .error (.typeError "closure Store nominal, target or capture count mismatch") := by
  trustIrCompilerProof { rfl } { trustIrReduce }

private def captured : Module :=
  {original with
   functions := [function 7 1 [(⟨0⟩, .U64)] [] [] [⟨0⟩],
     function 8 2 [(⟨0⟩, .Ptr)]
       [.Load (.Closure ⟨0⟩) ⟨0⟩ false none, .CallIndirect ⟨1⟩ ⟨0⟩ [] .C]
       [[⟨1⟩], [⟨2⟩]] [⟨2⟩],
     function 9 0 [] [.Const .U64 (.int 42), .MakeClosure ⟨0⟩ ⟨7⟩ [⟨0⟩],
       .Alloca (.Closure ⟨0⟩) none none, .Store (.Closure ⟨0⟩) ⟨2⟩ ⟨1⟩ false none,
       .Call ⟨8⟩ [⟨2⟩]] [[⟨0⟩], [⟨1⟩], [⟨2⟩], [], [⟨3⟩]] [⟨3⟩]]
   funcTys := [signature [] [.U64], signature [.U64] [.U64], signature [.Ptr] [.U64]]
   closureTys := [{func := ⟨0⟩, captures := [.U64]}]
   closureLayouts := [{closure := ⟨0⟩, size := 16, align := 8, captureOffsets := [8]}]}

theorem captured_closure_uses_real_child_codec_offset_and_callee_prefix :
    runValues captured 9 = .ok [.int 64 42] := by
  trustIrCompilerProof { rfl } { trustIrReduce }

private def service := prepare original .le64 []
private def capturedService := prepare captured .le64 []
private def allocated (size alignment : Nat) : MachineState :=
  let (_, memory) := Memory.empty.alloc size alignment 0 .rustStack
  {MachineState.empty with memory}
private def heldPointer : Value := .ptr 1024 (some ⟨0⟩)

/-- Pin reference-interpreter behavior rather than inventing an initialization
bit: an empty environment has no covered capture bytes. Source binding plus
the real allocation is still required, and no unrestricted-memory claim follows. -/
theorem zero_byte_unwritten_storage_has_source_bound_singleton_value :
    Sem.run (loadValue service none ⟨0⟩ heldPointer) (allocated 0 1) =
      .ok (.typedClosure ⟨0⟩ ⟨7⟩ [], allocated 0 1) := by
  trustIrCompilerProof { rfl } { trustIrReduce }

theorem zero_byte_unknown_allocation_still_refuses :
    Sem.run (loadValue service none ⟨0⟩ heldPointer) MachineState.empty =
      .error (.ub "Load: unknown allocation") := by
  trustIrCompilerProof { rfl } { trustIrReduce }

theorem zero_byte_wrong_provenance_still_refuses :
    Sem.run (loadValue service none ⟨0⟩ (.ptr 1024 none)) (allocated 0 1) =
      .error (.ub "Load: pointer value 1024 has no allocation provenance") := by
  trustIrCompilerProof { rfl } { trustIrReduce }

theorem nonempty_unwritten_capture_still_refuses :
    Sem.run (loadValue capturedService none ⟨0⟩ heldPointer) (allocated 16 8) =
      .error (.ub "Load: reading uninitialized covered memory") := by
  trustIrCompilerProof { rfl } { trustIrReduce }

theorem wrong_target_store_refuses_even_with_same_nominal_and_capture_shape :
    Sem.run (storeValue service none ⟨0⟩ heldPointer (.typedClosure ⟨0⟩ ⟨10⟩ [])) (allocated 0 1) =
      .error (.typeError "closure Store nominal, target or capture count mismatch") := by
  trustIrCompilerProof { rfl } { trustIrReduce }

theorem absent_original_constructors_cannot_be_replaced_by_geometry :
    let rows := {original with functions := [scalarTarget 7 37]}
    Sem.run (loadValue (prepare rows .le64 []) none ⟨0⟩ heldPointer) (allocated 0 1) =
      .error (.typeError "missing closure storage target") := by
  trustIrCompilerProof { rfl } { trustIrReduce }

theorem old_geometry_only_memory_service_still_refuses_closure_codec :
    Sem.run (AggregateMemory.loadValue service.memoryService none (.Closure ⟨0⟩) heldPointer)
      (allocated 0 1) =
      .error (.unsupported .layout s!"memory: {repr (SourceLayout.Error.unsupported (.Closure ⟨0⟩))}") := by
  trustIrCompilerProof { rfl } { trustIrReduce }

private def dead : MachineState :=
  let live := allocated 0 1
  {live with
    memory := {live.memory with
      allocations := live.memory.allocations.map (fun record => {record with alive := false})}}

theorem zero_byte_load_checks_real_allocation_liveness :
    Sem.run (loadValue service none ⟨0⟩ heldPointer) dead =
      .error (.ub "Load: use after dealloc") := by
  trustIrCompilerProof { rfl } { trustIrReduce }

theorem zero_byte_store_checks_real_allocation_liveness :
    Sem.run (storeValue service none ⟨0⟩ heldPointer (.typedClosure ⟨0⟩ ⟨7⟩ [])) dead =
      .error (.ub "Store: use after dealloc") := by
  trustIrCompilerProof { rfl } { trustIrReduce }

theorem wrong_nominal_cannot_use_same_empty_capture_shape :
    Sem.run (storeValue service none ⟨0⟩ heldPointer (.typedClosure ⟨1⟩ ⟨7⟩ [])) (allocated 0 1) =
      .error (.typeError "closure Store nominal, target or capture count mismatch") := by
  trustIrCompilerProof { rfl } { trustIrReduce }

theorem wrong_capture_count_cannot_use_same_nominal_target :
    Sem.run (storeValue service none ⟨0⟩ heldPointer (.typedClosure ⟨0⟩ ⟨7⟩ [.int 64 1])) (allocated 0 1) =
      .error (.typeError "closure Store nominal, target or capture count mismatch") := by
  trustIrCompilerProof { rfl } { trustIrReduce }

theorem whole_parent_extent_is_checked_before_field_decoding :
    Sem.run (loadValue capturedService none ⟨0⟩ heldPointer) (allocated 8 8) =
      .error (.ub "Load: access is out of bounds") := by
  trustIrCompilerProof { rfl } { trustIrReduce }

theorem whole_parent_default_alignment_is_checked :
    Sem.run (loadValue capturedService none ⟨0⟩ (.ptr 1025 (some ⟨0⟩))) (allocated 24 8) =
      .error (.ub "Load: pointer address 1025 is not aligned to 8") := by
  trustIrCompilerProof { rfl } { trustIrReduce }

/-- Explicit parent alignment retains the image decoder's byte semantics;
the adapter must not add a stronger child-address alignment check. -/
theorem explicit_unaligned_parent_roundtrip_uses_canonical_capture_image :
    (Sem.run (do
      storeValue capturedService none ⟨0⟩ (.ptr 1025 (some ⟨0⟩))
        (.typedClosure ⟨0⟩ ⟨7⟩ [.int 64 42]) false (some 1)
      loadValue capturedService none ⟨0⟩ (.ptr 1025 (some ⟨0⟩)) false (some 1)) (allocated 24 8)).map Prod.fst =
      .ok (.typedClosure ⟨0⟩ ⟨7⟩ [.int 64 42]) := by
  trustIrCompilerProof { rfl } { trustIrReduce }

theorem unreachable_original_decode_error_reaches_actual_storage_refusal :
    let broken := {original with functions := original.functions ++
      [{function 99 0 [] [] [] [] with blocks := .error (.unsupported "original hidden body")}]}
    runValues broken 9 = .error (.unsupported .layout "original hidden body") := by
  trustIrCompilerProof { rfl } { trustIrReduce }

/-- False goals used by the fresh-kernel hostile substitution controls. -/
def WrongBorrowedTarget : Prop := runValues original 9 = .ok [.int 64 99]
def WrongImportedStore : Prop :=
  runValues original 12 [.typedClosure ⟨0⟩ ⟨10⟩ []] = .ok [.int 64 0]
def WrongUninitializedCapture : Prop :=
  (Sem.run (loadValue capturedService none ⟨0⟩ heldPointer) (allocated 16 8)).map Prod.fst =
    .ok (.typedClosure ⟨0⟩ ⟨7⟩ [.int 64 0])

end TrustIr.OriginalClosureMemory.Checks
