-- Copyright 2026 Andrew Yates | Apache-2.0
import TrustIr.Proofs.BorrowedClosureCalls
import TrustIr.DecodedEntry

namespace TrustIr.OriginalClosureMemory.CallChecks
open TrustIrEval

private def sig (params returns : List Ty) : FuncTyDef := {params,returns,isVararg := false}
private def function (id ty : Nat) (block : BasicBlock) : Function :=
  {id := ⟨id⟩,name := "borrowed-closure-source",ty := ⟨ty⟩,entry := ⟨0⟩,
   isDeclaration := false,blocks := .ok [(⟨0⟩,block)]}
private def emptySource : Module :=
  {hasTargetInfo := true
   functions := [
     function 7 0 {params := [],body := [.Const .U64 (.int 37)],bodyResultDests := [[⟨0⟩]],terminator := .Return [⟨0⟩]},
     function 8 1 (borrowedLoadBlock ⟨0⟩ (some 1)),
     function 9 0
       {params := []
        body := [.MakeClosure ⟨0⟩ ⟨7⟩ [],.Alloca (.Closure ⟨0⟩) none (some 1),
          .Store (.Closure ⟨0⟩) ⟨1⟩ ⟨0⟩ false (some 1),.Call ⟨8⟩ [⟨1⟩],.CallIndirect ⟨2⟩ ⟨0⟩ [] .C]
        bodyResultDests := [[⟨0⟩],[⟨1⟩],[],[⟨2⟩],[⟨3⟩]]
        terminator := .Return [⟨3⟩]}]
   funcTys := [sig [] [.U64],sig [.Ptr] [.Closure ⟨0⟩]]
   closureTys := [{func := ⟨0⟩,captures := []}]
   closureLayouts := [{closure := ⟨0⟩,size := 0,align := 1,captureOffsets := []}]
   globals := [],enums := [],structs := [],types := []}
private def scalarSource : Module :=
  {emptySource with
   functions := [
     function 7 2 {params := [(⟨0⟩,.U64)],body := [],terminator := .Return [⟨0⟩]},
     function 8 1 (borrowedLoadBlock ⟨0⟩ none),
     function 9 0
       {params := []
        body := [.Const .U64 (.int 42),.MakeClosure ⟨0⟩ ⟨7⟩ [⟨0⟩],
          .Alloca (.Closure ⟨0⟩) none none,.Store (.Closure ⟨0⟩) ⟨2⟩ ⟨1⟩ false none,
          .Call ⟨8⟩ [⟨2⟩],.CallIndirect ⟨3⟩ ⟨0⟩ [] .C]
        bodyResultDests := [[⟨0⟩],[⟨1⟩],[⟨2⟩],[],[⟨3⟩],[⟨4⟩]]
        terminator := .Return [⟨4⟩]}]
   funcTys := [sig [] [.U64],sig [.Ptr] [.Closure ⟨0⟩],sig [.U64] [.U64]]
   closureTys := [{func := ⟨0⟩,captures := [.U64]}]
   closureLayouts := [{closure := ⟨0⟩,size := 16,align := 8,captureOffsets := [8]}]}

private def context (source : Module) : EvalContext :=
  (contextOf source 16).toOption.getD
    {functions := fun _ => none,funcPtrs := fun _ => none,funcTys := fun _ => none,
     maxCallDepth := 0,globalsTable := fun _ => none}
private def allocated (size alignment : Nat) : MachineState :=
  let (_,memory) := Memory.empty.alloc size alignment 0 .rustStack
  {MachineState.empty with memory}
private def pointer : Value := .ptr 1024 (some ⟨0⟩)
private def input (captures : List Value) : Value := .typedClosure ⟨0⟩ ⟨7⟩ captures
private def stored (source : Module) (captures : List Value) (size alignment : Nat) (align : Option Nat) : MachineState :=
  match Sem.run (storeValue (originalMemoryServiceOf source (context source).byteModel)
    (context source).functionOrder ⟨0⟩ pointer (input captures) false align (context source).byteModel) (allocated size alignment) with
  | .ok (_,after) => after
  | .error _ => allocated size alignment
private def emptyStored := stored emptySource [] 0 1 (some 1)
private def scalarStored := stored scalarSource [.int 64 42] 16 8 none

private theorem empty_inputs : SourceReadbackInputs emptySource (context emptySource) emptyStored.memory ⟨0⟩ [] := by
  unfold SourceReadbackInputs originalMemoryServiceOf
  refine ⟨_,rfl,?_,?_⟩
  · intro nominal actual position ty value plan typeRow
    change some {func := ⟨0⟩,captures := []} = some nominal at actual
    cases actual
    cases position <;> cases typeRow
  · intro nominal actual ty member
    change some {func := ⟨0⟩,captures := []} = some nominal at actual
    cases actual
    cases member

private theorem scalar_inputs : SourceReadbackInputs scalarSource (context scalarSource) scalarStored.memory ⟨0⟩ [.int 64 42] := by
  unfold SourceReadbackInputs originalMemoryServiceOf
  refine ⟨_,rfl,?_,?_⟩
  · intro nominal actual position ty value plan typeRow valueRow queried
    change some {func := ⟨0⟩,captures := [.U64]} = some nominal at actual
    cases actual
    cases position with
    | zero =>
      cases typeRow
      cases valueRow
      change Except.ok (AggregateMemory.Plan.leaf .U64 ⟨8,8⟩) = .ok plan at queried
      cases queried
      exact .scalar (.integer .U64 ⟨8,8⟩ 64 42 rfl rfl rfl)
    | succ n => cases n <;> cases typeRow
  · intro nominal actual ty member plan queried
    change some {func := ⟨0⟩,captures := [.U64]} = some nominal at actual
    cases actual
    rcases List.mem_cons.mp member with same | absent
    · subst ty
      change Except.ok (AggregateMemory.Plan.leaf .U64 ⟨8,8⟩) = .ok plan at queried
      cases queried
      exact ⟨.U64,⟨8,8⟩,rfl⟩
    · cases absent

/-- These controls invoke the GENERIC source-memory summary with actual context,
source function lookup, actual Store and actual standard call execution. -/
theorem empty_call_uses_general_source_memory_summary :
    ∃ (binding : ClosureStorage.Binding emptySource ⟨0⟩) (output : Value),
      [.typedClosure ⟨0⟩ ⟨7⟩ []] = [output] ∧
      ValueReadback emptySource ⟨0⟩ binding (context emptySource).byteModel emptyStored.memory (input []) output := by
  have assembled : contextOf emptySource 16 = .ok (context emptySource) := by rfl
  have function : ∃ callee, (context emptySource).functions ⟨8⟩ = some callee ∧
      callee.cfg callee.entryBlock = some (borrowedLoadBlock ⟨0⟩ (some 1)) := by exact ⟨_,rfl,rfl⟩
  obtain ⟨callee,found,body⟩ := function
  have storeRun : Sem.run (storeValue (originalMemoryServiceOf emptySource (context emptySource).byteModel)
      (context emptySource).functionOrder ⟨0⟩ pointer (input []) false (some 1) (context emptySource).byteModel)
      (allocated 0 1) = .ok ((),emptyStored) := by rfl
  have callRun : Sem.run (runCallReq (context emptySource) 8 8 ⟨8⟩ [pointer]) emptyStored =
      .ok ([.typedClosure ⟨0⟩ ⟨7⟩ []],emptyStored) := by rfl
  exact (source_borrowed_call_readback emptySource 16 (context emptySource) assembled ⟨8⟩ callee 7 8
    ⟨0⟩ ⟨0⟩ ⟨7⟩ [] pointer false (some 1) (allocated 0 1) emptyStored emptyStored _
    found body empty_inputs storeRun callRun).2

theorem captured_call_uses_general_source_memory_summary :
    ∃ (binding : ClosureStorage.Binding scalarSource ⟨0⟩) (output : Value),
      [.typedClosure ⟨0⟩ ⟨7⟩ [.int 64 42]] = [output] ∧
      ValueReadback scalarSource ⟨0⟩ binding (context scalarSource).byteModel scalarStored.memory (input [.int 64 42]) output := by
  have assembled : contextOf scalarSource 16 = .ok (context scalarSource) := by rfl
  have function : ∃ callee, (context scalarSource).functions ⟨8⟩ = some callee ∧
      callee.cfg callee.entryBlock = some (borrowedLoadBlock ⟨0⟩ none) := by exact ⟨_,rfl,rfl⟩
  obtain ⟨callee,found,body⟩ := function
  have storeRun : Sem.run (storeValue (originalMemoryServiceOf scalarSource (context scalarSource).byteModel)
      (context scalarSource).functionOrder ⟨0⟩ pointer (input [.int 64 42]) false none (context scalarSource).byteModel)
      (allocated 16 8) = .ok ((),scalarStored) := by rfl
  have callRun : Sem.run (runCallReq (context scalarSource) 8 8 ⟨8⟩ [pointer]) scalarStored =
      .ok ([.typedClosure ⟨0⟩ ⟨7⟩ [.int 64 42]],scalarStored) := by rfl
  exact (source_borrowed_call_readback scalarSource 16 (context scalarSource) assembled ⟨8⟩ callee 7 8
    ⟨0⟩ ⟨0⟩ ⟨7⟩ [.int 64 42] pointer false none (allocated 16 8) scalarStored scalarStored _
    found body scalar_inputs storeRun callRun).2

private def runValues (source : Module) : Except SemError (List Value) :=
  match runDecodedModule source 16 [] 32 .abort ⟨9⟩ [] with
  | .evaluated result => result.map Prod.fst
  | _ => .error (.typeError "control did not evaluate")

theorem public_caller_borrows_then_invokes_empty_closure : runValues emptySource = .ok [.int 64 37] := by
  trustIrCompilerProof {rfl} {trustIrReduce}
theorem public_caller_borrows_then_invokes_padded_capture : runValues scalarSource = .ok [.int 64 42] := by
  trustIrCompilerProof {rfl} {trustIrReduce}

/-- Same old returned closure value, but an actual source callee write changes
Memory. A value-only postcondition cannot justify this stronger memory rely. -/
private def writingSource : Module :=
  {scalarSource with functions := scalarSource.functions.map (fun f =>
    if f.id == ⟨8⟩ then function 8 1
      {params := [(⟨0⟩,.Ptr)],body := [.Load (.Closure ⟨0⟩) ⟨0⟩ false none,
        .Const .U64 (.int 99),.MakeClosure ⟨0⟩ ⟨7⟩ [⟨2⟩],
        .Store (.Closure ⟨0⟩) ⟨0⟩ ⟨3⟩ false none],
       bodyResultDests := [[⟨1⟩],[⟨2⟩],[⟨3⟩],[]],terminator := .Return [⟨1⟩]}
    else f)}
private def writingStored := stored writingSource [.int 64 42] 16 8 none
private def writerResult := Sem.run (runCallReq (context writingSource) 8 8 ⟨8⟩ [pointer]) writingStored

theorem source_write_returns_the_same_old_value :
    writerResult.map (fun pair => pair.1) = .ok [.typedClosure ⟨0⟩ ⟨7⟩ [.int 64 42]] := by
  trustIrCompilerProof {rfl} {trustIrReduce}
theorem source_write_changes_covered_memory :
    writerResult.map (fun pair => pair.2.memory.bytes 1032) = .ok (some 99) ∧ writingStored.memory.bytes 1032 = some 42 := by
  constructor <;> trustIrCompilerProof {rfl} {trustIrReduce}
theorem writing_callee_does_not_have_the_admitted_body :
    ∀ callee, (context writingSource).functions ⟨8⟩ = some callee →
      callee.cfg callee.entryBlock ≠ some (borrowedLoadBlock ⟨0⟩ none) := by
  intro callee selected
  let actual := ((context writingSource).functions ⟨8⟩).get (by rfl)
  have found : (context writingSource).functions ⟨8⟩ = some actual := by rfl
  have identical : callee = actual := Option.some.inj (selected.symm.trans found)
  subst callee
  intro same
  have counts := congrArg (fun block : Option BasicBlock => block.map (fun b => b.body.length)) same
  change some 4 = some 1 at counts
  cases counts

theorem borrowed_reader_refuses_uninitialized_capture :
    Sem.run (runCallReq (context scalarSource) 8 8 ⟨8⟩ [pointer]) (allocated 16 8) =
      .error (.ub "Load: reading uninitialized covered memory") := by
  trustIrCompilerProof {rfl} {trustIrReduce}

theorem empty_borrow_still_refuses_missing_provenance :
    Sem.run (runCallReq (context emptySource) 8 8 ⟨8⟩ [.ptr 1024 none]) (allocated 0 1) =
      .error (.ub "Load: pointer value 1024 has no allocation provenance") := by
  trustIrCompilerProof {rfl} {trustIrReduce}

theorem borrowed_reader_keeps_original_fuel_refusal :
    Sem.run (runCallReq (context emptySource) 0 8 ⟨8⟩ [pointer]) emptyStored = .error SemError.outOfFuel := by
  trustIrCompilerProof {rfl} {trustIrReduce}

/-- False targets for fresh-kernel substitution controls. -/
def WrongWriterMemoryRely : Prop := writerResult.map (fun pair => pair.2.memory.bytes 1032) = .ok (some 42)
def WrongEmptyResult : Prop := runValues emptySource = .ok [.int 64 99]
def WrongCapturedResult : Prop := runValues scalarSource = .ok [.int 64 99]

end TrustIr.OriginalClosureMemory.CallChecks
