-- Copyright 2026 Andrew Yates | Apache-2.0
import TrustIrRuntime
import TrustIr.Semantics.AggregateAccess

/-! Executable work controls. Static source rows are deliberately unrelated
    to the accessed type. Every repeated root query must hit the prepared
    success/error caches, not reconstruct the finite source domain. -/
namespace TrustIrEval.AggregateImageWork
open TrustIr TrustIr.AggregateMemory

private def tuple : Ty := .Tuple [.U8, .U64]
private def payload : Value := .aggregate [.int 8 7, .int 64 42]

private def run (unrelated repeats : Nat) : IO Unit := do
  let source : SourceLayout.Environment :=
    { hasTargetInfo := true, types := List.replicate unrelated (some .U64) }
  let missing : Ty := .Struct ⟨4294967295⟩
  let start ← IO.monoNanosNow
  let service := AggregateMemory.prepare source [tuple, missing, tuple]
  let (address, memory) := Memory.empty.alloc 16 8 0 .rustStack
  let pointer := Value.ptr address (some ⟨0⟩)
  let mut state : MachineState := { MachineState.empty with memory }
  let mut compilationWork := 0
  let mut layoutWork := 0
  for _ in List.range repeats do
    let (plan, work) := service.queryWithWork tuple
    compilationWork := compilationWork + work
    match plan with
    | .error error => throw (IO.userError s!"cached root failed: {repr error}")
    | .ok plan =>
      unless plan.layout.size == 16 && plan.layout.alignment == 8 do
        throw (IO.userError "wrong cached producer layout")
    let (layout, work) := service.queryLayoutWithWork tuple
    layoutWork := layoutWork + work
    match layout with
    | .error error => throw (IO.userError s!"cached layout failed: {repr error}")
    | .ok layout =>
      unless layout.size == 16 && layout.alignment == 8 do
        throw (IO.userError "wrong producer layout")
    let (missingPlan, missingWork) := service.queryWithWork missing
    compilationWork := compilationWork + missingWork
    match missingPlan with
    | .error (.typeError _) => pure ()
    | _ => throw (IO.userError "missing source row error changed")
    match Sem.run (AggregateMemory.storeValue service none tuple pointer payload) state with
    | .error error => throw (IO.userError s!"held store failed: {repr error}")
    | .ok (_, after) => state := after
    match Sem.run (AggregateMemory.loadValue service none tuple pointer) state with
    | .error error => throw (IO.userError s!"held load failed: {repr error}")
    | .ok (.aggregate [.int 8 7, .int 64 42], after) => state := after
    | _ => throw (IO.userError "held load result changed")
  unless compilationWork == 0 && layoutWork == 0 && state.nextValueId == 0 do
    throw (IO.userError s!"uncached work or private SSA publication: {compilationWork}/{layoutWork}")
  let stop ← IO.monoNanosNow
  IO.println s!"aggregate-image-cache unrelated_source_rows={unrelated} repetitions={repeats} plan_compiler_invocations={compilationWork} layout_invocations={layoutWork} private_ssa_binds={state.nextValueId} elapsed_ns={stop-start}:PASS"

end TrustIrEval.AggregateImageWork

def main : IO Unit := do
  for unrelated in [0, 1024, 32768] do
    TrustIrEval.AggregateImageWork.run unrelated 2048
