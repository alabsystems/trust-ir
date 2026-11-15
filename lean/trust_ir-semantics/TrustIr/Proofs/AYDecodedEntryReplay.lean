-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0
import TrustIr.DecodedEntry
import TrustIr.Proofs.AYUnaryEntryReplay

namespace TrustIr.AYUnaryReplay
open TrustIrEval

/-- Point receipts for the actual oracle preflight and public entry, including
preflight refusals. Ready receipts retain the real normalized args and state. -/
inductive DecodedEntryTrace (m : Module) (ctx : EvalContext) (initial : Except SemError MachineState)
    (fid : FuncId) (args : List Value) (fuel : Nat) where
  | blocked (error : EntryPreflightError) (actual : prepareDecodedEntry m ctx initial fid args = .blocked error)
  | ready (state : MachineState) (actualArgs : List Value)
      (actual : prepareDecodedEntry m ctx initial fid args = .ready state actualArgs)
      (trace : EntryTrace ctx fid actualArgs fuel state)

def DecodedEntryTrace.result {m ctx initial fid args fuel} :
    DecodedEntryTrace m ctx initial fid args fuel → PanicStrategy → RunEntryResult
  | .blocked error _,_ => error.result
  | .ready _ _ _ trace,strategy => .evaluated (trace.outcome strategy)

def DecodedEntryTrace.build (m : Module) (ctx : EvalContext) (initial : Except SemError MachineState)
    (fid : FuncId) (args : List Value) (fuel : Nat) : Except String (DecodedEntryTrace m ctx initial fid args fuel) :=
  match actual : prepareDecodedEntry m ctx initial fid args with
  | .blocked error => .ok (.blocked error actual)
  | .ready state actualArgs => do
    let trace ← EntryTrace.build ctx fid actualArgs fuel state
    .ok (.ready state actualArgs actual trace)

theorem DecodedEntryTrace.correct {m ctx initial fid args fuel}
    (checked : DecodedEntryTrace m ctx initial fid args fuel) (strategy : PanicStrategy) :
    runDecodedEntry m ctx initial fuel strategy fid args = checked.result strategy := by
  unfold runDecodedEntry
  cases checked with
  | blocked error actual => rw [actual]; rfl
  | ready state actualArgs actual trace =>
    rw [actual]
    exact congrArg RunEntryResult.evaluated (trace.correct strategy)

/-- Actual source context assembly and source-sized state initialization bind
the execution receipt to this complete decoded module, not an opaque context. -/
inductive DecodedModuleTrace (m : Module) (depth : Nat) (choices : List Bool)
    (fid : FuncId) (args : List Value) (fuel : Nat) where
  | assemblyError (error : DecodeError) (actual : contextOf m depth = .error error)
  | assembled (ctx : EvalContext) (actual : contextOf m depth = .ok ctx)
      (trace : DecodedEntryTrace m ctx (moduleEntryState m ctx choices) fid args fuel)

def DecodedModuleTrace.result {m depth choices fid args fuel} :
    DecodedModuleTrace m depth choices fid args fuel → PanicStrategy → RunEntryResult
  | .assemblyError error _,_ => .decodeError error
  | .assembled _ _ trace,strategy => trace.result strategy

def DecodedModuleTrace.build (m : Module) (depth : Nat) (choices : List Bool)
    (fid : FuncId) (args : List Value) (fuel : Nat) : Except String (DecodedModuleTrace m depth choices fid args fuel) :=
  match actual : contextOf m depth with
  | .error error => .ok (.assemblyError error actual)
  | .ok ctx => do
    let trace ← DecodedEntryTrace.build m ctx (moduleEntryState m ctx choices) fid args fuel
    .ok (.assembled ctx actual trace)

theorem DecodedModuleTrace.correct {m depth choices fid args fuel}
    (checked : DecodedModuleTrace m depth choices fid args fuel) (strategy : PanicStrategy) :
    runDecodedModule m depth choices fuel strategy fid args = checked.result strategy := by
  unfold runDecodedModule
  cases checked with
  | assemblyError error actual => rw [actual]; rfl
  | assembled ctx actual trace => rw [actual]; exact trace.correct strategy

/-- At zero CFG fuel, a receipt still retains all earlier oracle preflight
errors; this does not skip the original reachable-decode walk. -/
theorem DecodedEntryTrace.build_zero (m : Module) (ctx : EvalContext) (initial : Except SemError MachineState)
    (fid : FuncId) (args : List Value) :
    ∃ checked, DecodedEntryTrace.build m ctx initial fid args 0 = .ok checked := by
  unfold DecodedEntryTrace.build
  split
  · exact ⟨_,rfl⟩
  · rename_i state actualArgs actual
    obtain ⟨trace,built⟩ := EntryTrace.build_zero ctx fid actualArgs state
    rw [built]
    exact ⟨_,rfl⟩

theorem DecodedModuleTrace.build_zero (m : Module) (depth : Nat) (choices : List Bool)
    (fid : FuncId) (args : List Value) :
    ∃ checked, DecodedModuleTrace.build m depth choices fid args 0 = .ok checked := by
  unfold DecodedModuleTrace.build
  split
  · exact ⟨_,rfl⟩
  · rename_i ctx actual
    obtain ⟨trace,built⟩ := DecodedEntryTrace.build_zero m ctx (moduleEntryState m ctx choices) fid args
    rw [built]
    exact ⟨_,rfl⟩

/-- Receipts for exactly the original enumerated request rows. A terminal
execution error retains the next requested run, whose initial state is fresh. -/
inductive DecodedBatchEntries (m : Module) (ctx : EvalContext) (initial : Except SemError MachineState)
    (choices : List (List Bool)) (fuel : Nat) : List (Nat × (FuncId × List Value)) → Type where
  | nil : DecodedBatchEntries m ctx initial choices fuel []
  | cons {index fid args rest}
      (entry : DecodedEntryTrace m ctx (withEntryChoices initial (choices.getD index [])) fid args fuel)
      (tail : DecodedBatchEntries m ctx initial choices fuel rest) :
      DecodedBatchEntries m ctx initial choices fuel ((index,(fid,args))::rest)

def DecodedBatchEntries.results {m ctx initial choices fuel rows} :
    DecodedBatchEntries m ctx initial choices fuel rows → PanicStrategy → List (FuncId × RunEntryResult)
  | .nil,_ => []
  | .cons (fid := fid) entry tail,strategy => (fid,entry.result strategy)::tail.results strategy

def DecodedBatchEntries.build (m : Module) (ctx : EvalContext) (initial : Except SemError MachineState)
    (choices : List (List Bool)) (fuel : Nat) :
    (rows : List (Nat × (FuncId × List Value))) → Except String (DecodedBatchEntries m ctx initial choices fuel rows)
  | [] => .ok .nil
  | (index,(fid,args))::rest => do
    let entry ← DecodedEntryTrace.build m ctx (withEntryChoices initial (choices.getD index [])) fid args fuel
    let tail ← DecodedBatchEntries.build m ctx initial choices fuel rest
    .ok (.cons entry tail)

theorem DecodedBatchEntries.correct {m ctx initial choices fuel rows}
    (checked : DecodedBatchEntries m ctx initial choices fuel rows) (strategy : PanicStrategy) :
    rows.map (fun (index,(fid,args)) =>
      (fid,runDecodedEntry m ctx (withEntryChoices initial (choices.getD index [])) fuel strategy fid args)) =
      checked.results strategy := by
  induction checked with
  | nil => rfl
  | cons entry tail ih => simp only [List.map,entry.correct strategy,ih,DecodedBatchEntries.results]

inductive DecodedBatchTrace (m : Module) (runs : List (FuncId × List Value))
    (choices : List (List Bool)) (fuel depth : Nat) where
  | assemblyError (error : DecodeError) (actual : contextOf m depth = .error error)
  | assembled (ctx : EvalContext) (actual : contextOf m depth = .ok ctx)
      (entries : DecodedBatchEntries m ctx (initialStateForFunctionCount ctx.byteModel m.functions.length) choices fuel (trustIrEntryEnumFrom 0 runs))

def DecodedBatchTrace.results {m runs choices fuel depth} :
    DecodedBatchTrace m runs choices fuel depth → PanicStrategy → List (FuncId × RunEntryResult)
  | .assemblyError error _,_ => runs.map (fun (fid,_) => (fid,.decodeError error))
  | .assembled _ _ entries,strategy => entries.results strategy

def DecodedBatchTrace.build (m : Module) (runs : List (FuncId × List Value))
    (choices : List (List Bool)) (fuel depth : Nat) : Except String (DecodedBatchTrace m runs choices fuel depth) :=
  match actual : contextOf m depth with
  | .error error => .ok (.assemblyError error actual)
  | .ok ctx => do
    let entries ← DecodedBatchEntries.build m ctx (initialStateForFunctionCount ctx.byteModel m.functions.length) choices fuel (trustIrEntryEnumFrom 0 runs)
    .ok (.assembled ctx actual entries)

theorem DecodedBatchTrace.correct {m runs choices fuel depth}
    (checked : DecodedBatchTrace m runs choices fuel depth) (strategy : PanicStrategy) :
    runDecodedBatch m runs choices fuel depth strategy = checked.results strategy := by
  unfold runDecodedBatch runDecodedBatchWith
  cases checked with
  | assemblyError error actual => rw [actual]; rfl
  | assembled ctx actual entries => rw [actual]; exact entries.correct strategy

/-- The actual streaming production consumer receives these exact ordered
results without needing to materialize a list of all final machine states. -/
theorem DecodedBatchTrace.consume_correct {α : Type} {m runs choices fuel depth}
    (checked : DecodedBatchTrace m runs choices fuel depth) (consume : FuncId → RunEntryResult → α)
    (strategy : PanicStrategy) :
    runDecodedBatchWith consume m runs choices fuel depth strategy =
      (checked.results strategy).map (fun (fid,result) => consume fid result) := by
  rw [runDecodedBatchWith_eq_map,checked.correct strategy]

end TrustIr.AYUnaryReplay
