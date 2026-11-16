-- Copyright 2026 Andrew Yates | Apache-2.0
import TrustIr.Proofs.GenericCoroModuleContext
import TrustIr.Proofs.GenericCoroAllBlocksEntryEffects
import TrustIr.Proofs.GenericCoroEntryObservation

namespace TrustIr.GenericCoro.ModuleEntryEffects
open TrustIrEval ModuleFactory AllBlocksContext AllBlocksEntryEffects

/-- Raw entry effects for the ACTUAL contexts constructed from the produced
    decoded function lists. No framed-return equality is used here. -/
theorem produced_context_entryEffects (source : Module) (targets : List Function)
    (produced : Produced source.funcTys.toArray
      (directHeaders (headerIndex source.funcTys.toArray source.functions)) source.functions targets)
    (maxDepth : Nat) (sourceContext targetContext : EvalContext)
    (sourceBuilt : contextOf source maxDepth = .ok sourceContext)
    (targetBuilt : contextOf {source with functions := targets} maxDepth = .ok targetContext) :
    EntryEffects sourceContext targetContext := by
  obtain ⟨base, updates, sourceEq, targetEq, replacements⟩ :=
    ModuleContext.produced_context_updates source targets produced maxDepth sourceContext targetContext
      sourceBuilt targetBuilt
  rw [sourceEq, targetEq]
  exact installFirst_entryEffects updates replacements base

/-- A successful publication of the actual decoded Module factory preserves
    raw evaluator effects for every requested entry and every exact resource
    pair, with the same cleared input state. -/
theorem transform_ready_entryEffects (source target : Module)
    (actual : ModuleFactory.transform source = .ready target) (maxDepth : Nat)
    (sourceContext targetContext : EvalContext)
    (sourceBuilt : contextOf source maxDepth = .ok sourceContext)
    (targetBuilt : contextOf target maxDepth = .ok targetContext) :
    EntryEffects sourceContext targetContext := by
  have fields := (ModuleFactory.transform_ready source target actual).1
  have targetEq : target = {source with functions := target.functions} := by
    have updated := congrArg (fun module : Module => {module with functions := target.functions}) fields
    exact updated
  have produced := ModuleFactory.transform_produced source target actual
  rw [targetEq] at targetBuilt
  exact produced_context_entryEffects source target.functions produced maxDepth sourceContext targetContext
    sourceBuilt targetBuilt

end TrustIr.GenericCoro.ModuleEntryEffects

namespace TrustIr.GenericCoro.ModuleEntryEffects
open TrustIrEval ModuleFactory AllBlocksContext AllBlocksEntryEffects

/-- Entry ABI/argument checks, actual unwind conversion and return-poison
    checks preserve the raw effects. There is NO framed return-arity check. -/
theorem entry_observe_eq (source target : EvalContext) (related : EntryEffects source target)
    (requested : FuncId) (args : List Value) (fuel : Nat) (strategy : PanicStrategy)
    (world : MachineState) :
    EntryObservation.observe
      (Sem.run (evalFunctionInContext source requested args fuel strategy) (callerWorld world)) =
    EntryObservation.observe
      (Sem.run (evalFunctionInContext target requested args fuel strategy) (callerWorld world)) := by
  have headers := related.headers requested
  cases sourceFound : source.functions requested with
  | none =>
    cases targetFound : target.functions requested with
    | none =>
      exact EntryObservation.missing_entry_observe_eq source target requested sourceFound targetFound
        args fuel strategy (callerWorld world)
    | some targetFunction =>
      rw [sourceFound, targetFound] at headers
      cases headers
  | some sourceFunction =>
    cases targetFound : target.functions requested with
    | none =>
      rw [sourceFound, targetFound] at headers
      cases headers
    | some targetFunction =>
      rw [sourceFound, targetFound] at headers
      cases headers with
      | present _ _ body _ =>
        apply EntryObservation.entry_observe_eq_of_steps source target requested sourceFunction targetFunction
          sourceFound targetFound body related.itemChecks args fuel strategy (callerWorld world)
        rw [← related.maxDepth]
        exact related.effects requested sourceFunction targetFunction sourceFound targetFound
          fuel source.maxCallDepth args strategy world

/-- Public entry observation for the actual Module producer and actual
    successfully constructed contexts, at the same exact resources. All
    non-SSA output fields and complete errors remain observable. -/
theorem transform_ready_entry_observe_eq (source target : Module)
    (actual : ModuleFactory.transform source = .ready target) (maxDepth : Nat)
    (sourceContext targetContext : EvalContext)
    (sourceBuilt : contextOf source maxDepth = .ok sourceContext)
    (targetBuilt : contextOf target maxDepth = .ok targetContext)
    (requested : FuncId) (args : List Value) (fuel : Nat) (strategy : PanicStrategy)
    (world : MachineState) :
    EntryObservation.observe
      (Sem.run (evalFunctionInContext sourceContext requested args fuel strategy) (callerWorld world)) =
    EntryObservation.observe
      (Sem.run (evalFunctionInContext targetContext requested args fuel strategy) (callerWorld world)) :=
  entry_observe_eq sourceContext targetContext
    (transform_ready_entryEffects source target actual maxDepth sourceContext targetContext sourceBuilt targetBuilt)
    requested args fuel strategy world

/-- Preserve context-construction failures as well as the actual entry
    observation after success. The entry observation hides only output SSA
    storage; this does not change raw Outcome or program_refines. -/
theorem transform_ready_constructed_entry_observe_eq (source target : Module)
    (actual : ModuleFactory.transform source = .ready target) (maxDepth : Nat)
    (requested : FuncId) (args : List Value) (fuel : Nat) (strategy : PanicStrategy)
    (world : MachineState) :
    (contextOf source maxDepth).map (fun context => EntryObservation.observe
      (Sem.run (evalFunctionInContext context requested args fuel strategy) (callerWorld world))) =
    (contextOf target maxDepth).map (fun context => EntryObservation.observe
      (Sem.run (evalFunctionInContext context requested args fuel strategy) (callerWorld world))) := by
  have constructed := ModuleContext.transform_ready_context_calls source target actual maxDepth
  cases sourceBuilt : contextOf source maxDepth with
  | error error =>
    cases targetBuilt : contextOf target maxDepth with
    | error targetError =>
      rw [sourceBuilt, targetBuilt] at constructed
      change error = targetError at constructed
      rw [constructed]
    | ok targetContext =>
      rw [sourceBuilt, targetBuilt] at constructed
      change False at constructed
      exact constructed.elim
  | ok sourceContext =>
    cases targetBuilt : contextOf target maxDepth with
    | error error =>
      rw [sourceBuilt, targetBuilt] at constructed
      change False at constructed
      exact constructed.elim
    | ok targetContext =>
      exact congrArg Except.ok (transform_ready_entry_observe_eq source target actual maxDepth
        sourceContext targetContext sourceBuilt targetBuilt requested args fuel strategy world)

/-- A concrete initial-state specialization with no freshness or successful
    entry premise. The generic theorem also admits arbitrary initial memory,
    globals, permissions, exception data and float-choice fields. -/
theorem transform_ready_initial_entry_observe_eq (source target : Module)
    (actual : ModuleFactory.transform source = .ready target) (maxDepth : Nat)
    (requested : FuncId) (args : List Value) (fuel : Nat) (strategy : PanicStrategy) :
    (contextOf source maxDepth).map (fun context => EntryObservation.observe
      (Sem.run (evalFunctionInContext context requested args fuel strategy) MachineState.empty)) =
    (contextOf target maxDepth).map (fun context => EntryObservation.observe
      (Sem.run (evalFunctionInContext context requested args fuel strategy) MachineState.empty)) := by
  exact transform_ready_constructed_entry_observe_eq source target actual maxDepth requested args fuel strategy
    MachineState.empty

end TrustIr.GenericCoro.ModuleEntryEffects
