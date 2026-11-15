-- Copyright 2026 Andrew Yates | Apache-2.0
import TrustIr.Proofs.GenericCoroPrefixCalls
import TrustIr.Proofs.UnwindProps

namespace TrustIr.GenericCoro.EntryObservation
open Prefix

/-- Public entry observation retains returned values and every non-SSA field.
    Complete errors, including an embedded unwind state, remain exact. This
    is a new projection, not a change to the existing raw Outcome contract. -/
def observe (outcome : Except SemError (List Value × MachineState)) :
    Except SemError (List Value × MachineState) :=
  outcome.map (fun result => (result.1, callerWorld result.2))

theorem observe_eq_of_effectRelation
    {source target : Except SemError (List Value × MachineState)}
    (related : EffectRelation source target) : observe source = observe target := by
  cases related with
  | error error => rfl
  | returned values source target world =>
    simp only [observe, Except.map, world]

/-- The actual entry unwind handler only transforms identical error data;
    successful private SSA differences remain private. -/
theorem exitUnwinding_effect (strategy : PanicStrategy) (source target : Sem (List Value))
    (sourceState targetState : MachineState)
    (related : EffectRelation (Sem.run source sourceState) (Sem.run target targetState)) :
    EffectRelation (Sem.run (exitUnwinding strategy source) sourceState)
      (Sem.run (exitUnwinding strategy target) targetState) := by
  cases strategy with
  | abort => exact related
  | unwind =>
    simp only [exitUnwinding, Sem.run_tryCatch]
    generalize sourceRun : Sem.run source sourceState = sourceResult at related ⊢
    generalize targetRun : Sem.run target targetState = targetResult at related ⊢
    cases related with
    | returned values source target world => exact .returned values source target world
    | error error =>
      cases error <;> first | exact .error _ | skip
      rename_i exception state
      simp only [Except.tryCatch]
      cases found : state.exceptions.find? (fun row => row.1 == exception) with
      | none => simp only [found]; exact .error _
      | some row =>
        rcases row with ⟨address, ty, message, site⟩
        simp only [found]
        exact .error _

/-- The real entry return guard tests the shared values and leaves successful
    states unchanged. It adds no framed-call return-arity check. -/
theorem returnGuard_effect (source target : Sem (List Value))
    (sourceState targetState : MachineState)
    (related : EffectRelation (Sem.run source sourceState) (Sem.run target targetState)) :
    EffectRelation
      (Sem.run (do let values ← source; Sem.rejectPoisonValues values "Call returns"; pure values) sourceState)
      (Sem.run (do let values ← target; Sem.rejectPoisonValues values "Call returns"; pure values) targetState) := by
  simp only [Sem.run_bind]
  generalize sourceRun : Sem.run source sourceState = sourceResult at related ⊢
  generalize targetRun : Sem.run target targetState = targetResult at related ⊢
  cases related with
  | error error => exact .error error
  | returned values source target world =>
    simp only [Except.bind]
    cases poison : values.any Value.isPoison with
    | false =>
      rw [Sem.rejectPoisonValues_run_ok values "Call returns" source poison,
        Sem.rejectPoisonValues_run_ok values "Call returns" target poison]
      exact .returned values source target world
    | true =>
      simp only [Sem.rejectPoisonValues, poison, if_true]
      exact .error _

/-- Lift actual raw entry-step effects through the entry's own ABI, argument,
    unwind and return-poison handling. The hypothesis refers to each real
    context's own depth; no framed-call return-arity check is substituted. -/
theorem entry_effect_of_steps (source target : EvalContext) (requested : FuncId)
    (sourceFunction targetFunction : EvalFunction)
    (sourceFound : source.functions requested = some sourceFunction)
    (targetFound : target.functions requested = some targetFunction)
    (body : sourceFunction.body = targetFunction.body)
    (args : List Value) (fuel : Nat) (strategy : PanicStrategy) (state : MachineState)
    (steps : EffectRelation
      (Sem.run (stepNWithContext (source.forFunction sourceFunction) fuel source.maxCallDepth
        sourceFunction.cfg sourceFunction.entryBlock args strategy) state)
      (Sem.run (stepNWithContext (target.forFunction targetFunction) fuel target.maxCallDepth
        targetFunction.cfg targetFunction.entryBlock args strategy) state)) :
    EffectRelation
      (Sem.run (evalFunctionInContext source requested args fuel strategy) state)
      (Sem.run (evalFunctionInContext target requested args fuel strategy) state) := by
  have tail := returnGuard_effect _ _ state state
    (exitUnwinding_effect strategy _ _ state state steps)
  simp only [evalFunctionInContext, sourceFound, targetFound, pure_bind]
  rw [← body]
  cases abi : sourceFunction.body.abi with
  | some signature =>
    simp only [requireUntypedAbi, abi, Option.isSome, if_true]
    exact .error _
  | none =>
    simp only [requireUntypedAbi, abi, Option.isSome, Bool.false_eq_true, if_false, pure_bind]
    cases arity : checkCallArity args sourceFunction.body.paramTys with
    | error message =>
      simp only [arity]
      exact .error _
    | ok unit =>
      cases unit
      simp only [arity, pure_bind]
      cases poison : args.any Value.isPoison with
      | true =>
        simp only [Sem.rejectPoisonValues, poison, if_true]
        exact .error _
      | false =>
        have clean : Sem.rejectPoisonValues args "Call arguments" = pure () := by
          simp only [Sem.rejectPoisonValues, poison, Bool.false_eq_true, if_false]
        rw [clean]
        simpa only [pure_bind] using tail

theorem entry_observe_eq_of_steps (source target : EvalContext) (requested : FuncId)
    (sourceFunction targetFunction : EvalFunction)
    (sourceFound : source.functions requested = some sourceFunction)
    (targetFound : target.functions requested = some targetFunction)
    (body : sourceFunction.body = targetFunction.body)
    (args : List Value) (fuel : Nat) (strategy : PanicStrategy) (state : MachineState)
    (steps : EffectRelation
      (Sem.run (stepNWithContext (source.forFunction sourceFunction) fuel source.maxCallDepth
        sourceFunction.cfg sourceFunction.entryBlock args strategy) state)
      (Sem.run (stepNWithContext (target.forFunction targetFunction) fuel target.maxCallDepth
        targetFunction.cfg targetFunction.entryBlock args strategy) state)) :
    observe (Sem.run (evalFunctionInContext source requested args fuel strategy) state) =
      observe (Sem.run (evalFunctionInContext target requested args fuel strategy) state) :=
  observe_eq_of_effectRelation (entry_effect_of_steps source target requested sourceFunction targetFunction
    sourceFound targetFound body args fuel strategy state steps)

theorem missing_entry_observe_eq (source target : EvalContext) (requested : FuncId)
    (sourceMissing : source.functions requested = none) (targetMissing : target.functions requested = none)
    (args : List Value) (fuel : Nat) (strategy : PanicStrategy) (state : MachineState) :
    observe (Sem.run (evalFunctionInContext source requested args fuel strategy) state) =
      observe (Sem.run (evalFunctionInContext target requested args fuel strategy) state) := by
  simp only [evalFunctionInContext, sourceMissing, targetMissing]
  rfl

end TrustIr.GenericCoro.EntryObservation
