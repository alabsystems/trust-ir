-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0
import TrustIr.Proofs.UnwindProps

/-! The existing public function-entry guards and decomposition, without an
AY replay strategy dependency. Public names and proof bodies are unchanged. -/
namespace TrustIr.AYUnaryReplay

/-- The public runner's actual entry checks, in their original order. -/
def entryChecks (ctx : EvalContext) (entry : FuncId) (args : List Value) : Sem EvalFunction := do
  let function ← match ctx.functions entry with
    | some function => pure function
    | none => Sem.throwTypeError "evalFunctionInContext: undefined entry function"
  requireUntypedAbi function.body.abi
  match checkCallArity args function.body.paramTys with
  | .ok () => pure ()
  | .error message => Sem.throwTypeError ("evalFunctionInContext: " ++ message)
  Sem.rejectPoisonValues args "Call arguments"
  let _ ← Sem.fromMemoryExcept (checkFunctionItemValues ctx function.body.paramTys args)
  pure function

/-- Keep unwind conversion and return poison checking outside the checked
CFG receipt. The replacement action is used only at its indexed start state. -/
def finishEntry (strategy : PanicStrategy) (action : Sem (List Value)) : Sem (List Value) := do
  let values ← exitUnwinding strategy action
  Sem.rejectPoisonValues values "Call returns"
  pure values

/-- The public runner's contextual return validation follows its original
unwind conversion and poison check, using the selected function's return types. -/
def checkedFinishEntry (ctx : EvalContext) (returnTys : List Ty)
    (strategy : PanicStrategy) (action : Sem (List Value)) : Sem (List Value) := do
  let values ← finishEntry strategy action
  let _ ← Sem.fromMemoryExcept (checkFunctionItemValues ctx returnTys values)
  pure values

theorem entry_decomposition (ctx : EvalContext) (entry : FuncId) (args : List Value)
    (fuel : Nat) (strategy : PanicStrategy) :
    evalFunctionInContext ctx entry args fuel strategy = (do
      let function ← entryChecks ctx entry args
      checkedFinishEntry ctx function.body.returnTys strategy (stepNWithContext (ctx.forFunction function) fuel ctx.maxCallDepth
        function.cfg function.entryBlock args strategy)) := by
  cases found : ctx.functions entry with
  | none =>
    simp only [evalFunctionInContext, entryChecks, found, checkedFinishEntry, finishEntry, bind_assoc]
    rfl
  | some function =>
    simp only [evalFunctionInContext, entryChecks, found, pure_bind, checkedFinishEntry, finishEntry, bind_assoc]
    congr 1
    funext _unit
    cases arity : checkCallArity args function.body.paramTys with
    | error message => simp only [arity, bind_assoc, pure_bind]
    | ok unit => cases unit; simp only [arity, bind_assoc, pure_bind]

/-- Identical raw outcomes at this state have identical public entry outcomes,
including the original unwind handler's exception lookup and full error data. -/
theorem finishEntry_congr (strategy : PanicStrategy) (left right : Sem (List Value))
    (state : MachineState) (same : Sem.run left state = Sem.run right state) :
    Sem.run (finishEntry strategy left) state = Sem.run (finishEntry strategy right) state := by
  have exited : Sem.run (exitUnwinding strategy left) state = Sem.run (exitUnwinding strategy right) state := by
    cases strategy with
    | abort => exact same
    | unwind => simp only [exitUnwinding, Sem.run_tryCatch, same]
  simp only [finishEntry, Sem.run_bind, exited]

theorem checkedFinishEntry_congr (ctx : EvalContext) (returnTys : List Ty)
    (strategy : PanicStrategy) (left right : Sem (List Value))
    (state : MachineState) (same : Sem.run left state = Sem.run right state) :
    Sem.run (checkedFinishEntry ctx returnTys strategy left) state =
      Sem.run (checkedFinishEntry ctx returnTys strategy right) state := by
  have finished := finishEntry_congr strategy left right state same
  simp only [checkedFinishEntry, Sem.run_bind, finished]

end TrustIr.AYUnaryReplay
