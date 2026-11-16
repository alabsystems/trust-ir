-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0
import TrustIr.Proofs.AYUnaryCFGReplay
import TrustIr.Proofs.UnwindProps

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

/-- A bounded point execution of the public entry. Failed entry guards retain
no invented CFG proof; successful guards retain the actual scoped function,
state and source-indexed checked CFG trace. -/
inductive EntryTrace (ctx : EvalContext) (entry : FuncId) (args : List Value)
    (fuel : Nat) (state : MachineState) where
  | rejected (error : SemError) (actual : Sem.run (entryChecks ctx entry args) state = .error error)
  | executed (function : EvalFunction) (afterChecks : MachineState)
      (actual : Sem.run (entryChecks ctx entry args) state = .ok (function,afterChecks))
      (trace : CFGTrace (ctx.forFunction function) function.cfg fuel function.entryBlock args afterChecks)

def EntryTrace.outcome {ctx entry args fuel state} (checked : EntryTrace ctx entry args fuel state)
    (strategy : PanicStrategy) : Except SemError (List Value × MachineState) :=
  match checked with
  | .rejected error _ => .error error
  | .executed function afterChecks _ trace => Sem.run (checkedFinishEntry ctx function.body.returnTys strategy (fun _ => trace.outcome)) afterChecks

def EntryTrace.build (ctx : EvalContext) (entry : FuncId) (args : List Value)
    (fuel : Nat) (state : MachineState) : Except String (EntryTrace ctx entry args fuel state) :=
  match actual : Sem.run (entryChecks ctx entry args) state with
  | .error error => .ok (.rejected error actual)
  | .ok (function,afterChecks) => do
    let trace ← CFGTrace.build (ctx.forFunction function) function.cfg fuel function.entryBlock args afterChecks
    .ok (.executed function afterChecks actual trace)

theorem EntryTrace.correct {ctx entry args fuel state} (checked : EntryTrace ctx entry args fuel state)
    (strategy : PanicStrategy) :
    Sem.run (evalFunctionInContext ctx entry args fuel strategy) state = checked.outcome strategy := by
  rw [entry_decomposition, Sem.run_bind]
  cases checked with
  | rejected error actual => rw [actual]; rfl
  | executed function afterChecks actual trace =>
    rw [actual]
    change Sem.run (checkedFinishEntry ctx function.body.returnTys strategy _) afterChecks = _
    exact checkedFinishEntry_congr ctx function.body.returnTys strategy _ _ afterChecks (trace.correct ctx.maxCallDepth strategy)

theorem EntryTrace.built_correct (ctx : EvalContext) (entry : FuncId) (args : List Value)
    (fuel : Nat) (state : MachineState) (checked : EntryTrace ctx entry args fuel state)
    (_built : EntryTrace.build ctx entry args fuel state = .ok checked) (strategy : PanicStrategy) :
    Sem.run (evalFunctionInContext ctx entry args fuel strategy) state = checked.outcome strategy := checked.correct strategy

/-- Entry guards retain precedence over CFG fuel exhaustion. In particular,
zero fuel never inspects or requires support for an unreachable body. -/
theorem EntryTrace.build_zero (ctx : EvalContext) (entry : FuncId) (args : List Value)
    (state : MachineState) :
    ∃ checked, EntryTrace.build ctx entry args 0 state = .ok checked := by
  unfold EntryTrace.build
  split <;> exact ⟨_,rfl⟩

/-- A rejected public entry does not request any CFG or unary receipts. -/
theorem EntryTrace.build_rejected (ctx : EvalContext) (entry : FuncId) (args : List Value)
    (fuel : Nat) (state : MachineState) (error : SemError)
    (actual : Sem.run (entryChecks ctx entry args) state = .error error) :
    EntryTrace.build ctx entry args fuel state = .ok (.rejected error actual) := by
  unfold EntryTrace.build
  split
  · rename_i held selected
    have same := actual.symm.trans selected
    cases same
    rfl
  · rename_i function after selected
    have impossible := actual.symm.trans selected
    cases impossible

end TrustIr.AYUnaryReplay
