-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0
import TrustIr.Proofs.AYUnaryCFGReplay
import TrustIr.Proofs.UnwindProps
import TrustIr.Proofs.FunctionEntryLayer

namespace TrustIr.AYUnaryReplay

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
