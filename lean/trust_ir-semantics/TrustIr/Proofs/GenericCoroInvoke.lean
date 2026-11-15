-- Copyright 2026 Andrew Yates | Apache-2.0
import TrustIr.Proofs.GenericCoroProps
import TrustIr.Proofs.HeldMemoryFrames
import TrustIr.Proofs.UnwindProps

namespace TrustIr.GenericCoro

/-- Return checking occurs before restoring the saved caller, exactly as in
    the contextual Invoke and InvokeIndirect branches. -/
def finishInvokeReturnWith {α : Type} (check : List Value → Sem Unit) (frame : StackFrame)
    (values : List Value) (normal : List Value → Sem α) : Sem α := do
  check values
  let state ← Sem.getState
  Sem.setState (restoreFrame state frame [])
  normal values

theorem finishInvokeReturnWith_eq {α : Type} (check : List Value → Sem Unit)
    (equivariant : ∀ values, HeldMemoryFrames.Equivariant (check values))
    (frame : StackFrame) (values : List Value) (normal : List Value → Sem α)
    (source target : MachineState) (world : callerWorld source = callerWorld target) :
    Sem.run (finishInvokeReturnWith check frame values normal) source =
      Sem.run (finishInvokeReturnWith check frame values normal) target := by
  unfold finishInvokeReturnWith
  simp only [Sem.run_bind]
  rw [equivariant_transport (check values) (equivariant values) source target world]
  cases checked : Sem.run (check values) source with
  | error error => rfl
  | ok result => rfl

/-- Both normal and caught-unwind outcomes restore the real saved frame.
    The embedded throw state is kept intact by the catch operation. -/
def finishInvokeWith {α : Type} (strategy : PanicStrategy) (check : List Value → Sem Unit)
    (frame : StackFrame) (callee : Sem (List Value))
    (normal : List Value → Sem α) (unwind : Addr → Sem α) : Sem α := do
  let outcome ← invokeCatch strategy callee
  match outcome with
  | .inl values => finishInvokeReturnWith check frame values normal
  | .inr (exception, state) =>
    Sem.setState (restoreFrame state frame [])
    unwind exception

private theorem run_tryCatch {α : Type} (action : Sem α) (handler : SemError → Sem α)
    (state : MachineState) :
    Sem.run (tryCatch action handler) state =
      (match Sem.run action state with
       | .ok result => .ok result
       | .error error => Sem.run (handler error) state) := by
  rw [Sem.run_tryCatch]
  cases Sem.run action state <;> rfl

trustIrDenseMatch
/-- Catching preserves the exact exception and embedded throw state. -/
theorem invokeCatch_run (strategy : PanicStrategy) (callee : Sem (List Value))
    (state : MachineState) :
    Sem.run (invokeCatch strategy callee) state =
      (match Sem.run callee state with
       | .ok (values, after) => .ok (.inl values, after)
       | .error error =>
         match strategy, error with
         | .unwind, .unwinding exception after => .ok (.inr (exception, after), state)
         | _, _ => .error error) := by
  cases strategy <;> simp only [invokeCatch, run_tryCatch, Sem.run_bind, Sem.run_pure]
  all_goals
    cases run : Sem.run callee state with
    | error error => cases error <;> rfl
    | ok result => cases result <;> rfl

/-- Exact callee errors and equal returned values/non-SSA worlds suffice for
    equality after the actual invoke restoration, with arbitrary continuations. -/
theorem finishInvokeWith_eq_of_effectRelation {α : Type} (strategy : PanicStrategy)
    (check : List Value → Sem Unit)
    (equivariant : ∀ values, HeldMemoryFrames.Equivariant (check values))
    (frame : StackFrame) (source target : Sem (List Value))
    (normal : List Value → Sem α) (unwind : Addr → Sem α)
    (sourceState targetState : MachineState)
    (related : EffectRelation (Sem.run source sourceState) (Sem.run target targetState)) :
    Sem.run (finishInvokeWith strategy check frame source normal unwind) sourceState =
      Sem.run (finishInvokeWith strategy check frame target normal unwind) targetState := by
  unfold finishInvokeWith
  simp only [Sem.run_bind]
  rw [invokeCatch_run, invokeCatch_run]
  generalize sourceRun : Sem.run source sourceState = sourceResult at related ⊢
  generalize targetRun : Sem.run target targetState = targetResult at related ⊢
  cases related with
  | error error => cases strategy <;> cases error <;> rfl
  | returned values source target world =>
    exact finishInvokeReturnWith_eq check equivariant frame values normal source target world

end TrustIr.GenericCoro

#trustIrAxiomsExact TrustIr.GenericCoro.invokeCatch_run == []
#trustIrAxiomsExact TrustIr.GenericCoro.finishInvokeWith == []
#trustIrAxiomsExact TrustIr.GenericCoro.finishInvokeWith_eq_of_effectRelation == []
