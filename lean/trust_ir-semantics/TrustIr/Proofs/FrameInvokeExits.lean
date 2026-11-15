-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0
import TrustIr.Proofs.FrameInvokeBoundary

namespace TrustIr.FrameLifetime
open GenericCoro GenericCoro.Prefix

/-- Successful read-only checks are insufficient for an exit theorem: a check
must also be unable to manufacture an unchecked embedded unwind state. -/
def CallCheckNoUnwind {α : Type} (action : Sem α) : Prop :=
  ∀ state exception after, Sem.run action state ≠ .error (.unwinding exception after)

theorem FrameCalleeExit.history (before middle : MachineState)
    (result : Except SemError (List Value × MachineState)) (history : HistoryExtends before middle)
    (valid : FrameCalleeExit middle result) : FrameCalleeExit before result := by
  cases result with
  | ok pair => exact ⟨valid.1,valid.2.1,history.trans valid.2.2⟩
  | error error =>
    cases error <;> first | exact True.intro | exact ⟨valid.1,history.trans valid.2⟩

/-- Original Invoke arity/poison validation can refuse a return but cannot
introduce a synthetic unwind state. -/
theorem invoke_returns_no_unwind (ctx : EvalContext) (returnTys : List Ty)
    (message : String) (values : List Value) :
    CallCheckNoUnwind (checkReturns ctx returnTys true false message values) := by
  intro state exception after run
  unfold checkReturns Sem.rejectPoisonValues at run
  cases arity : checkReturnArity values returnTys with
  | error error =>
    simp [arity,Sem.throwTypeError,Sem.run,StateT.run,StateT.bind,StateT.lift,
      throw,throwThe,MonadExceptOf.throw,bind,pure,Except.bind,Except.pure] at run
  | ok unit =>
    cases unit
    simp only [arity,pure_bind,Bool.false_eq_true,↓reduceIte] at run
    split at run <;>
      simp [Sem.throwUB,Sem.run,StateT.run,StateT.bind,StateT.lift,
        throw,throwThe,MonadExceptOf.throw,bind,pure,Except.bind,Except.pure] at run

/-- Full exit preservation for the real Invoke frame protocol, including
uncaught and rethrown unwinds from either continuation. Callee and continuation
exit contracts remain explicit until the recursive CFG induction supplies them. -/
theorem invoke_frame_exit (strategy : PanicStrategy) (check : List Value → Sem Unit)
    (callee : Sem (List Value)) (normal : List Value → Sem (List Value)) (unwind : Addr → Sem (List Value))
    (s : MachineState) (valid : WellMintedState s)
    (readonly : ∀ returned, CallCheckReadOnly (check returned))
    (safe : ∀ returned, CallCheckNoUnwind (check returned))
    (execution : FrameCalleeExit (callerWorld s) (Sem.run callee (callerWorld s)))
    (normalValid : ∀ returned before, WellMintedState before → MintedArgs before.nextFrameLineage returned →
      FrameCalleeExit before (Sem.run (normal returned) before))
    (unwindValid : ∀ exception before, WellMintedState before →
      FrameCalleeExit before (Sem.run (unwind exception) before)) :
    FrameCalleeExit s (Sem.run (invokeFrameWith strategy check callee normal unwind) s) := by
  change FrameCalleeExit s (Sem.run (finishInvokeWith strategy check (saveFrame s none) callee normal unwind) (callerWorld s))
  unfold finishInvokeWith
  rw [Sem.run_bind,invokeCatch_run]
  cases executed : Sem.run callee (callerWorld s) with
  | ok pair =>
    obtain ⟨returned,after⟩ := pair
    rw [executed] at execution
    obtain ⟨afterValid,incoming,history⟩ := execution
    simp only [Except.bind]
    unfold finishInvokeReturnWith
    rw [Sem.run_bind]
    cases checked : Sem.run (check returned) after with
    | error error =>
      simp only [Except.bind]
      cases error <;> first
        | exact True.intro
        | exact False.elim (safe returned after _ _ checked)
    | ok pair =>
      obtain ⟨unit,middle⟩ := pair
      cases unit
      have same := readonly returned after ((),middle) checked
      change middle = after at same
      subst middle
      simp only [Except.bind]
      change FrameCalleeExit s (Sem.run (normal returned) (restoreFrame after (saveFrame s none) []))
      obtain ⟨restoredValid,returnedValid,restoredHistory⟩ := restore_frame_after_exit s after returned valid afterValid incoming history
      exact FrameCalleeExit.history s _ _ restoredHistory (normalValid returned _ restoredValid returnedValid)
  | error error =>
    rw [executed] at execution
    cases strategy with
    | abort =>
      change FrameCalleeExit s (.error error)
      exact FrameCalleeExit.history s (callerWorld s) _ (history_clear_locals s) execution
    | unwind =>
      cases error
      case unwinding exception after =>
        obtain ⟨afterValid,history⟩ := execution
        change FrameCalleeExit s (Sem.run (unwind exception) (restoreFrame after (saveFrame s none) []))
        obtain ⟨restoredValid,_,restoredHistory⟩ := restore_frame_after_exit s after [] valid afterValid (fun _ member => nomatch member) history
        exact FrameCalleeExit.history s _ _ restoredHistory (unwindValid exception _ restoredValid)
      all_goals exact True.intro

/-- Original Invoke checker, with both checker premises discharged. -/
theorem checked_invoke_frame_exit (strategy : PanicStrategy) (ctx : EvalContext) (returnTys : List Ty)
    (message : String) (callee : Sem (List Value)) (normal : List Value → Sem (List Value))
    (unwind : Addr → Sem (List Value)) (s : MachineState) (valid : WellMintedState s)
    (execution : FrameCalleeExit (callerWorld s) (Sem.run callee (callerWorld s)))
    (normalValid : ∀ returned before, WellMintedState before → MintedArgs before.nextFrameLineage returned →
      FrameCalleeExit before (Sem.run (normal returned) before))
    (unwindValid : ∀ exception before, WellMintedState before →
      FrameCalleeExit before (Sem.run (unwind exception) before)) :
    FrameCalleeExit s (Sem.run (invokeFrameWith strategy (checkReturns ctx returnTys true false message) callee normal unwind) s) :=
  invoke_frame_exit strategy _ callee normal unwind s valid
    (fun returned => check_returns_readonly ctx returnTys true false message returned)
    (fun returned => invoke_returns_no_unwind ctx returnTys message returned)
    execution normalValid unwindValid

/-- A real Resume propagates the exact current state, after validating its
recorded exception pointer. It cannot substitute an arbitrary throw world. -/
theorem resume_unwind_state (id : ValueId) (s after : MachineState) (exception : Addr)
    (run : Sem.run (semResumeUnwind id) s = .error (.unwinding exception after)) : after = s := by
  cases found : s.lookupValue id with
  | none =>
    simp [semResumeUnwind,Sem.lookupValue,found,Sem.throwTypeError,Sem.run,Sem.getState,
      StateT.run,StateT.bind,StateT.get,StateT.pure,StateT.lift,
      bind,pure,Except.bind,Except.pure,throw,throwThe,MonadExceptOf.throw] at run
  | some held =>
    cases held
    case ptr address provenance =>
      by_cases recorded : s.exceptions.any (fun row => row.1 == address) = true
      · simp only [semResumeUnwind,Sem.lookupValue,found,Sem.run,Sem.getState,
          StateT.run,StateT.bind,StateT.get,StateT.pure,StateT.lift,
          bind,pure,Except.bind,Except.pure,throw,throwThe,MonadExceptOf.throw,recorded,↓reduceIte] at run
        cases run
        rfl
      · simp [semResumeUnwind,Sem.lookupValue,found,Sem.throwUB,Sem.run,Sem.getState,
          StateT.run,StateT.bind,StateT.get,StateT.pure,StateT.lift,
          bind,pure,Except.bind,Except.pure,throw,throwThe,MonadExceptOf.throw,recorded] at run
    all_goals simp [semResumeUnwind,Sem.lookupValue,found,Sem.throwUB,Sem.run,Sem.getState,
      StateT.run,StateT.bind,StateT.get,StateT.pure,StateT.lift,
      bind,pure,Except.bind,Except.pure,throw,throwThe,MonadExceptOf.throw] at run

/-- Re-raising through a pad with no catch/cleanup preserves the exact input
state; every other pad refusal remains its original non-unwind error. -/
theorem enter_pad_unwind_state (cfg : CFG) (exception : Addr) (dest : BlockId)
    (s after : MachineState) (raised : Addr)
    (run : Sem.run (semEnterPad cfg exception dest) s = .error (.unwinding raised after)) : after = s := by
  cases found : cfg dest with
  | none =>
    simp [semEnterPad,found,Sem.throwTypeError,Sem.run,StateT.run,StateT.lift,
      throw,throwThe,MonadExceptOf.throw,bind,pure,Except.bind,Except.pure] at run
  | some block =>
    cases pad : block.body.head?.bind Inst.padClauses with
    | none =>
      simp [semEnterPad,found,pad,Sem.throwTypeError,Sem.run,StateT.run,StateT.lift,
        throw,throwThe,MonadExceptOf.throw,bind,pure,Except.bind,Except.pure] at run
    | some pair =>
      obtain ⟨cleanup,clauses⟩ := pair
      simp only [semEnterPad,found,pad,Sem.run,Sem.getState,Sem.setState,Sem.modifyState,
        StateT.run,StateT.bind,StateT.get,StateT.set,StateT.pure,StateT.lift,Function.comp_apply,
        bind,pure,Except.bind,Except.pure] at run
      cases recorded : s.exceptions.find? (fun row => row.1 == exception) with
      | none =>
        simp [recorded,Sem.throwTypeError,StateT.lift,throw,throwThe,MonadExceptOf.throw,bind,pure,Except.bind,Except.pure] at run
      | some entry =>
        obtain ⟨address,id,message,site⟩ := entry
        simp only [recorded] at run
        by_cases typed : clauses.any (· != 0) = true
        · simp [typed,Sem.throwUnsupported,StateT.lift,throw,throwThe,MonadExceptOf.throw,bind,pure,Except.bind,Except.pure] at run
        · simp only [typed,↓reduceIte] at run
          by_cases catches : clauses.contains 0 = true
          · simp only [catches,↓reduceIte] at run
            cases run
          · simp only [catches,↓reduceIte] at run
            cases cleanup <;> simp only [Bool.false_eq_true,↓reduceIte] at run
            · cases run
              rfl
            · cases run

end TrustIr.FrameLifetime

