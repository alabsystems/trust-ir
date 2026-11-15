-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0
import TrustIr.Proofs.FrameAllTailCalls

namespace TrustIr.FrameLifetime
open GenericCoro GenericCoro.Prefix

private theorem run_bind {α β : Type} (action : Sem α) (next : α → Sem β) (state : MachineState) :
    Sem.run (action >>= next) state =
      (Sem.run action state >>= fun pair => Sem.run (next pair.1) pair.2) := rfl

private theorem split_bind_success {α β : Type} (action : Sem α) (next : α → Sem β)
    (s final : MachineState) (result : β)
    (run : Sem.run (action >>= next) s = .ok (result, final)) :
    ∃ value middle, Sem.run action s = .ok (value, middle) ∧
      Sem.run (next value) middle = .ok (result, final) := by
  rw [run_bind] at run
  cases step : Sem.run action s with
  | error error => simp [step, bind, Except.bind] at run
  | ok pair => exact ⟨pair.1, pair.2, rfl, by simpa [step] using run⟩

/-- Both exits that Invoke can consume carry a valid non-rewinding frame
world. Other errors propagate and make no claim about a missing final state. -/
def FrameCalleeExit (before : MachineState) : Except SemError (List Value × MachineState) → Prop
  | .ok (values,after) => DirectFrameResult before after values
  | .error (.unwinding _ after) => WellMintedState after ∧ HistoryExtends before after
  | .error _ => True

def CaughtFrameExit (before : MachineState) :
    (List Value ⊕ (Addr × MachineState)) × MachineState → Prop
  | (.inl values,after) => DirectFrameResult before after values
  | (.inr (_,after),_) => WellMintedState after ∧ HistoryExtends before after

/-- The catch consumes the actual embedded throw state. In the caught case
its ordinary StateT state is still the input state, as in invokeCatch_run. -/
theorem invoke_catch_frame_exit (strategy : PanicStrategy) (callee : Sem (List Value))
    (s : MachineState) (outcome : List Value ⊕ (Addr × MachineState)) (final : MachineState)
    (execution : FrameCalleeExit s (Sem.run callee s))
    (run : Sem.run (invokeCatch strategy callee) s = .ok (outcome,final)) :
    CaughtFrameExit s (outcome,final) := by
  rw [invokeCatch_run] at run
  cases executed : Sem.run callee s with
  | ok pair =>
    rw [executed] at execution run
    cases pair
    cases run
    exact execution
  | error error =>
    rw [executed] at execution run
    cases strategy <;> cases error <;> first
      | (cases run; exact execution)
      | cases run

/-- Restoring caller SSA values uses the later counter and live-lineage table.
No older closed handle can be revived by restoration. -/
theorem restore_frame_after_exit (s after : MachineState) (values : List Value)
    (valid : WellMintedState s) (afterValid : WellMintedState after)
    (incoming : MintedArgs after.nextFrameLineage values)
    (history : HistoryExtends (callerWorld s) after) :
    DirectFrameResult s (restoreFrame after (saveFrame s none) []) values := by
  have history := (history_clear_locals s).trans history
  have saved := saved_values_history s after (saveFrame s none) valid.values history
  exact ⟨WellMintedState.restore after (saveFrame s none) [] afterValid.table saved (fun _ member => nomatch member),
    incoming,history.trans (history_restore after (saveFrame s none) [])⟩

/-- The real Invoke frame protocol covers both checked normal returns and
caught unwinds. Continuations consume the actual restored caller state; the
embedded unwind-state contract remains explicit until CFG induction supplies it. -/
theorem invoke_frame_success (strategy : PanicStrategy) (check : List Value → Sem Unit)
    (callee : Sem (List Value)) (normal : List Value → Sem (List Value)) (unwind : Addr → Sem (List Value))
    (s final : MachineState) (values : List Value) (valid : WellMintedState s)
    (readonly : ∀ returned, CallCheckReadOnly (check returned))
    (execution : FrameCalleeExit (callerWorld s) (Sem.run callee (callerWorld s)))
    (normalValid : ∀ returned before after result, WellMintedState before → MintedArgs before.nextFrameLineage returned →
      Sem.run (normal returned) before = .ok (result,after) → DirectFrameResult before after result)
    (unwindValid : ∀ exception before after result, WellMintedState before →
      Sem.run (unwind exception) before = .ok (result,after) → DirectFrameResult before after result)
    (run : Sem.run (invokeFrameWith strategy check callee normal unwind) s = .ok (values,final)) :
    DirectFrameResult s final values := by
  change Sem.run (finishInvokeWith strategy check (saveFrame s none) callee normal unwind) (callerWorld s) = .ok (values,final) at run
  unfold finishInvokeWith at run
  obtain ⟨outcome,middle,caught,tail⟩ := split_bind_success _ _ (callerWorld s) final values run
  have caughtValid := invoke_catch_frame_exit strategy callee (callerWorld s) outcome middle execution caught
  cases outcome with
  | inl returned =>
    obtain ⟨afterValid,returnedValid,history⟩ := caughtValid
    unfold finishInvokeReturnWith at tail
    obtain ⟨unit,checked,guarded,tail⟩ := split_bind_success _ _ middle final values tail
    cases unit
    have same := readonly returned middle ((),checked) guarded
    change checked = middle at same
    subst checked
    change Sem.run (normal returned) (restoreFrame middle (saveFrame s none) []) = .ok (values,final) at tail
    obtain ⟨restoredValid,incoming,restoredHistory⟩ := restore_frame_after_exit s middle returned valid afterValid returnedValid history
    obtain ⟨finalValid,returnedValid,nextHistory⟩ := normalValid returned _ final values restoredValid incoming tail
    exact ⟨finalValid,returnedValid,restoredHistory.trans nextHistory⟩
  | inr pair =>
    obtain ⟨exception,after⟩ := pair
    obtain ⟨afterValid,history⟩ := caughtValid
    change Sem.run (unwind exception) (restoreFrame after (saveFrame s none) []) = .ok (values,final) at tail
    obtain ⟨restoredValid,_,restoredHistory⟩ := restore_frame_after_exit s after [] valid afterValid (fun _ member => nomatch member) history
    obtain ⟨finalValid,returnedValid,nextHistory⟩ := unwindValid exception _ final values restoredValid tail
    exact ⟨finalValid,returnedValid,restoredHistory.trans nextHistory⟩

/-- Discharge the read-only premise for the original Invoke arity/poison
checker, rather than assuming an independently successful return check. -/
theorem checked_invoke_frame_success (strategy : PanicStrategy) (ctx : EvalContext) (returnTys : List Ty)
    (message : String) (callee : Sem (List Value)) (normal : List Value → Sem (List Value))
    (unwind : Addr → Sem (List Value)) (s final : MachineState) (values : List Value)
    (valid : WellMintedState s)
    (execution : FrameCalleeExit (callerWorld s) (Sem.run callee (callerWorld s)))
    (normalValid : ∀ returned before after result, WellMintedState before → MintedArgs before.nextFrameLineage returned →
      Sem.run (normal returned) before = .ok (result,after) → DirectFrameResult before after result)
    (unwindValid : ∀ exception before after result, WellMintedState before →
      Sem.run (unwind exception) before = .ok (result,after) → DirectFrameResult before after result)
    (run : Sem.run (invokeFrameWith strategy (checkReturns ctx returnTys true false message) callee normal unwind) s =
      .ok (values,final)) : DirectFrameResult s final values :=
  invoke_frame_success strategy _ callee normal unwind s final values valid
    (fun returned => check_returns_readonly ctx returnTys true false message returned)
    execution normalValid unwindValid run

private theorem word_allocation_no_unwind (model : ByteModel) (memory : Memory)
    (exception : Addr) (after : MachineState) :
    checkWordAllocation model memory 1 1 0 ≠ .error (.unwinding exception after) := by
  intro run
  unfold checkWordAllocation at run
  simp only [bind,pure,Except.bind,Except.pure,throw,throwThe,MonadExceptOf.throw] at run
  repeat' first | (solve | cases run) | contradiction | split at run

/-- Actual exception allocation changes memory/exception bookkeeping, not
caller locals or the frame lineage history. Allocation refusals remain intact. -/
theorem exception_allocation_frame_success (message : String) (site : Option PanicOutcomeSite)
    (model : ByteModel) (s final : MachineState) (exception : Addr) (valid : WellMintedState s)
    (run : Sem.run (semAllocException message site model) s = .ok (exception,final)) :
    WellMintedState final ∧ HistoryExtends s final := by
  cases decision : checkWordAllocation model s.memory 1 1 0 with
  | error error =>
    simp [semAllocException,Sem.checkTargetAllocation,Sem.fromMemoryExcept,decision,
      Sem.run,Sem.getState,Sem.setState,StateT.run,StateT.bind,StateT.get,StateT.set,StateT.pure,
      StateT.lift,bind,pure,Except.bind,Except.pure,throw,throwThe,MonadExceptOf.throw] at run
  | ok unit =>
    cases unit
    simp only [semAllocException,Sem.checkTargetAllocation,Sem.fromMemoryExcept,
      Sem.run,Sem.getState,Sem.setState,StateT.run,StateT.bind,StateT.get,StateT.set,StateT.pure,
      StateT.lift,bind,pure,Except.bind,Except.pure,decision] at run
    cases run
    exact ⟨⟨valid.table,valid.values⟩,⟨Nat.le_refl _,fun _ _ closed => closed⟩⟩

/-- Allocation refusal cannot manufacture an embedded unwind state. -/
theorem exception_allocation_no_unwind (message : String) (site : Option PanicOutcomeSite)
    (model : ByteModel) (s after : MachineState) (exception : Addr) :
    Sem.run (semAllocException message site model) s ≠ .error (.unwinding exception after) := by
  intro run
  cases decision : checkWordAllocation model s.memory 1 1 0 with
  | error error =>
    simp [semAllocException,Sem.checkTargetAllocation,Sem.fromMemoryExcept,decision,
      Sem.run,Sem.getState,Sem.setState,StateT.run,StateT.bind,StateT.get,StateT.set,StateT.pure,
      StateT.lift,bind,pure,Except.bind,Except.pure,throw,throwThe,MonadExceptOf.throw] at run
    subst error
    exact word_allocation_no_unwind model s.memory exception after decision
  | ok unit =>
    cases unit
    simp [semAllocException,Sem.checkTargetAllocation,Sem.fromMemoryExcept,decision,
      Sem.run,Sem.getState,Sem.setState,StateT.run,StateT.bind,StateT.get,StateT.set,StateT.pure,
      StateT.lift,bind,pure,Except.bind,Except.pure,throw,throwThe,MonadExceptOf.throw] at run

/-- The embedded state of a real raise, including its exception allocation,
is frame-valid and retains lineage history. No arbitrary throw state is trusted. -/
theorem raise_frame_exit {α : Type} (message : String) (site : Option PanicOutcomeSite)
    (model : ByteModel) (s after : MachineState) (exception : Addr) (valid : WellMintedState s)
    (run : Sem.run (semRaise (α := α) message site model) s = .error (.unwinding exception after)) :
    WellMintedState after ∧ HistoryExtends s after := by
  unfold semRaise at run
  rw [Sem.run_bind] at run
  cases allocated : Sem.run (semAllocException message site model) s with
  | error error =>
    simp only [allocated,Except.bind] at run
    cases run
    exact False.elim (exception_allocation_no_unwind message site model s after exception allocated)
  | ok pair =>
    obtain ⟨address,final⟩ := pair
    simp only [allocated,Except.bind] at run
    change Except.error (SemError.unwinding address final) = Except.error (SemError.unwinding exception after) at run
    cases run
    exact exception_allocation_frame_success message site model s after exception valid allocated

/-- A successful original landing-pad entry changes only the exception hand,
while retaining recursive frame validity and lineage history. -/
theorem enter_pad_frame_success (cfg : CFG) (exception : Addr) (dest : BlockId)
    (s final : MachineState) (valid : WellMintedState s)
    (run : Sem.run (semEnterPad cfg exception dest) s = .ok ((),final)) :
    WellMintedState final ∧ HistoryExtends s final := by
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
            exact ⟨⟨valid.table,valid.values⟩,⟨Nat.le_refl _,fun _ _ closed => closed⟩⟩
          · simp only [catches,↓reduceIte] at run
            cases cleanup <;> simp only [Bool.false_eq_true,↓reduceIte] at run
            · cases run
            · cases run
              exact ⟨⟨valid.table,valid.values⟩,⟨Nat.le_refl _,fun _ _ closed => closed⟩⟩

end TrustIr.FrameLifetime
