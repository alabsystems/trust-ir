-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0
import TrustIr.Proofs.FrameDirectCalls

namespace TrustIr.FrameLifetime
open GenericCoro GenericCoro.Prefix

/-- Successful return validation observes the state without changing it. -/
def CallCheckReadOnly {α : Type} (action : Sem α) : Prop :=
  ∀ state result, Sem.run action state = .ok result → result.2 = state

private theorem pure_readonly {α : Type} (value : α) : CallCheckReadOnly (pure value : Sem α) := by
  intro state result run
  cases run
  rfl

private theorem throw_readonly {α : Type} (error : SemError) : CallCheckReadOnly (throw error : Sem α) := by
  intro state result run
  cases run

private theorem bind_readonly {α β : Type} (action : Sem α) (next : α → Sem β)
    (first : CallCheckReadOnly action) (rest : ∀ value, CallCheckReadOnly (next value)) :
    CallCheckReadOnly (action >>= next) := by
  intro state result run
  rw [Sem.run_bind] at run
  cases executed : Sem.run action state with
  | error error => rw [executed] at run; cases run
  | ok pair =>
    have tail : Sem.run (next pair.1) pair.2 = .ok result := by simpa [executed] using run
    exact (rest pair.1 pair.2 result tail).trans (first state pair executed)

private theorem forIn_readonly {α β : Type} (items : List α) (initial : β)
    (action : α → β → Sem (ForInStep β))
    (readonly : ∀ item ∈ items, ∀ value, CallCheckReadOnly (action item value)) :
    CallCheckReadOnly (forIn items initial action) := by
  induction items generalizing initial with
  | nil => exact pure_readonly _
  | cons item rest ih =>
    rw [List.forIn_cons]
    refine bind_readonly _ _ (readonly item ((trustIrListMemConsSelf _ _)) initial) ?_
    intro step
    cases step with
    | done value => exact pure_readonly _
    | yield value => exact ih value (fun item member => readonly item (List.mem_cons_of_mem _ member))

/-- Includes original arity, poison and typed-closure return validation. -/
theorem check_returns_readonly (ctx : EvalContext) (returnTys : List Ty)
    (poison closure : Bool) (message : String) (values : List Value) :
    CallCheckReadOnly (checkReturns ctx returnTys poison closure message values) := by
  unfold checkReturns
  apply bind_readonly
  · split <;> first | exact pure_readonly _ | exact throw_readonly _
  · intro _
    apply bind_readonly
    · cases poison <;> simp only [Bool.false_eq_true, if_false, if_true]
      · exact pure_readonly _
      · unfold Sem.rejectPoisonValues
        split <;> first | exact pure_readonly _ | exact throw_readonly _
    · intro _
      cases closure <;> simp only [Bool.false_eq_true, if_false, if_true]
      · exact pure_readonly _
      · apply bind_readonly
        · apply forIn_readonly
          intro input member _
          cases input
          dsimp only
          split <;> first
            | exact pure_readonly _
            | exact bind_readonly _ _ (throw_readonly _) (fun _ => pure_readonly _)
        · intro _
          exact pure_readonly _

/-- Consume actual callee and return-check success before restoring the caller.
The check is not replaced by an independently assumed successful validation. -/
theorem checked_call_frame_success (check : List Value → Sem Unit) (callee : Sem (List Value))
    (s final : MachineState) (values : List Value) (valid : WellMintedState s)
    (readonly : ∀ returned, CallCheckReadOnly (check returned))
    (execution : ∀ after returned, Sem.run callee (callerWorld s) = .ok (returned,after) →
      DirectFrameResult (callerWorld s) after returned)
    (run : Sem.run (callFrameWith check callee) s = .ok (values,final)) : DirectFrameResult s final values := by
  change Sem.run (finishCalleeWith check (saveFrame s none) callee) (callerWorld s) = .ok (values,final) at run
  unfold finishCalleeWith at run
  rw [Sem.run_bind] at run
  cases executed : Sem.run callee (callerWorld s) with
  | error error => rw [executed] at run; cases run
  | ok pair =>
    obtain ⟨returned,after⟩ := pair
    have tail := run
    simp only [executed, Except.bind] at tail
    obtain ⟨afterValid,returnedValid,calleeHistory⟩ := execution after returned executed
    rw [Sem.run_bind] at tail
    cases checked : Sem.run (check returned) after with
    | error error => rw [checked] at tail; cases tail
    | ok pair =>
      obtain ⟨unit,middle⟩ := pair
      cases unit
      have same := readonly returned after ((),middle) checked
      change middle = after at same
      subst middle
      simp only [checked, Except.bind] at tail
      change Except.ok (returned,restoreFrame after (saveFrame s none) []) = Except.ok (values,final) at tail
      cases tail
      have history := (history_clear_locals s).trans calleeHistory
      have saved := saved_values_history s after (saveFrame s none) valid.values history
      exact ⟨WellMintedState.restore after (saveFrame s none) [] afterValid.table saved (fun _ member => nomatch member),
        returnedValid,history.trans (history_restore after (saveFrame s none) [])⟩

/-- The concrete checked return boundary used by indirect calls. Dispatch and
argument preparation must still establish the recursive execution contract. -/
theorem indirect_return_frame_success (ctx : EvalContext) (returnTys : List Ty)
    (closure : Bool) (message : String) (callee : Sem (List Value))
    (s final : MachineState) (values : List Value) (valid : WellMintedState s)
    (execution : ∀ after returned, Sem.run callee (callerWorld s) = .ok (returned,after) →
      DirectFrameResult (callerWorld s) after returned)
    (run : Sem.run (callFrameWith (checkReturns ctx returnTys true closure message) callee) s =
      .ok (values,final)) : DirectFrameResult s final values :=
  checked_call_frame_success _ callee s final values valid
    (fun returned => check_returns_readonly ctx returnTys true closure message returned) execution run

end TrustIr.FrameLifetime
