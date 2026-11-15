-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0
import TrustIr.Proofs.FramePublicationExits

namespace TrustIr.FrameLifetime
open GenericCoro GenericCoro.Prefix

private theorem pure_readonly {α : Type} (value : α) : CallCheckReadOnly (pure value : Sem α) := by
  intro state result run
  cases run
  rfl

private theorem throw_readonly {α : Type} (error : SemError) : CallCheckReadOnly (throw error : Sem α) := by
  intro state result run
  cases run

private theorem bind_readonly {α β : Type} (action : Sem α) (next : α → Sem β)
    (first : CallCheckReadOnly action) (rest : ∀ value, CallCheckReadOnly (next value)) : CallCheckReadOnly (action >>= next) := by
  intro state result run
  rw [Sem.run_bind] at run
  cases executed : Sem.run action state with
  | error error => rw [executed] at run; cases run
  | ok pair =>
    have tail : Sem.run (next pair.1) pair.2 = .ok result := by simpa [executed] using run
    exact (rest pair.1 pair.2 result tail).trans (first state pair executed)

private theorem pure_no_unwind {α : Type} (value : α) : CallCheckNoUnwind (pure value : Sem α) := by
  intro state exception after run
  cases run

private theorem type_no_unwind {α : Type} (message : String) : CallCheckNoUnwind (Sem.throwTypeError message : Sem α) := by
  intro state exception after run
  cases run

private theorem ub_no_unwind {α : Type} (message : String) : CallCheckNoUnwind (Sem.throwUB message : Sem α) := by
  intro state exception after run
  cases run

private theorem unsupported_no_unwind {α : Type} (feature : UnsupportedFeature) (message : String) :
    CallCheckNoUnwind (Sem.throwUnsupported feature message : Sem α) := by
  intro state exception after run
  cases run

/-- Original ABI/arity/poison header checking only observes caller state. -/
theorem direct_header_readonly (body : FuncBody) (args : List Value) : CallCheckReadOnly (directCallHeader body args) := by
  unfold directCallHeader requireUntypedAbi Sem.rejectPoisonValues
  repeat' first
    | exact pure_readonly _
    | exact throw_readonly _
    | (refine bind_readonly _ _ ?_ (fun value => ?_) <;> dsimp only)
    | split

theorem direct_header_no_unwind (body : FuncBody) (args : List Value) : CallCheckNoUnwind (directCallHeader body args) := by
  unfold directCallHeader requireUntypedAbi Sem.rejectPoisonValues
  repeat' first
    | exact pure_no_unwind _
    | exact type_no_unwind _
    | exact ub_no_unwind _
    | exact unsupported_no_unwind _ _
    | (refine CallCheckNoUnwind.bind _ _ ?_ (fun value => ?_) <;> dsimp only)
    | split

/-- A header receipt transports the current argument bound, without imposing
that the captured arguments be valid in unrelated states. -/
theorem direct_header_frame_exit (body : FuncBody) (args : List Value) (state : MachineState)
    (valid : WellMintedState state) (incoming : MintedArgs state.nextFrameLineage args) :
    FrameActionExit (fun bound _ => MintedArgs bound args) state (Sem.run (directCallHeader body args) state) := by
  cases executed : Sem.run (directCallHeader body args) state with
  | ok pair =>
    obtain ⟨unit,after⟩ := pair
    cases unit
    have same := direct_header_readonly body args state ((),after) executed
    change after = state at same
    subst after
    exact ⟨valid,incoming,.refl _⟩
  | error error =>
    cases error <;> first | exact True.intro | exact False.elim (direct_header_no_unwind body args state _ _ executed)

/-- Actual target resolution retains both function-table provenance and the
already-minted argument receipt for the next checks. -/
theorem target_lookup_arguments_exit (ctx : EvalContext) (id : FuncId) (args : List Value) (state : MachineState)
    (declaredMessage missingMessage : String)
    (valid : WellMintedState state) (incoming : MintedArgs state.nextFrameLineage args) :
    FrameActionExit (fun bound callee => ctx.functions id = some callee ∧ MintedArgs bound args) state
      (Sem.run (ctx.lookupDirectCallee id declaredMessage missingMessage) state) := by
  cases found : ctx.functions id with
  | some callee =>
    simp only [EvalContext.lookupDirectCallee,found]
    exact ⟨valid,⟨rfl,incoming⟩,.refl _⟩
  | none =>
    cases declared : ctx.declared id <;>
      simp [EvalContext.lookupDirectCallee,found,declared,Sem.throwTypeError,Sem.throwUnsupported,
        Sem.run,StateT.run,StateT.lift,throw,throwThe,MonadExceptOf.throw,bind,pure,Except.bind,Except.pure,FrameActionExit]

theorem direct_lookup_arguments_exit (ctx : EvalContext) (id : FuncId) (args : List Value) (state : MachineState)
    (valid : WellMintedState state) (incoming : MintedArgs state.nextFrameLineage args) :
    FrameActionExit (fun bound callee => ctx.functions id = some callee ∧ MintedArgs bound args) state
      (Sem.run (ctx.lookupDirectCallee id "Call: callee is a bodyless declaration" "Call: undefined function") state) :=
  target_lookup_arguments_exit ctx id args state "Call: callee is a bodyless declaration" "Call: undefined function" valid incoming

/-- Original direct body-call dispatch preserves both normal and unwind
exits. The smaller-fuel callee EXIT contract must be supplied by CFG induction;
a success-only callee hypothesis is insufficient. All original guards and
publication are consumed from the same execution path. -/
theorem direct_body_call_exit (recurse : Recurse) (ctx : EvalContext) (depth : Nat)
    (strategy : PanicStrategy) (id : FuncId) (args dests : List ValueId) (state : MachineState)
    (valid : WellMintedState state)
    (execution : ∀ callee, ctx.functions id = some callee → ∀ childDepth values before,
      WellMintedState before → MintedArgs before.nextFrameLineage values →
      FrameCalleeExit before (Sem.run (recurse (ctx.forFunction callee) childDepth callee.cfg callee.entryBlock values strategy) before)) :
    FrameActionExit (fun _ _ => True) state
      (Sem.run (evalBodyStep recurse ctx depth strategy (.Call id args,dests)) state) := by
  rw [evalBodyStep_call]
  unfold bodyCall
  apply FrameActionExit.bind MintedArgs (fun _ _ => True) _ _ state (lookup_arguments_action args state valid)
  intro values before beforeValid incoming
  cases depth with
  | zero => exact True.intro
  | succ depth =>
    apply FrameActionExit.bind (fun bound callee => ctx.functions id = some callee ∧ MintedArgs bound values)
      (fun _ _ => True) _ _ before (direct_lookup_arguments_exit ctx id values before beforeValid incoming)
    intro callee caller callerValid receipt
    obtain ⟨found,incoming⟩ := receipt
    apply FrameActionExit.bind (fun bound _ => MintedArgs bound values) (fun _ _ => True) _ _ caller
      (direct_header_frame_exit callee.body values caller callerValid incoming)
    intro unit checked checkedValid incoming
    cases unit
    have enteredValid : WellMintedState (callerWorld checked) := ⟨checkedValid.table,values_empty _⟩
    have called := direct_call_frame_exit callee.body.returnTys _ checked checkedValid
      (execution callee found depth values (callerWorld checked) enteredValid incoming)
    apply FrameActionExit.bind MintedArgs (fun _ _ => True) _ _ checked ((FrameActionExit.callee checked _).2 called)
    intro returned restored restoredValid returnedValid
    apply FrameActionExit.bind (fun _ _ => True) (fun _ _ => True) _ _ restored
      (call_results_frame_exit ctx (.Call id args) dests returned restored restoredValid returnedValid)
    intro unit published publishedValid _
    cases unit
    exact ⟨publishedValid,True.intro,.refl _⟩

end TrustIr.FrameLifetime
