-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0
import TrustIr.Proofs.FrameDirectBodyExits

namespace TrustIr.FrameLifetime
open GenericCoro GenericCoro.Prefix

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

private theorem lookup_no_unwind (id : ValueId) : CallCheckNoUnwind (Sem.lookupValue id) := by
  intro state exception after run
  cases found : state.lookupValue id with
  | none =>
    simp [Sem.lookupValue,found,Sem.throwTypeError,Sem.run,Sem.getState,StateT.run,StateT.bind,
      StateT.get,StateT.pure,StateT.lift,bind,pure,Except.bind,Except.pure,throw,throwThe,MonadExceptOf.throw] at run
  | some value =>
    simp [Sem.lookupValue,found,Sem.run,Sem.getState,StateT.run,StateT.bind,
      StateT.get,StateT.pure,StateT.lift,bind,pure,Except.bind,Except.pure] at run

private theorem partial_no_unwind (value : Value) (message : String) : CallCheckNoUnwind (Sem.rejectPartial value message) := by
  cases value <;> first | exact pure_no_unwind _ | exact ub_no_unwind _

local macro "control_no_unwind_leaves" : tactic => `(tactic|
  repeat' first
    | exact pure_no_unwind _
    | exact type_no_unwind _
    | exact ub_no_unwind _
    | exact unsupported_no_unwind _ _
    | exact lookup_no_unwind _
    | exact partial_no_unwind _ _
    | exact lookup_arguments_no_unwind _
    | (refine CallCheckNoUnwind.bind _ _ ?_ (fun value => ?_) <;> dsimp only)
    | split)

/-- Original ordinary controls inspect only their selected inputs and emit no
synthetic unwind state; callbacks belong to the later transfer phase. -/
theorem FrameControl.action_no_unwind {inst : Inst} (site : FrameControl inst) : CallCheckNoUnwind site.action := by
  cases site <;> unfold FrameControl.action
  · unfold semBr; control_no_unwind_leaves
  · unfold semCondBr; control_no_unwind_leaves
  · unfold semSwitch; control_no_unwind_leaves
  · unfold semReturn; control_no_unwind_leaves
  · exact pure_no_unwind _

theorem FrameControl.action_frame_exit {inst : Inst} (site : FrameControl inst) :
    FrameActionValid TransferValues site.action := by
  apply frame_action_of_success_no_unwind _ _ site.action_no_unwind
  intro state after result valid run
  obtain ⟨same,transported⟩ := site.action_success state after result valid run
  subst after
  exact ⟨valid,transported,.refl _⟩

/-- Ordinary terminators cannot produce a value result or a call request. -/
def OrdinaryTermValues (bound : Nat) : InstrResult → Prop
  | .terminator result => TransferValues bound result
  | _ => False

theorem FrameControl.term_no_unwind {inst : Inst} (site : FrameControl inst)
    (ctx : EvalContext) (depth : Nat) (cfg : CFG) (strategy : PanicStrategy) :
    CallCheckNoUnwind (stepTermWithContext ctx depth cfg inst strategy) := by
  rw [site.stepTerm]
  exact CallCheckNoUnwind.bind _ _ site.action_no_unwind (fun _ => pure_no_unwind _)

theorem FrameControl.term_frame_exit {inst : Inst} (site : FrameControl inst)
    (ctx : EvalContext) (depth : Nat) (cfg : CFG) (strategy : PanicStrategy) :
    FrameActionValid OrdinaryTermValues (stepTermWithContext ctx depth cfg inst strategy) := by
  apply frame_action_of_success_no_unwind _ _ (site.term_no_unwind ctx depth cfg strategy)
  intro state after result valid run
  obtain ⟨step,shape,same,transported⟩ := site.term_success ctx depth cfg strategy state after result valid run
  subst result
  subst after
  exact ⟨valid,transported,.refl _⟩

/-- The original final transfer consumes ordinary return/edge arguments. The
continuation's full exit contract is required, since a selected successor may
raise or rethrow even though the control instruction itself cannot unwind. -/
theorem ordinary_transfer_frame_exit (recurse : Recurse) (ctx : EvalContext) (depth : Nat)
    (cfg : CFG) (block : BasicBlock) (strategy : PanicStrategy) (result : StepResult)
    (state : MachineState) (valid : WellMintedState state) (transported : TransferValues state.nextFrameLineage result)
    (continuation : ∀ pc args before, WellMintedState before → MintedArgs before.nextFrameLineage args →
      FrameCalleeExit before (Sem.run (recurse ctx depth cfg pc args strategy) before)) :
    FrameCalleeExit state (Sem.run (evalTransfer recurse ctx depth cfg block strategy result) state) := by
  cases result with
  | Continue next args => exact continuation next args state valid transported
  | Ret args => exact ⟨valid,transported,.refl _⟩
  | Stuck => exact True.intro
  | CallReq _ _ => cases transported
  | CallIndirectReq _ _ _ => cases transported
  | InvokeReq _ _ _ _ _ => cases transported
  | InvokeIndirectReq _ _ _ _ _ _ => cases transported
  | SeqMapReq _ _ => cases transported

/-- Original contextual stepping followed by its ordinary final transfer.
The body/prefix and recursive CFG proof remain separate obligations. -/
theorem FrameControl.dispatch_frame_exit {inst : Inst} (site : FrameControl inst)
    (recurse : Recurse) (ctx : EvalContext) (depth : Nat) (cfg : CFG) (block : BasicBlock)
    (strategy : PanicStrategy) (state : MachineState) (valid : WellMintedState state)
    (continuation : ∀ pc args before, WellMintedState before → MintedArgs before.nextFrameLineage args →
      FrameCalleeExit before (Sem.run (recurse ctx depth cfg pc args strategy) before)) :
    FrameActionExit MintedArgs state (Sem.run (do
      let termResult ← stepTermWithContext ctx depth cfg inst strategy
      let result ← match termResult with
        | .terminator step => pure step
        | .value _ => Sem.throwTypeError "basic block does not end with a terminator"
        | .values _ => Sem.throwTypeError "basic block does not end with a terminator"
      evalTransfer recurse ctx depth cfg block strategy result) state) := by
  apply FrameActionExit.bind OrdinaryTermValues MintedArgs _ _ state (site.term_frame_exit ctx depth cfg strategy state valid)
  intro result before beforeValid transported
  cases result with
  | terminator step =>
    exact (FrameActionExit.callee before _).2 (ordinary_transfer_frame_exit recurse ctx depth cfg block strategy step before beforeValid transported continuation)
  | value _ => cases transported
  | values _ => cases transported

end TrustIr.FrameLifetime
