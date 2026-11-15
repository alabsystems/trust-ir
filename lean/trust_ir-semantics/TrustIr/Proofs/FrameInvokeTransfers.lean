-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0
import TrustIr.Proofs.FrameControlExits

namespace TrustIr.FrameLifetime
open GenericCoro GenericCoro.Prefix

/-- Original normal continuation: publish first, then read the normal edge
arguments (which may name those results), then resume at caller depth. -/
theorem invoke_normal_frame_exit (recurse : Recurse) (ctx : EvalContext) (depth : Nat)
    (cfg : CFG) (block : BasicBlock) (strategy : PanicStrategy) (next : BlockId) (ids : List ValueId)
    (values : List Value) (state : MachineState) (valid : WellMintedState state)
    (incoming : MintedArgs state.nextFrameLineage values)
    (continuation : ∀ pc args before, WellMintedState before → MintedArgs before.nextFrameLineage args →
      FrameCalleeExit before (Sem.run (recurse ctx depth cfg pc args strategy) before)) :
    FrameCalleeExit state (Sem.run (do
      ctx.bindCallResults block.terminator block.terminatorResultDests values
      let args ← ids.mapM Sem.lookupValue
      recurse ctx depth cfg next args strategy) state) := by
  apply (FrameActionExit.callee state _).1
  apply FrameActionExit.bind (fun _ _ => True) MintedArgs _ _ state
    (call_results_frame_exit ctx block.terminator block.terminatorResultDests values state valid incoming)
  intro unit published publishedValid _
  cases unit
  apply FrameActionExit.bind MintedArgs MintedArgs _ _ published (lookup_arguments_action ids published publishedValid)
  intro args before beforeValid transported
  exact (FrameActionExit.callee before _).2 (continuation next args before beforeValid transported)

/-- Original caught-unwind continuation, including semEnterPad refusals and
no-action rethrows. The selected pad runs at the caller's original depth. -/
theorem invoke_unwind_frame_exit (recurse : Recurse) (ctx : EvalContext) (depth : Nat)
    (cfg : CFG) (strategy : PanicStrategy) (next : BlockId) (exception : Addr)
    (state : MachineState) (valid : WellMintedState state)
    (continuation : ∀ pc args before, WellMintedState before → MintedArgs before.nextFrameLineage args →
      FrameCalleeExit before (Sem.run (recurse ctx depth cfg pc args strategy) before)) :
    FrameCalleeExit state (Sem.run (do
      semEnterPad cfg exception next
      recurse ctx depth cfg next [] strategy) state) := by
  apply (FrameActionExit.callee state _).1
  apply FrameActionExit.bind (fun _ _ => True) MintedArgs _ _ state (enter_pad_frame_action cfg exception next state valid)
  intro unit before beforeValid _
  cases unit
  exact (FrameActionExit.callee before _).2 (continuation next [] before beforeValid (fun _ member => nomatch member))

private theorem abi_arguments_exit (abi : Option SignatureAbi) (args : List Value) (state : MachineState)
    (valid : WellMintedState state) (incoming : MintedArgs state.nextFrameLineage args) :
    FrameActionExit (fun bound _ => MintedArgs bound args) state (Sem.run (requireUntypedAbi abi) state) := by
  unfold requireUntypedAbi
  split
  · exact True.intro
  · exact ⟨valid,incoming,.refl _⟩

private theorem poison_arguments_exit (args : List Value) (state : MachineState)
    (valid : WellMintedState state) (incoming : MintedArgs state.nextFrameLineage args) :
    FrameActionExit (fun bound _ => MintedArgs bound args) state (Sem.run (Sem.rejectPoisonValues args "Call arguments") state) := by
  unfold Sem.rejectPoisonValues
  split
  · exact True.intro
  · exact ⟨valid,incoming,.refl _⟩

/-- Complete original direct Invoke transfer under full callee and successor
exit contracts. Callee depth decreases; BOTH caller continuations keep depth.
No independent successful header/return/publication check is assumed. -/
theorem direct_invoke_transfer_exit (recurse : Recurse) (ctx : EvalContext) (depth : Nat)
    (cfg : CFG) (block : BasicBlock) (strategy : PanicStrategy) (id : FuncId) (args : List Value)
    (normal : BlockId) (normalIds : List ValueId) (unwind : BlockId)
    (state : MachineState) (valid : WellMintedState state) (incoming : MintedArgs state.nextFrameLineage args)
    (callees : ∀ callee, ctx.functions id = some callee → ∀ childDepth values before,
      WellMintedState before → MintedArgs before.nextFrameLineage values →
      FrameCalleeExit before (Sem.run (recurse (ctx.forFunction callee) childDepth callee.cfg callee.entryBlock values strategy) before))
    (continuation : ∀ pc values before, WellMintedState before → MintedArgs before.nextFrameLineage values →
      FrameCalleeExit before (Sem.run (recurse ctx depth cfg pc values strategy) before)) :
    FrameCalleeExit state (Sem.run (evalTransfer recurse ctx depth cfg block strategy (.InvokeReq id args normal normalIds unwind)) state) := by
  cases depth with
  | zero => exact True.intro
  | succ depth =>
    rw [evalTransfer_invoke_succ]
    apply (FrameActionExit.callee state _).1
    apply FrameActionExit.bind (fun bound callee => ctx.functions id = some callee ∧ MintedArgs bound args) MintedArgs _ _ state
      (target_lookup_arguments_exit ctx id args state "Invoke: callee is a bodyless declaration" "Invoke: undefined function" valid incoming)
    intro callee caller callerValid receipt
    obtain ⟨found,incoming⟩ := receipt
    apply FrameActionExit.bind (fun bound _ => MintedArgs bound args) MintedArgs _ _ caller
      (abi_arguments_exit callee.body.abi args caller callerValid incoming)
    intro unit checked checkedValid incoming
    cases unit
    cases arity : checkCallArity args callee.body.paramTys with
    | error message =>
      simp [arity,Sem.throwTypeError,Sem.run,StateT.run,StateT.bind,StateT.lift,
        throw,throwThe,MonadExceptOf.throw,bind,pure,Except.bind,Except.pure,FrameActionExit]
    | ok unit =>
      cases unit
      simp only [arity,pure_bind]
      apply FrameActionExit.bind (fun bound _ => MintedArgs bound args) MintedArgs _ _ checked
        (poison_arguments_exit args checked checkedValid incoming)
      intro unit before beforeValid incoming
      cases unit
      apply (FrameActionExit.callee before _).2
      apply checked_invoke_frame_exit strategy ctx callee.body.returnTys "Invoke: " _ _ _ before beforeValid
      · exact callees callee found depth args (callerWorld before) ⟨beforeValid.table,values_empty _⟩ incoming
      · intro returned restored restoredValid returnedValid
        exact invoke_normal_frame_exit recurse ctx (depth+1) cfg block strategy normal normalIds returned restored restoredValid returnedValid continuation
      · intro exception restored restoredValid
        exact invoke_unwind_frame_exit recurse ctx (depth+1) cfg strategy unwind exception restored restoredValid continuation

/-- Direct Invoke request creation reads ordered SSA arguments before the
transfer's depth/header checks. It never changes the caller state. -/
def InvokeRequestValues (id : FuncId) (normal : BlockId) (ids : List ValueId) (unwind : BlockId)
    (bound : Nat) (result : InstrResult) : Prop :=
  ∃ args, result = .terminator (.InvokeReq id args normal ids unwind) ∧ MintedArgs bound args

theorem invoke_request_frame_exit (ctx : EvalContext) (depth : Nat) (cfg : CFG) (strategy : PanicStrategy)
    (id : FuncId) (args : List ValueId) (normal : BlockId) (ids : List ValueId) (unwind : BlockId) :
    FrameActionValid (InvokeRequestValues id normal ids unwind)
      (stepTermWithContext ctx depth cfg (.Invoke id args normal ids unwind) strategy) := by
  have anchored : stepTermWithContext ctx depth cfg (.Invoke id args normal ids unwind) strategy =
      (args.mapM Sem.lookupValue >>= fun values => pure (.terminator (.InvokeReq id values normal ids unwind))) := by
    cases strategy <;> rfl
  rw [anchored]
  intro state valid
  apply FrameActionExit.bind MintedArgs (InvokeRequestValues id normal ids unwind) _ _ state (lookup_arguments_action args state valid)
  intro values before beforeValid incoming
  exact ⟨beforeValid,⟨values,rfl,incoming⟩,.refl _⟩


/-- Original direct Invoke terminator dispatch, from source SSA argument lookup
through the complete transfer. Recursive callee and caller CFG exit contracts
remain explicit; argument lookup precedes the transfer's depth guard. -/
theorem direct_invoke_dispatch_exit (recurse : Recurse) (ctx : EvalContext) (depth : Nat)
    (cfg : CFG) (block : BasicBlock) (strategy : PanicStrategy) (id : FuncId) (ids : List ValueId)
    (normal : BlockId) (normalIds : List ValueId) (unwind : BlockId)
    (state : MachineState) (valid : WellMintedState state)
    (callees : ∀ callee, ctx.functions id = some callee → ∀ childDepth values before,
      WellMintedState before → MintedArgs before.nextFrameLineage values →
      FrameCalleeExit before (Sem.run (recurse (ctx.forFunction callee) childDepth callee.cfg callee.entryBlock values strategy) before))
    (continuation : ∀ pc values before, WellMintedState before → MintedArgs before.nextFrameLineage values →
      FrameCalleeExit before (Sem.run (recurse ctx depth cfg pc values strategy) before)) :
    FrameActionExit MintedArgs state (Sem.run (do
      let termResult ← stepTermWithContext ctx depth cfg (.Invoke id ids normal normalIds unwind) strategy
      let result ← match termResult with
        | .terminator step => pure step
        | .value _ => Sem.throwTypeError "basic block does not end with a terminator"
        | .values _ => Sem.throwTypeError "basic block does not end with a terminator"
      evalTransfer recurse ctx depth cfg block strategy result) state) := by
  apply FrameActionExit.bind (InvokeRequestValues id normal normalIds unwind) MintedArgs _ _ state
    (invoke_request_frame_exit ctx depth cfg strategy id ids normal normalIds unwind state valid)
  intro result before beforeValid receipt
  obtain ⟨args,shape,incoming⟩ := receipt
  subst result
  exact (FrameActionExit.callee before _).2
    (direct_invoke_transfer_exit recurse ctx depth cfg block strategy id args normal normalIds unwind before beforeValid incoming callees continuation)

end TrustIr.FrameLifetime
