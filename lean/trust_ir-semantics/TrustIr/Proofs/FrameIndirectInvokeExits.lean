-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0
import TrustIr.Proofs.FrameInvokeTransfers

namespace TrustIr.FrameLifetime
open GenericCoro GenericCoro.Prefix

private theorem poison_arguments_exit (args : List Value) (state : MachineState)
    (valid : WellMintedState state) (incoming : MintedArgs state.nextFrameLineage args) :
    FrameActionExit (fun bound _ => MintedArgs bound args) state
      (Sem.run (Sem.rejectPoisonValues args "InvokeIndirect arguments") state) := by
  unfold Sem.rejectPoisonValues
  split
  · exact True.intro
  · exact ⟨valid,incoming,.refl _⟩

/-- Original raw indirect Invoke transfer, including its pointer, signature,
body, arity and poison refusals. This production branch has no ABI prelude.
Callee and caller CFG exit contracts remain explicit. -/
theorem indirect_invoke_transfer_exit (recurse : Recurse) (ctx : EvalContext) (depth : Nat)
    (cfg : CFG) (block : BasicBlock) (strategy : PanicStrategy) (address : Nat) (sig : FuncTyId)
    (args : List Value) (normal : BlockId) (normalIds : List ValueId) (unwind : BlockId)
    (state : MachineState) (valid : WellMintedState state) (incoming : MintedArgs state.nextFrameLineage args)
    (callees : ∀ id callee, ctx.funcPtrs address = some id → ctx.functions id = some callee →
      ∀ childDepth values before, WellMintedState before → MintedArgs before.nextFrameLineage values →
      FrameCalleeExit before (Sem.run (recurse (ctx.forFunction callee) childDepth callee.cfg callee.entryBlock values strategy) before))
    (continuation : ∀ pc values before, WellMintedState before → MintedArgs before.nextFrameLineage values →
      FrameCalleeExit before (Sem.run (recurse ctx depth cfg pc values strategy) before)) :
    FrameCalleeExit state (Sem.run (evalTransfer recurse ctx depth cfg block strategy
      (.InvokeIndirectReq address sig args normal normalIds unwind)) state) := by
  cases depth with
  | zero => exact True.intro
  | succ depth =>
    rw [evalTransfer_invokeIndirect_succ]
    cases pointer : ctx.funcPtrs address with
    | none =>
      simp [pointer,Sem.throwUB,Sem.run,StateT.run,StateT.bind,StateT.lift,
        throw,throwThe,MonadExceptOf.throw,bind,pure,Except.bind,Except.pure,FrameCalleeExit]
    | some id =>
      cases declaration : ctx.funcTys sig with
      | none =>
        simp [pointer,declaration,Sem.throwTypeError,Sem.run,StateT.run,StateT.bind,StateT.lift,
          throw,throwThe,MonadExceptOf.throw,bind,pure,Except.bind,Except.pure,FrameCalleeExit]
      | some signature =>
        cases found : ctx.functions id with
        | none =>
          simp [pointer,declaration,found,Sem.throwTypeError,Sem.run,StateT.run,StateT.bind,StateT.lift,
            throw,throwThe,MonadExceptOf.throw,bind,pure,Except.bind,Except.pure,FrameCalleeExit]
        | some callee =>
          simp only [pointer,declaration,found,pure_bind]
          cases matched : checkIndirectSignature signature callee.body with
          | error message =>
            simp [matched,Sem.throwTypeError,Sem.run,StateT.run,StateT.bind,StateT.lift,
              throw,throwThe,MonadExceptOf.throw,bind,pure,Except.bind,Except.pure,FrameCalleeExit]
          | ok unit =>
            cases unit
            simp only [matched,pure_bind]
            cases arity : checkCallArity args callee.body.paramTys with
            | error message =>
              simp [arity,Sem.throwTypeError,Sem.run,StateT.run,StateT.bind,StateT.lift,
                throw,throwThe,MonadExceptOf.throw,bind,pure,Except.bind,Except.pure,FrameCalleeExit]
            | ok unit =>
              cases unit
              simp only [arity,pure_bind]
              apply (FrameActionExit.callee state _).1
              apply FrameActionExit.bind (fun bound _ => MintedArgs bound args) MintedArgs _ _ state
                (poison_arguments_exit args state valid incoming)
              intro unit before beforeValid incoming
              cases unit
              apply (FrameActionExit.callee before _).2
              apply checked_invoke_frame_exit strategy ctx callee.body.returnTys "InvokeIndirect: " _ _ _ before beforeValid
              · exact callees id callee pointer found depth args (callerWorld before) ⟨beforeValid.table,values_empty _⟩ incoming
              · intro returned restored restoredValid returnedValid
                exact invoke_normal_frame_exit recurse ctx (depth+1) cfg block strategy normal normalIds returned restored restoredValid returnedValid continuation
              · intro exception restored restoredValid
                exact invoke_unwind_frame_exit recurse ctx (depth+1) cfg strategy unwind exception restored restoredValid continuation

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

private theorem lookup_success (s final : MachineState) (id : ValueId) (value : Value)
    (run : Sem.run (Sem.lookupValue id) s = .ok (value, final)) :
    s.lookupValue id = some value ∧ final = s := by
  cases lookup : s.lookupValue id with
  | none =>
    simp [Sem.lookupValue, Sem.run, Sem.getState, Sem.throwTypeError, lookup,
      StateT.run, StateT.bind, StateT.get, StateT.pure, StateT.lift, bind, pure,
      Except.bind, Except.pure, throw, throwThe, MonadExceptOf.throw] at run
  | some held =>
    simp [Sem.lookupValue, Sem.run, Sem.getState, lookup, StateT.run,
      StateT.bind, StateT.get, StateT.pure, bind, pure, Except.bind, Except.pure] at run
    rcases run with ⟨rfl, rfl⟩
    exact ⟨rfl, rfl⟩


/-- Both actual request routes produced by contextual InvokeIndirect. -/
def IndirectInvokeValues (bound : Nat) : StepResult → Prop
  | .InvokeReq _ args _ _ _ | .InvokeIndirectReq _ _ args _ _ _ => MintedArgs bound args
  | _ => False

def IndirectInvokeTermValues (bound : Nat) : InstrResult → Prop
  | .terminator step => IndirectInvokeValues bound step
  | _ => False

private theorem finish_request (bound : Nat) (request : StepResult) (s final : MachineState)
    (result : InstrResult) (valid : IndirectInvokeValues bound request)
    (run : Sem.run (pure (.terminator request) : Sem InstrResult) s = .ok (result,final)) :
    final = s ∧ IndirectInvokeTermValues bound result := by
  cases run
  exact ⟨rfl,valid⟩

private theorem raw_request_success (model : ByteModel) (calleeId : ValueId) (sig : FuncTyId)
    (args : List ValueId) (conv : CallingConv) (normal : BlockId) (ids : List ValueId) (unwind : BlockId)
    (s final : MachineState) (result : InstrResult) (valid : WellMintedState s)
    (run : Sem.run (stepInst (.InvokeIndirect calleeId sig args conv normal ids unwind) model) s = .ok (result,final)) :
    final = s ∧ IndirectInvokeTermValues s.nextFrameLineage result := by
  obtain ⟨held,middle,looked,tail⟩ := split_bind_success _ _ s final result run
  obtain ⟨found,same⟩ := lookup_success s middle calleeId held looked
  subst middle
  cases held
  case ptr address provenance =>
    simp only [pure_bind] at tail
    obtain ⟨values,middle,looked,tail⟩ := split_bind_success _ _ s final result tail
    obtain ⟨same,incoming⟩ := lookup_args_success args s middle values valid looked
    subst middle
    exact finish_request s.nextFrameLineage (.InvokeIndirectReq address sig values normal ids unwind) s final result incoming tail
  all_goals cases tail

/-- Successful contextual preparation keeps state and produces minted values
on either request route. Typed closures retain their original raw fallback. -/
theorem indirect_invoke_request_success (ctx : EvalContext) (depth : Nat) (cfg : CFG)
    (strategy : PanicStrategy) (calleeId : ValueId) (sig : FuncTyId) (args : List ValueId) (conv : CallingConv)
    (normal : BlockId) (ids : List ValueId) (unwind : BlockId)
    (s final : MachineState) (result : InstrResult) (valid : WellMintedState s)
    (run : Sem.run (stepTermWithContext ctx depth cfg (.InvokeIndirect calleeId sig args conv normal ids unwind) strategy) s = .ok (result,final)) :
    final = s ∧ IndirectInvokeTermValues s.nextFrameLineage result := by
  have anchored : stepTermWithContext ctx depth cfg (.InvokeIndirect calleeId sig args conv normal ids unwind) strategy =
      closureTermWithContext ctx depth (.InvokeIndirect calleeId sig args conv normal ids unwind)
        (stepInst (.InvokeIndirect calleeId sig args conv normal ids unwind) ctx.byteModel) := by
    cases strategy <;> rfl
  rw [anchored] at run
  obtain ⟨held,middle,looked,tail⟩ := split_bind_success _ _ s final result run
  obtain ⟨found,same⟩ := lookup_success s middle calleeId held looked
  subst middle
  obtain ⟨unit, middle, checked, tail⟩ := split_bind_success _ _ s final result tail
  have same := memory_check_success_state _ s middle unit checked
  subst middle
  cases unit
  cases held
  case nullPtr => cases tail
  case fnItem target _ =>
    cases depth with
    | zero => cases tail
    | succ depth =>
      obtain ⟨id, middle, header, tail⟩ := split_bind_success _ _ s final result tail
      have same := memory_check_success_state _ s middle id header
      subst middle
      obtain ⟨values, middle, looked, tail⟩ := split_bind_success _ _ s final result tail
      obtain ⟨same, incoming⟩ := lookup_args_success args s middle values valid looked
      subst middle
      obtain ⟨callee, middle, resolved, tail⟩ := split_bind_success _ _ s final result tail
      have same := memory_check_success_state _ s middle callee resolved
      subst middle
      exact finish_request s.nextFrameLineage (.InvokeReq id values normal ids unwind) s final result incoming tail
  case fnDef held fn _ =>
    obtain ⟨values,middle,looked,tail⟩ := split_bind_success _ _ s final result tail
    obtain ⟨same,incoming⟩ := lookup_args_success args s middle values valid looked
    subst middle
    cases depth with
    | zero => cases tail
    | succ depth =>
      cases checked : functionCallWithConvention ctx held fn sig conv with
      | error error => simp only [checked] at tail; cases tail
      | ok id =>
        simp only [checked,pure_bind] at tail
        exact finish_request s.nextFrameLineage (.InvokeReq id values normal ids unwind) s final result incoming tail
  all_goals exact raw_request_success ctx.byteModel calleeId sig args conv normal ids unwind s final result valid tail

private theorem pure_no_unwind {α : Type} (value : α) : CallCheckNoUnwind (pure value : Sem α) := by
  intro state exception after run
  cases run

private theorem lookup_no_unwind (id : ValueId) : CallCheckNoUnwind (Sem.lookupValue id) := by
  intro state exception after run
  cases found : state.lookupValue id <;>
    simp [Sem.lookupValue,Sem.run,Sem.getState,found,Sem.throwTypeError,StateT.run,StateT.bind,
      StateT.get,StateT.pure,StateT.lift,bind,pure,Except.bind,Except.pure,throw,throwThe,MonadExceptOf.throw] at run

private theorem raw_request_no_unwind (model : ByteModel) (calleeId : ValueId) (sig : FuncTyId)
    (args : List ValueId) (conv : CallingConv) (normal : BlockId) (ids : List ValueId) (unwind : BlockId) :
    CallCheckNoUnwind (stepInst (.InvokeIndirect calleeId sig args conv normal ids unwind) model) := by
  apply CallCheckNoUnwind.bind _ _ (lookup_no_unwind calleeId)
  intro value
  cases value
  case ptr address provenance =>
    simp only [pure_bind]
    exact CallCheckNoUnwind.bind _ _ (lookup_arguments_no_unwind args) (fun _ => pure_no_unwind _)
  all_goals intro state exception after run; cases run

/-- Original body resolution retains its static-error premise for nominal
items and FnDef values; raw pointer fallbacks cannot create unwind states. -/
theorem indirect_invoke_request_no_unwind (ctx : EvalContext) (safe : StaticFunctionErrors ctx)
    (depth : Nat) (cfg : CFG) (strategy : PanicStrategy) (calleeId : ValueId) (sig : FuncTyId)
    (args : List ValueId) (conv : CallingConv) (normal : BlockId) (ids : List ValueId) (unwind : BlockId) :
    CallCheckNoUnwind (stepTermWithContext ctx depth cfg (.InvokeIndirect calleeId sig args conv normal ids unwind) strategy) := by
  have anchored : stepTermWithContext ctx depth cfg (.InvokeIndirect calleeId sig args conv normal ids unwind) strategy =
      closureTermWithContext ctx depth (.InvokeIndirect calleeId sig args conv normal ids unwind)
        (stepInst (.InvokeIndirect calleeId sig args conv normal ids unwind) ctx.byteModel) := by
    cases strategy <;> rfl
  rw [anchored]
  apply CallCheckNoUnwind.bind _ _ (lookup_no_unwind calleeId)
  intro value
  apply CallCheckNoUnwind.bind _ _
    (lift_validation_no_unwind _ (function_item_callee_type_no_unwind ctx calleeId value))
  intro unit
  cases unit
  cases value
  case nullPtr => intro state exception after run; cases run
  case fnItem target =>
    cases depth with
    | zero => intro state exception after run; cases run
    | succ depth =>
      apply CallCheckNoUnwind.bind _ _
        (lift_validation_no_unwind _ (function_item_call_no_unwind ctx target sig conv))
      intro function
      apply CallCheckNoUnwind.bind _ _ (lookup_arguments_no_unwind args)
      intro values
      apply CallCheckNoUnwind.bind _ _
        (lift_validation_no_unwind _ (function_item_body_no_unwind ctx safe function))
      intro callee
      exact pure_no_unwind _
  case fnDef held fn =>
    apply CallCheckNoUnwind.bind _ _ (lookup_arguments_no_unwind args)
    intro values
    cases depth with
    | zero => intro state exception after run; cases run
    | succ depth =>
      cases checked : functionCallWithConvention ctx held fn sig conv with
      | error error =>
        intro state exception after run
        simp only [checked] at run
        cases run
        exact function_call_with_convention_no_unwind ctx safe held fn sig conv exception after checked
      | ok id =>
        simp only [checked,pure_bind]
        exact pure_no_unwind _
  all_goals exact raw_request_no_unwind ctx.byteModel calleeId sig args conv normal ids unwind

/-- Complete preparation exit law, including malformed, unsupported and
out-of-fuel refusals, for both original contextual routes. -/
theorem indirect_invoke_request_exit (ctx : EvalContext) (safe : StaticFunctionErrors ctx)
    (depth : Nat) (cfg : CFG) (strategy : PanicStrategy) (calleeId : ValueId) (sig : FuncTyId)
    (args : List ValueId) (conv : CallingConv) (normal : BlockId) (ids : List ValueId) (unwind : BlockId) :
    FrameActionValid IndirectInvokeTermValues
      (stepTermWithContext ctx depth cfg (.InvokeIndirect calleeId sig args conv normal ids unwind) strategy) := by
  apply frame_action_of_success_no_unwind _ _ (indirect_invoke_request_no_unwind ctx safe depth cfg strategy calleeId sig args conv normal ids unwind)
  intro state after result valid run
  obtain ⟨same,transported⟩ := indirect_invoke_request_success ctx depth cfg strategy calleeId sig args conv normal ids unwind state after result valid run
  subst after
  exact ⟨valid,transported,.refl _⟩


/-- Complete original contextual InvokeIndirect dispatch. FnDef preparation
selects direct Invoke; raw pointer preparation selects indirect Invoke.
All recursive CFG exits, including caller successors, remain explicit. -/
theorem indirect_invoke_dispatch_exit (recurse : Recurse) (ctx : EvalContext)
    (safe : StaticFunctionErrors ctx) (depth : Nat) (cfg : CFG) (block : BasicBlock)
    (strategy : PanicStrategy) (calleeId : ValueId) (sig : FuncTyId) (args : List ValueId) (conv : CallingConv)
    (normal : BlockId) (ids : List ValueId) (unwind : BlockId)
    (state : MachineState) (valid : WellMintedState state)
    (callees : ∀ id callee, ctx.functions id = some callee → ∀ childDepth values before,
      WellMintedState before → MintedArgs before.nextFrameLineage values →
      FrameCalleeExit before (Sem.run (recurse (ctx.forFunction callee) childDepth callee.cfg callee.entryBlock values strategy) before))
    (continuation : ∀ pc values before, WellMintedState before → MintedArgs before.nextFrameLineage values →
      FrameCalleeExit before (Sem.run (recurse ctx depth cfg pc values strategy) before)) :
    FrameActionExit MintedArgs state (Sem.run (do
      let termResult ← stepTermWithContext ctx depth cfg (.InvokeIndirect calleeId sig args conv normal ids unwind) strategy
      let result ← match termResult with
        | .terminator step => pure step
        | .value _ => Sem.throwTypeError "basic block does not end with a terminator"
        | .values _ => Sem.throwTypeError "basic block does not end with a terminator"
      evalTransfer recurse ctx depth cfg block strategy result) state) := by
  apply FrameActionExit.bind IndirectInvokeTermValues MintedArgs _ _ state
    (indirect_invoke_request_exit ctx safe depth cfg strategy calleeId sig args conv normal ids unwind state valid)
  intro result before beforeValid transported
  cases result with
  | value _ => cases transported
  | values _ => cases transported
  | terminator step =>
    apply (FrameActionExit.callee before _).2
    cases step with
    | InvokeReq id values next nextIds pad =>
      exact direct_invoke_transfer_exit recurse ctx depth cfg block strategy id values next nextIds pad before beforeValid transported (callees id) continuation
    | InvokeIndirectReq address signature values next nextIds pad =>
      exact indirect_invoke_transfer_exit recurse ctx depth cfg block strategy address signature values next nextIds pad before beforeValid transported
        (fun id callee _ found => callees id callee found) continuation
    | Continue _ _ => cases transported
    | Ret _ => cases transported
    | Stuck => cases transported
    | CallReq _ _ => cases transported
    | CallIndirectReq _ _ _ => cases transported
    | SeqMapReq _ _ => cases transported

end TrustIr.FrameLifetime
