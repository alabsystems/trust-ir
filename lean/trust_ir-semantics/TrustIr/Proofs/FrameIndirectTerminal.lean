-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0
import TrustIr.Proofs.FrameTailRecursion

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

/-- Only the two call request forms can leave indirect terminal preparation. -/
def IndirectTerminalValues (bound : Nat) : StepResult → Prop
  | .CallReq _ values | .CallIndirectReq _ _ values => MintedArgs bound values
  | _ => False

private theorem finish_request (bound : Nat) (request : StepResult) (s final : MachineState)
    (result : InstrResult) (valid : IndirectTerminalValues bound request)
    (run : Sem.run (pure (.terminator request) : Sem InstrResult) s = .ok (result,final)) :
    ∃ step, result = .terminator step ∧ final = s ∧ IndirectTerminalValues bound step := by
  cases run
  exact ⟨request,rfl,rfl,valid⟩

/-- Original bare raw-pointer request creation retains ordered argument lookup. -/
theorem raw_terminal_request_success (model : ByteModel) (calleeId : ValueId) (sig : FuncTyId)
    (args : List ValueId) (conv : CallingConv) (s final : MachineState)
    (result : InstrResult) (valid : WellMintedState s)
    (run : Sem.run (stepInst (.CallIndirect calleeId sig args conv) model) s = .ok (result,final)) :
    ∃ step, result = .terminator step ∧ final = s ∧ IndirectTerminalValues s.nextFrameLineage step := by
  obtain ⟨held,middle,looked,tail⟩ := split_bind_success _ _ s final result run
  obtain ⟨found,same⟩ := lookup_success s middle calleeId held looked
  subst middle
  cases held
  case ptr address provenance =>
    simp only [pure_bind] at tail
    obtain ⟨values,middle,looked,tail⟩ := split_bind_success _ _ s final result tail
    obtain ⟨same,incoming⟩ := lookup_args_success args s middle values valid looked
    subst middle
    exact finish_request s.nextFrameLineage (.CallIndirectReq address sig values) s final result incoming tail
  all_goals cases tail

/-- Contextual terminal dispatch, including nominal item headers, legacy
FnDef values and closure captures, preserves state and minted call arguments. -/
theorem indirect_terminal_request_success (ctx : EvalContext) (depth : Nat) (cfg : CFG)
    (strategy : PanicStrategy) (calleeId : ValueId) (sig : FuncTyId) (args : List ValueId) (conv : CallingConv)
    (s final : MachineState) (result : InstrResult) (valid : WellMintedState s)
    (run : Sem.run (stepTermWithContext ctx depth cfg (.CallIndirect calleeId sig args conv) strategy) s = .ok (result,final)) :
    ∃ step, result = .terminator step ∧ final = s ∧ IndirectTerminalValues s.nextFrameLineage step := by
  have anchored : stepTermWithContext ctx depth cfg (.CallIndirect calleeId sig args conv) strategy =
      closureTermWithContext ctx depth (.CallIndirect calleeId sig args conv)
        (stepInst (.CallIndirect calleeId sig args conv) ctx.byteModel) := by
    cases strategy <;> rfl
  rw [anchored] at run
  obtain ⟨held,middle,looked,tail⟩ := split_bind_success _ _ s final result run
  obtain ⟨found,same⟩ := lookup_success s middle calleeId held looked
  subst middle
  have heldValid := valid.values calleeId held found
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
      exact finish_request s.nextFrameLineage (.CallReq id values) s final result incoming tail
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
        exact finish_request s.nextFrameLineage (.CallReq id values) s final result incoming tail
  case typedClosure cid fn captures _ =>
    obtain ⟨values,middle,looked,tail⟩ := split_bind_success _ _ s final result tail
    obtain ⟨same,incoming⟩ := lookup_args_success args s middle values valid looked
    subst middle
    cases depth with
    | zero => cases tail
    | succ depth =>
      cases checked : closureCall ctx cid fn captures sig values conv with
      | error error => simp only [checked] at tail; cases tail
      | ok prepared =>
        simp only [checked,pure_bind] at tail
        exact finish_request s.nextFrameLineage (.CallReq prepared.1 prepared.2) s final result
          (closure_call_arguments_minted s.nextFrameLineage ctx cid fn captures values sig conv prepared heldValid incoming checked) tail
  all_goals exact raw_terminal_request_success ctx.byteModel calleeId sig args conv s final result valid tail

private def ReadOnly {α : Type} (action : Sem α) : Prop :=
  ∀ state result, Sem.run action state = .ok result → result.2 = state

private theorem pure_readonly {α : Type} (value : α) : ReadOnly (pure value : Sem α) := by
  intro state result run
  cases run
  rfl

private theorem throw_readonly {α : Type} (error : SemError) : ReadOnly (throw error : Sem α) := by
  intro state result run
  cases run

private theorem poison_readonly (values : List Value) (message : String) :
    ReadOnly (Sem.rejectPoisonValues values message) := by
  unfold Sem.rejectPoisonValues
  split
  · exact throw_readonly _
  · exact pure_readonly _

private theorem abi_readonly (body : FuncBody) : ReadOnly (requireUntypedAbi body.abi) := by
  unfold requireUntypedAbi
  split <;> first | exact pure_readonly _ | exact throw_readonly _

/-- The actual raw indirect transfer retains signature/ABI/header checks,
executes the selected callee, checks returns and restores the caller. -/
theorem raw_terminal_transfer_success (recurse : Recurse) (ctx : EvalContext) (depth : Nat)
    (cfg : CFG) (block : BasicBlock) (strategy : PanicStrategy) (address : Addr) (sig : FuncTyId)
    (args : List Value) (s final : MachineState) (values : List Value) (valid : WellMintedState s)
    (incoming : MintedArgs s.nextFrameLineage args) (callees : FrameCalleeContract recurse ctx strategy)
    (run : Sem.run (evalTransfer recurse ctx depth cfg block strategy (.CallIndirectReq address sig args)) s = .ok (values,final)) :
    DirectFrameResult s final values := by
  rw [evalTransfer_indirect_eq] at run
  cases depth with
  | zero => cases run
  | succ depth =>
    cases pointer : ctx.funcPtrs address with
    | none =>
      simp [terminalIndirect,pointer,Sem.throwUB,Sem.run,StateT.run,StateT.bind,StateT.lift,
        throw,throwThe,MonadExceptOf.throw,bind,pure,Except.bind,Except.pure] at run
    | some id =>
      cases declaration : ctx.funcTys sig with
      | none =>
        simp [terminalIndirect,pointer,declaration,Sem.throwTypeError,Sem.run,StateT.run,StateT.bind,StateT.lift,
          throw,throwThe,MonadExceptOf.throw,bind,pure,Except.bind,Except.pure] at run
      | some signature =>
        cases found : ctx.functions id with
        | none =>
          simp [terminalIndirect,pointer,declaration,found,Sem.throwTypeError,Sem.run,StateT.run,StateT.bind,StateT.lift,
            throw,throwThe,MonadExceptOf.throw,bind,pure,Except.bind,Except.pure] at run
        | some callee =>
          simp only [terminalIndirect,pointer,declaration,found,pure_bind] at run
          obtain ⟨unit,middle,checked,tail⟩ := split_bind_success _ _ s final values run
          cases unit
          have same : middle = s := by
            unfold requireUntypedAbi at checked
            split at checked
            · cases checked
            · cases checked; rfl
          subst middle
          cases matched : checkIndirectSignature signature callee.body with
          | error message =>
            simp [matched,Sem.throwTypeError,Sem.run,StateT.run,StateT.bind,StateT.lift,
              throw,throwThe,MonadExceptOf.throw,bind,pure,Except.bind,Except.pure] at tail
          | ok unit =>
            cases unit
            simp only [matched,pure_bind] at tail
            obtain ⟨unit,middle,checked,tail⟩ := split_bind_success _ _ s final values tail
            cases unit
            have same := abi_readonly callee.body s ((),middle) checked
            change middle = s at same
            subst middle
            cases arity : checkCallArity args callee.body.paramTys with
            | error message =>
              simp [arity,Sem.throwTypeError,Sem.run,StateT.run,StateT.bind,StateT.lift,
                throw,throwThe,MonadExceptOf.throw,bind,pure,Except.bind,Except.pure] at tail
            | ok unit =>
              cases unit
              simp only [arity,pure_bind] at tail
              obtain ⟨unit,middle,checked,tail⟩ := split_bind_success _ _ s final values tail
              cases unit
              have same := poison_readonly args "CallIndirect arguments" s ((),middle) checked
              change middle = s at same
              subst middle
              have enteredValid : WellMintedState (callerWorld s) := ⟨valid.table,values_empty _⟩
              exact indirect_return_frame_success ctx callee.body.returnTys false "CallIndirect: " _ s final values valid
                (fun after returned executed => callees id callee found depth args (callerWorld s) after returned enteredValid incoming executed) tail

end TrustIr.FrameLifetime
