-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0
import TrustIr.Proofs.FrameUnwindRecursion
import TrustIr.Proofs.FrameIndirectTerminal

namespace TrustIr.FrameLifetime
open GenericCoro GenericCoro.Prefix

/-- Actual terminal direct transfer, including failed headers, recursive unwinds
and state-dependent closure return checks. -/
theorem terminal_direct_transfer_exit (recurse : Recurse) (ctx : EvalContext) (depth : Nat)
    (cfg : CFG) (block : BasicBlock) (strategy : PanicStrategy) (id : FuncId) (args : List Value)
    (state : MachineState) (valid : WellMintedState state)
    (incoming : MintedArgs state.nextFrameLineage args)
    (callees : FrameCalleeExitContract recurse ctx strategy) :
    FrameCalleeExit state (Sem.run (evalTransfer recurse ctx depth cfg block strategy (.CallReq id args)) state) := by
  rw [evalTransfer_call_eq]
  unfold terminalCall
  cases depth with
  | zero => exact True.intro
  | succ depth =>
    apply (FrameActionExit.callee state _).1
    apply FrameActionExit.bind (fun bound callee => ctx.functions id = some callee ∧ MintedArgs bound args)
      MintedArgs _ _ state (direct_lookup_arguments_exit ctx id args state valid incoming)
    intro callee caller callerValid receipt
    obtain ⟨found,incoming⟩ := receipt
    apply FrameActionExit.bind (fun bound _ => MintedArgs bound args) MintedArgs _ _ caller
      (direct_header_frame_exit callee.body args caller callerValid incoming)
    intro unit checked checkedValid incoming
    cases unit
    change FrameActionExit MintedArgs checked (Sem.run (callFrameWith
      (checkReturns ctx callee.body.returnTys true
        (terminalClosureCheck block.terminator (saveFrame checked none)) "Call: ")
      (recurse (ctx.forFunction callee) depth callee.cfg callee.entryBlock args strategy)) checked)
    exact (FrameActionExit.callee checked _).2
      (checked_call_frame_exit ctx callee.body.returnTys true _ "Call: " _ checked checkedValid
        (callees id callee found depth args (callerWorld checked) ⟨checkedValid.table,values_empty _⟩ incoming))

private theorem abi_arguments_exit (abi : Option SignatureAbi) (args : List Value) (state : MachineState)
    (valid : WellMintedState state) (incoming : MintedArgs state.nextFrameLineage args) :
    FrameActionExit (fun bound _ => MintedArgs bound args) state (Sem.run (requireUntypedAbi abi) state) := by
  unfold requireUntypedAbi
  split
  · exact True.intro
  · exact ⟨valid,incoming,.refl _⟩

private theorem poison_arguments_exit (args : List Value) (state : MachineState)
    (valid : WellMintedState state) (incoming : MintedArgs state.nextFrameLineage args) :
    FrameActionExit (fun bound _ => MintedArgs bound args) state
      (Sem.run (Sem.rejectPoisonValues args "CallIndirect arguments") state) := by
  unfold Sem.rejectPoisonValues
  split
  · exact True.intro
  · exact ⟨valid,incoming,.refl _⟩

/-- Original raw terminal indirect transfer retains ABI, signature, arity and
poison checks, and the actual callee's normal or embedded unwind exit. -/
theorem raw_terminal_transfer_exit (recurse : Recurse) (ctx : EvalContext) (depth : Nat)
    (cfg : CFG) (block : BasicBlock) (strategy : PanicStrategy) (address : Addr) (sig : FuncTyId)
    (args : List Value) (state : MachineState) (valid : WellMintedState state)
    (incoming : MintedArgs state.nextFrameLineage args) (callees : FrameCalleeExitContract recurse ctx strategy) :
    FrameCalleeExit state (Sem.run (evalTransfer recurse ctx depth cfg block strategy (.CallIndirectReq address sig args)) state) := by
  rw [evalTransfer_indirect_eq]
  cases depth with
  | zero => exact True.intro
  | succ depth =>
    cases pointer : ctx.funcPtrs address with
    | none =>
      simp [terminalIndirect,pointer,Sem.throwUB,Sem.run,StateT.run,StateT.bind,StateT.lift,
        throw,throwThe,MonadExceptOf.throw,bind,pure,Except.bind,Except.pure,FrameCalleeExit]
    | some id =>
      cases declaration : ctx.funcTys sig with
      | none =>
        simp [terminalIndirect,pointer,declaration,Sem.throwTypeError,Sem.run,StateT.run,StateT.bind,StateT.lift,
          throw,throwThe,MonadExceptOf.throw,bind,pure,Except.bind,Except.pure,FrameCalleeExit]
      | some signature =>
        cases found : ctx.functions id with
        | none =>
          simp [terminalIndirect,pointer,declaration,found,Sem.throwTypeError,Sem.run,StateT.run,StateT.bind,StateT.lift,
            throw,throwThe,MonadExceptOf.throw,bind,pure,Except.bind,Except.pure,FrameCalleeExit]
        | some callee =>
          simp only [terminalIndirect,pointer,declaration,found,pure_bind]
          apply (FrameActionExit.callee state _).1
          apply FrameActionExit.bind (fun bound _ => MintedArgs bound args) MintedArgs _ _ state
            (abi_arguments_exit signature.abi args state valid incoming)
          intro unit caller callerValid incoming
          cases unit
          cases matched : checkIndirectSignature signature callee.body with
          | error message => simp [matched,Sem.throwTypeError,Sem.run,StateT.run,StateT.bind,StateT.lift,
              throw,throwThe,MonadExceptOf.throw,bind,pure,Except.bind,Except.pure,FrameActionExit]
          | ok unit =>
            cases unit
            simp only [matched,pure_bind]
            apply FrameActionExit.bind (fun bound _ => MintedArgs bound args) MintedArgs _ _ caller
              (abi_arguments_exit callee.body.abi args caller callerValid incoming)
            intro unit checked checkedValid incoming
            cases unit
            cases arity : checkCallArity args callee.body.paramTys with
            | error message => simp [arity,Sem.throwTypeError,Sem.run,StateT.run,StateT.bind,StateT.lift,
                throw,throwThe,MonadExceptOf.throw,bind,pure,Except.bind,Except.pure,FrameActionExit]
            | ok unit =>
              cases unit
              simp only [arity,pure_bind]
              apply FrameActionExit.bind (fun bound _ => MintedArgs bound args) MintedArgs _ _ checked
                (poison_arguments_exit args checked checkedValid incoming)
              intro unit before beforeValid incoming
              cases unit
              exact (FrameActionExit.callee before _).2
                (checked_call_frame_exit ctx callee.body.returnTys true false "CallIndirect: " _ before beforeValid
                  (callees id callee found depth args (callerWorld before) ⟨beforeValid.table,values_empty _⟩ incoming))

/-- Ordered original SSA argument lookup and the selected terminal transfer
share one exit proof; header refusals need no independently successful premise. -/
theorem terminal_direct_dispatch_exit (recurse : Recurse) (ctx : EvalContext) (depth : Nat)
    (cfg : CFG) (block : BasicBlock) (strategy : PanicStrategy) (id : FuncId) (ids : List ValueId)
    (state : MachineState) (valid : WellMintedState state)
    (callees : FrameCalleeExitContract recurse ctx strategy) :
    FrameActionExit MintedArgs state (Sem.run (do
      let termResult ← stepTermWithContext ctx depth cfg (.Call id ids) strategy
      let result ← match termResult with
        | .terminator step => pure step
        | .value _ => Sem.throwTypeError "basic block does not end with a terminator"
        | .values _ => Sem.throwTypeError "basic block does not end with a terminator"
      evalTransfer recurse ctx depth cfg block strategy result) state) := by
  have request : stepTermWithContext ctx depth cfg (.Call id ids) strategy =
      (ids.mapM Sem.lookupValue >>= fun values => pure (.terminator (.CallReq id values))) := by
    cases strategy <;> rfl
  rw [request]
  simp only [bind_assoc,pure_bind]
  apply FrameActionExit.bind MintedArgs MintedArgs _ _ state (lookup_arguments_action ids state valid)
  intro args caller callerValid incoming
  exact (FrameActionExit.callee caller _).2
    (terminal_direct_transfer_exit recurse ctx depth cfg block strategy id args caller callerValid incoming callees)

private theorem pure_no_unwind {α : Type} (value : α) : CallCheckNoUnwind (pure value : Sem α) := by
  intro state exception after run
  cases run

private theorem lookup_no_unwind (id : ValueId) : CallCheckNoUnwind (Sem.lookupValue id) := by
  intro state exception after run
  cases found : state.lookupValue id <;>
    simp [Sem.lookupValue,Sem.run,Sem.getState,found,Sem.throwTypeError,StateT.run,StateT.bind,
      StateT.get,StateT.pure,StateT.lift,bind,pure,Except.bind,Except.pure,throw,throwThe,MonadExceptOf.throw] at run

private theorem raw_request_no_unwind (model : ByteModel) (calleeId : ValueId) (sig : FuncTyId)
    (args : List ValueId) (conv : CallingConv)  :
    CallCheckNoUnwind (stepInst (.CallIndirect calleeId sig args conv) model) := by
  apply CallCheckNoUnwind.bind _ _ (lookup_no_unwind calleeId)
  intro value
  cases value
  case ptr address provenance =>
    simp only [pure_bind]
    exact CallCheckNoUnwind.bind _ _ (lookup_arguments_no_unwind args) (fun _ => pure_no_unwind _)
  all_goals intro state exception after run; cases run

/-- Only FnDef preparation reads functionErrors. Its static-error premise
prevents injected arbitrary unwind states; raw pointer fallbacks cannot unwind. -/
theorem indirect_terminal_request_no_unwind (ctx : EvalContext) (safe : StaticFunctionErrors ctx)
    (depth : Nat) (cfg : CFG) (strategy : PanicStrategy) (calleeId : ValueId) (sig : FuncTyId)
    (args : List ValueId) (conv : CallingConv)  :
    CallCheckNoUnwind (stepTermWithContext ctx depth cfg (.CallIndirect calleeId sig args conv) strategy) := by
  have anchored : stepTermWithContext ctx depth cfg (.CallIndirect calleeId sig args conv) strategy =
      closureTermWithContext ctx depth (.CallIndirect calleeId sig args conv)
        (stepInst (.CallIndirect calleeId sig args conv) ctx.byteModel) := by
    cases strategy <;> rfl
  rw [anchored]
  apply CallCheckNoUnwind.bind _ _ (lookup_no_unwind calleeId)
  intro value
  cases value
  case nullPtr => intro state exception after run; cases run
  case fnDef held fn =>
    apply CallCheckNoUnwind.bind _ _ (lookup_arguments_no_unwind args)
    intro values
    cases depth with
    | zero => intro state exception after run; cases run
    | succ depth =>
      cases checked : functionCall ctx held fn sig with
      | error error =>
        intro state exception after run
        simp only [checked] at run
        cases run
        exact function_call_no_unwind ctx safe held fn sig exception after checked
      | ok id =>
        simp only [checked,pure_bind]
        exact pure_no_unwind _
  case typedClosure cid fn captures =>
    apply CallCheckNoUnwind.bind _ _ (lookup_arguments_no_unwind args)
    intro values
    cases depth with
    | zero => intro state exception after run; cases run
    | succ depth =>
      cases checked : closureCall ctx cid fn captures sig values conv with
      | error error =>
        intro state exception after run
        simp only [checked] at run
        cases run
        exact closure_call_no_unwind ctx cid fn captures sig values conv exception after checked
      | ok prepared =>
        simp only [checked,pure_bind]
        exact pure_no_unwind _
  all_goals exact raw_request_no_unwind ctx.byteModel calleeId sig args conv


def IndirectTerminalTermValues (bound : Nat) : InstrResult → Prop
  | .terminator step => IndirectTerminalValues bound step
  | _ => False

/-- Full contextual terminal preparation, including recursive closure checks.
The static-error hypothesis restricts only FnDef function-error injection. -/
theorem indirect_terminal_request_exit (ctx : EvalContext) (safe : StaticFunctionErrors ctx)
    (depth : Nat) (cfg : CFG) (strategy : PanicStrategy) (calleeId : ValueId) (sig : FuncTyId)
    (args : List ValueId) (conv : CallingConv) :
    FrameActionValid IndirectTerminalTermValues
      (stepTermWithContext ctx depth cfg (.CallIndirect calleeId sig args conv) strategy) := by
  apply frame_action_of_success_no_unwind _ _ (indirect_terminal_request_no_unwind ctx safe depth cfg strategy calleeId sig args conv)
  intro state after result valid run
  obtain ⟨step,shape,same,transported⟩ := indirect_terminal_request_success ctx depth cfg strategy calleeId sig args conv state after result valid run
  subst result
  subst after
  exact ⟨valid,transported,.refl _⟩

/-- Full original raw/FnDef/closure terminal dispatch. Callees' actual unwind
states retain the callee's throw state; normal exits restore caller locals. -/
theorem terminal_indirect_dispatch_exit (recurse : Recurse) (ctx : EvalContext) (safe : StaticFunctionErrors ctx)
    (depth : Nat) (cfg : CFG) (block : BasicBlock) (strategy : PanicStrategy)
    (calleeId : ValueId) (sig : FuncTyId) (args : List ValueId) (conv : CallingConv)
    (state : MachineState) (valid : WellMintedState state)
    (callees : FrameCalleeExitContract recurse ctx strategy) :
    FrameActionExit MintedArgs state (Sem.run (do
      let termResult ← stepTermWithContext ctx depth cfg (.CallIndirect calleeId sig args conv) strategy
      let result ← match termResult with
        | .terminator step => pure step
        | .value _ => Sem.throwTypeError "basic block does not end with a terminator"
        | .values _ => Sem.throwTypeError "basic block does not end with a terminator"
      evalTransfer recurse ctx depth cfg block strategy result) state) := by
  apply FrameActionExit.bind IndirectTerminalTermValues MintedArgs _ _ state
    (indirect_terminal_request_exit ctx safe depth cfg strategy calleeId sig args conv state valid)
  intro result before beforeValid transported
  cases result with
  | value _ => cases transported
  | values _ => cases transported
  | terminator step =>
    apply (FrameActionExit.callee before _).2
    cases step with
    | CallReq id values =>
      exact terminal_direct_transfer_exit recurse ctx depth cfg block strategy id values before beforeValid transported callees
    | CallIndirectReq address signature values =>
      exact raw_terminal_transfer_exit recurse ctx depth cfg block strategy address signature values before beforeValid transported callees
    | Continue _ _ => cases transported
    | Ret _ => cases transported
    | Stuck => cases transported
    | InvokeReq _ _ _ _ _ => cases transported
    | InvokeIndirectReq _ _ _ _ _ _ => cases transported
    | SeqMapReq _ _ => cases transported

end TrustIr.FrameLifetime
