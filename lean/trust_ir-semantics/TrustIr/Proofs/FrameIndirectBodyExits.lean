-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0
import TrustIr.Proofs.FrameClosureExits

namespace TrustIr.FrameLifetime
open GenericCoro GenericCoro.Prefix

private theorem lookup_no_unwind (id : ValueId) : CallCheckNoUnwind (Sem.lookupValue id) := by
  intro state exception after run
  cases found : state.lookupValue id <;>
    simp [Sem.lookupValue,Sem.run,Sem.getState,found,Sem.throwTypeError,StateT.run,StateT.bind,
      StateT.get,StateT.pure,StateT.lift,bind,pure,Except.bind,Except.pure,throw,throwThe,MonadExceptOf.throw] at run

/-- Single original SSA lookup transports recursive frame identities. -/
theorem lookup_value_frame_action (id : ValueId) : FrameActionValid MintedValue (Sem.lookupValue id) := by
  apply frame_action_of_success_no_unwind _ _ (lookup_no_unwind id)
  intro state after value valid run
  cases found : state.lookupValue id with
  | none =>
    simp [Sem.lookupValue,Sem.run,Sem.getState,found,Sem.throwTypeError,StateT.run,StateT.bind,
      StateT.get,StateT.pure,StateT.lift,bind,pure,Except.bind,Except.pure,throw,throwThe,MonadExceptOf.throw] at run
  | some held =>
    simp [Sem.lookupValue,Sem.run,Sem.getState,found,StateT.run,StateT.bind,StateT.get,
      StateT.pure,bind,pure,Except.bind,Except.pure] at run
    rcases run with ⟨rfl,rfl⟩
    exact ⟨valid,valid.values id held found,.refl _⟩

private theorem address_receipt_exit (held : Value) (state : MachineState)
    (valid : WellMintedState state) (incoming : MintedValue state.nextFrameLineage held) :
    FrameActionExit (fun bound _ => MintedValue bound held) state (Sem.run (indirectAddress held) state) := by
  cases held <;> first | exact ⟨valid,incoming,.refl _⟩ | exact True.intro

private theorem arguments_with_held_exit (held : Value) (ids : List ValueId) (state : MachineState)
    (valid : WellMintedState state) (incoming : MintedValue state.nextFrameLineage held) :
    FrameActionExit (fun bound args => MintedValue bound held ∧ MintedArgs bound args) state
      (Sem.run (ids.mapM Sem.lookupValue) state) := by
  cases executed : Sem.run (ids.mapM Sem.lookupValue) state with
  | ok pair =>
    obtain ⟨args,after⟩ := pair
    obtain ⟨same,transported⟩ := lookup_args_success ids state after args valid executed
    subst after
    exact ⟨valid,⟨incoming,transported⟩,.refl _⟩
  | error error =>
    cases error <;> first
      | exact True.intro
      | exact False.elim (lookup_arguments_no_unwind ids state _ _ executed)

private def modeArguments (held : Value) (ids : List ValueId) : Sem (List Value) :=
  match held with | .fnItem _ => pure [] | _ => ids.mapM Sem.lookupValue

private theorem mode_arguments_with_held_exit (held : Value) (ids : List ValueId) (state : MachineState)
    (valid : WellMintedState state) (incoming : MintedValue state.nextFrameLineage held) :
    FrameActionExit (fun bound args => MintedValue bound held ∧ MintedArgs bound args) state
      (Sem.run (modeArguments held ids) state) := by
  cases held
  case fnItem target => exact ⟨valid, ⟨incoming, fun _ member => by cases member⟩, .refl _⟩
  all_goals exact arguments_with_held_exit _ ids state valid incoming

private theorem abi_no_unwind (abi : Option SignatureAbi) : CallCheckNoUnwind (requireUntypedAbi abi) := by
  intro state exception after run
  unfold requireUntypedAbi at run
  split at run <;> cases run

private theorem raw_arguments_no_unwind (ctx : EvalContext) (address : Addr) (sig : FuncTyId) (args : List Value) :
    CallCheckNoUnwind (rawIndirectArguments ctx address sig args) := by
  cases pointer : ctx.funcPtrs address with
  | none => intro state exception after run; simp only [rawIndirectArguments,pointer] at run; cases run
  | some id =>
    cases signature : ctx.funcTys sig with
    | none => intro state exception after run; simp only [rawIndirectArguments,pointer,signature,pure_bind] at run; cases run
    | some declaration =>
      cases found : ctx.functions id with
      | none => intro state exception after run; simp only [rawIndirectArguments,pointer,signature,found,pure_bind] at run; cases run
      | some callee =>
        simp only [rawIndirectArguments,pointer,signature,found,pure_bind]
        apply CallCheckNoUnwind.bind _ _ (abi_no_unwind declaration.abi)
        intro unit
        cases unit
        cases checked : checkIndirectSignature declaration callee.body with
        | error message => intro state exception after run; simp only [checked] at run; cases run
        | ok unit =>
          cases unit
          intro state exception after run
          simp only [checked,pure_bind] at run
          cases run

/-- Full indirect preparation safety: FnDef uses static context errors;
recursive closure validation and raw-pointer preparation cannot unwind. -/
theorem indirect_arguments_no_unwind (ctx : EvalContext) (safe : StaticFunctionErrors ctx)
    (held : Value) (address : Addr) (sig : FuncTyId) (args : List Value) (conv : CallingConv) :
    CallCheckNoUnwind (indirectArguments ctx held address sig args conv) := by
  cases held
  case fnDef ty fn => exact function_arguments_no_unwind ctx safe ty fn address sig args conv
  case typedClosure cid fn captures =>
    cases checked : closureCall ctx cid fn captures sig args conv with
    | ok call => intro state exception after run; simp only [indirectArguments,checked] at run; cases run
    | error error =>
      intro state exception after run
      simp only [indirectArguments,checked] at run
      cases run
      exact closure_call_no_unwind ctx cid fn captures sig args conv exception after checked
  all_goals exact raw_arguments_no_unwind ctx address sig args

/-- Original preparation retains minted arguments, including prepended closure
captures. Captured values are checked at this actual caller's bound. -/
theorem indirect_arguments_frame_exit (ctx : EvalContext) (safe : StaticFunctionErrors ctx)
    (held : Value) (address : Addr) (sig : FuncTyId) (args : List Value) (conv : CallingConv)
    (state : MachineState) (valid : WellMintedState state)
    (heldValid : MintedValue state.nextFrameLineage held) (incoming : MintedArgs state.nextFrameLineage args) :
    FrameActionExit (fun bound call => MintedArgs bound call.2) state
      (Sem.run (indirectArguments ctx held address sig args conv) state) := by
  cases executed : Sem.run (indirectArguments ctx held address sig args conv) state with
  | ok pair =>
    obtain ⟨call,after⟩ := pair
    obtain ⟨same,transported⟩ := indirect_arguments_success state.nextFrameLineage ctx held address sig args conv state after call heldValid incoming executed
    subst after
    exact ⟨valid,transported,.refl _⟩
  | error error =>
    cases error <;> first
      | exact True.intro
      | exact False.elim (indirect_arguments_no_unwind ctx safe held address sig args conv state _ _ executed)

theorem deferred_indirect_arguments_no_unwind (ctx : EvalContext) (safe : StaticFunctionErrors ctx)
    (held : Value) (address : Addr) (sig : FuncTyId) (ids : List ValueId) (args : List Value)
    (conv : CallingConv) :
    CallCheckNoUnwind (deferredIndirectArguments ctx held address sig ids args conv) := by
  cases held
  case fnItem target =>
    cases checked : functionItemCall ctx target sig conv with
    | error error =>
      intro state exception after run
      simp only [deferredIndirectArguments, checked] at run
      cases run
      exact function_item_call_no_unwind ctx target sig conv exception after checked
    | ok id =>
      simp only [deferredIndirectArguments, checked]
      apply CallCheckNoUnwind.bind _ _ (lookup_arguments_no_unwind ids)
      intro values state exception after run
      cases run
  all_goals
    unfold deferredIndirectArguments
    exact indirect_arguments_no_unwind ctx safe _ address sig args conv

/-- Actual nominal application defers argument reads until header validation;
all modes preserve the same recursive argument and complete-world contract. -/
theorem deferred_indirect_arguments_frame_exit (ctx : EvalContext) (safe : StaticFunctionErrors ctx)
    (held : Value) (address : Addr) (sig : FuncTyId) (ids : List ValueId) (args : List Value)
    (conv : CallingConv) (state : MachineState) (valid : WellMintedState state)
    (heldValid : MintedValue state.nextFrameLineage held) (incoming : MintedArgs state.nextFrameLineage args) :
    FrameActionExit (fun bound call => MintedArgs bound call.2) state
      (Sem.run (deferredIndirectArguments ctx held address sig ids args conv) state) := by
  cases executed : Sem.run (deferredIndirectArguments ctx held address sig ids args conv) state with
  | ok pair =>
    obtain ⟨call, after⟩ := pair
    obtain ⟨same, transported⟩ := deferred_indirect_arguments_success ctx held address sig ids args conv
      state after call valid heldValid incoming executed
    subst after
    exact ⟨valid, transported, .refl _⟩
  | error error =>
    cases error <;> first
      | exact True.intro
      | exact False.elim (deferred_indirect_arguments_no_unwind ctx safe held address sig ids args conv
          state _ _ executed)

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

private def closure_returns (held : Value) : Bool :=
  match held with | .typedClosure _ _ _ => true | _ => false

private def afterArguments (recurse : Recurse) (ctx : EvalContext) (depth : Nat)
    (strategy : PanicStrategy) (held : Value) (address : Addr) (calleeId : ValueId)
    (sig : FuncTyId) (ids : List ValueId) (conv : CallingConv) (dests : List ValueId)
    (values : List Value) : Sem (ForInStep Unit) := do
  match depth with
  | 0 => throw SemError.outOfFuel
  | depth + 1 =>
    let (id, values) ← deferredIndirectArguments ctx held address sig ids values conv
    let callee ← match ctx.functions id with
      | some callee => pure callee
      | none =>
        match held with
        | .fnItem _ => Sem.fromMemoryExcept (resolveFunctionItemBody ctx id)
        | _ => Sem.throwTypeError "CallIndirect: undefined function"
    requireUntypedAbi callee.body.abi
    match checkCallArity values callee.body.paramTys with
    | .ok () => pure ()
    | .error message => Sem.throwTypeError ("CallIndirect: " ++ message)
    Sem.rejectPoisonValues values "CallIndirect arguments"
    let results ← callFrameWith
      (checkReturns ctx callee.body.returnTys true
        (match held with | .typedClosure _ _ _ => true | _ => false) "CallIndirect: ")
      (recurse (ctx.forFunction callee) depth callee.cfg callee.entryBlock values strategy)
    ctx.bindCallResults (.CallIndirect calleeId sig ids conv) dests results
  pure (.yield ())

private theorem bodyIndirect_mode_eq (recurse : Recurse) (ctx : EvalContext) (depth : Nat)
    (strategy : PanicStrategy) (calleeId : ValueId) (sig : FuncTyId)
    (ids : List ValueId) (conv : CallingConv) (dests : List ValueId) :
    bodyIndirect recurse ctx depth strategy calleeId sig ids conv dests = (do
      let held ← Sem.lookupValue calleeId
      let _ ← Sem.fromMemoryExcept (checkFunctionItemCalleeType ctx calleeId held)
      let address ← indirectAddress held
      let values ← modeArguments held ids
      afterArguments recurse ctx depth strategy held address calleeId sig ids conv dests values) := by
  unfold bodyIndirect
  apply bind_same
  intro held
  apply bind_same
  intro checked
  cases checked
  apply bind_same
  intro address
  cases held <;> rfl

/-- Complete original indirect body-call exits, with actual recursive closure
argument/return checks and result publication. The callee full exit contract
remains an explicit recursive CFG induction obligation. -/
theorem indirect_body_call_exit (recurse : Recurse) (ctx : EvalContext) (safe : StaticFunctionErrors ctx)
    (depth : Nat) (strategy : PanicStrategy) (calleeId : ValueId) (sig : FuncTyId)
    (ids : List ValueId) (conv : CallingConv) (dests : List ValueId)
    (state : MachineState) (valid : WellMintedState state)
    (callees : ∀ id callee, ctx.functions id = some callee → ∀ childDepth values before,
      WellMintedState before → MintedArgs before.nextFrameLineage values →
      FrameCalleeExit before (Sem.run (recurse (ctx.forFunction callee) childDepth callee.cfg callee.entryBlock values strategy) before)) :
    FrameActionExit (fun _ _ => True) state
      (Sem.run (evalBodyStep recurse ctx depth strategy (.CallIndirect calleeId sig ids conv,dests)) state) := by
  rw [evalBodyStep_indirect, bodyIndirect_mode_eq]
  apply FrameActionExit.bind MintedValue (fun _ _ => True) _ _ state (lookup_value_frame_action calleeId state valid)
  intro held caller callerValid heldValid
  apply FrameActionExit.bind (fun bound _ => MintedValue bound held) (fun _ _ => True) _ _ caller
    (static_check_frame_exit _ (function_item_callee_type_no_unwind ctx calleeId held) _ caller callerValid
      (fun _ _ => heldValid))
  intro unit caller callerValid heldValid
  cases unit
  apply FrameActionExit.bind (fun bound _ => MintedValue bound held) (fun _ _ => True) _ _ caller
    (address_receipt_exit held caller callerValid heldValid)
  intro address caller callerValid heldValid
  apply FrameActionExit.bind (fun bound args => MintedValue bound held ∧ MintedArgs bound args) (fun _ _ => True) _ _ caller
    (mode_arguments_with_held_exit held ids caller callerValid heldValid)
  intro args caller callerValid receipt
  obtain ⟨heldValid,incoming⟩ := receipt
  unfold afterArguments
  cases depth with
  | zero => exact True.intro
  | succ depth =>
    apply FrameActionExit.bind (fun bound call => MintedArgs bound call.2) (fun _ _ => True) _ _ caller
      (deferred_indirect_arguments_frame_exit ctx safe held address sig ids args conv caller callerValid heldValid incoming)
    intro call caller callerValid incoming
    rcases call with ⟨id,args⟩
    dsimp only at incoming ⊢
    cases found : ctx.functions id with
    | none =>
      cases held <;> try
        simp [found,Sem.throwTypeError,Sem.run,StateT.run,StateT.bind,StateT.lift,
          throw,throwThe,MonadExceptOf.throw,bind,pure,Except.bind,Except.pure,FrameActionExit]
      case fnItem target =>
        cases body : resolveFunctionItemBody ctx id with
        | ok callee => exact False.elim (function_item_body_missing ctx id found callee body)
        | error error =>
          simp only [body,Sem.fromMemoryExcept,Sem.run,StateT.run,StateT.bind,StateT.lift,
            bind,Except.bind,throw,throwThe,MonadExceptOf.throw]
          cases error <;> first
            | exact True.intro
            | exact False.elim (function_item_body_no_unwind ctx safe id _ _ body)
    | some callee =>
      simp only [found,pure_bind]
      apply FrameActionExit.bind (fun bound _ => MintedArgs bound args) (fun _ _ => True) _ _ caller
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
        apply FrameActionExit.bind (fun bound _ => MintedArgs bound args) (fun _ _ => True) _ _ checked
          (poison_arguments_exit args checked checkedValid incoming)
        intro unit before beforeValid incoming
        cases unit
        apply FrameActionExit.bind MintedArgs (fun _ _ => True) _ _ before
          ((FrameActionExit.callee before _).2 (checked_call_frame_exit ctx callee.body.returnTys true
            (closure_returns held) "CallIndirect: " _ before beforeValid
            (callees id callee found depth args (callerWorld before) ⟨beforeValid.table,values_empty _⟩ incoming)))
        intro returned restored restoredValid returnedValid
        apply FrameActionExit.bind (fun _ _ => True) (fun _ _ => True) _ _ restored
          (call_results_frame_exit ctx (.CallIndirect calleeId sig ids conv) dests returned restored restoredValid returnedValid)
        intro unit published publishedValid _
        cases unit
        exact ⟨publishedValid,True.intro,.refl _⟩

end TrustIr.FrameLifetime
