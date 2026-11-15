-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0
import TrustIr.Proofs.FrameIndirectArguments

namespace TrustIr.FrameLifetime
open GenericCoro GenericCoro.Prefix HistoryEffects

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

private def ReadOnly {α : Type} (action : Sem α) : Prop :=
  ∀ state result, Sem.run action state = .ok result → result.2 = state

private theorem pure_readonly {α : Type} (value : α) : ReadOnly (pure value : Sem α) := by
  intro state result run
  cases run
  rfl

private theorem throw_readonly {α : Type} (error : SemError) : ReadOnly (throw error : Sem α) := by
  intro state result run
  cases run

private theorem bind_readonly {α β : Type} (action : Sem α) (next : α → Sem β)
    (first : ReadOnly action) (rest : ∀ value, ReadOnly (next value)) : ReadOnly (action >>= next) := by
  intro state result run
  rw [Sem.run_bind] at run
  cases executed : Sem.run action state with
  | error error => rw [executed] at run; cases run
  | ok pair =>
    have tail : Sem.run (next pair.1) pair.2 = .ok result := by simpa [executed] using run
    exact (rest pair.1 pair.2 result tail).trans (first state pair executed)

private theorem poison_readonly (values : List Value) (message : String) :
    ReadOnly (Sem.rejectPoisonValues values message) := by
  unfold Sem.rejectPoisonValues
  split
  · exact throw_readonly _
  · exact pure_readonly _

private theorem address_readonly (held : Value) : ReadOnly (indirectAddress held) := by
  cases held <;> first | exact pure_readonly _ | exact throw_readonly _

private theorem abi_readonly (body : FuncBody) : ReadOnly (requireUntypedAbi body.abi) := by
  unfold requireUntypedAbi
  split <;> first | exact pure_readonly _ | exact throw_readonly _

/-- The original indirect body-call path, including actual target resolution,
closure capture preparation, return checking and contextual publication. -/
theorem indirect_call_body_success (recurse : Recurse) (ctx : EvalContext) (depth : Nat)
    (strategy : PanicStrategy) (calleeId : ValueId) (sig : FuncTyId)
    (args : List ValueId) (conv : CallingConv) (dests : List ValueId)
    (s final : MachineState) (outcome : ForInStep Unit) (valid : WellMintedState s)
    (execution : ∀ id callee, ctx.functions id = some callee → ∀ childDepth values before after returned,
      WellMintedState before → MintedArgs before.nextFrameLineage values →
      Sem.run (recurse (ctx.forFunction callee) childDepth callee.cfg callee.entryBlock values strategy) before = .ok (returned,after) →
      DirectFrameResult before after returned)
    (run : Sem.run (evalBodyStep recurse ctx depth strategy (.CallIndirect calleeId sig args conv,dests)) s = .ok (outcome,final)) :
    WellMintedState final ∧ HistoryExtends s final := by
  rw [evalBodyStep_indirect] at run
  obtain ⟨held,middle,looked,tail⟩ := split_bind_success _ _ s final outcome run
  obtain ⟨found,same⟩ := lookup_success s middle calleeId held looked
  subst middle
  have heldValid := valid.values calleeId held found
  obtain ⟨address,middle,checked,tail⟩ := split_bind_success _ _ s final outcome tail
  have same := address_readonly held s (address,middle) checked
  change middle = s at same
  subst middle
  obtain ⟨values,middle,looked,tail⟩ := split_bind_success _ _ s final outcome tail
  obtain ⟨same,incoming⟩ := lookup_args_success args s middle values valid looked
  subst middle
  cases depth with
  | zero => cases tail
  | succ depth =>
    obtain ⟨resolved,middle,prepared,tail⟩ := split_bind_success _ _ s final outcome tail
    obtain ⟨same,preparedValid⟩ := indirect_arguments_success s.nextFrameLineage ctx held address sig values conv s middle resolved heldValid incoming prepared
    subst middle
    cases target : ctx.functions resolved.1 with
    | none =>
      simp [target,Sem.throwTypeError,Sem.run,StateT.run,StateT.bind,StateT.lift,throw,throwThe,
        MonadExceptOf.throw,bind,pure,Except.bind,Except.pure] at tail
    | some callee =>
      simp only [target,pure_bind] at tail
      obtain ⟨unit,middle,checked,tail⟩ := split_bind_success _ _ s final outcome tail
      cases unit
      have same := abi_readonly callee.body s ((),middle) checked
      change middle = s at same
      subst middle
      cases arity : checkCallArity resolved.2 callee.body.paramTys with
      | error message =>
        simp [arity,Sem.throwTypeError,Sem.run,StateT.run,StateT.bind,StateT.lift,throw,throwThe,
          MonadExceptOf.throw,bind,pure,Except.bind,Except.pure] at tail
      | ok unit =>
        cases unit
        simp only [arity,pure_bind] at tail
        obtain ⟨unit,middle,checked,tail⟩ := split_bind_success _ _ s final outcome tail
        cases unit
        have same := poison_readonly resolved.2 "CallIndirect arguments" s ((),middle) checked
        change middle = s at same
        subst middle
        obtain ⟨returned,restored,called,tail⟩ := split_bind_success _ _ s final outcome tail
        have enteredValid : WellMintedState (callerWorld s) := ⟨valid.table,values_empty _⟩
        obtain ⟨restoredValid,returnedValid,history⟩ := indirect_return_frame_success ctx callee.body.returnTys _ "CallIndirect: " _ s restored returned valid
          (fun after results executed => execution resolved.1 callee target depth resolved.2 (callerWorld s) after results enteredValid preparedValid executed) called
        obtain ⟨unit,published,bound,tail⟩ := split_bind_success _ _ restored final outcome tail
        cases unit
        have publishedValid := restoredValid.call_results_success ctx (.CallIndirect calleeId sig args conv) dests returned restored published returnedValid bound
        have publicationHistory := (call_results_history ctx (.CallIndirect calleeId sig args conv) dests returned).extends restored published () bound
        change Except.ok (.yield (),published) = Except.ok (outcome,final) at tail
        cases tail
        exact ⟨publishedValid,history.trans publicationHistory⟩

/-- Covered values and direct calls, plus all original indirect body calls. -/
inductive CallFrameInstruction : Inst → Prop where
  | direct {inst : Inst} (site : DirectFrameInstruction inst) : CallFrameInstruction inst
  | indirect (callee : ValueId) (sig : FuncTyId) (args : List ValueId) (conv : CallingConv) :
      CallFrameInstruction (.CallIndirect callee sig args conv)

def CallFrameCFG (ctx : EvalContext) (cfg : CFG) : Prop :=
  ∀ pc block, cfg pc = some block →
    (∀ row ∈ bodyInstsWithResultDests (ctx.resolveBlock block).body
      (ctx.resolveBlock block).bodyResultDests, CallFrameInstruction row.1) ∧
    Nonempty (FrameControl (ctx.resolveBlock block).terminator)

/-- Every supplied executable target has the same covered grammar. Missing
or declared-only targets retain the actual interpreter's refusal behavior. -/
def CallFrameProgram (ctx : EvalContext) : Prop :=
  ∀ id function, ctx.functions id = some function → CallFrameCFG ctx function.cfg

theorem CallFrameCFG.forFunction (ctx : EvalContext) (function : EvalFunction) (cfg : CFG)
    (grammar : CallFrameCFG ctx cfg) : CallFrameCFG (ctx.forFunction function) cfg := grammar

theorem CallFrameProgram.forFunction (ctx : EvalContext) (function : EvalFunction)
    (program : CallFrameProgram ctx) : CallFrameProgram (ctx.forFunction function) := program

/-- A recursive summary used only as the smaller-fuel induction hypothesis. -/
def CallFrameRecursion (recurse : Recurse) (strategy : PanicStrategy) : Prop :=
  ∀ ctx cfg depth pc args s final values,
    CallFrameCFG ctx cfg → CallFrameProgram ctx →
    WellMintedState s → MintedArgs s.nextFrameLineage args →
    Sem.run (recurse ctx depth cfg pc args strategy) s = .ok (values,final) → DirectFrameResult s final values

/-- A call-site contract independent of the caller and callee CFG grammar.
Consumers discharge it from their own smaller-fuel induction hypotheses. -/
def FrameCalleeContract (recurse : Recurse) (ctx : EvalContext) (strategy : PanicStrategy) : Prop :=
  ∀ id callee, ctx.functions id = some callee → ∀ childDepth args before after returned,
    WellMintedState before → MintedArgs before.nextFrameLineage args →
    Sem.run (recurse (ctx.forFunction callee) childDepth callee.cfg callee.entryBlock args strategy) before = .ok (returned,after) →
    DirectFrameResult before after returned

theorem call_frame_body_with_callees (recurse : Recurse) (ctx : EvalContext) (depth : Nat)
    (strategy : PanicStrategy) (inst : Inst) (site : CallFrameInstruction inst) (dests : List ValueId)
    (s final : MachineState) (outcome : ForInStep Unit) (valid : WellMintedState s) (callees : FrameCalleeContract recurse ctx strategy)
    (run : Sem.run (evalBodyStep recurse ctx depth strategy (inst,dests)) s = .ok (outcome,final)) :
    WellMintedState final ∧ HistoryExtends s final := by
  cases site with
  | direct site =>
    cases site with
    | value site =>
      exact ⟨valid.frame_body_success recurse ctx depth strategy inst site dests s final outcome run,
        frame_body_history recurse ctx depth strategy inst site dests s final outcome valid run⟩
    | call id args =>
      exact direct_call_body_success recurse ctx depth strategy id args dests s final outcome valid
        (fun callee found => callees id callee found) run
  | indirect calleeId sig args conv =>
    exact indirect_call_body_success recurse ctx depth strategy calleeId sig args conv dests s final outcome valid
      callees run

theorem call_frame_body_list_with_callees (recurse : Recurse) (ctx : EvalContext) (depth : Nat)
    (strategy : PanicStrategy) (rows : List (Inst × List ValueId)) (s final : MachineState)
    (sites : ∀ row ∈ rows, CallFrameInstruction row.1) (valid : WellMintedState s) (callees : FrameCalleeContract recurse ctx strategy)
    (run : Sem.run (evalBody recurse ctx depth strategy rows) s = .ok ((),final)) :
    WellMintedState final ∧ HistoryExtends s final := by
  induction rows generalizing s with
  | nil =>
    change Except.ok ((),s) = Except.ok ((),final) at run
    cases run
    exact ⟨valid,.refl _⟩
  | cons row rest ih =>
    rw [evalBody_cons] at run
    obtain ⟨outcome,middle,first,tail⟩ := split_bind_success _ _ s final () run
    obtain ⟨middleValid,firstHistory⟩ := call_frame_body_with_callees recurse ctx depth strategy row.1
      (sites row (.head rest)) row.2 s middle outcome valid callees first
    obtain ⟨finalValid,tailHistory⟩ := ih middle (fun row member => sites row (.tail _ member)) middleValid tail
    exact ⟨finalValid,firstHistory.trans tailHistory⟩

theorem call_frame_body_success (recurse : Recurse) (ctx : EvalContext) (depth : Nat)
    (strategy : PanicStrategy) (inst : Inst) (site : CallFrameInstruction inst) (dests : List ValueId)
    (s final : MachineState) (outcome : ForInStep Unit) (program : CallFrameProgram ctx)
    (valid : WellMintedState s) (recursive : CallFrameRecursion recurse strategy)
    (run : Sem.run (evalBodyStep recurse ctx depth strategy (inst,dests)) s = .ok (outcome,final)) :
    WellMintedState final ∧ HistoryExtends s final := by
  exact call_frame_body_with_callees recurse ctx depth strategy inst site dests s final outcome valid
    (fun id callee found childDepth args before after returned beforeValid incoming executed =>
      recursive (ctx.forFunction callee) callee.cfg childDepth callee.entryBlock args before after returned
        ((program id callee found).forFunction ctx callee callee.cfg)
        (program.forFunction ctx callee) beforeValid incoming executed) run

theorem call_frame_body_list_success (recurse : Recurse) (ctx : EvalContext) (depth : Nat)
    (strategy : PanicStrategy) (rows : List (Inst × List ValueId)) (s final : MachineState)
    (sites : ∀ row ∈ rows, CallFrameInstruction row.1) (program : CallFrameProgram ctx)
    (valid : WellMintedState s) (recursive : CallFrameRecursion recurse strategy)
    (run : Sem.run (evalBody recurse ctx depth strategy rows) s = .ok ((),final)) :
    WellMintedState final ∧ HistoryExtends s final := by
  induction rows generalizing s with
  | nil =>
    change Except.ok ((),s) = Except.ok ((),final) at run
    cases run
    exact ⟨valid,.refl _⟩
  | cons row rest ih =>
    rw [evalBody_cons] at run
    obtain ⟨outcome,middle,first,tail⟩ := split_bind_success _ _ s final () run
    obtain ⟨middleValid,firstHistory⟩ := call_frame_body_success recurse ctx depth strategy row.1
      (sites row (.head rest)) row.2 s middle outcome program valid recursive first
    obtain ⟨finalValid,tailHistory⟩ := ih middle (fun row member => sites row (.tail _ member)) middleValid tail
    exact ⟨finalValid,firstHistory.trans tailHistory⟩

theorem call_frame_layer_success (recurse : Recurse) (ctx : EvalContext) (depth : Nat)
    (cfg : CFG) (pc : BlockId) (args : List Value) (strategy : PanicStrategy)
    (s final : MachineState) (values : List Value) (grammar : CallFrameCFG ctx cfg)
    (program : CallFrameProgram ctx) (valid : WellMintedState s)
    (incoming : MintedArgs s.nextFrameLineage args) (recursive : CallFrameRecursion recurse strategy)
    (run : Sem.run (evalLayer recurse ctx depth cfg pc args strategy) s = .ok (values,final)) :
    DirectFrameResult s final values := by
  cases found : cfg pc with
  | none =>
    simp [evalLayer,found,Sem.throwTypeError,Sem.run,StateT.run,StateT.lift,
      throw,throwThe,MonadExceptOf.throw,bind,pure,Except.bind,Except.pure] at run
  | some block =>
    obtain ⟨sites,⟨control⟩⟩ := grammar pc block found
    simp only [evalLayer,found] at run
    obtain ⟨unit,bound,params,tail⟩ := split_bind_success _ _ s final values run
    cases unit
    have boundValid := valid.checked_params_success _ args s bound incoming params
    have paramsHistory := (checked_params_history _ args).extends s bound () params
    obtain ⟨unit,afterBody,body,tail⟩ := split_bind_success _ _ bound final values tail
    cases unit
    obtain ⟨bodyValid,bodyHistory⟩ := call_frame_body_list_success recurse ctx depth strategy _ bound afterBody sites program boundValid recursive body
    obtain ⟨result,afterTerm,term,tail⟩ := split_bind_success _ _ afterBody final values tail
    obtain ⟨step,shape,same,transported⟩ := control.term_success ctx depth cfg strategy afterBody afterTerm result bodyValid term
    subst result
    subst afterTerm
    cases step with
    | Continue next nextArgs =>
      obtain ⟨afterValid,returned,nextHistory⟩ := recursive ctx cfg depth next nextArgs afterBody final values grammar program bodyValid transported tail
      exact ⟨afterValid,returned,paramsHistory.trans (bodyHistory.trans nextHistory)⟩
    | Ret returned =>
      change Except.ok (returned,afterBody) = Except.ok (values,final) at tail
      cases tail
      exact ⟨bodyValid,transported,paramsHistory.trans bodyHistory⟩
    | Stuck =>
      change Except.error (SemError.ub "reached unreachable") = Except.ok (values,final) at tail
      contradiction
    | CallReq _ _ => cases transported
    | CallIndirectReq _ _ _ => cases transported
    | InvokeReq _ _ _ _ _ => cases transported
    | InvokeIndirectReq _ _ _ _ _ _ => cases transported
    | SeqMapReq _ _ => cases transported

/-- Original bounded recursive execution with direct and indirect BODY calls preserves
recursive frame identities, returned values and non-rewinding/non-reviving
history. The recursive contract above is discharged by fuel induction. -/
theorem call_frame_cfg_success (ctx : EvalContext) (cfg : CFG) (grammar : CallFrameCFG ctx cfg)
    (program : CallFrameProgram ctx) (fuel depth : Nat) (pc : BlockId) (args : List Value)
    (strategy : PanicStrategy) (s final : MachineState) (values : List Value)
    (valid : WellMintedState s) (incoming : MintedArgs s.nextFrameLineage args)
    (run : Sem.run (stepNWithContext ctx fuel depth cfg pc args strategy) s = .ok (values,final)) :
    DirectFrameResult s final values := by
  induction fuel generalizing ctx cfg depth pc args s final values with
  | zero =>
    simp [stepNWithContext,Sem.run,StateT.run,StateT.lift,
      throw,throwThe,MonadExceptOf.throw,bind,pure,Except.bind,Except.pure] at run
  | succ fuel ih =>
    rw [stepNWithContext_succ_layer] at run
    exact call_frame_layer_success _ ctx depth cfg pc args strategy s final values grammar program valid incoming
      (fun subCtx subCFG subDepth next nextArgs before after returned subGrammar subProgram beforeValid subIncoming executed =>
        ih subCtx subCFG subGrammar subProgram subDepth next nextArgs before after returned beforeValid subIncoming executed) run

/-- Previously covered direct-call CFGs embed without strengthening their rows. -/
theorem DirectFrameCFG.calls (ctx : EvalContext) (cfg : CFG) (grammar : DirectFrameCFG ctx cfg) :
    CallFrameCFG ctx cfg := by
  intro pc block found
  obtain ⟨sites,control⟩ := grammar pc block found
  exact ⟨fun row member => .direct (sites row member),control⟩

end TrustIr.FrameLifetime
