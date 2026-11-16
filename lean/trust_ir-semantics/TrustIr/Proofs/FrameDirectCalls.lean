-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0
import TrustIr.Proofs.FrameExecutionHistory
import TrustIr.Proofs.GenericCoroPrefixCalls

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

/-- The covered value grammar plus actual direct body calls. -/
inductive DirectFrameInstruction : Inst → Prop where
  | value {inst : Inst} (site : FrameInstruction inst) : DirectFrameInstruction inst
  | call (id : FuncId) (args : List ValueId) : DirectFrameInstruction (.Call id args)

def DirectFrameCFG (ctx : EvalContext) (cfg : CFG) : Prop :=
  ∀ pc block, cfg pc = some block →
    (∀ row ∈ bodyInstsWithResultDests (ctx.resolveBlock block).body
      (ctx.resolveBlock block).bodyResultDests, DirectFrameInstruction row.1) ∧
    Nonempty (FrameControl (ctx.resolveBlock block).terminator)

/-- Every supplied executable target has the same covered grammar. Missing
or declared-only targets retain the actual interpreter's refusal behavior. -/
def DirectFrameProgram (ctx : EvalContext) : Prop :=
  ∀ id function, ctx.functions id = some function → DirectFrameCFG ctx function.cfg

theorem DirectFrameCFG.forFunction (ctx : EvalContext) (function : EvalFunction) (cfg : CFG)
    (grammar : DirectFrameCFG ctx cfg) : DirectFrameCFG (ctx.forFunction function) cfg := grammar

theorem DirectFrameProgram.forFunction (ctx : EvalContext) (function : EvalFunction)
    (program : DirectFrameProgram ctx) : DirectFrameProgram (ctx.forFunction function) := program

/-- The two components needed at a recursive function boundary, plus returned
value validity at the later counter. -/
def DirectFrameResult (before after : MachineState) (values : List Value) : Prop :=
  WellMintedState after ∧ MintedArgs after.nextFrameLineage values ∧ HistoryExtends before after

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

private theorem header_readonly (body : FuncBody) (values : List Value) :
    ReadOnly (directCallHeader body values) := by
  unfold directCallHeader requireUntypedAbi
  repeat' first
    | exact poison_readonly _ _
    | exact pure_readonly _
    | exact throw_readonly _
    | (refine bind_readonly _ _ ?_ (fun value => ?_) <;> dsimp only)
    | split

private theorem direct_lookup_success (ctx : EvalContext) (id : FuncId)
    (s final : MachineState) (callee : EvalFunction)
    (run : Sem.run (ctx.lookupDirectCallee id "Call: callee is a bodyless declaration" "Call: undefined function") s = .ok (callee,final)) :
    ctx.functions id = some callee ∧ final = s := by
  cases found : ctx.functions id with
  | none =>
    cases declared : ctx.declared id <;>
      simp [EvalContext.lookupDirectCallee,found,declared,Sem.throwTypeError,Sem.throwUnsupported,Sem.run,
        StateT.run,StateT.lift,throw,throwThe,MonadExceptOf.throw,bind,pure,Except.bind,Except.pure] at run
  | some function =>
    simp only [EvalContext.lookupDirectCallee,found] at run
    change Except.ok (function,s) = Except.ok (callee,final) at run
    cases run
    exact ⟨rfl,rfl⟩

theorem WellMintedState.call_results_success (ctx : EvalContext) (inst : Inst)
    (dests : List ValueId) (values : List Value) (s final : MachineState)
    (valid : WellMintedState s) (incoming : MintedArgs s.nextFrameLineage values)
    (run : Sem.run (ctx.bindCallResults inst dests values) s = .ok ((),final)) : WellMintedState final := by
  by_cases arity : dests.length = values.length
  · simp only [EvalContext.bindCallResults,arity,bne_self_eq_false,Bool.false_eq_true,↓reduceIte] at run
    obtain ⟨unit,middle,checked,tail⟩ := split_bind_success _ _ s final () run
    cases unit
    have same := result_checks_success_state ctx inst dests values s middle checked
    subst middle
    exact valid.bind_result_dests_success dests values s final incoming tail
  · exact valid.bind_result_dests_success dests values s final incoming
      (by simpa [EvalContext.bindCallResults,arity] using run)

theorem call_results_history (ctx : EvalContext) (inst : Inst) (dests : List ValueId) (values : List Value) :
    KeepsHistory (ctx.bindCallResults inst dests values) := by
  unfold EvalContext.bindCallResults
  rw [HistoryEffects.conditional_property_iff HistoryEffects.KeepsHistory]
  constructor
  · intro selected
    exact result_dests_history _ _
  · intro selected
    exact bind_history _ _ (result_checks_history _ _ _ _) (fun _ => result_dests_history _ _)

/-- The actual caller reset, checked returns and restoration consume the
recursive execution summary; no independent return-check success is assumed. -/
theorem call_frame_success (returnTys : List Ty) (callee : Sem (List Value))
    (s final : MachineState) (values : List Value) (valid : WellMintedState s)
    (execution : ∀ after returned, Sem.run callee (callerWorld s) = .ok (returned,after) →
      DirectFrameResult (callerWorld s) after returned)
    (run : Sem.run (callFrame returnTys callee) s = .ok (values,final)) : DirectFrameResult s final values := by
  change Sem.run (finishCall returnTys (saveFrame s none) callee) (callerWorld s) = .ok (values,final) at run
  obtain ⟨returned,after,executed,tail⟩ := split_bind_success callee _ (callerWorld s) final values run
  obtain ⟨afterValid,returnedValid,calleeHistory⟩ := execution after returned executed
  cases arity : checkReturnArity returned returnTys with
  | error error =>
    simp [arity,Sem.throwTypeError,Sem.run,StateT.run,StateT.bind,StateT.lift,
      throw,throwThe,MonadExceptOf.throw,bind,Except.bind] at tail
  | ok unit =>
    cases unit
    simp only [arity,pure_bind] at tail
    obtain ⟨unit,checked,guarded,tail⟩ := split_bind_success (Sem.rejectPoisonValues returned "Call returns") _ after final values tail
    cases unit
    have same := poison_readonly returned "Call returns" after ((),checked) guarded
    change checked = after at same
    subst checked
    change Except.ok (returned,restoreFrame after (saveFrame s none) []) = Except.ok (values,final) at tail
    cases tail
    have history := (history_clear_locals s).trans calleeHistory
    have saved := saved_values_history s after (saveFrame s none) valid.values history
    exact ⟨WellMintedState.restore after (saveFrame s none) [] afterValid.table saved (fun _ member => nomatch member),
      returnedValid,history.trans (history_restore after (saveFrame s none) [])⟩

/-- Complete original direct body-call path, under the smaller-fuel recursive
execution contract at actual target lookups. -/
theorem direct_call_body_success (recurse : Recurse) (ctx : EvalContext) (depth : Nat)
    (strategy : PanicStrategy) (id : FuncId) (args dests : List ValueId)
    (s final : MachineState) (outcome : ForInStep Unit) (valid : WellMintedState s)
    (execution : ∀ callee, ctx.functions id = some callee → ∀ childDepth values before after returned,
      WellMintedState before → MintedArgs before.nextFrameLineage values →
      Sem.run (recurse (ctx.forFunction callee) childDepth callee.cfg callee.entryBlock values strategy) before = .ok (returned,after) →
      DirectFrameResult before after returned)
    (run : Sem.run (evalBodyStep recurse ctx depth strategy (.Call id args,dests)) s = .ok (outcome,final)) :
    WellMintedState final ∧ HistoryExtends s final := by
  rw [evalBodyStep_call] at run
  obtain ⟨values,middle,looked,tail⟩ := split_bind_success (args.mapM Sem.lookupValue) _ s final outcome run
  obtain ⟨same,incoming⟩ := lookup_args_success args s middle values valid looked
  subst middle
  cases depth with
  | zero => cases tail
  | succ depth =>
    obtain ⟨callee,middle,looked,tail⟩ := split_bind_success _ _ s final outcome tail
    obtain ⟨found,same⟩ := direct_lookup_success ctx id s middle callee looked
    subst middle
    obtain ⟨unit,middle,checked,tail⟩ := split_bind_success (directCallHeader callee.body values) _ s final outcome tail
    cases unit
    have same := header_readonly callee.body values s ((),middle) checked
    change middle = s at same
    subst middle
    obtain ⟨returned,restored,called,tail⟩ := split_bind_success _ _ s final outcome tail
    have enteredValid : WellMintedState (callerWorld s) := ⟨valid.table,values_empty _⟩
    obtain ⟨restoredValid,returnedValid,history⟩ := call_frame_success callee.body.returnTys _ s restored returned valid
      (fun after results executed => execution callee found depth values (callerWorld s) after results enteredValid incoming executed) called
    obtain ⟨unit,published,bound,tail⟩ := split_bind_success _ _ restored final outcome tail
    cases unit
    have publishedValid := restoredValid.call_results_success ctx (.Call id args) dests returned restored published returnedValid bound
    have publicationHistory := (call_results_history ctx (.Call id args) dests returned).extends restored published () bound
    change Except.ok (.yield (),published) = Except.ok (outcome,final) at tail
    cases tail
    exact ⟨publishedValid,history.trans publicationHistory⟩

/-- A recursive summary used only as the smaller-fuel induction hypothesis. -/
def DirectFrameRecursion (recurse : Recurse) (strategy : PanicStrategy) : Prop :=
  ∀ ctx cfg depth pc args s final values,
    DirectFrameCFG ctx cfg → DirectFrameProgram ctx →
    WellMintedState s → MintedArgs s.nextFrameLineage args →
    Sem.run (recurse ctx depth cfg pc args strategy) s = .ok (values,final) → DirectFrameResult s final values

theorem direct_frame_body_success (recurse : Recurse) (ctx : EvalContext) (depth : Nat)
    (strategy : PanicStrategy) (inst : Inst) (site : DirectFrameInstruction inst) (dests : List ValueId)
    (s final : MachineState) (outcome : ForInStep Unit) (program : DirectFrameProgram ctx)
    (valid : WellMintedState s) (recursive : DirectFrameRecursion recurse strategy)
    (run : Sem.run (evalBodyStep recurse ctx depth strategy (inst,dests)) s = .ok (outcome,final)) :
    WellMintedState final ∧ HistoryExtends s final := by
  cases site with
  | value site =>
    exact ⟨valid.frame_body_success recurse ctx depth strategy inst site dests s final outcome run,
      frame_body_history recurse ctx depth strategy inst site dests s final outcome valid run⟩
  | call id args =>
    exact direct_call_body_success recurse ctx depth strategy id args dests s final outcome valid
      (fun callee found childDepth values before after returned beforeValid incoming executed =>
        recursive (ctx.forFunction callee) callee.cfg childDepth callee.entryBlock values before after returned
          ((program id callee found).forFunction ctx callee callee.cfg)
          (program.forFunction ctx callee) beforeValid incoming executed) run

theorem direct_frame_body_list_success (recurse : Recurse) (ctx : EvalContext) (depth : Nat)
    (strategy : PanicStrategy) (rows : List (Inst × List ValueId)) (s final : MachineState)
    (sites : ∀ row ∈ rows, DirectFrameInstruction row.1) (program : DirectFrameProgram ctx)
    (valid : WellMintedState s) (recursive : DirectFrameRecursion recurse strategy)
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
    obtain ⟨middleValid,firstHistory⟩ := direct_frame_body_success recurse ctx depth strategy row.1
      (sites row (.head rest)) row.2 s middle outcome program valid recursive first
    obtain ⟨finalValid,tailHistory⟩ := ih middle (fun row member => sites row (.tail _ member)) middleValid tail
    exact ⟨finalValid,firstHistory.trans tailHistory⟩

theorem direct_frame_layer_success (recurse : Recurse) (ctx : EvalContext) (depth : Nat)
    (cfg : CFG) (pc : BlockId) (args : List Value) (strategy : PanicStrategy)
    (s final : MachineState) (values : List Value) (grammar : DirectFrameCFG ctx cfg)
    (program : DirectFrameProgram ctx) (valid : WellMintedState s)
    (incoming : MintedArgs s.nextFrameLineage args) (recursive : DirectFrameRecursion recurse strategy)
    (run : Sem.run (evalLayer recurse ctx depth cfg pc args strategy) s = .ok (values,final)) :
    DirectFrameResult s final values := by
  cases found : cfg pc with
  | none =>
    simp [evalLayer,found,Sem.throwTypeError,Sem.run,StateT.run,StateT.lift,
      throw,throwThe,MonadExceptOf.throw,bind,pure,Except.bind,Except.pure] at run
  | some block =>
    obtain ⟨sites,⟨control⟩⟩ := grammar pc block found
    simp only [evalLayer,found] at run
    obtain ⟨unit, checkedState, checked, run⟩ := split_bind_success _ _ s final values run
    have same := memory_check_success_state _ s checkedState unit checked
    subst checkedState
    cases unit
    obtain ⟨unit,bound,params,tail⟩ := split_bind_success _ _ s final values run
    cases unit
    have boundValid := valid.checked_params_success _ args s bound incoming params
    have paramsHistory := (checked_params_history _ args).extends s bound () params
    obtain ⟨unit,afterBody,body,tail⟩ := split_bind_success _ _ bound final values tail
    cases unit
    obtain ⟨bodyValid,bodyHistory⟩ := direct_frame_body_list_success recurse ctx depth strategy _ bound afterBody sites program boundValid recursive body
    obtain ⟨result,afterTerm,term,tail⟩ := split_bind_success _ _ afterBody final values tail
    obtain ⟨step,shape,same,transported⟩ := control.term_success ctx depth cfg strategy afterBody afterTerm result bodyValid term
    subst result
    subst afterTerm
    cases step with
    | Continue next nextArgs =>
      obtain ⟨afterValid,returned,nextHistory⟩ := recursive ctx cfg depth next nextArgs afterBody final values grammar program bodyValid transported tail
      exact ⟨afterValid,returned,paramsHistory.trans (bodyHistory.trans nextHistory)⟩
    | Ret returned =>
      change Sem.run (GenericCoro.checkedReturn ctx returned) afterBody = .ok (values,final) at tail
      obtain ⟨same, equal⟩ := checked_return_success ctx returned values afterBody final tail
      subst final
      subst values
      exact ⟨bodyValid,transported,paramsHistory.trans bodyHistory⟩
    | Stuck =>
      change Except.error (SemError.ub "reached unreachable") = Except.ok (values,final) at tail
      contradiction
    | CallReq _ _ => cases transported
    | CallIndirectReq _ _ _ => cases transported
    | InvokeReq _ _ _ _ _ => cases transported
    | InvokeIndirectReq _ _ _ _ _ _ => cases transported
    | SeqMapReq _ _ => cases transported

/-- Original bounded recursive execution with direct BODY calls preserves
recursive frame identities, returned values and non-rewinding/non-reviving
history. The recursive contract above is discharged by fuel induction. -/
theorem direct_frame_cfg_success (ctx : EvalContext) (cfg : CFG) (grammar : DirectFrameCFG ctx cfg)
    (program : DirectFrameProgram ctx) (fuel depth : Nat) (pc : BlockId) (args : List Value)
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
    exact direct_frame_layer_success _ ctx depth cfg pc args strategy s final values grammar program valid incoming
      (fun subCtx subCFG subDepth next nextArgs before after returned subGrammar subProgram beforeValid subIncoming executed =>
        ih subCtx subCFG subGrammar subProgram subDepth next nextArgs before after returned beforeValid subIncoming executed) run

/-- Existing call-free CFG qualifications embed in the extended body grammar. -/
theorem FrameCFG.direct (ctx : EvalContext) (cfg : CFG) (grammar : FrameCFG ctx cfg) : DirectFrameCFG ctx cfg := by
  intro pc block found
  obtain ⟨sites,control⟩ := grammar pc block found
  exact ⟨fun row member => .value (sites row member),control⟩

end TrustIr.FrameLifetime
