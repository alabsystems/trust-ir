-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0
import TrustIr.Proofs.FrameTailBoundary

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

/-- Ordinary control transfers and actual direct terminal calls. -/
inductive TailFrameControl : Inst → Type where
  | ordinary {inst : Inst} (control : FrameControl inst) : TailFrameControl inst
  | call (id : FuncId) (args : List ValueId) : TailFrameControl (.Call id args)

def TailFrameCFG (ctx : EvalContext) (cfg : CFG) : Prop :=
  ∀ pc block, cfg pc = some block →
    (∀ row ∈ bodyInstsWithResultDests (ctx.resolveBlock block).body
      (ctx.resolveBlock block).bodyResultDests, CallFrameInstruction row.1) ∧
    Nonempty (TailFrameControl (ctx.resolveBlock block).terminator)

def TailFrameProgram (ctx : EvalContext) : Prop :=
  ∀ id function, ctx.functions id = some function → TailFrameCFG ctx function.cfg

theorem TailFrameCFG.forFunction (ctx : EvalContext) (function : EvalFunction) (cfg : CFG)
    (grammar : TailFrameCFG ctx cfg) : TailFrameCFG (ctx.forFunction function) cfg := grammar

theorem TailFrameProgram.forFunction (ctx : EvalContext) (function : EvalFunction)
    (program : TailFrameProgram ctx) : TailFrameProgram (ctx.forFunction function) := program

/-- This summary is used only for the smaller-fuel evaluator. -/
def TailFrameRecursion (recurse : Recurse) (strategy : PanicStrategy) : Prop :=
  ∀ ctx cfg depth pc args s final values,
    TailFrameCFG ctx cfg → TailFrameProgram ctx →
    WellMintedState s → MintedArgs s.nextFrameLineage args →
    Sem.run (recurse ctx depth cfg pc args strategy) s = .ok (values,final) → DirectFrameResult s final values

theorem TailFrameRecursion.callees (recurse : Recurse) (ctx : EvalContext) (strategy : PanicStrategy)
    (recursive : TailFrameRecursion recurse strategy) (program : TailFrameProgram ctx) :
    FrameCalleeContract recurse ctx strategy := by
  intro id callee found childDepth args before after returned beforeValid incoming executed
  exact recursive (ctx.forFunction callee) callee.cfg childDepth callee.entryBlock args before after returned
    ((program id callee found).forFunction ctx callee callee.cfg)
    (program.forFunction ctx callee) beforeValid incoming executed

theorem tail_frame_layer_success (recurse : Recurse) (ctx : EvalContext) (depth : Nat)
    (cfg : CFG) (pc : BlockId) (args : List Value) (strategy : PanicStrategy)
    (s final : MachineState) (values : List Value) (grammar : TailFrameCFG ctx cfg)
    (program : TailFrameProgram ctx) (valid : WellMintedState s)
    (incoming : MintedArgs s.nextFrameLineage args) (recursive : TailFrameRecursion recurse strategy)
    (run : Sem.run (evalLayer recurse ctx depth cfg pc args strategy) s = .ok (values,final)) :
    DirectFrameResult s final values := by
  rw [evalLayer_eq_transfer] at run
  cases found : cfg pc with
  | none =>
    simp [found,Sem.throwTypeError,Sem.run,StateT.run,StateT.lift,
      throw,throwThe,MonadExceptOf.throw,bind,pure,Except.bind,Except.pure] at run
  | some block =>
    obtain ⟨sites,⟨control⟩⟩ := grammar pc block found
    simp only [found] at run
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
    have callees := recursive.callees recurse ctx strategy program
    obtain ⟨bodyValid,bodyHistory⟩ := call_frame_body_list_with_callees recurse ctx depth strategy _ bound afterBody sites boundValid callees body
    obtain ⟨result,afterTerm,term,tail⟩ := split_bind_success _ _ afterBody final values tail
    generalize termEq : (ctx.resolveBlock block).terminator = termInst at control term
    cases control with
    | ordinary control =>
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
    | call id ids =>
      obtain ⟨callArgs,shape,same,transported⟩ := terminal_call_request_success ctx depth cfg strategy id ids afterBody afterTerm result bodyValid term
      subst result
      subst afterTerm
      change Sem.run (evalTransfer recurse ctx depth cfg (ctx.resolveBlock block) strategy (.CallReq id callArgs)) afterBody = .ok (values,final) at tail
      obtain ⟨afterValid,returned,callHistory⟩ := terminal_direct_transfer_success recurse ctx depth cfg (ctx.resolveBlock block) strategy id callArgs afterBody final values bodyValid transported
        (fun callee found childDepth before after returned beforeValid childIncoming executed =>
          callees id callee found childDepth callArgs before after returned beforeValid childIncoming executed) tail
      exact ⟨afterValid,returned,paramsHistory.trans (bodyHistory.trans callHistory)⟩

/-- Original bounded evaluation through arbitrary recursive direct terminal
calls and mixed direct/indirect body calls. Callee preservation is discharged by
fuel induction; no independently successful header/return checks are assumed. -/
theorem tail_frame_cfg_success (ctx : EvalContext) (cfg : CFG) (grammar : TailFrameCFG ctx cfg)
    (program : TailFrameProgram ctx) (fuel depth : Nat) (pc : BlockId) (args : List Value)
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
    exact tail_frame_layer_success _ ctx depth cfg pc args strategy s final values grammar program valid incoming
      (fun subCtx subCFG subDepth next nextArgs before after returned subGrammar subProgram beforeValid subIncoming executed =>
        ih subCtx subCFG subGrammar subProgram subDepth next nextArgs before after returned beforeValid subIncoming executed) run

theorem CallFrameCFG.tail (ctx : EvalContext) (cfg : CFG) (grammar : CallFrameCFG ctx cfg) :
    TailFrameCFG ctx cfg := by
  intro pc block found
  obtain ⟨sites,⟨control⟩⟩ := grammar pc block found
  exact ⟨sites,⟨.ordinary control⟩⟩

theorem CallFrameProgram.tail (ctx : EvalContext) (program : CallFrameProgram ctx) : TailFrameProgram ctx := by
  intro id function found
  exact (program id function found).tail ctx function.cfg

end TrustIr.FrameLifetime
