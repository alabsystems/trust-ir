-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0
import TrustIr.Proofs.FrameIndirectCalls
import TrustIr.Proofs.GenericCoroPrefixTransfer

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


/-- Ordered terminal Call argument lookup neither changes state nor invents
frame identities. Header validation belongs to the actual terminal transfer. -/
theorem terminal_call_request_success (ctx : EvalContext) (depth : Nat) (cfg : CFG)
    (strategy : PanicStrategy) (id : FuncId) (args : List ValueId)
    (s final : MachineState) (result : InstrResult) (valid : WellMintedState s)
    (run : Sem.run (stepTermWithContext ctx depth cfg (.Call id args) strategy) s = .ok (result,final)) :
    ∃ values, result = .terminator (.CallReq id values) ∧ final = s ∧ MintedArgs s.nextFrameLineage values := by
  have anchored : stepTermWithContext ctx depth cfg (.Call id args) strategy =
      (args.mapM Sem.lookupValue >>= fun values => pure (.terminator (.CallReq id values))) := by
    cases strategy <;> rfl
  rw [anchored] at run
  obtain ⟨values,middle,looked,tail⟩ := split_bind_success _ _ s final result run
  obtain ⟨same,incoming⟩ := lookup_args_success args s middle values valid looked
  subst middle
  change Except.ok (.terminator (.CallReq id values),s) = Except.ok (result,final) at tail
  cases tail
  exact ⟨values,rfl,rfl,incoming⟩

/-- Actual terminal direct transfer preserves identities and history, including
its state-dependent typed-closure return check. The recursive execution
contract is explicit here and must be discharged by a CFG fuel induction. -/
theorem terminal_direct_transfer_success (recurse : Recurse) (ctx : EvalContext) (depth : Nat)
    (cfg : CFG) (block : BasicBlock) (strategy : PanicStrategy) (id : FuncId) (args : List Value)
    (s final : MachineState) (values : List Value) (valid : WellMintedState s)
    (incoming : MintedArgs s.nextFrameLineage args)
    (execution : ∀ callee, ctx.functions id = some callee → ∀ childDepth before after returned,
      WellMintedState before → MintedArgs before.nextFrameLineage args →
      Sem.run (recurse (ctx.forFunction callee) childDepth callee.cfg callee.entryBlock args strategy) before = .ok (returned,after) →
      DirectFrameResult before after returned)
    (run : Sem.run (evalTransfer recurse ctx depth cfg block strategy (.CallReq id args)) s = .ok (values,final)) :
    DirectFrameResult s final values := by
  rw [evalTransfer_call_eq] at run
  cases depth with
  | zero => cases run
  | succ depth =>
    change Sem.run (ctx.lookupDirectCallee id "Call: callee is a bodyless declaration" "Call: undefined function" >>= _) s = .ok (values,final) at run
    obtain ⟨callee,middle,looked,tail⟩ := split_bind_success _ _ s final values run
    obtain ⟨found,same⟩ := direct_lookup_success ctx id s middle callee looked
    subst middle
    obtain ⟨unit,middle,checked,tail⟩ := split_bind_success (directCallHeader callee.body args) _ s final values tail
    cases unit
    have same := header_readonly callee.body args s ((),middle) checked
    change middle = s at same
    subst middle
    change Sem.run (callFrameWith (checkReturns ctx callee.body.returnTys true
      (terminalClosureCheck block.terminator (saveFrame s none)) "Call: ")
      (recurse (ctx.forFunction callee) depth callee.cfg callee.entryBlock args strategy)) s = .ok (values,final) at tail
    have enteredValid : WellMintedState (callerWorld s) := ⟨valid.table,values_empty _⟩
    exact indirect_return_frame_success ctx callee.body.returnTys _ "Call: " _ s final values valid
      (fun after returned executed => execution callee found depth (callerWorld s) after returned enteredValid incoming executed) tail

/-- Concrete bounded terminal transfer into the recursively covered body-call
program. This discharges the boundary contract using the existing CFG theorem;
it does not yet admit terminal calls inside that callee grammar. -/
theorem terminal_direct_transfer_cfg_success (ctx : EvalContext) (fuel depth : Nat)
    (cfg : CFG) (block : BasicBlock) (strategy : PanicStrategy) (id : FuncId) (args : List Value)
    (s final : MachineState) (values : List Value) (program : CallFrameProgram ctx)
    (valid : WellMintedState s) (incoming : MintedArgs s.nextFrameLineage args)
    (run : Sem.run (evalTransfer (fun child depth cfg pc args strategy =>
      stepNWithContext child fuel depth cfg pc args strategy) ctx depth cfg block strategy (.CallReq id args)) s =
      .ok (values,final)) : DirectFrameResult s final values := by
  apply terminal_direct_transfer_success _ ctx depth cfg block strategy id args s final values valid incoming ?_ run
  intro callee found childDepth before after returned beforeValid childIncoming executed
  exact call_frame_cfg_success (ctx.forFunction callee) callee.cfg
    ((program id callee found).forFunction ctx callee callee.cfg)
    (program.forFunction ctx callee) fuel childDepth callee.entryBlock args strategy before after returned beforeValid childIncoming executed

end TrustIr.FrameLifetime
