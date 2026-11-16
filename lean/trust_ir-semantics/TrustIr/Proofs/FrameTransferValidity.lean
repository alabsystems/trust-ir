-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0
import TrustIr.Proofs.FrameBodyValidity

namespace TrustIr.FrameLifetime
open GenericCoro.Prefix

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

/-- Successful evaluator return postchecks retain both the original values
and the exact world; refusal outcomes are deliberately unconstrained here. -/
theorem checked_return_success (ctx : EvalContext) (returned values : List Value)
    (s final : MachineState)
    (run : Sem.run (GenericCoro.checkedReturn ctx returned) s = .ok (values, final)) :
    final = s ∧ values = returned := by
  cases expected : ctx.functionReturnTypes with
  | none =>
    simp only [GenericCoro.checkedReturn, expected] at run
    cases run
    exact ⟨rfl, rfl⟩
  | some expected =>
    simp only [GenericCoro.checkedReturn, expected] at run
    obtain ⟨unit, middle, checked, finished⟩ := split_bind_success _ _ s final values run
    have same := memory_check_success_state _ s middle unit checked
    subst middle
    cases finished
    exact ⟨rfl, rfl⟩

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

private theorem parameter_fold_valid (params : List (ValueId × Ty)) (args : List Value)
    (bound : Nat) (locals : ValueMap) (valid : MintedValues bound locals)
    (incoming : MintedArgs bound args) :
    MintedValues bound ((params.zip args).foldl
      (fun locals binding => locals.set binding.1.1 binding.2) locals) := by
  induction params generalizing args locals with
  | nil => exact valid
  | cons param rest ih =>
    cases args with
    | nil => exact valid
    | cons arg args =>
      exact ih args (locals.set param.1 arg)
        (values_set valid param.1 arg (incoming arg (.head args)))
        (fun value member => incoming value (.tail arg member))

/-- Actual block binding preserves identity validity even with duplicate or
colliding parameter ids. All incoming values must be valid; type checks alone
cannot establish this input-language premise. -/
theorem WellMintedState.params_success (params : List (ValueId × Ty)) (args : List Value)
    (s final : MachineState) (valid : WellMintedState s)
    (incoming : MintedArgs s.nextFrameLineage args)
    (run : Sem.run (bindBlockParams params args) s = .ok ((), final)) :
    WellMintedState final := by
  by_cases arity : params.length = args.length
  · have exactRun : Sem.run (bindBlockParams params args) s = .ok ((),
        { s with locals := (params.zip args).foldl (fun locals binding => locals.set binding.1.1 binding.2) s.locals, nextValueId := params.foldl (fun next param => max next (param.1.index + 1)) s.nextValueId }) := by
      simp [bindBlockParams, arity, Sem.run, Sem.getState, Sem.setState,
        StateT.run, StateT.bind, StateT.get, StateT.set, StateT.pure, bind, pure, Except.bind, Except.pure]
    rw [exactRun] at run
    cases run
    exact ⟨valid.table, parameter_fold_valid params args _ s.locals valid.values incoming⟩
  · simp [bindBlockParams, arity, Sem.throwTypeError, Sem.run,
      StateT.run, StateT.lift, bind, pure, Except.bind, Except.pure,
      throw, throwThe, MonadExceptOf.throw] at run

theorem WellMintedState.checked_params_success (params : List (ValueId × Ty)) (args : List Value)
    (s final : MachineState) (valid : WellMintedState s)
    (incoming : MintedArgs s.nextFrameLineage args)
    (run : Sem.run (bindBlockParamsChecked params args) s = .ok ((), final)) :
    WellMintedState final := by
  by_cases arity : params.length = args.length
  · cases chars : checkSSACharValues (params.map Prod.snd) args with
    | error error =>
      simp [bindBlockParamsChecked, arity, chars, Sem.run,
        StateT.run, StateT.lift, throw, throwThe, MonadExceptOf.throw, bind, pure, Except.bind, Except.pure] at run
    | ok unit =>
      cases unit
      exact WellMintedState.params_success params args s final valid incoming
        (by simpa [bindBlockParamsChecked, arity, chars] using run)
  · exact WellMintedState.params_success params args s final valid incoming
      (by simpa [bindBlockParamsChecked, arity] using run)

/-- Ordinary controls transport only looked-up values, never call requests. -/
def TransferValues (bound : Nat) : StepResult → Prop
  | .Continue _ args | .Ret args => MintedArgs bound args
  | .Stuck => True
  | _ => False

private theorem lookup_finish_success (ids : List ValueId) (encode : List Value → StepResult)
    (s final : MachineState) (result : StepResult) (valid : WellMintedState s)
    (allowed : ∀ args, MintedArgs s.nextFrameLineage args → TransferValues s.nextFrameLineage (encode args))
    (run : Sem.run (ids.mapM Sem.lookupValue >>= fun args => pure (encode args)) s = .ok (result, final)) :
    final = s ∧ TransferValues s.nextFrameLineage result := by
  obtain ⟨args, middle, looked, finished⟩ := split_bind_success _ _ s final result run
  obtain ⟨same, incoming⟩ := lookup_args_success ids s middle args valid looked
  subst middle
  change Except.ok (encode args, s) = Except.ok (result, final) at finished
  have equal := Except.ok.inj finished
  have resultEq : encode args = result := congrArg Prod.fst equal
  have stateEq : s = final := congrArg Prod.snd equal
  exact ⟨stateEq.symm, resultEq ▸ allowed args incoming⟩

theorem br_transfer_success (target : BlockId) (ids : List ValueId)
    (s final : MachineState) (result : StepResult) (valid : WellMintedState s)
    (run : Sem.run (semBr target ids) s = .ok (result, final)) :
    final = s ∧ TransferValues s.nextFrameLineage result :=
  lookup_finish_success ids (.Continue target) s final result valid (fun _ incoming => incoming) run

theorem return_transfer_success (ids : List ValueId)
    (s final : MachineState) (result : StepResult) (valid : WellMintedState s)
    (run : Sem.run (semReturn ids) s = .ok (result, final)) :
    final = s ∧ TransferValues s.nextFrameLineage result :=
  lookup_finish_success ids .Ret s final result valid (fun _ incoming => incoming) run

private theorem reject_success_state (value : Value) (op : String) (s final : MachineState)
    (run : Sem.run (Sem.rejectPartial value op) s = .ok ((), final)) : final = s := by
  cases value <;>
    simp [Sem.rejectPartial, Sem.run, Sem.throwUB, StateT.run, StateT.pure,
      StateT.lift, pure, Except.pure, throw, throwThe, MonadExceptOf.throw,
      bind, Except.bind] at run <;> exact run.symm

theorem cond_transfer_success (condition : ValueId) (yes no : BlockId)
    (yesIds noIds : List ValueId) (s final : MachineState) (result : StepResult)
    (valid : WellMintedState s)
    (run : Sem.run (semCondBr condition yes yesIds no noIds) s = .ok (result, final)) :
    final = s ∧ TransferValues s.nextFrameLineage result := by
  obtain ⟨value, middle, looked, tail⟩ := split_bind_success (Sem.lookupValue condition) _ s final result run
  obtain ⟨_, same⟩ := lookup_success s middle condition value looked
  subst middle
  obtain ⟨unit, middle, checked, tail⟩ := split_bind_success (Sem.rejectPartial value "CondBr") _ s final result tail
  cases unit
  have same := reject_success_state value "CondBr" s middle checked
  subst middle
  cases value with
  | bool bit =>
    cases bit
    · exact br_transfer_success no noIds s final result valid tail
    · exact br_transfer_success yes yesIds s final result valid tail
  | int width integer =>
    cases nonzero : integer != 0 with
    | false => exact br_transfer_success no noIds s final result valid (by simpa [nonzero] using tail)
    | true => exact br_transfer_success yes yesIds s final result valid (by simpa [nonzero] using tail)
  | float _ =>
    simp [Sem.throwTypeError, Sem.run, StateT.run, StateT.lift,
      throw, throwThe, MonadExceptOf.throw, bind, pure, Except.bind, Except.pure] at tail
  | ptr _ _ =>
    simp [Sem.throwTypeError, Sem.run, StateT.run, StateT.lift,
      throw, throwThe, MonadExceptOf.throw, bind, pure, Except.bind, Except.pure] at tail
  | array _ =>
    simp [Sem.throwTypeError, Sem.run, StateT.run, StateT.lift,
      throw, throwThe, MonadExceptOf.throw, bind, pure, Except.bind, Except.pure] at tail
  | aggregate _ =>
    simp [Sem.throwTypeError, Sem.run, StateT.run, StateT.lift,
      throw, throwThe, MonadExceptOf.throw, bind, pure, Except.bind, Except.pure] at tail
  | vector _ =>
    simp [Sem.throwTypeError, Sem.run, StateT.run, StateT.lift,
      throw, throwThe, MonadExceptOf.throw, bind, pure, Except.bind, Except.pure] at tail
  | fnItem _ =>
    simp [Sem.throwTypeError, Sem.run, StateT.run, StateT.lift,
      throw, throwThe, MonadExceptOf.throw, bind, pure, Except.bind, Except.pure] at tail
  | sourceFrame _ _ _ _ =>
    simp [Sem.throwTypeError, Sem.run, StateT.run, StateT.lift,
      throw, throwThe, MonadExceptOf.throw, bind, pure, Except.bind, Except.pure] at tail
  | frame _ _ =>
    simp [Sem.throwTypeError, Sem.run, StateT.run, StateT.lift,
      throw, throwThe, MonadExceptOf.throw, bind, pure, Except.bind, Except.pure] at tail
  | set _ =>
    simp [Sem.throwTypeError, Sem.run, StateT.run, StateT.lift,
      throw, throwThe, MonadExceptOf.throw, bind, pure, Except.bind, Except.pure] at tail
  | sequence _ =>
    simp [Sem.throwTypeError, Sem.run, StateT.run, StateT.lift,
      throw, throwThe, MonadExceptOf.throw, bind, pure, Except.bind, Except.pure] at tail
  | record _ =>
    simp [Sem.throwTypeError, Sem.run, StateT.run, StateT.lift,
      throw, throwThe, MonadExceptOf.throw, bind, pure, Except.bind, Except.pure] at tail
  | closure _ _ =>
    simp [Sem.throwTypeError, Sem.run, StateT.run, StateT.lift,
      throw, throwThe, MonadExceptOf.throw, bind, pure, Except.bind, Except.pure] at tail
  | fnDef _ _ =>
    simp [Sem.throwTypeError, Sem.run, StateT.run, StateT.lift,
      throw, throwThe, MonadExceptOf.throw, bind, pure, Except.bind, Except.pure] at tail
  | typedClosure _ _ _ =>
    simp [Sem.throwTypeError, Sem.run, StateT.run, StateT.lift,
      throw, throwThe, MonadExceptOf.throw, bind, pure, Except.bind, Except.pure] at tail
  | fatPtr _ _ _ =>
    simp [Sem.throwTypeError, Sem.run, StateT.run, StateT.lift,
      throw, throwThe, MonadExceptOf.throw, bind, pure, Except.bind, Except.pure] at tail
  | «partial» _ =>
    simp [Sem.throwTypeError, Sem.run, StateT.run, StateT.lift,
      throw, throwThe, MonadExceptOf.throw, bind, pure, Except.bind, Except.pure] at tail
  | undef _ =>
    simp [Sem.throwTypeError, Sem.run, StateT.run, StateT.lift,
      throw, throwThe, MonadExceptOf.throw, bind, pure, Except.bind, Except.pure] at tail
  | nullPtr  =>
    simp [Sem.throwTypeError, Sem.run, StateT.run, StateT.lift,
      throw, throwThe, MonadExceptOf.throw, bind, pure, Except.bind, Except.pure] at tail
  | uninit  =>
    simp [Sem.throwTypeError, Sem.run, StateT.run, StateT.lift,
      throw, throwThe, MonadExceptOf.throw, bind, pure, Except.bind, Except.pure] at tail

theorem switch_transfer_success (scrutinee : ValueId) (default : BlockId)
    (defaultIds : List ValueId) (cases_ : List SwitchCase)
    (s final : MachineState) (result : StepResult) (valid : WellMintedState s)
    (run : Sem.run (semSwitch scrutinee default defaultIds cases_) s = .ok (result, final)) :
    final = s ∧ TransferValues s.nextFrameLineage result := by
  obtain ⟨value, middle, looked, tail⟩ := split_bind_success (Sem.lookupValue scrutinee) _ s final result run
  obtain ⟨_, same⟩ := lookup_success s middle scrutinee value looked
  subst middle
  obtain ⟨unit, middle, checked, tail⟩ := split_bind_success (Sem.rejectPartial value "Switch") _ s final result tail
  cases unit
  have same := reject_success_state value "Switch" s middle checked
  subst middle
  cases chosen : matchSwitchCase value cases_ with
  | none => exact br_transfer_success default defaultIds s final result valid (by simpa [semBr, chosen] using tail)
  | some selected =>
    cases link : selected.value.hasSymbolAddr with
    | false =>
      exact br_transfer_success selected.target selected.args s final result valid
        (by simpa [semBr, chosen, link] using tail)
    | true =>
      simp [chosen, link, Sem.throwUnsupported, Sem.run, StateT.run, StateT.lift,
        throw, throwThe, MonadExceptOf.throw, bind, pure, Except.bind, Except.pure] at tail

/-- Original ordinary controls, retaining ordered arguments and switch cases. -/
inductive FrameControl : Inst → Type where
  | br (target : BlockId) (args : List ValueId) : FrameControl (.Br target args)
  | cond (condition : ValueId) (yes : BlockId) (yesArgs : List ValueId)
      (no : BlockId) (noArgs : List ValueId) : FrameControl (.CondBr condition yes yesArgs no noArgs)
  | switch (value : ValueId) (target : BlockId) (args : List ValueId)
      (cases_ : List SwitchCase) (exhaustive : Bool) : FrameControl (.Switch value target args cases_ exhaustive)
  | ret (args : List ValueId) : FrameControl (.Return args)
  | unreachable : FrameControl .Unreachable

def FrameControl.action {inst : Inst} : FrameControl inst → Sem StepResult
  | .br target args => semBr target args
  | .cond condition yes yesArgs no noArgs => semCondBr condition yes yesArgs no noArgs
  | .switch value target args cases_ _ => semSwitch value target args cases_
  | .ret args => semReturn args
  | .unreachable => pure .Stuck

theorem FrameControl.stepTerm {inst : Inst} (site : FrameControl inst) (ctx : EvalContext)
    (depth : Nat) (cfg : CFG) (strategy : PanicStrategy) :
    stepTermWithContext ctx depth cfg inst strategy =
      (site.action >>= fun result => pure (.terminator result)) := by
  cases site <;> cases strategy <;> rfl

theorem FrameControl.action_success {inst : Inst} (site : FrameControl inst)
    (s final : MachineState) (result : StepResult) (valid : WellMintedState s)
    (run : Sem.run site.action s = .ok (result, final)) :
    final = s ∧ TransferValues s.nextFrameLineage result := by
  cases site with
  | br target args => exact br_transfer_success target args s final result valid run
  | cond condition yes yesArgs no noArgs => exact cond_transfer_success condition yes no yesArgs noArgs s final result valid run
  | switch value target args cases_ exhaustive => exact switch_transfer_success value target args cases_ s final result valid run
  | ret args => exact return_transfer_success args s final result valid run
  | unreachable =>
    change Except.ok (.Stuck, s) = Except.ok (result, final) at run
    cases run
    exact ⟨rfl, True.intro⟩

theorem FrameControl.term_success {inst : Inst} (site : FrameControl inst)
    (ctx : EvalContext) (depth : Nat) (cfg : CFG) (strategy : PanicStrategy)
    (s final : MachineState) (result : InstrResult) (valid : WellMintedState s)
    (run : Sem.run (stepTermWithContext ctx depth cfg inst strategy) s = .ok (result, final)) :
    ∃ step, result = .terminator step ∧ final = s ∧ TransferValues s.nextFrameLineage step := by
  rw [site.stepTerm] at run
  obtain ⟨step, middle, executed, finished⟩ := split_bind_success _ _ s final result run
  obtain ⟨same, transported⟩ := site.action_success s middle step valid executed
  subst middle
  change Except.ok (.terminator step, s) = Except.ok (result, final) at finished
  have equal := Except.ok.inj finished
  exact ⟨step, (congrArg Prod.fst equal).symm, (congrArg Prod.snd equal).symm, transported⟩

/-- Static grammar of the actual context-resolved CFG, including unreachable
blocks. Bodies use the complete FrameInstruction grammar and ordinary controls.
This is not an admission claim about arbitrary validated programs. -/
def FrameCFG (ctx : EvalContext) (cfg : CFG) : Prop :=
  ∀ pc block, cfg pc = some block →
    (∀ row ∈ bodyInstsWithResultDests (ctx.resolveBlock block).body
      (ctx.resolveBlock block).bodyResultDests, FrameInstruction row.1) ∧
    Nonempty (FrameControl (ctx.resolveBlock block).terminator)

/-- One actual block layer preserves recursive identities, given the same
property of its smaller-fuel ordinary edge continuation. -/
theorem frame_layer_success (recurse : Recurse) (ctx : EvalContext) (depth : Nat)
    (cfg : CFG) (pc : BlockId) (args : List Value) (strategy : PanicStrategy)
    (s final : MachineState) (values : List Value) (grammar : FrameCFG ctx cfg)
    (valid : WellMintedState s) (incoming : MintedArgs s.nextFrameLineage args)
    (continuation : ∀ next nextArgs before after returned,
      WellMintedState before → MintedArgs before.nextFrameLineage nextArgs →
      Sem.run (recurse ctx depth cfg next nextArgs strategy) before = .ok (returned, after) →
      WellMintedState after ∧ MintedArgs after.nextFrameLineage returned)
    (run : Sem.run (evalLayer recurse ctx depth cfg pc args strategy) s = .ok (values, final)) :
    WellMintedState final ∧ MintedArgs final.nextFrameLineage values := by
  cases found : cfg pc with
  | none =>
    simp [evalLayer, found, Sem.throwTypeError, Sem.run, StateT.run, StateT.lift,
      throw, throwThe, MonadExceptOf.throw, bind, pure, Except.bind, Except.pure] at run
  | some block =>
    obtain ⟨sites, ⟨control⟩⟩ := grammar pc block found
    simp only [evalLayer, found] at run
    obtain ⟨unit, checkedState, checked, run⟩ := split_bind_success _ _ s final values run
    have same := memory_check_success_state _ s checkedState unit checked
    subst checkedState
    cases unit
    obtain ⟨unit, bound, params, tail⟩ := split_bind_success _ _ s final values run
    cases unit
    have boundValid := WellMintedState.checked_params_success _ args s bound valid incoming params
    obtain ⟨unit, afterBody, body, tail⟩ := split_bind_success _ _ bound final values tail
    cases unit
    have bodyValid := WellMintedState.frame_body_list_success recurse ctx depth strategy _ bound afterBody sites boundValid body
    obtain ⟨result, afterTerm, term, tail⟩ := split_bind_success _ _ afterBody final values tail
    obtain ⟨step, shape, same, transported⟩ := control.term_success ctx depth cfg strategy afterBody afterTerm result bodyValid term
    subst result
    subst afterTerm
    cases step with
    | Continue next nextArgs => exact continuation next nextArgs afterBody final values bodyValid transported tail
    | Ret returned =>
      change Sem.run (GenericCoro.checkedReturn ctx returned) afterBody = .ok (values,final) at tail
      obtain ⟨same, equal⟩ := checked_return_success ctx returned values afterBody final tail
      subst final
      subst values
      exact ⟨bodyValid, transported⟩
    | Stuck =>
      change Except.error (SemError.ub "reached unreachable") = Except.ok (values, final) at tail
      contradiction
    | CallReq _ _ => cases transported
    | CallIndirectReq _ _ _ => cases transported
    | InvokeReq _ _ _ _ _ => cases transported
    | InvokeIndirectReq _ _ _ _ _ _ => cases transported
    | SeqMapReq _ _ => cases transported

/-- Partial correctness for the ORIGINAL fuel-bounded evaluator: every
successful run of a frame CFG preserves recursive identity well-formedness
and returns only recursively valid values. No sufficient-fuel assumption or
replacement interpreter is introduced. -/
theorem WellMintedState.frame_cfg_success (ctx : EvalContext) (cfg : CFG)
    (grammar : FrameCFG ctx cfg) (fuel depth : Nat) (pc : BlockId) (args : List Value)
    (strategy : PanicStrategy) (s final : MachineState) (values : List Value)
    (valid : WellMintedState s) (incoming : MintedArgs s.nextFrameLineage args)
    (run : Sem.run (stepNWithContext ctx fuel depth cfg pc args strategy) s = .ok (values, final)) :
    WellMintedState final ∧ MintedArgs final.nextFrameLineage values := by
  induction fuel generalizing pc args s final values with
  | zero =>
    simp [stepNWithContext, Sem.run, StateT.run, StateT.lift,
      throw, throwThe, MonadExceptOf.throw, bind, pure, Except.bind, Except.pure] at run
  | succ fuel ih =>
    rw [stepNWithContext_succ_layer] at run
    exact frame_layer_success _ ctx depth cfg pc args strategy s final values grammar valid incoming
      (fun next nextArgs before after returned valid incoming executed =>
        ih next nextArgs before after returned valid incoming executed) run

private def transferExampleDefinition : BindingFrameDef := ⟨⟨0⟩, "transfer", [⟨"x", .I32⟩]⟩

/-- Two actual blocks transport the old and updated snapshots independently,
then close both aliases through the old snapshot in the successor block. -/
def transferExampleCFG : CFG := fun pc =>
  if pc == ⟨0⟩ then some {
    params := [(⟨5⟩, .I32)]
    body := [.OpenFrame transferExampleDefinition, .BindSlot ⟨10⟩ 0 ⟨5⟩]
    bodyResultDests := [[⟨10⟩], [⟨11⟩]]
    terminator := .Br ⟨1⟩ [⟨10⟩, ⟨11⟩] }
  else if pc == ⟨1⟩ then some {
    params := [(⟨20⟩, .Ptr), (⟨21⟩, .Ptr)]
    body := [.LoadSlot ⟨21⟩ 0 .I32, .CloseFrame ⟨20⟩]
    bodyResultDests := [[⟨42⟩], []]
    terminator := .Return [⟨42⟩, ⟨20⟩, ⟨21⟩] }
  else none

theorem transfer_example_grammar (ctx : EvalContext) : FrameCFG ctx transferExampleCFG := by
  intro pc block found
  by_cases first : pc = ⟨0⟩
  · subst pc
    simp [transferExampleCFG] at found
    cases found
    constructor
    · intro row member
      change row ∈ [(.OpenFrame transferExampleDefinition, [⟨10⟩]),
        (.BindSlot ⟨10⟩ 0 ⟨5⟩, [⟨11⟩])] at member
      simp at member
      rcases member with rfl | rfl
      · exact .open _
      · exact .bind _ _ _
    · exact ⟨.br ⟨1⟩ [⟨10⟩, ⟨11⟩]⟩
  · by_cases second : pc = ⟨1⟩
    · subst pc
      simp [transferExampleCFG] at found
      cases found
      constructor
      · intro row member
        change row ∈ [(.LoadSlot ⟨21⟩ 0 .I32, [⟨42⟩]), (.CloseFrame ⟨20⟩, [])] at member
        simp at member
        rcases member with rfl | rfl
        · exact .load _ _ _
        · exact .close _
      · exact ⟨.ret [⟨42⟩, ⟨20⟩, ⟨21⟩]⟩
    · simp [transferExampleCFG, first, second] at found

/-- Entry arguments are a real well-formed-input premise: actual checked
parameter publication can introduce an externally forged unminted identity. -/
theorem incoming_identity_premise_needed :
    let final := { MachineState.empty with
      locals := ValueMap.empty.set ⟨0⟩ (.frame 0 []), nextValueId := 1 }
    Sem.run (bindBlockParamsChecked [(⟨0⟩, .Ptr)] [.frame 0 []]) MachineState.empty = .ok ((), final) ∧
      ¬ WellMintedState final := by
  constructor
  · rfl
  · intro valid
    exact Nat.not_lt_zero 0 (valid.values ⟨0⟩ (.frame 0 []) rfl 0 (.root []))

end TrustIr.FrameLifetime

