-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0
import TrustIr.Proofs.FrameHistoryEffects
import TrustIr.Proofs.FrameTransferValidity

namespace TrustIr.FrameLifetime
open GenericCoro.Prefix HistoryEffects

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

/-- A complete SSA rewrite retains the current history, including arbitrary
publication collisions, result retirement and allocation-cursor changes. -/
theorem ssa_edit_history (locals : MachineState → ValueMap) (cursor : MachineState → Nat) :
    KeepsHistory (do
      let state ← Sem.getState
      Sem.setState { state with locals := locals state, nextValueId := cursor state }) := by
  intro state result run
  cases run
  rfl

theorem result_dests_history (dests : List ValueId) (args : List Value) :
    KeepsHistory (bindResultDests dests args) := by
  unfold bindResultDests
  split
  · exact throw_history _
  · exact ssa_edit_history _ _

theorem result_checks_history (ctx : EvalContext) (inst : Inst) (dests : List ValueId) (values : List Value) :
    KeepsHistory (ctx.checkInstructionResults inst dests values) := by
  intro state result run
  rcases result with ⟨unit,after⟩
  cases unit
  have same := result_checks_success_state ctx inst dests values state after run
  rw [same]


local macro "publication_history" : tactic =>
  `(tactic| with_reducible (repeat' (first
    | exact result_dests_history _ _
    | exact result_checks_history _ _ _ _
    | exact ssa_edit_history _ _
    | exact get_history
    | exact pure_history _
    | exact throw_history _
    | exact throwTypeError_history _
    | exact lookup_history _
    | exact mapM_history Sem.lookupValue _ lookup_history
    | (refine bind_history _ _ ?_ (fun value => ?_) <;> dsimp only)
    | split)))

theorem instruction_dests_history (result : InstrResult) (dests : List ValueId) :
    KeepsHistory (bindInstrResultDests result dests) := by
  unfold bindInstrResultDests
  publication_history

theorem instruction_results_history (ctx : EvalContext) (inst : Inst) (result : InstrResult) (dests : List ValueId) :
    KeepsHistory (ctx.bindInstructionResults inst result dests) := by
  unfold EvalContext.bindInstructionResults
  with_reducible repeat' first
    | exact instruction_dests_history _ _
    | exact result_checks_history _ _ _ _
    | exact lookup_history _
    | exact mapM_history Sem.lookupValue _ lookup_history
    | (refine bind_history _ _ ?_ (fun value => ?_) <;> dsimp only)
    | split

theorem block_params_history (params : List (ValueId × Ty)) (args : List Value) :
    KeepsHistory (bindBlockParams params args) := by
  unfold bindBlockParams
  split
  · exact throw_history _
  · exact ssa_edit_history _ _

theorem checked_params_history (params : List (ValueId × Ty)) (args : List Value) :
    KeepsHistory (bindBlockParamsChecked params args) := by
  unfold bindBlockParamsChecked
  with_reducible repeat' first
    | exact block_params_history _ _
    | exact throw_history _
    | split

private theorem mapped_history {α : Type} (action : Sem α) (encode : α → InstrResult)
    (preserve : ∀ state final value, Sem.run action state = .ok (value,final) → HistoryExtends state final)
    (s final : MachineState) (result : InstrResult)
    (run : Sem.run (action >>= fun value => pure (encode value)) s = .ok (result, final)) : HistoryExtends s final := by
  obtain ⟨value, middle, executed, tail⟩ := split_bind_success _ _ s final result run
  change Except.ok (encode value,middle) = Except.ok (result,final) at tail
  cases tail
  exact preserve s final value executed

private theorem mapped_keep_history {α : Type} (action : Sem α) (encode : α → InstrResult)
    (keep : KeepsHistory action) (s final : MachineState) (result : InstrResult)
    (run : Sem.run (action >>= fun value => pure (encode value)) s = .ok (result, final)) : HistoryExtends s final :=
  (bind_history action _ keep (fun _ => pure_history _)).extends s final result run

/-- Every successful covered instruction extends actual lineage history.
This is independent of the recursive value-validity premise. -/
theorem frame_step_history (ctx : EvalContext) (inst : Inst) (site : FrameInstruction inst)
    (s final : MachineState) (result : InstrResult)
    (run : Sem.run (stepInstWithContext ctx inst) s = .ok (result,final)) : HistoryExtends s final := by
  cases site with
  | «open» definition => exact contextual_open_history ctx definition s final result run
  | close frame => exact contextual_close_history ctx frame s final result run
  | bind frame slot value => exact (contextual_bind_history ctx frame slot value).extends s final result run
  | load frame slot ty => exact (contextual_load_history ctx frame slot ty).extends s final result run
  | unary op ty operand =>
    exact mapped_keep_history (semUnOp op ty operand) (fun id => .value (some id)) (semUnOp_history op ty operand) s final result run
  | overflow op ty left right =>
    exact mapped_keep_history (semOverflow op ty left right) (fun ids => .values [ids.1,ids.2]) (semOverflow_history op ty left right) s final result run
  | cast op srcTy dstTy operand =>
    exact (contextual_cast_history ctx op srcTy dstTy operand).extends s final result run
  | icmp op ty left right =>
    exact mapped_keep_history (semICmpInst op ty left right ctx.byteModel) (fun id => .value (some id)) (semICmpInst_history op ty left right ctx.byteModel) s final result run
  | fcmp op ty left right =>
    exact mapped_keep_history (semFCmpInst op ty left right) (fun id => .value (some id)) (semFCmpInst_history op ty left right) s final result run
  | ptrData ty operand =>
    exact mapped_keep_history (semPtrData ty operand ctx.byteModel) (fun id => .value (some id)) (semPtrData_history ty operand ctx.byteModel) s final result run
  | ptrMetadata ty metadataTy operand =>
    exact mapped_keep_history (semPtrMetadata ty metadataTy operand ctx.byteModel) (fun id => .value (some id)) (semPtrMetadata_history ty metadataTy operand ctx.byteModel) s final result run
  | ptrFromParts ty metadataTy data metadata =>
    exact mapped_keep_history (semPtrFromParts ty metadataTy data metadata ctx.byteModel) (fun id => .value (some id)) (semPtrFromParts_history ty metadataTy data metadata ctx.byteModel) s final result run
  | sequenceAdd ty operand k =>
    exact mapped_keep_history (semSeqMapAddK ty operand k) (fun id => .value (some id)) (semSeqMapAddK_history ty operand k) s final result run
  | sequenceNot ty operand =>
    exact mapped_keep_history (semSeqMapNot ty operand) (fun id => .value (some id)) (semSeqMapNot_history ty operand) s final result run
  | select ty condition yes no => exact (contextual_select_history ctx ty condition yes no).extends s final result run
  | makeAggregate ty variant fields => exact (contextual_aggregate_history ctx ty variant fields).extends s final result run
  | makeClosure cid fn captures => exact (contextual_closure_history ctx cid fn captures).extends s final result run
  | arraySplat ty operand => exact (contextual_splat_history ctx ty operand).extends s final result run
  | extractField ty operand field => exact (contextual_extract_history ctx ty operand field).extends s final result run
  | insertField ty operand field value => exact (contextual_insert_history ctx ty operand value field).extends s final result run
  | binary op ty left right =>
    rw [binary_step_eq] at run
    apply mapped_keep_history (binaryAction op ty left right) (fun id => .value (some id)) ?_ s final result run
    unfold binaryAction
    split
    · exact semBoolBinOpInst_history op left right
    · exact semBinOp_history op ty left right
  | extractElement ty array index =>
    exact mapped_keep_history _ (fun id => .value (some id))
      (semExtractElementUsing_history (ctx.elementIndex index) ty array index (context_elementIndex_history ctx index)) s final result run
  | insertElement ty array index value =>
    exact mapped_keep_history _ (fun id => .value (some id))
      (semInsertElementUsing_history (ctx.elementIndex index) ty array index value (context_elementIndex_history ctx index)) s final result run
  | copy ty operand =>
    exact (bind_history (Sem.lookupValue operand) _ (lookup_history operand) (fun value =>
      bind_history (Sem.bindFresh value) _ (bindFresh_history value) (fun _ => pure_history _))).extends s final result run
  | undef ty =>
    change Sem.run (if isPartialLoadTy ty then (do
      let id ← Sem.bindFresh (.undef ty)
      pure (InstrResult.value (some id))) else Sem.throwUB (nonpartialUndefMessage ty)) s = .ok (result,final) at run
    exact (ite_history _ _ _ (bind_history _ _ (bindFresh_history _) (fun _ => pure_history _)) (throwUB_history _)).extends s final result run
  | null =>
    exact mapped_keep_history (Sem.bindFresh .nullPtr) (fun id => .value (some id)) (bindFresh_history _) s final result run

/-- History extends through the ORIGINAL production body and publication. -/
theorem frame_body_history (recurse : Recurse) (ctx : EvalContext) (depth : Nat)
    (strategy : PanicStrategy) (inst : Inst) (site : FrameInstruction inst)
    (dests : List ValueId) (s final : MachineState) (outcome : ForInStep Unit)
    (valid : WellMintedState s)
    (run : Sem.run (evalBodyStep recurse ctx depth strategy (inst,dests)) s = .ok (outcome,final)) :
    HistoryExtends s final := by
  cases stepped : Sem.run (stepInstWithContext ctx inst) s with
  | error error =>
    rw [frame_body_error recurse ctx depth strategy inst site dests s error stepped] at run
    contradiction
  | ok pair =>
    rcases pair with ⟨result,after⟩
    obtain ⟨shape,_⟩ := valid.frame_step_success ctx inst site s after result stepped
    have first := frame_step_history ctx inst site s after result stepped
    rw [frame_body_computed recurse ctx depth strategy inst site dests s after result shape stepped] at run
    exact first.trans ((bind_history _ _ (instruction_results_history ctx inst result dests)
      (fun _ => pure_history _)).extends after final outcome run)

theorem frame_body_list_history (recurse : Recurse) (ctx : EvalContext) (depth : Nat)
    (strategy : PanicStrategy) (rows : List (Inst × List ValueId)) (s final : MachineState)
    (sites : ∀ row ∈ rows, FrameInstruction row.1) (valid : WellMintedState s)
    (run : Sem.run (evalBody recurse ctx depth strategy rows) s = .ok ((),final)) : HistoryExtends s final := by
  induction rows generalizing s with
  | nil =>
    change Except.ok ((),s) = Except.ok ((),final) at run
    cases run
    exact .refl _
  | cons row rest ih =>
    rw [evalBody_cons] at run
    obtain ⟨outcome,middle,first,tail⟩ := split_bind_success _ _ s final () run
    have history := frame_body_history recurse ctx depth strategy row.1 (sites row (.head rest)) row.2 s middle outcome valid first
    have preserved := valid.frame_body_success recurse ctx depth strategy row.1 (sites row (.head rest)) row.2 s middle outcome first
    exact history.trans (ih middle (fun row member => sites row (.tail _ member)) preserved tail)

theorem frame_layer_history (recurse : Recurse) (ctx : EvalContext) (depth : Nat)
    (cfg : CFG) (pc : BlockId) (args : List Value) (strategy : PanicStrategy)
    (s final : MachineState) (values : List Value) (grammar : FrameCFG ctx cfg)
    (valid : WellMintedState s) (incoming : MintedArgs s.nextFrameLineage args)
    (continuation : ∀ next nextArgs before after returned,
      WellMintedState before → MintedArgs before.nextFrameLineage nextArgs →
      Sem.run (recurse ctx depth cfg next nextArgs strategy) before = .ok (returned,after) → HistoryExtends before after)
    (run : Sem.run (evalLayer recurse ctx depth cfg pc args strategy) s = .ok (values,final)) : HistoryExtends s final := by
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
    have bodyValid := boundValid.frame_body_list_success recurse ctx depth strategy _ bound afterBody sites body
    have bodyHistory := frame_body_list_history recurse ctx depth strategy _ bound afterBody sites boundValid body
    obtain ⟨result,afterTerm,term,tail⟩ := split_bind_success _ _ afterBody final values tail
    obtain ⟨step,shape,same,transported⟩ := control.term_success ctx depth cfg strategy afterBody afterTerm result bodyValid term
    subst result
    subst afterTerm
    cases step with
    | Continue next nextArgs =>
      exact paramsHistory.trans (bodyHistory.trans (continuation next nextArgs afterBody final values bodyValid transported tail))
    | Ret returned =>
      change Sem.run (GenericCoro.checkedReturn ctx returned) afterBody = .ok (values,final) at tail
      obtain ⟨same, equal⟩ := checked_return_success ctx returned values afterBody final tail
      subst final
      subst values
      exact paramsHistory.trans bodyHistory
    | Stuck =>
      change Except.error (SemError.ub "reached unreachable") = Except.ok (values,final) at tail
      contradiction
    | CallReq _ _ => cases transported
    | CallIndirectReq _ _ _ => cases transported
    | InvokeReq _ _ _ _ _ => cases transported
    | InvokeIndirectReq _ _ _ _ _ _ => cases transported
    | SeqMapReq _ _ => cases transported

/-- Original bounded CFG execution never rewinds the lineage counter or revives
an older closed identity. This augments, rather than replaces, value validity. -/
theorem frame_cfg_history (ctx : EvalContext) (cfg : CFG) (grammar : FrameCFG ctx cfg)
    (fuel depth : Nat) (pc : BlockId) (args : List Value) (strategy : PanicStrategy)
    (s final : MachineState) (values : List Value) (valid : WellMintedState s)
    (incoming : MintedArgs s.nextFrameLineage args)
    (run : Sem.run (stepNWithContext ctx fuel depth cfg pc args strategy) s = .ok (values,final)) :
    HistoryExtends s final := by
  induction fuel generalizing pc args s final values with
  | zero =>
    simp [stepNWithContext,Sem.run,StateT.run,StateT.lift,
      throw,throwThe,MonadExceptOf.throw,bind,pure,Except.bind,Except.pure] at run
  | succ fuel ih =>
    rw [stepNWithContext_succ_layer] at run
    exact frame_layer_history _ ctx depth cfg pc args strategy s final values grammar valid incoming
      (fun next nextArgs before after returned valid incoming executed =>
        ih next nextArgs before after returned valid incoming executed) run

/-- A real successful covered callee run suffices to restore a caller's saved
locals at the later identity bound, including closures of caller-owned lineages.
This boundary law does not qualify the complete call/SeqMap dispatch machinery. -/
theorem restore_after_frame_cfg (ctx : EvalContext) (cfg : CFG) (grammar : FrameCFG ctx cfg)
    (fuel depth : Nat) (pc : BlockId) (args : List Value) (strategy : PanicStrategy)
    (caller after : MachineState) (dest : Option ValueId) (values : List Value)
    (valid : WellMintedState caller) (incoming : MintedArgs caller.nextFrameLineage args)
    (run : Sem.run (stepNWithContext ctx fuel depth cfg pc args strategy)
      {caller with locals := ValueMap.empty,nextValueId := 0} = .ok (values,after)) :
    WellMintedState (restoreFrame after (saveFrame caller dest) values) ∧
      HistoryExtends caller (restoreFrame after (saveFrame caller dest) values) := by
  let entered := {caller with locals := ValueMap.empty,nextValueId := 0}
  have enteredValid : WellMintedState entered := ⟨valid.table,values_empty _⟩
  obtain ⟨afterValid,returned⟩ := enteredValid.frame_cfg_success ctx cfg grammar fuel depth pc args strategy entered after values incoming run
  have calleeHistory := frame_cfg_history ctx cfg grammar fuel depth pc args strategy entered after values enteredValid incoming run
  have history := (history_clear_locals caller).trans calleeHistory
  have saved : MintedValues after.nextFrameLineage (saveFrame caller dest).locals :=
    saved_values_history caller after (saveFrame caller dest) valid.values history
  exact ⟨WellMintedState.restore after (saveFrame caller dest) values afterValid.table saved returned,
    history.trans (history_restore after (saveFrame caller dest) values)⟩

end TrustIr.FrameLifetime
