-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0
import TrustIr.Proofs.FrameAggregateActions

namespace TrustIr.FrameLifetime
open GenericCoro GenericCoro.Prefix NoUnwindEffects

/-- Every constructor of the existing ordinary frame instruction grammar
has full contextual primitive safety; no dynamic context-error premise is
needed for this non-calling grammar. -/
theorem FrameInstruction.step_no_unwind {inst : Inst} (site : FrameInstruction inst) (ctx : EvalContext) :
    CallCheckNoUnwind (stepInstWithContext ctx inst) := by
  cases site with
  | «open» definition =>
    exact contextual_open_no_unwind ctx definition
  | bind frame slot value =>
    exact contextual_bind_no_unwind ctx frame slot value
  | load frame slot ty =>
    exact contextual_load_no_unwind ctx frame slot ty
  | close frame =>
    exact contextual_close_no_unwind ctx frame
  | unary op ty operand =>
    exact CallCheckNoUnwind.bind _ _ (unary_action_no_unwind op ty operand) (fun _ => pure_safe _)
  | icmp op ty left right =>
    exact CallCheckNoUnwind.bind _ _ (integer_compare_action_no_unwind op ty left right ctx.byteModel) (fun _ => pure_safe _)
  | fcmp op ty left right =>
    exact CallCheckNoUnwind.bind _ _ (float_compare_action_no_unwind op ty left right) (fun _ => pure_safe _)
  | cast op srcTy dstTy operand =>
    exact contextual_cast_no_unwind ctx op srcTy dstTy operand
  | overflow op ty left right =>
    exact CallCheckNoUnwind.bind _ _ (overflow_action_no_unwind op ty left right) (fun _ => pure_safe _)
  | ptrData ty operand =>
    exact CallCheckNoUnwind.bind _ _ (pointer_data_action_no_unwind ty operand ctx.byteModel) (fun _ => pure_safe _)
  | ptrMetadata ty metadataTy operand =>
    exact CallCheckNoUnwind.bind _ _ (pointer_metadata_action_no_unwind ty metadataTy operand ctx.byteModel) (fun _ => pure_safe _)
  | ptrFromParts ty metadataTy data metadata =>
    exact CallCheckNoUnwind.bind _ _ (pointer_parts_action_no_unwind ty metadataTy data metadata ctx.byteModel) (fun _ => pure_safe _)
  | sequenceAdd ty operand k =>
    exact CallCheckNoUnwind.bind _ _ (sequence_add_action_no_unwind ty operand k) (fun _ => pure_safe _)
  | sequenceNot ty operand =>
    exact CallCheckNoUnwind.bind _ _ (sequence_not_action_no_unwind ty operand) (fun _ => pure_safe _)
  | binary op ty left right =>
    rw [binary_step_eq]
    apply CallCheckNoUnwind.bind
    · unfold binaryAction
      split
      · exact boolean_action_no_unwind op left right
      · exact binary_action_no_unwind op ty left right
    · intro _
      exact pure_safe _
  | select ty condition yes no => exact contextual_select_no_unwind ctx ty condition yes no
  | makeAggregate ty variant ids => exact contextual_aggregate_no_unwind ctx ty variant ids
  | makeClosure cid fn ids => exact contextual_closure_no_unwind ctx cid fn ids
  | arraySplat ty operand => exact contextual_splat_no_unwind ctx ty operand
  | extractField ty operand field => exact contextual_extract_no_unwind ctx ty operand field
  | insertField ty operand field value => exact contextual_insert_no_unwind ctx ty operand value field
  | extractElement ty array index =>
    exact CallCheckNoUnwind.bind _ _ (extract_element_action_no_unwind (ctx.elementIndex index) ty array index
      (context_element_index_no_unwind ctx index)) (fun _ => pure_safe _)
  | insertElement ty array index value =>
    exact CallCheckNoUnwind.bind _ _ (insert_element_action_no_unwind (ctx.elementIndex index) ty array index value
      (context_element_index_no_unwind ctx index)) (fun _ => pure_safe _)
  | copy ty operand =>
    exact CallCheckNoUnwind.bind _ _ (lookup_safe operand) (fun value =>
      CallCheckNoUnwind.bind _ _ (fresh_safe value) (fun _ => pure_safe _))
  | undef ty =>
    change CallCheckNoUnwind (if isPartialLoadTy ty then (do
      let id ← Sem.bindFresh (.undef ty)
      pure (InstrResult.value (some id))) else Sem.throwUB (nonpartialUndefMessage ty))
    split
    · exact CallCheckNoUnwind.bind _ _ (fresh_safe _) (fun _ => pure_safe _)
    · exact ub_safe _
  | null => exact CallCheckNoUnwind.bind _ _ (fresh_safe .nullPtr) (fun _ => pure_safe _)

/-- Full contextual ordinary instruction exits, with actual state and history. -/
theorem FrameInstruction.step_frame_exit {inst : Inst} (site : FrameInstruction inst) (ctx : EvalContext) :
    FrameActionValid (fun _ result => BodyValueResult result) (stepInstWithContext ctx inst) :=
  frame_step_exit_of_no_unwind ctx inst site (site.step_no_unwind ctx)

theorem FrameInstruction.body_frame_exit {inst : Inst} (site : FrameInstruction inst)
    (recurse : Recurse) (ctx : EvalContext) (depth : Nat) (strategy : PanicStrategy) (dests : List ValueId) :
    FrameActionValid (fun _ _ => True) (evalBodyStep recurse ctx depth strategy (inst,dests)) :=
  frame_body_exit_of_no_unwind recurse ctx depth strategy inst site dests (site.step_no_unwind ctx)

theorem frame_ordinary_body_list_exit (recurse : Recurse) (ctx : EvalContext) (depth : Nat)
    (strategy : PanicStrategy) (rows : List (Inst × List ValueId))
    (sites : ∀ row ∈ rows, FrameInstruction row.1) :
    FrameActionValid (fun _ _ => True) (evalBody recurse ctx depth strategy rows) :=
  frame_body_list_exit recurse ctx depth strategy rows
    (fun row member => (sites row member).body_frame_exit recurse ctx depth strategy row.2)

/-- Full call-site exit contract; it constrains actual embedded unwind states,
not just normally returning executions. CFG induction supplies this premise. -/
def FrameCalleeExitContract (recurse : Recurse) (ctx : EvalContext) (strategy : PanicStrategy) : Prop :=
  ∀ id callee, ctx.functions id = some callee → ∀ childDepth args before,
    WellMintedState before → MintedArgs before.nextFrameLineage args →
    FrameCalleeExit before (Sem.run (recurse (ctx.forFunction callee) childDepth callee.cfg callee.entryBlock args strategy) before)

theorem DirectFrameInstruction.body_frame_exit {inst : Inst} (site : DirectFrameInstruction inst)
    (recurse : Recurse) (ctx : EvalContext) (depth : Nat) (strategy : PanicStrategy) (dests : List ValueId)
    (callees : FrameCalleeExitContract recurse ctx strategy) :
    FrameActionValid (fun _ _ => True) (evalBodyStep recurse ctx depth strategy (inst,dests)) := by
  cases site with
  | value site => exact site.body_frame_exit recurse ctx depth strategy dests
  | call id args =>
    intro state valid
    exact direct_body_call_exit recurse ctx depth strategy id args dests state valid (callees id)

theorem CallFrameInstruction.body_frame_exit {inst : Inst} (site : CallFrameInstruction inst)
    (recurse : Recurse) (ctx : EvalContext) (safe : StaticFunctionErrors ctx) (depth : Nat)
    (strategy : PanicStrategy) (dests : List ValueId) (callees : FrameCalleeExitContract recurse ctx strategy) :
    FrameActionValid (fun _ _ => True) (evalBodyStep recurse ctx depth strategy (inst,dests)) := by
  cases site with
  | direct site => exact site.body_frame_exit recurse ctx depth strategy dests callees
  | indirect callee sig args conv =>
    intro state valid
    exact indirect_body_call_exit recurse ctx safe depth strategy callee sig args conv dests state valid callees

theorem frame_call_body_list_exit (recurse : Recurse) (ctx : EvalContext) (safe : StaticFunctionErrors ctx)
    (depth : Nat) (strategy : PanicStrategy) (rows : List (Inst × List ValueId))
    (sites : ∀ row ∈ rows, CallFrameInstruction row.1) (callees : FrameCalleeExitContract recurse ctx strategy) :
    FrameActionValid (fun _ _ => True) (evalBody recurse ctx depth strategy rows) :=
  frame_body_list_exit recurse ctx depth strategy rows
    (fun row member => (sites row member).body_frame_exit recurse ctx safe depth strategy row.2 callees)

end TrustIr.FrameLifetime
