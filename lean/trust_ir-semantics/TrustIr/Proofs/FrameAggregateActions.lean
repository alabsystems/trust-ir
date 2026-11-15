-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0
import TrustIr.Proofs.FrameAggregateChecks

namespace TrustIr.FrameLifetime
open GenericCoro GenericCoro.Prefix NoUnwindEffects

set_option maxHeartbeats 2000000

private theorem lookup_lanes_no_unwind (ids : List ValueId) : CallCheckNoUnwind (lookupLanes ids) := by
  induction ids with
  | nil => exact pure_safe _
  | cons id rest ih =>
    exact CallCheckNoUnwind.bind _ _ (lookup_safe id) (fun value =>
      CallCheckNoUnwind.bind _ _ (reject_safe value "MakeAggregate") (fun _ =>
        CallCheckNoUnwind.bind _ _ ih (fun _ => pure_safe _)))

local macro "checked_value_leaves" : tactic => `(tactic|
  first
    | exact select_values_no_unwind _ _ _ _
    | exact vector_element_no_unwind _ _ _
    | exact vector_insert_no_unwind _ _ _ _
    | exact sequence_add_values_no_unwind _ _
    | exact sequence_not_values_no_unwind _
    | exact aggregate_value_no_unwind _ _ _ _
    | exact array_value_no_unwind _ _ _ _ _ _
    | exact declared_field_no_unwind _ _ _ _ _
    | exact make_closure_no_unwind _ _ _ _
    | exact closure_extract_no_unwind _ _ _ _ _ _
    | exact closure_insert_no_unwind _ _ _ _ _ _ _)

local macro "action_leaves" : tactic => `(tactic|
  repeat' first
    | exact pure_safe _
    | exact type_safe _
    | exact ub_safe _
    | exact unsupported_safe _ _
    | exact fresh_safe _
    | exact lookup_safe _
    | exact lookup_lanes_no_unwind _
    | exact lookup_arguments_no_unwind _
    | exact reject_safe _ _
    | (refine checked_error_safe _ _ (by assumption) ?_; checked_value_leaves)
    | (refine CallCheckNoUnwind.bind _ _ ?_ (fun value => ?_) <;> try dsimp only)
    | (split <;> try dsimp only))

theorem extract_field_action_no_unwind (ty : Ty) (id : ValueId) (field : Nat) :
    CallCheckNoUnwind (semExtractField ty id field) := by
  unfold semExtractField
  action_leaves

theorem insert_field_action_no_unwind (ty : Ty) (id : ValueId) (field : Nat) (value : ValueId) :
    CallCheckNoUnwind (semInsertField ty id field value) := by
  unfold semInsertField
  action_leaves

theorem make_aggregate_action_no_unwind (ty : Ty) (variant : Option Nat) (ids : List ValueId) :
    CallCheckNoUnwind (semMakeAggregate ty variant ids) := by
  unfold semMakeAggregate
  action_leaves

theorem array_splat_action_no_unwind (ty : Ty) (id : ValueId) :
    CallCheckNoUnwind (semArraySplat ty id) := by
  unfold semArraySplat
  action_leaves

theorem sequence_add_action_no_unwind (ty : Ty) (id : ValueId) (k : Nat) :
    CallCheckNoUnwind (semSeqMapAddK ty id k) := by
  unfold semSeqMapAddK
  action_leaves

theorem sequence_not_action_no_unwind (ty : Ty) (id : ValueId) :
    CallCheckNoUnwind (semSeqMapNot ty id) := by
  unfold semSeqMapNot
  action_leaves

theorem context_element_index_no_unwind (ctx : EvalContext) (id : ValueId) (value : Value) :
    CallCheckNoUnwind (ctx.elementIndex id value) := by
  intro state exception after run
  cases checked : ctx.integerOperand id value with
  | error error =>
    simp only [EvalContext.elementIndex,checked,bind,Except.bind] at run
    cases run
    exact context_integer_no_unwind ctx id value exception after checked
  | ok integer =>
    cases indexed : nonnegativeElementIndex integer with
    | error error =>
      simp only [EvalContext.elementIndex,checked,bind,Except.bind,indexed] at run
      cases run
      exact nonnegative_index_no_unwind integer exception after indexed
    | ok index =>
      simp only [EvalContext.elementIndex,checked,bind,Except.bind,indexed] at run
      cases run

theorem extract_element_action_no_unwind (indexOf : Value → Sem Nat) (ty : Ty) (array index : ValueId)
    (indexSafe : ∀ value, CallCheckNoUnwind (indexOf value)) :
    CallCheckNoUnwind (semExtractElementUsing indexOf ty array index) := by
  unfold semExtractElementUsing
  apply CallCheckNoUnwind.bind _ _ (lookup_safe array)
  intro heldArray
  apply CallCheckNoUnwind.bind _ _ (lookup_safe index)
  intro heldIndex
  apply CallCheckNoUnwind.bind _ _ (indexSafe heldIndex)
  intro position
  action_leaves

theorem insert_element_action_no_unwind (indexOf : Value → Sem Nat) (ty : Ty) (array index value : ValueId)
    (indexSafe : ∀ value, CallCheckNoUnwind (indexOf value)) :
    CallCheckNoUnwind (semInsertElementUsing indexOf ty array index value) := by
  unfold semInsertElementUsing
  apply CallCheckNoUnwind.bind _ _ (lookup_safe array)
  intro heldArray
  apply CallCheckNoUnwind.bind _ _ (lookup_safe index)
  intro heldIndex
  apply CallCheckNoUnwind.bind _ _ (lookup_safe value)
  intro heldValue
  apply CallCheckNoUnwind.bind _ _ (indexSafe heldIndex)
  intro position
  action_leaves

private theorem target_address_no_unwind (model : ByteModel) (message : String) (address : Nat) :
    CallCheckNoUnwind (Sem.targetAddress model message address) := by
  cases model with
  | le64 => exact pure_safe _
  | le32 =>
    simp only [Sem.targetAddress]
    split <;> first | exact pure_safe _ | exact ub_safe _

theorem pointer_data_action_no_unwind (ty : Ty) (id : ValueId) (model : ByteModel) :
    CallCheckNoUnwind (semPtrData ty id model) := by
  unfold semPtrData
  repeat' first
    | exact target_address_no_unwind _ _ _
    | (solve | action_leaves)
    | (refine CallCheckNoUnwind.bind _ _ ?_ (fun value => ?_) <;> try dsimp only)
    | (split <;> try dsimp only)

theorem pointer_metadata_action_no_unwind (ty metadataTy : Ty) (id : ValueId) (model : ByteModel) :
    CallCheckNoUnwind (semPtrMetadata ty metadataTy id model) := by
  unfold semPtrMetadata
  repeat' first
    | exact target_address_no_unwind _ _ _
    | (solve | action_leaves)
    | (refine CallCheckNoUnwind.bind _ _ ?_ (fun value => ?_) <;> try dsimp only)
    | (split <;> try dsimp only)

theorem pointer_parts_action_no_unwind (ty metadataTy : Ty) (data metadata : ValueId) (model : ByteModel) :
    CallCheckNoUnwind (semPtrFromParts ty metadataTy data metadata model) := by
  unfold semPtrFromParts
  repeat' first
    | exact target_address_no_unwind _ _ _
    | (solve | action_leaves)
    | (refine CallCheckNoUnwind.bind _ _ ?_ (fun value => ?_) <;> try dsimp only)
    | (split <;> try dsimp only)

private theorem bare_extract_no_unwind (ty : Ty) (id : ValueId) (field : Nat) (model : ByteModel) :
    CallCheckNoUnwind (stepInst (.ExtractField ty id field) model) :=
  CallCheckNoUnwind.bind _ _ (extract_field_action_no_unwind ty id field) (fun _ => pure_safe _)

private theorem bare_insert_no_unwind (ty : Ty) (id value : ValueId) (field : Nat) (model : ByteModel) :
    CallCheckNoUnwind (stepInst (.InsertField ty id field value) model) :=
  CallCheckNoUnwind.bind _ _ (insert_field_action_no_unwind ty id field value) (fun _ => pure_safe _)

private theorem bare_splat_no_unwind (ty : Ty) (id : ValueId) (model : ByteModel) :
    CallCheckNoUnwind (stepInst (.ArraySplat ty id) model) :=
  CallCheckNoUnwind.bind _ _ (array_splat_action_no_unwind ty id) (fun _ => pure_safe _)

local macro "context_leaves" : tactic => `(tactic|
  with_reducible repeat' first
    | exact bare_extract_no_unwind _ _ _ _
    | exact bare_insert_no_unwind _ _ _ _ _
    | exact bare_splat_no_unwind _ _ _
    | exact pure_safe _
    | exact type_safe _
    | exact ub_safe _
    | exact unsupported_safe _ _
    | exact fresh_safe _
    | exact lookup_safe _
    | exact lookup_lanes_no_unwind _
    | exact lookup_arguments_no_unwind _
    | exact reject_safe _ _
    | (refine checked_error_safe _ _ (by assumption) ?_; checked_value_leaves)
    | (refine CallCheckNoUnwind.bind _ _ ?_ (fun value => ?_) <;> try dsimp only)
    | (split <;> try dsimp only))

theorem contextual_extract_no_unwind (ctx : EvalContext) (ty : Ty) (id : ValueId) (field : Nat) :
    CallCheckNoUnwind (stepInstWithContext ctx (.ExtractField ty id field)) := by
  unfold stepInstWithContext
  context_leaves

theorem contextual_insert_no_unwind (ctx : EvalContext) (ty : Ty) (id value : ValueId) (field : Nat) :
    CallCheckNoUnwind (stepInstWithContext ctx (.InsertField ty id field value)) := by
  unfold stepInstWithContext
  context_leaves

theorem contextual_splat_no_unwind (ctx : EvalContext) (ty : Ty) (id : ValueId) :
    CallCheckNoUnwind (stepInstWithContext ctx (.ArraySplat ty id)) := by
  unfold stepInstWithContext
  context_leaves

theorem contextual_closure_no_unwind (ctx : EvalContext) (cid : ClosureTyId) (fn : FuncId) (ids : List ValueId) :
    CallCheckNoUnwind (stepInstWithContext ctx (.MakeClosure cid fn ids)) := by
  unfold stepInstWithContext
  context_leaves

theorem contextual_aggregate_no_unwind (ctx : EvalContext) (ty : Ty) (variant : Option Nat) (ids : List ValueId) :
    CallCheckNoUnwind (stepInstWithContext ctx (.MakeAggregate ty variant ids)) := by
  cases ty <;> unfold stepInstWithContext
  all_goals first
    | exact CallCheckNoUnwind.bind _ _ (make_aggregate_action_no_unwind _ variant ids) (fun _ => pure_safe _)
    | context_leaves

theorem contextual_select_no_unwind (ctx : EvalContext) (ty : Ty) (condition yes no : ValueId) :
    CallCheckNoUnwind (stepInstWithContext ctx (.Select ty condition yes no)) := by
  rw [select_step_eq]
  unfold selectTransport
  action_leaves

end TrustIr.FrameLifetime
