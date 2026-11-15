-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0
import TrustIr.Proofs.FrameBodyExits

namespace TrustIr.FrameLifetime
open GenericCoro GenericCoro.Prefix

set_option maxHeartbeats 2000000

private theorem ok_safe {α : Type} (value : α) : ExceptNoUnwind (.ok value) := by
  intro exception after run
  cases run

private theorem type_safe {α : Type} (message : String) :
    ExceptNoUnwind (.error (.typeError message) : Except SemError α) := by
  intro exception after run
  cases run

private theorem ub_safe {α : Type} (message : String) :
    ExceptNoUnwind (.error (.ub message) : Except SemError α) := by
  intro exception after run
  cases run

private theorem unsupported_safe {α : Type} (feature : UnsupportedFeature) (message : String) :
    ExceptNoUnwind (.error (.unsupported feature message) : Except SemError α) := by
  intro exception after run
  cases run



local macro "pure_leaves" : tactic => `(tactic|
  repeat' first
    | exact ok_safe _
    | exact type_safe _
    | exact ub_safe _
    | exact unsupported_safe _ _
    | exact cast_float_membership_no_unwind _ _
    | exact vector_lane_no_unwind _ _ _
    | exact vector_shape_no_unwind _ _ _
    | (refine ExceptNoUnwind.bind _ _ ?_ (fun input => ?_) <;> try dsimp only)
    | (split <;> try dsimp only))

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 4096 in
theorem aggregate_lane_no_unwind (model : ByteModel) (ty : Ty) (value : Value) :
    ExceptNoUnwind (checkAggregateLane model ty value) := by
  unfold checkAggregateLane
  dsimp only
  by_cases inspected : (value.isPoison || value.isUninit) = true
  · simp (config := { iota := false }) only [inspected,if_true,bind,pure,Except.bind,Except.pure,throw,throwThe,MonadExceptOf.throw]
    exact ub_safe _
  · simp (config := { iota := false }) only [inspected,if_false,bind,pure,Except.bind,Except.pure,throw,throwThe,MonadExceptOf.throw]
    cases value with
    | aggregate lanes =>
      cases lanes <;> cases ty <;> dsimp only
      all_goals pure_leaves
    | _ =>
      cases ty <;> dsimp only
      all_goals pure_leaves

theorem array_register_no_unwind (table : Option LocalTypeTable) (ty : Ty) (id : ValueId) :
    ExceptNoUnwind (checkArrayRegisterType table ty id) := by
  unfold checkArrayRegisterType
  try dsimp only
  pure_leaves

theorem declared_field_type_no_unwind (ctx : EvalContext) (ty : Ty) (held : Value) (field : Nat) :
    ExceptNoUnwind (declaredFieldTy ctx ty held field) := by
  unfold declaredFieldTy
  try dsimp only
  pure_leaves

theorem typed_integer_no_unwind (model : ByteModel) (ty : Ty) (value : Value) :
    ExceptNoUnwind (typedIntegerValue model ty value) := by
  unfold typedIntegerValue
  try dsimp only
  pure_leaves

theorem nonnegative_index_no_unwind (value : Int) :
    ExceptNoUnwind (nonnegativeElementIndex value) := by
  unfold nonnegativeElementIndex
  try dsimp only
  pure_leaves

theorem vector_element_no_unwind (ty : Ty) (value : Value) (index : Nat) :
    ExceptNoUnwind (getVectorElement ty value index) := by
  unfold getVectorElement
  try dsimp only
  pure_leaves

theorem vector_insert_no_unwind (ty : Ty) (value : Value) (index : Nat) (replacement : Value) :
    ExceptNoUnwind (setVectorElement ty value index replacement) := by
  unfold setVectorElement
  try dsimp only
  pure_leaves

local macro "context_validation_leaves" : tactic => `(tactic|
  repeat' first
    | exact aggregate_lane_no_unwind _ _ _
    | exact array_register_no_unwind _ _ _
    | exact declared_field_type_no_unwind _ _ _ _
    | exact typed_integer_no_unwind _ _ _
    | (solve | pure_leaves)
    | (refine ExceptNoUnwind.forM _ _ (fun input => ?_); try rcases input with ⟨left,right⟩; try dsimp only)
    | (refine ExceptNoUnwind.bind _ _ ?_ (fun input => ?_) <;> try dsimp only)
    | (split <;> try dsimp only))

theorem aggregate_value_no_unwind (ctx : EvalContext) (ty : Ty) (variant : Option Nat) (lanes : List Value) :
    ExceptNoUnwind (makeAggregateValueWithContext ctx ty variant lanes) := by
  unfold makeAggregateValueWithContext
  context_validation_leaves

theorem array_value_no_unwind (ctx : EvalContext) (element : TyId) (count : Nat) (variant : Option Nat) (ids : List ValueId) (lanes : List Value) :
    ExceptNoUnwind (makeArrayValueWithContext ctx element count variant ids lanes) := by
  unfold makeArrayValueWithContext
  context_validation_leaves

theorem declared_field_no_unwind (ctx : EvalContext) (id : ValueId) (held : Value) (field : Nat) (ty : Ty) :
    ExceptNoUnwind (checkDeclaredField ctx id held field ty) := by
  unfold checkDeclaredField
  context_validation_leaves

theorem context_integer_no_unwind (ctx : EvalContext) (id : ValueId) (value : Value) :
    ExceptNoUnwind (ctx.integerOperand id value) := by
  unfold EvalContext.integerOperand
  context_validation_leaves

theorem vector_lanes_no_unwind (ty : Ty) (poison : Bool) (values : List Value) :
    ExceptNoUnwind (checkVectorLanes ty poison values) := by
  induction values with
  | nil => exact ok_safe _
  | cons value rest ih => exact ExceptNoUnwind.bind _ _ (vector_lane_no_unwind ty poison value) (fun _ => ih)

theorem select_lanes_no_unwind (mask left right : List Value) :
    ExceptNoUnwind (semVectorSelectLanes mask left right) := by
  induction mask generalizing left right with
  | nil => cases left <;> cases right <;> first | exact ok_safe _ | exact type_safe _
  | cons value rest ih =>
    cases value
    case bool bit =>
      cases bit <;> cases left <;> cases right <;>
        first
          | exact type_safe _
          | exact ExceptNoUnwind.bind _ _ (ih _ _) (fun _ => ok_safe _)
    all_goals cases left <;> cases right <;> exact type_safe _

theorem select_values_no_unwind (ty : Ty) (mask : List Value) (left right : Value) :
    ExceptNoUnwind (semVectorSelectValues ty mask left right) := by
  unfold semVectorSelectValues
  repeat' first
    | exact select_lanes_no_unwind _ _ _
    | exact vector_lanes_no_unwind _ _ _
    | (solve | pure_leaves)
    | (refine ExceptNoUnwind.bind _ _ ?_ (fun input => ?_) <;> try dsimp only)
    | (split <;> try dsimp only)

theorem sequence_add_values_no_unwind (k : Nat) (values : List Value) :
    ExceptNoUnwind (seqMapAddKList k values) := by
  induction values with
  | nil => exact ok_safe _
  | cons value rest ih =>
    cases value
    case int width raw =>
      cases checked : seqMapAddKList k rest with
      | error error =>
        simp only [seqMapAddKList,checked]
        intro exception after run
        cases run
        exact ih exception after checked
      | ok mapped =>
        simp only [seqMapAddKList,checked]
        exact ok_safe _
    all_goals exact type_safe _

theorem sequence_not_values_no_unwind (values : List Value) :
    ExceptNoUnwind (seqMapNotList values) := by
  induction values with
  | nil => exact ok_safe _
  | cons value rest ih =>
    cases value
    case bool bit =>
      cases checked : seqMapNotList rest with
      | error error =>
        simp only [seqMapNotList,checked]
        intro exception after run
        cases run
        exact ih exception after checked
      | ok mapped =>
        simp only [seqMapNotList,checked]
        exact ok_safe _
    all_goals exact type_safe _

end TrustIr.FrameLifetime
