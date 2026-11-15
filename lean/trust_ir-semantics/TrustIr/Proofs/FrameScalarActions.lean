-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0
import TrustIr.Proofs.FrameScalarExits

namespace TrustIr.FrameLifetime
open GenericCoro GenericCoro.Prefix

set_option maxHeartbeats 2000000

namespace NoUnwindEffects

theorem pure_safe {α : Type} (value : α) : CallCheckNoUnwind (pure value : Sem α) := by
  intro state exception after run
  cases run

theorem type_safe {α : Type} (message : String) : CallCheckNoUnwind (Sem.throwTypeError message : Sem α) := by
  intro state exception after run
  cases run

theorem ub_safe {α : Type} (message : String) : CallCheckNoUnwind (Sem.throwUB message : Sem α) := by
  intro state exception after run
  cases run

theorem unsupported_safe {α : Type} (feature : UnsupportedFeature) (message : String) :
    CallCheckNoUnwind (Sem.throwUnsupported feature message : Sem α) := by
  intro state exception after run
  cases run

theorem get_safe : CallCheckNoUnwind Sem.getState := by
  intro state exception after run
  cases run

theorem fresh_safe (value : Value) : CallCheckNoUnwind (Sem.bindFresh value) := by
  intro state exception after run
  cases run

theorem pair_safe (left right : Value) : CallCheckNoUnwind (Sem.bindFreshPair left right) := by
  exact CallCheckNoUnwind.bind _ _ (fresh_safe left) (fun _ =>
    CallCheckNoUnwind.bind _ _ (fresh_safe right) (fun _ => pure_safe _))

theorem lookup_safe (id : ValueId) : CallCheckNoUnwind (Sem.lookupValue id) := by
  intro state exception after run
  cases found : state.lookupValue id <;>
    simp [Sem.lookupValue,Sem.run,Sem.getState,found,Sem.throwTypeError,StateT.run,StateT.bind,
      StateT.get,StateT.pure,StateT.lift,bind,pure,Except.bind,Except.pure,throw,throwThe,MonadExceptOf.throw] at run

theorem reject_safe (value : Value) (message : String) : CallCheckNoUnwind (Sem.rejectPartial value message) := by
  cases value <;> first | exact pure_safe _ | exact ub_safe _

theorem choice_safe : CallCheckNoUnwind Sem.nextFloatZeroChoice := by
  intro state exception after run
  cases run

theorem checked_safe {α β : Type} (result : Except SemError α) (next : α → Sem β)
    (safe : ExceptNoUnwind result) (rest : ∀ value, CallCheckNoUnwind (next value)) :
    CallCheckNoUnwind (match result with | .ok value => next value | .error error => throw error) := by
  cases result with
  | ok value => exact rest value
  | error error =>
    intro state exception after run
    cases run
    exact safe exception after rfl

theorem checked_error_safe {α β : Type} (result : Except SemError α) (error : SemError)
    (failed : result = .error error) (safe : ExceptNoUnwind result) : CallCheckNoUnwind (throw error : Sem β) := by
  intro state exception after run
  cases run
  exact safe exception after failed

end NoUnwindEffects
open NoUnwindEffects

local macro "value_safety" : tactic => `(tactic|
  first
    | exact unary_value_no_unwind _ _ _
    | exact binary_values_no_unwind _ _ _ _
    | exact boolean_values_no_unwind _ _ _
    | exact overflow_value_no_unwind _ _ _ _ _
    | exact integer_compare_values_no_unwind _ _ _ _ _
    | exact float_compare_values_no_unwind _ _ _ _
    | exact minmax_candidates_no_unwind _ _ _ _)

local macro "action_leaves" : tactic => `(tactic|
  repeat' first
    | exact pure_safe _
    | exact type_safe _
    | exact ub_safe _
    | exact unsupported_safe _ _
    | exact fresh_safe _
    | exact pair_safe _ _
    | exact lookup_safe _
    | exact reject_safe _ _
    | exact choice_safe
    | (refine checked_error_safe _ _ (by assumption) ?_; value_safety)
    | (refine checked_safe _ _ ?_ (fun value => ?_) <;> first | value_safety | skip)
    | exact unary_value_no_unwind _ _ _
    | exact binary_values_no_unwind _ _ _ _
    | exact boolean_values_no_unwind _ _ _
    | exact overflow_value_no_unwind _ _ _ _ _
    | exact integer_compare_values_no_unwind _ _ _ _ _
    | exact float_compare_values_no_unwind _ _ _ _
    | exact minmax_candidates_no_unwind _ _ _ _
    | (refine CallCheckNoUnwind.bind _ _ ?_ (fun value => ?_) <;> try dsimp only)
    | (split <;> try dsimp only))

theorem unary_action_no_unwind (op : UnOp) (ty : Ty) (id : ValueId) : CallCheckNoUnwind (semUnOp op ty id) := by
  unfold semUnOp
  action_leaves

theorem binary_deterministic_no_unwind (op : BinOp) (ty : Ty) (left right : ValueId) :
    CallCheckNoUnwind (semBinOpDeterministic op ty left right) := by
  unfold semBinOpDeterministic
  action_leaves

theorem boolean_action_no_unwind (op : BinOp) (left right : ValueId) :
    CallCheckNoUnwind (semBoolBinOpInst op left right) := by
  unfold semBoolBinOpInst
  action_leaves

theorem overflow_action_no_unwind (op : OverflowOp) (ty : Ty) (left right : ValueId) :
    CallCheckNoUnwind (semOverflow op ty left right) := by
  unfold semOverflow
  action_leaves

theorem integer_compare_action_no_unwind (op : ICmpOp) (ty : Ty) (left right : ValueId) (model : ByteModel) :
    CallCheckNoUnwind (semICmpInst op ty left right model) := by
  unfold semICmpInst
  action_leaves

theorem float_compare_action_no_unwind (op : FCmpOp) (ty : Ty) (left right : ValueId) :
    CallCheckNoUnwind (semFCmpInst op ty left right) := by
  unfold semFCmpInst
  action_leaves

theorem minmax_action_no_unwind (op : BinOp) (ty : Ty) (left right : Float) :
    CallCheckNoUnwind (semFloatMinMaxAt op ty left right) := by
  unfold semFloatMinMaxAt
  action_leaves

theorem minmax_scalar_no_unwind (op : BinOp) (ty : Ty) (left right : Value) :
    CallCheckNoUnwind (semFloatMinMaxScalarValue op ty left right) := by
  unfold semFloatMinMaxScalarValue
  repeat' first
    | exact minmax_action_no_unwind _ _ _ _
    | (solve | action_leaves)
    | (refine CallCheckNoUnwind.bind _ _ ?_ (fun value => ?_) <;> try dsimp only)
    | (split <;> try dsimp only)

theorem minmax_lanes_no_unwind (op : BinOp) (ty : Ty) (left right : List Value) :
    CallCheckNoUnwind (semFloatMinMaxLanes op ty left right) := by
  induction left generalizing right with
  | nil => cases right <;> first | exact pure_safe _ | exact type_safe _
  | cons first rest ih =>
    cases right with
    | nil => exact type_safe _
    | cons other others =>
      exact CallCheckNoUnwind.bind _ _ (minmax_scalar_no_unwind op ty first other) (fun _ =>
        CallCheckNoUnwind.bind _ _ (ih others) (fun _ => pure_safe _))

theorem minmax_values_no_unwind (op : BinOp) (ty : Ty) (left right : Value) :
    CallCheckNoUnwind (semFloatMinMaxValues op ty left right) := by
  unfold semFloatMinMaxValues
  repeat' first
    | exact minmax_scalar_no_unwind _ _ _ _
    | exact minmax_lanes_no_unwind _ _ _ _
    | (solve | action_leaves)
    | (refine CallCheckNoUnwind.bind _ _ ?_ (fun value => ?_) <;> try dsimp only)
    | (split <;> try dsimp only)

theorem binary_action_no_unwind (op : BinOp) (ty : Ty) (left right : ValueId) :
    CallCheckNoUnwind (semBinOp op ty left right) := by
  unfold semBinOp
  split
  · unfold semFloatMinMax
    exact CallCheckNoUnwind.bind _ _ (lookup_safe left) (fun lhs =>
      CallCheckNoUnwind.bind _ _ (lookup_safe right) (fun rhs =>
        CallCheckNoUnwind.bind _ _ (minmax_values_no_unwind op ty lhs rhs) fresh_safe))
  · exact binary_deterministic_no_unwind op ty left right

end TrustIr.FrameLifetime
