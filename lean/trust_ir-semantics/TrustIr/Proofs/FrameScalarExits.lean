-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0
import TrustIr.Proofs.FrameIndirectBodyExits

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


private theorem float_safe (ty : Ty) (value : Float) : ExceptNoUnwind (checkFloatAt ty value) := by
  unfold checkFloatAt
  repeat' first | exact ok_safe _ | exact type_safe _ | split

private theorem round_safe (ty : Ty) (value : Float) : ExceptNoUnwind (roundFloatAt ty value) := by
  unfold roundFloatAt
  repeat' first | exact ok_safe _ | exact type_safe _ | split

local macro "pure_leaves" : tactic => `(tactic|
  repeat' first
    | exact ok_safe _
    | exact type_safe _
    | exact ub_safe _
    | exact unsupported_safe _ _
    | exact float_safe _ _
    | exact round_safe _ _
    | (refine ExceptNoUnwind.bind _ _ ?_ (fun input => ?_) <;> try dsimp only)
    | (split <;> try dsimp only))

theorem integer_binary_no_unwind (op : BinOp) (width : Nat) (lhs rhs : Int) :
    ExceptNoUnwind (semIntBinOp op width lhs rhs) := by
  unfold semIntBinOp
  pure_leaves

theorem float_binary_no_unwind (op : BinOp) (lhs rhs : Float) :
    ExceptNoUnwind (semFloatBinOp op lhs rhs) := by
  unfold semFloatBinOp
  pure_leaves

theorem float_binary_at_no_unwind (op : BinOp) (ty : Ty) (lhs rhs : Float) :
    ExceptNoUnwind (semFloatBinOpAt op ty lhs rhs) := by
  unfold semFloatBinOpAt
  repeat' first
    | exact float_binary_no_unwind _ _ _
    | (solve | pure_leaves)
    | (refine ExceptNoUnwind.bind _ _ ?_ (fun input => ?_) <;> try dsimp only)
    | (split <;> try dsimp only)

theorem integer_unary_no_unwind (op : UnOp) (width : Nat) (value : Int) :
    ExceptNoUnwind (semIntUnOp op width value) := by
  unfold semIntUnOp
  pure_leaves

theorem float_unary_no_unwind (op : UnOp) (value : Float) :
    ExceptNoUnwind (semFloatUnOp op value) := by
  unfold semFloatUnOp
  pure_leaves

theorem float_unary_at_no_unwind (op : UnOp) (ty : Ty) (value : Float) :
    ExceptNoUnwind (semFloatUnOpAt op ty value) := by
  unfold semFloatUnOpAt
  repeat' first
    | exact float_unary_no_unwind _ _
    | (solve | pure_leaves)
    | (refine ExceptNoUnwind.bind _ _ ?_ (fun input => ?_) <;> try dsimp only)
    | (split <;> try dsimp only)

theorem vector_shape_no_unwind (count : Nat) (ty : Ty) (values : List Value) :
    ExceptNoUnwind (checkVectorShape count ty values) := by
  unfold checkVectorShape
  pure_leaves

theorem vector_lane_no_unwind (ty : Ty) (poison : Bool) (value : Value) :
    ExceptNoUnwind (checkVectorLaneType ty poison value) := by
  unfold checkVectorLaneType
  pure_leaves

theorem boolean_binary_no_unwind (op : BinOp) (lhs rhs : Bool) :
    ExceptNoUnwind (semBoolBinOp op lhs rhs) := by
  unfold semBoolBinOp
  pure_leaves

theorem overflow_value_no_unwind (op : OverflowOp) (width : Nat) (signed : Bool) (lhs rhs : Int) :
    ExceptNoUnwind (semOverflowOp op width signed lhs rhs) := by
  unfold semOverflowOp
  pure_leaves

local macro "value_leaves" : tactic => `(tactic|
  repeat' first
    | exact integer_binary_no_unwind _ _ _ _
    | exact float_binary_at_no_unwind _ _ _ _
    | exact integer_unary_no_unwind _ _ _
    | exact float_unary_at_no_unwind _ _ _
    | exact vector_shape_no_unwind _ _ _
    | exact vector_lane_no_unwind _ _ _
    | exact boolean_binary_no_unwind _ _ _
    | (solve | pure_leaves)
    | (refine ExceptNoUnwind.bind _ _ ?_ (fun input => ?_) <;> try dsimp only)
    | (split <;> try dsimp only))

theorem vector_unary_lane_no_unwind (op : UnOp) (ty : Ty) (value : Value) :
    ExceptNoUnwind (semVectorUnOpLane op ty value) := by
  unfold semVectorUnOpLane
  value_leaves

theorem vector_binary_lane_no_unwind (op : BinOp) (ty : Ty) (lhs rhs : Value) :
    ExceptNoUnwind (semVectorBinOpLane op ty lhs rhs) := by
  unfold semVectorBinOpLane
  value_leaves

theorem vector_unary_no_unwind (op : UnOp) (ty : Ty) (values : List Value) :
    ExceptNoUnwind (semVectorUnOp op ty values) := by
  induction values with
  | nil => exact ok_safe _
  | cons value rest ih =>
    exact ExceptNoUnwind.bind _ _ (vector_unary_lane_no_unwind op ty value) (fun _ =>
      ExceptNoUnwind.bind _ _ ih (fun _ => ok_safe _))

theorem vector_binary_no_unwind (op : BinOp) (ty : Ty) (lhs rhs : List Value) :
    ExceptNoUnwind (semVectorBinOp op ty lhs rhs) := by
  induction lhs generalizing rhs with
  | nil => cases rhs <;> first | exact ok_safe _ | exact type_safe _
  | cons value rest ih =>
    cases rhs with
    | nil => exact type_safe _
    | cons right rights =>
      exact ExceptNoUnwind.bind _ _ (vector_binary_lane_no_unwind op ty value right) (fun _ =>
        ExceptNoUnwind.bind _ _ (ih rights) (fun _ => ok_safe _))

theorem unary_value_no_unwind (op : UnOp) (ty : Ty) (value : Value) :
    ExceptNoUnwind (semUnOpValue op ty value) := by
  unfold semUnOpValue
  repeat' first
    | exact vector_unary_no_unwind _ _ _
    | (solve | value_leaves)
    | (refine ExceptNoUnwind.bind _ _ ?_ (fun input => ?_) <;> try dsimp only)
    | (split <;> try dsimp only)

theorem binary_values_no_unwind (op : BinOp) (ty : Ty) (lhs rhs : Value) :
    ExceptNoUnwind (semBinOpValues op ty lhs rhs) := by
  unfold semBinOpValues
  repeat' first
    | exact vector_binary_no_unwind _ _ _ _
    | (solve | value_leaves)
    | (refine ExceptNoUnwind.bind _ _ ?_ (fun input => ?_) <;> try dsimp only)
    | (split <;> try dsimp only)

theorem boolean_values_no_unwind (op : BinOp) (lhs rhs : Value) :
    ExceptNoUnwind (semBoolBinOpValues op lhs rhs) := by
  unfold semBoolBinOpValues
  value_leaves

theorem minmax_candidates_no_unwind (op : BinOp) (ty : Ty) (lhs rhs : Float) :
    ExceptNoUnwind (floatMinMaxCandidates op ty lhs rhs) := by
  unfold floatMinMaxCandidates
  pure_leaves


theorem integer_compare_operand_no_unwind (width : Nat) (value : Value) :
    ExceptNoUnwind (icmpIntValue width value) := by
  unfold icmpIntValue
  pure_leaves

theorem boolean_compare_operand_no_unwind (value : Value) : ExceptNoUnwind (icmpBoolValue value) := by
  unfold icmpBoolValue
  pure_leaves

theorem pointer_compare_operand_no_unwind (model : ByteModel) (value : Value) :
    ExceptNoUnwind (pointerComparisonAddress model value) := by
  unfold pointerComparisonAddress
  pure_leaves

theorem vector_integer_compare_no_unwind (op : ICmpOp) (width : Nat) (lhs rhs : List Value) :
    ExceptNoUnwind (semVectorICmp op width lhs rhs) := by
  induction lhs generalizing rhs with
  | nil => cases rhs <;> first | exact ok_safe _ | exact type_safe _
  | cons value rest ih =>
    cases rhs with
    | nil => exact type_safe _
    | cons right rights =>
      exact ExceptNoUnwind.bind _ _ (integer_compare_operand_no_unwind width value) (fun _ =>
        ExceptNoUnwind.bind _ _ (integer_compare_operand_no_unwind width right) (fun _ =>
          ExceptNoUnwind.bind _ _ (ih rights) (fun _ => ok_safe _)))

theorem vector_boolean_compare_no_unwind (op : ICmpOp) (lhs rhs : List Value) :
    ExceptNoUnwind (semVectorBoolICmp op lhs rhs) := by
  induction lhs generalizing rhs with
  | nil => cases rhs <;> first | exact ok_safe _ | exact type_safe _
  | cons value rest ih =>
    cases rhs with
    | nil => exact type_safe _
    | cons right rights =>
      exact ExceptNoUnwind.bind _ _ (boolean_compare_operand_no_unwind value) (fun _ =>
        ExceptNoUnwind.bind _ _ (boolean_compare_operand_no_unwind right) (fun _ =>
          ExceptNoUnwind.bind _ _ (ih rights) (fun _ => ok_safe _)))

theorem vector_float_compare_no_unwind (op : FCmpOp) (ty : Ty) (lhs rhs : List Value) :
    ExceptNoUnwind (semVectorFCmp op ty lhs rhs) := by
  induction lhs generalizing rhs with
  | nil => cases rhs <;> first | exact ok_safe _ | exact type_safe _
  | cons value rest ih =>
    cases rhs with
    | nil => exact type_safe _
    | cons right rights =>
      unfold semVectorFCmp
      repeat' first
        | exact ih rights
        | (solve | value_leaves)
        | (refine ExceptNoUnwind.bind _ _ ?_ (fun input => ?_) <;> try dsimp only)
        | (split <;> try dsimp only)

theorem integer_compare_values_no_unwind (op : ICmpOp) (ty : Ty) (lhs rhs : Value) (model : ByteModel) :
    ExceptNoUnwind (semICmpValues op ty lhs rhs model) := by
  unfold semICmpValues
  repeat' first
    | exact pointer_compare_operand_no_unwind _ _
    | exact integer_compare_operand_no_unwind _ _
    | exact boolean_compare_operand_no_unwind _
    | exact vector_integer_compare_no_unwind _ _ _ _
    | exact vector_boolean_compare_no_unwind _ _ _
    | (solve | pure_leaves)
    | (refine ExceptNoUnwind.bind _ _ ?_ (fun input => ?_) <;> try dsimp only)
    | (split <;> try dsimp only)

theorem float_compare_values_no_unwind (op : FCmpOp) (ty : Ty) (lhs rhs : Value) :
    ExceptNoUnwind (semFCmpValues op ty lhs rhs) := by
  unfold semFCmpValues
  repeat' first
    | exact vector_float_compare_no_unwind _ _ _ _
    | (solve | value_leaves)
    | (refine ExceptNoUnwind.bind _ _ ?_ (fun input => ?_) <;> try dsimp only)
    | (split <;> try dsimp only)

end TrustIr.FrameLifetime
