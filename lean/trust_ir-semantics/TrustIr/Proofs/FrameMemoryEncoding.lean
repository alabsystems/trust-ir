-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0
import TrustIr.Proofs.FrameBlockDecoding

namespace TrustIr.FrameLifetime

private theorem encode_float_exit (ty : Ty) (value : Float) :
    DecodeFrameExit (fun _ => True) (encodeFloatAt ty value) := by
  unfold encodeFloatAt
  repeat' first
    | exact True.intro
    | split
    | (dsimp only; split)

private theorem encode_vector_lane_exit (ty : Ty) (value : Value) :
    DecodeFrameExit (fun _ => True) (encodeVectorLane ty value) := by
  unfold encodeVectorLane
  repeat' first
    | (solve | exact True.intro)
    | (solve | exact encode_float_exit _ _)
    | (simp only [Except.bind,pure_bind])
    | (refine DecodeFrameExit.bind (fun _ => True) (fun _ => True) _ _ (encode_float_exit _ _) ?_; intro bytes _)
    | split
    | (dsimp only; split)

private theorem encode_vector_lanes_exit (ty : Ty) (values : List Value) :
    DecodeFrameExit (fun _ => True) (encodeVectorLanes ty values) := by
  induction values with
  | nil => exact True.intro
  | cons head tail ih =>
    rw [encodeVectorLanes]
    apply DecodeFrameExit.bind (fun _ => True) (fun _ => True) _ _ (encode_vector_lane_exit ty head)
    intro first _
    apply DecodeFrameExit.bind (fun _ => True) (fun _ => True) _ _ ih
    intro rest _
    exact True.intro

private theorem encode_scalar_vector_exit (count : Nat) (ty : Ty) (value : Value) :
    DecodeFrameExit (fun _ => True) (encodeScalarVectorAt count ty value) := by
  unfold encodeScalarVectorAt
  repeat' first
    | (solve | exact True.intro)
    | (simp only [Except.bind,pure_bind])
    | (refine DecodeFrameExit.bind (fun _ => True) (fun _ => True) _ _ (encode_vector_lanes_exit _ _) ?_; intro bytes _)
    | split
    | (dsimp only; split)

private theorem encode_value_exit (ty : Ty) (value : Value) :
    DecodeFrameExit (fun _ => True) (encodeValueAt ty value) := by
  unfold encodeValueAt
  repeat' first
    | exact True.intro
    | exact encode_float_exit _ _
    | exact encode_scalar_vector_exit _ _ _
    | split
    | (dsimp only; split)

private theorem encode_typed_model_exit (model : ByteModel) (ty : Ty) (value : Value) :
    DecodeFrameExit (fun _ => True) (encodeTypedAtModel model ty value) := by
  unfold encodeTypedAtModel
  repeat' first
    | exact True.intro
    | exact encode_float_exit _ _
    | exact encode_scalar_vector_exit _ _ _
    | split
    | (dsimp only; split)

private theorem pointer_image_exit (model : ByteModel) (value : Value) :
    DecodeFrameExit (fun _ => True) (checkPointerImageWords model value) := by
  unfold checkPointerImageWords
  repeat' first
    | (solve | exact True.intro)
    | (simp only [Except.bind,pure_bind])
    | split
    | (dsimp only; split)

private theorem encode_memory_exit (model : ByteModel) (ty : Ty) (value : Value) :
    DecodeFrameExit (fun _ => True) (encodeMemoryAt model ty value) := by
  unfold encodeMemoryAt
  apply DecodeFrameExit.bind (fun _ => True) (fun _ => True) _ _ (pointer_image_exit model value)
  intro _ _
  cases model with
  | le64 => exact encode_value_exit ty value
  | le32 => exact encode_typed_model_exit _ ty value

private theorem function_address_exit (model : ByteModel) (order : FunctionAddressOrder) (target : FuncId) :
    DecodeFrameExit (fun _ => True) (functionAddressOf model order target) := by
  unfold functionAddressOf checkedFunctionAddress
  repeat' first
    | (solve | exact True.intro)
    | (simp only [Except.bind,pure_bind])
    | split
    | (dsimp only; split)

/-- Every original scalar/vector/function byte encoder has static errors;
none may inject an arbitrary runtime unwind world. -/
theorem encode_functions_no_unwind (model : ByteModel) (order : FunctionAddressOrder) (ty : Ty) (value : Value) :
    ExceptNoUnwind (encodeMemoryWithFunctions model order ty value) := by
  apply DecodeFrameExit.no_unwind (fun _ => True)
  unfold encodeMemoryWithFunctions
  repeat' first
    | (solve | exact True.intro)
    | (solve | exact encode_memory_exit _ _ _)
    | (simp only [Except.bind,pure_bind])
    | (refine DecodeFrameExit.bind (fun _ => True) (fun _ => True) _ _ (function_address_exit _ _ _) ?_; intro address _)
    | split
    | (dsimp only; split)

end TrustIr.FrameLifetime
