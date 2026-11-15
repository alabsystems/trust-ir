-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0
import TrustIr.Basic

namespace TrustIr.TargetWidthDefinition

-- Exact pre-consolidation definitions, retained only as proof references.
def legacyWidth : Ty -> Option Nat
  | .Bool     => some 1
  | .I8       => some 8
  | .I16      => some 16
  | .I32      => some 32
  | .I64      => some 64
  | .I128     => some 128
  -- Issue #53: unsigned integer widths match their signed counterparts.
  | .U8       => some 8
  | .U16      => some 16
  | .U32      => some 32
  | .U64      => some 64
  | .U128     => some 128
  -- v25: pointer-width integers at the model's 64-bit pin; char is 32-bit.
  | .Isize    => some 64
  | .Usize    => some 64
  | .Char     => some 32
  | .F16      => some 16
  | .F32      => some 32
  | .F64      => some 64
  | .Vector lanes elemTy =>
    match legacyWidth elemTy with
    | some elemWidth => some (lanes * elemWidth)
    | none => none
  | .Ptr      => some 64
  -- Pointer-like types are 64-bit
  | .Ref _    => some 64
  | .RefMut _ => some 64
  | .PtrConst _ => some 64
  | .PtrMut _ => some 64
  | .Rc _     => some 64
  -- v43: a handle is exactly one pointer word at the model's 64-bit pin
  -- (mirrors Rust `bit_width_with(64)`; context-free `bit_width` is `None`).
  | .Handle _ _ => some 64
  -- Zero-sized and compound types have no fixed bit width
  | _         => none

def legacyModelWidth (model : ByteModel) : Ty → Option Nat
  | .Isize | .Usize | .Ptr | .Ref _ | .RefMut _ | .PtrConst _ | .PtrMut _ | .Rc _
  | .Handle _ _ => some model.pointerBits
  | .Vector lanes elem => (legacyModelWidth model elem).map (lanes * ·)
  | ty => legacyWidth ty


theorem default_unchanged (ty : Ty) : ty.bitWidth = legacyWidth ty := by
  cases ty <;> simp only [Ty.bitWidth,Ty.bitWidthAtPointerBits,legacyWidth]
  case Vector lanes elem =>
    rw [show elem.bitWidthAtPointerBits 64 = legacyWidth elem from default_unchanged elem]
    cases legacyWidth elem <;> rfl
termination_by sizeOf ty

theorem model_unchanged (model : ByteModel) (ty : Ty) : ty.bitWidthAtModel model = legacyModelWidth model ty := by
  cases ty <;> simp only [Ty.bitWidthAtModel,Ty.bitWidthAtPointerBits,legacyModelWidth,legacyWidth]
  case Vector lanes elem =>
    rw [show elem.bitWidthAtPointerBits model.pointerBits = legacyModelWidth model elem from model_unchanged model elem]
termination_by sizeOf ty

theorem query_unchanged (model : ByteModel) (ty : Ty) :
    ty.bitWidthFor model = (match model with
      | .le64 => legacyWidth ty
      | .le32 => legacyModelWidth .le32 ty) := by
  cases model with
  | le32 => exact model_unchanged .le32 ty
  | le64 => exact default_unchanged ty

end TrustIr.TargetWidthDefinition
