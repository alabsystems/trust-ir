-- Copyright 2026 Andrew Yates
-- Author: Andrew Yates <andrewyates.name@gmail.com>
-- Licensed under the Apache License, Version 2.0

import TrustIr.Semantics.Eval

namespace TrustIr

set_option smartUnfolding false

theorem exceptSem_pure {α : Type} (value : α) :
    (pure value : Except SemError α) = .ok value := rfl

theorem exceptSem_ok_bind {α β : Type} (value : α) (next : α → Except SemError β) :
    ((Except.ok value : Except SemError α) >>= next) = next value := rfl

/-!
Single-step equations for the total checked constant converters. Explicit
WellFounded.fix_eq proofs avoid Lean 4.8's expensive automatic equations for
their mutually recursive matchers. These equations repeat the actual clauses;
they add no conversion rule or success assumption. Lean 4.30 uses its generated
unfolding equation on the defining side only, keeping recursive calls in the
stated equation intact.
-/

theorem constValueAtChecked_eq (ty : Ty) (c : Constant) (model : ByteModel)
    (allowUninitFields : Bool) : constValueAtChecked ty c model allowUninitFields = (do
  if !constPointerFormsSupported ty c then
    throw (.typeError "constant requires null pointer spellings and matching inline field census")
  match ty, c with
  -- The preceding grammar check proves the exact zero spelling in these
  -- branches; nonzero words and malformed pairs have already been refused.
  | .Ptr, .int _ => pure .nullPtr
  | .FatPtr kind, .aggregate _ => pure (constNullFatPointer kind model)
  | ty, .int i =>
    if ty.isInteger then pure (constValueAt ty (.int i) model)
    else throw (.typeError "integer constant requires an integer declared type")
  | .U128, .u128 value => pure (.int 128 (Int.ofNat value))
  | .Bool, .bool value => pure (.bool value)
  | .F16, .float value => pure (.float (constFloatAt .F16 value))
  | .F32, .float value => pure (.float (constFloatAt .F32 value))
  | .F64, .float value => pure (.float value)
  | .Unit, .phantomData => pure (.aggregate [])
  | .Func signature, .fnDef target => pure (.fnDef signature target)
  | .FnItem _, .fnItem _ =>
    throw (.typeError "FnItem: constant requires an original source function declaration")
  | .Tuple tys, .aggregate cs =>
    if tys.length != cs.length then
      throw (.typeError "tuple constant field count does not match its declared type")
    let fields ← constFieldsAtChecked tys cs model allowUninitFields
    pure (.aggregate fields)
  | .Vector count elemTy, .vector cs =>
    if (vectorScalarByteSize elemTy).isNone then
      throw (.typeError "vector constant requires an admitted scalar lane type")
    if count == 0 || cs.length != count then
      throw (.unsupported .vectorShape "vector constant lane count does not match its declared type")
    let lanes ← constLanesAtChecked elemTy cs model
    pure (.vector lanes)
  | .Array _ count, .bytes data _ =>
    if data.length != count then
      throw (.typeError "bytes constant length does not match its declared array type")
    constMissingDefinition ty c .enumDefTable
      "Const: a bytes constant's U8 element type needs the module's type table"
  | .Array _ count, .array cs | .Array _ count, .aggregate cs =>
    if cs.length != count then
      throw (.typeError "array constant length does not match its declared type")
    constMissingDefinition ty c .enumDefTable
      "Const: an array constant's element type needs the module's type table"
  | .Array _ count, .splat _ actual =>
    if actual != count then
      throw (.typeError "splat constant length does not match its declared array type")
    constMissingDefinition ty c .enumDefTable
      "Const: a splat constant's element type needs the module's type table"
  | .Struct _, .aggregate _ =>
    constMissingDefinition ty c .enumDefTable
      "Const: a struct constant's fields need the module's struct table"
  | .Enum _, .aggregate (.int _ :: _) =>
    constMissingDefinition ty c .enumDefTable
      "Const: an enum constant's fields need the module's enum table"
  | .Sequence _, .sequence _ | .Set _ _, .set _ | .Record _, .record _
  | .Record _, .aggregate _ =>
    constMissingDefinition ty c .enumDefTable
      "Const: named aggregate constants need the module's definition tables"
  | .Closure _, .closure _ _ =>
    constMissingDefinition ty c .closureDefTable
      "Const: a closure constant's captures need the module's closure table"
  | _, _ => throw (.typeError "constant does not match its declared type")
  ) := by
  trustIrCompilerProof {
  conv =>
    lhs
    delta constValueAtChecked constValueAtChecked._mutual
    rw [WellFounded.fix_eq]
  cases ty <;> cases c <;> try rfl
  rename_i id cs
  cases cs with
  | nil => rfl
  | cons head rest => cases head <;> rfl
  } {
    conv =>
      lhs
      unfold constValueAtChecked
    rfl
  }

theorem constFieldsAtChecked_eq (tys : List Ty) (cs : List Constant)
    (model : ByteModel) (allowUninit : Bool) :
    constFieldsAtChecked tys cs model allowUninit = (
  match tys, cs with
  | [], [] => pure []
  | _ :: tys, .uninit :: cs => do
    if !allowUninit then
      throw (.typeError "uninit is only a direct field of an instruction tuple/struct constant")
    let rest ← constFieldsAtChecked tys cs model allowUninit
    pure (.uninit :: rest)
  | ty :: tys, c :: cs => do
    let first ← constValueAtChecked ty c model false
    let rest ← constFieldsAtChecked tys cs model allowUninit
    pure (first :: rest)
  | _, _ => throw (.typeError "constant field count does not match its declared type")
  ) := by
  trustIrCompilerProof {
  conv =>
    lhs
    delta constFieldsAtChecked constValueAtChecked._mutual
    rw [WellFounded.fix_eq]
  cases tys with
  | nil => cases cs <;> rfl
  | cons ty tys =>
    cases cs with
    | nil => rfl
    | cons c cs => cases c <;> rfl
  } {
    conv =>
      lhs
      unfold constFieldsAtChecked
    rfl
  }

theorem constLanesAtChecked_eq (elemTy : Ty) (cs : List Constant) (model : ByteModel) :
    constLanesAtChecked elemTy cs model = (
  match cs with
  | [] => pure []
  | c :: cs => do
    let first ← constValueAtChecked elemTy c model false
    let rest ← constLanesAtChecked elemTy cs model
    pure (first :: rest)
  ) := by
  trustIrCompilerProof {
  conv =>
    lhs
    delta constLanesAtChecked constValueAtChecked._mutual
    rw [WellFounded.fix_eq]
  cases cs <;> rfl
  } {
    conv =>
      lhs
      unfold constLanesAtChecked
    rfl
  }

theorem constValueAtWithDefsIn_int_eq (ctx : ConstantEvalContext) (ty : Ty) (value : Int)
    (allowUninitFields : Bool) :
    constValueAtWithDefsIn ctx ty (.int value) allowUninitFields = (do
      if !constPointerFormsSupported ty (.int value) then
        throw (.typeError "constant requires null pointer spellings and matching inline field census")
      match ty with
      | .FnItem _ => throw (.typeError "FnItem: constant and nominal type must have the same identity")
      | _ => constValueAtChecked ty (.int value) ctx.byteModel allowUninitFields) := by
  trustIrCompilerProof {
  conv =>
    lhs
    delta constValueAtWithDefsIn constValueAtWithDefsIn._mutual
    rw [WellFounded.fix_eq]
  cases ty <;> rfl
  } {
    conv =>
      lhs
      unfold constValueAtWithDefsIn
    cases ty <;> rfl
  }

theorem constValueAtWithDefsIn_splat_eq (ctx : ConstantEvalContext) (element : TyId)
    (count : Nat) (value : Constant) (actual : Nat) (allowUninitFields : Bool) :
    constValueAtWithDefsIn ctx (.Array element count) (.splat value actual) allowUninitFields = (do
      if !constPointerFormsSupported (.Array element count) (.splat value actual) then
        throw (.typeError "constant requires null pointer spellings and matching inline field census")
      if actual != count then
        throw (.typeError "Const: splat constant length does not match the type")
      let elemTy ← match ctx.types element with
        | some t => pure t
        | none => throw (.unsupported .enumDefTable
            "Const: an array constant's element type needs the module's type table")
      let v ← constValueAtWithDefsIn ctx elemTy value false
      pure (.array (CompactArray.Packed.uniform count v))) := by
  trustIrCompilerProof {
  conv =>
    lhs
    delta constValueAtWithDefsIn constValueAtWithDefsIn._mutual
    rw [WellFounded.fix_eq]
  rfl
  } {
    conv =>
      lhs
      unfold constValueAtWithDefsIn
    rfl
  }

end TrustIr
