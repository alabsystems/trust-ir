-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0
import TrustIr.Proofs.ConstantTypingEquations

set_option smartUnfolding false
namespace TrustIr

/-! Single-step equations for the original mutually recursive contextual
constant converters. Each equation unfolds the actual well-founded definition;
these clauses introduce no new conversion rule or success assumption. -/

theorem constValueAtWithDefsIn_eq (ctx : ConstantEvalContext) (ty : Ty) (c : Constant)
    (allowUninitFields : Bool := true) :
    constValueAtWithDefsIn ctx ty c allowUninitFields = ( do
  if !constPointerFormsSupported ty c then
    throw (.typeError "constant requires null pointer spellings and matching inline field census")
  match ty, c with
  | .FnItem expected, .fnItem held =>
    if expected != held then throw (.typeError "FnItem: constant identity differs from type")
    match ctx.functionItems expected with
    | some (.ok _) => pure (.fnItem expected)
    | some (.error message) => throw (.typeError message)
    | none => throw (.typeError "FnItem: original function declaration is absent")
  | .FnItem _, _ | _, .fnItem _ =>
    throw (.typeError "FnItem: constant and nominal type must have the same identity")
  | .Closure cid, .closure fn cs => do
    let d ← match ctx.closures cid with
      | some d => pure d
      | none => throw (.unsupported .closureDefTable "closure definition is absent")
    if d.captures.length != cs.length then
      throw (.typeError "Const: closure capture arity mismatch")
    let captures ← constFieldsAtWithDefsIn ctx d.captures cs
    pure (.typedClosure cid fn captures)
  | _, .closure _ _ => throw (.typeError "Const: closure requires a nominal closure type")
  | .Enum eid, .aggregate cs =>
    match ctx.enums eid with
    | none =>
      throw (.unsupported .enumDefTable
        "Const: an enum constant's lane types need the module's enum table")
    | some d =>
      match cs with
      | .int disc :: fieldCs => do
        let discs ← match enumEffectiveDiscriminants d with
          | some ds => pure ds
          | none => throw (.typeError "Const: enum has no canonical discriminant assignment")
        let repr ← match enumCanonicalTagRepr d with
          | some r => pure r
          | none => throw (.typeError "Const: enum has no canonical tag representation")
        let variantIdx ← match listIndexOf? discs disc with
          | some i => pure i
          | none => throw (.typeError "Const: discriminant names no variant of the enum")
        let variant ← match (trustIrListGet? d.variants variantIdx) with
          | some v => pure v
          | none => throw (.typeError "Const: discriminant names no variant of the enum")
        if variant.fields.length != fieldCs.length then
          throw (.typeError "Const: enum constant payload arity does not match the variant")
        let lanes ← constFieldsAtWithDefsIn ctx variant.fields fieldCs
        -- The variant is found by the discriminant's VALUE (`disc`, an `Int`,
        -- negative for `Less = -1`); the tag LANE holds its residue at the tag
        -- width, the representation every other integer value has.
        pure (.aggregate (Value.intAt repr.bitWidth disc :: lanes))
      | _ => throw (.typeError "Const: an enum constant is `[integer discriminant, fields..]`")
  | .Struct sid, .aggregate cs =>
    match ctx.structs sid with
    | none =>
      throw (.unsupported .enumDefTable
        "Const: a struct constant's lane types need the module's struct table")
    | some d => do
      if d.fields.length != cs.length then
        throw (.typeError "Const: struct constant arity does not match the definition")
      let lanes ← constUninitFieldsAtWithDefsIn ctx (d.fields.map (·.ty)) cs allowUninitFields
      pure (.aggregate lanes)
  | .Tuple tys, .aggregate cs =>
    if tys.length == cs.length then do
      let lanes ← constUninitFieldsAtWithDefsIn ctx tys cs allowUninitFields
      pure (.aggregate lanes)
    else throw (.typeError "Const: tuple constant arity does not match the type")
  | .Array tid n, .bytes data _ => do
    if data.length != n then
      throw (.typeError "Const: bytes constant length does not match the array type")
    let elemTy ← match ctx.types tid with
      | some t => pure t
      | none => throw (.unsupported .enumDefTable
          "Const: a bytes constant's element type needs the module's type table")
    if !(elemTy == .U8) then
      throw (.typeError "Const: bytes constant requires an array of U8")
    pure (.array (CompactArray.Packed.ofArray (data.map (fun byte => .int 8 (Int.ofNat byte.toNat))).toArray))
  | .Array tid n, .array cs | .Array tid n, .aggregate cs => do
    if cs.length != n then
      throw (.typeError "Const: array constant length does not match the type")
    let elemTy ← match ctx.types tid with
      | some t => pure t
      | none => throw (.unsupported .enumDefTable
          "Const: an array constant's element type needs the module's type table")
    let lanes ← constLanesAtWithDefsIn ctx elemTy cs
    pure (.array (CompactArray.Packed.ofArray lanes.toArray))
  | .Sequence tid, .sequence cs => do
    let elemTy ← match ctx.types tid with
      | some t => pure t
      | none => throw (.unsupported .enumDefTable
          "Const: a sequence constant's element type needs the module's type table")
    let lanes ← constLanesAtWithDefsIn ctx elemTy cs
    pure (.sequence lanes)
  | _, .sequence _ => throw (.typeError "Const: sequence requires a sequence type")
  | .Set tid _, .set cs => do
    let elemTy ← match ctx.types tid with
      | some t => pure t
      | none => throw (.unsupported .enumDefTable
          "Const: a set constant's element type needs the module's type table")
    let lanes ← constLanesAtWithDefsIn ctx elemTy cs
    pure (.set lanes)
  | _, .set _ => throw (.typeError "Const: set requires a set type")
  | .Record rid, .aggregate cs => do
    let d ← match ctx.records rid with
      | some d => pure d
      | none => throw (.unsupported .enumDefTable
          "Const: a record constant's field types need the module's record table")
    if d.fields.length != cs.length then
      throw (.typeError "Const: record constant arity does not match the definition")
    let lanes ← constFieldsAtWithDefsIn ctx (d.fields.map (·.ty)) cs
    pure (.record ((d.fields.map (·.name)).zip lanes))
  | .Record rid, .record fs => do
    let d ← match ctx.records rid with
      | some d => pure d
      | none => throw (.unsupported .enumDefTable
          "Const: a record constant's field types need the module's record table")
    if d.fields.length != fs.length then
      throw (.typeError "Const: record constant arity does not match the definition")
    if !constRecordNamesDistinct fs then
      throw (.typeError "Const: record constant repeats a declared field name")
    let fields ← constRecordFieldsAtWithDefsIn ctx d.fields fs
    pure (.record fields)
  | _, .record _ => throw (.typeError "Const: record requires a record type")
  | .Vector count elemTy, .vector cs => do
    if (vectorScalarByteSize elemTy).isNone then
      throw (.typeError "vector constant requires an admitted scalar lane type")
    if count == 0 || cs.length != count then
      throw (.unsupported .vectorShape "vector constant lane count does not match its declared type")
    let lanes ← constLanesAtWithDefsIn ctx elemTy cs
    pure (.vector lanes)
  | .Array tid n, .splat elem count => do
    if count != n then
      throw (.typeError "Const: splat constant length does not match the type")
    let elemTy ← match ctx.types tid with
      | some t => pure t
      | none => throw (.unsupported .enumDefTable
          "Const: an array constant's element type needs the module's type table")
    let v ← constValueAtWithDefsIn ctx elemTy elem false
    pure (.array (CompactArray.Packed.uniform n v))
  | _, _ => constValueAtChecked ty c ctx.byteModel allowUninitFields) := by
  trustIrCompilerProof {
    conv =>
      lhs
      delta constValueAtWithDefsIn constValueAtWithDefsIn._mutual
      rw [WellFounded.fix_eq]
    cases ty <;> cases c <;> try rfl
    all_goals
      rename_i id cs
      cases cs with
      | nil => rfl
      | cons head rest => cases head <;> rfl
  } {
    conv =>
      lhs
      unfold constValueAtWithDefsIn
    rfl
  }

theorem constUninitFieldsAtWithDefsIn_eq (ctx : ConstantEvalContext) (tys : List Ty)
    (cs : List Constant) (allowUninit : Bool) :
    constUninitFieldsAtWithDefsIn ctx tys cs allowUninit = (
  match tys, cs with
  | [], [] => pure []
  | _ :: tys, .uninit :: cs => do
    if !allowUninit then
      throw (.typeError "uninit is only a direct field of an instruction tuple/struct constant")
    let rest ← constUninitFieldsAtWithDefsIn ctx tys cs allowUninit
    pure (.uninit :: rest)
  | ty :: tys, c :: cs => do
    let first ← constValueAtWithDefsIn ctx ty c false
    let rest ← constUninitFieldsAtWithDefsIn ctx tys cs allowUninit
    pure (first :: rest)
  | _, _ => throw (.typeError "Const: field count does not match its declared type")) := by
  trustIrCompilerProof {
    conv =>
      lhs
      delta constUninitFieldsAtWithDefsIn constValueAtWithDefsIn._mutual
      rw [WellFounded.fix_eq]
    cases tys <;> cases cs <;> try rfl
    all_goals rename_i head tail first rest; cases first <;> rfl
  } {
    conv =>
      lhs
      unfold constUninitFieldsAtWithDefsIn
    rfl
  }

theorem constFieldsAtWithDefsIn_eq (ctx : ConstantEvalContext) (tys : List Ty) (cs : List Constant) :
    constFieldsAtWithDefsIn ctx tys cs = (
  match tys, cs with
  | t :: ts, c :: cs => do
    let v ← constValueAtWithDefsIn ctx t c false
    let vs ← constFieldsAtWithDefsIn ctx ts cs
    pure (v :: vs)
  | [], [] => pure []
  | _, _ => throw (.typeError "Const: field count does not match its declared type")) := by
  trustIrCompilerProof {
    conv =>
      lhs
      delta constFieldsAtWithDefsIn constValueAtWithDefsIn._mutual
      rw [WellFounded.fix_eq]
    cases tys <;> cases cs <;> try rfl
    all_goals rename_i head tail first rest; cases first <;> rfl
  } {
    conv =>
      lhs
      unfold constFieldsAtWithDefsIn
    rfl
  }

theorem constLanesAtWithDefsIn_eq (ctx : ConstantEvalContext) (elemTy : Ty) (cs : List Constant) :
    constLanesAtWithDefsIn ctx elemTy cs = (
  match cs with
  | [] => pure []
  | c :: cs => do
    let v ← constValueAtWithDefsIn ctx elemTy c false
    let vs ← constLanesAtWithDefsIn ctx elemTy cs
    pure (v :: vs)) := by
  trustIrCompilerProof {
    conv =>
      lhs
      delta constLanesAtWithDefsIn constValueAtWithDefsIn._mutual
      rw [WellFounded.fix_eq]
    cases cs <;> rfl
  } {
    conv =>
      lhs
      unfold constLanesAtWithDefsIn
    rfl
  }

theorem constRecordFieldsAtWithDefsIn_eq (ctx : ConstantEvalContext) (declared : List FieldDef)
    (fields : List (String × Constant)) :
    constRecordFieldsAtWithDefsIn ctx declared fields = (
  match fields with
  | [] => pure []
  | (name, c) :: rest => do
    let field ← match declared.find? (fun f => f.name == name) with
      | some f => pure f
      | none => throw (.typeError s!"Const: record field {name} not declared")
    let v ← constValueAtWithDefsIn ctx field.ty c false
    let vs ← constRecordFieldsAtWithDefsIn ctx declared rest
    pure ((name, v) :: vs)) := by
  trustIrCompilerProof {
    conv =>
      lhs
      delta constRecordFieldsAtWithDefsIn constValueAtWithDefsIn._mutual
      rw [WellFounded.fix_eq]
    cases fields <;> rfl
  } {
    conv =>
      lhs
      unfold constRecordFieldsAtWithDefsIn
    rfl
  }

end TrustIr
