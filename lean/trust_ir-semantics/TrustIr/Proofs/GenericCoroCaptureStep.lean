-- Copyright 2026 Andrew Yates | Apache-2.0
import TrustIr.Semantics.Eval

namespace TrustIr.GenericCoro.Prefix

/-- A proof-only one-step view of the actual recursive capture checker.
    The callback exposes its recursive uses so context congruences can rewrite
    it once. The anchoring equation below checks this complete step against
    production, including every error and traversal order. -/
def captureCheckStep (ctx : EvalContext)
    (recurse : Ty → Value → Except SemError Unit) (ty : Ty) (v : Value) :
    Except SemError Unit := do
  let mismatch := Except.error (SemError.typeError "closure value does not match its declared type")
  if v.isPoison || v.isUninit then
    throw (.ub "closure boundary: uninitialized value")
  match ty, v with
  | .Bool, .bool _ => pure ()
  | .Char, .int w n =>
    if w != 32 then mismatch
    else if n < 0 || !(decide (validChar n.toNat)) then
      throw (.ub "closure boundary: invalid Unicode scalar value")
    else pure ()
  | t, .int w n =>
    if !(t.isInteger && t.bitWidthFor ctx.byteModel == some w) then mismatch
    else if 0 ≤ n && n < (2 : Int) ^ w then pure () else mismatch
  | .F16, .float f | .F32, .float f | .F64, .float f => checkFloatAt ty f
  | .Ptr, .ptr _ _ | .Ptr, .nullPtr
  | .Ref _, .ptr _ _ | .Ref _, .nullPtr
  | .RefMut _, .ptr _ _ | .RefMut _, .nullPtr
  | .PtrConst _, .ptr _ _ | .PtrConst _, .nullPtr
  | .PtrMut _, .ptr _ _ | .PtrMut _, .nullPtr => pure ()
  | .Unit, .aggregate [] => pure ()
  | .Func sig, .fnDef held _ => if sig == held then pure () else mismatch
  | .Func _, .nullPtr => pure ()
  | .Tuple ts, .aggregate vs =>
    if ts.length != vs.length then mismatch
    else (ts.zip vs).forM (fun (t, x) =>
      if x.isUninit then pure () else recurse t x)
  | .Struct sid, .aggregate vs =>
    let d ← match ctx.structs sid with
      | some d => pure d
      | none => throw (.unsupported .enumDefTable "closure capture struct definition is absent")
    if d.fields.length != vs.length then mismatch
    else (d.fields.zip vs).forM (fun (f, x) =>
      if x.isUninit then pure () else recurse f.ty x)
  | .Array tid n, .array vs =>
    let t ← match ctx.types tid with
      | some t => pure t
      | none => throw (.unsupported .enumDefTable "closure capture element type is absent")
    if n != vs.size then mismatch
    else vs.tree.checkStored (recurse t)
  | .Vector n elemTy, .vector vs =>
    if n == 0 || n != vs.length then mismatch
    else vs.forM (recurse elemTy)
  | .Sequence tid, .sequence vs | .Set tid _, .set vs =>
    let elemTy ← match ctx.types tid with
      | some t => pure t
      | none => throw (.unsupported .enumDefTable "closure capture element type is absent")
    vs.forM (recurse elemTy)
  | .Record rid, .record fields =>
    let d ← match ctx.records rid with
      | some d => pure d
      | none => throw (.unsupported .enumDefTable "closure capture record definition is absent")
    if d.fields.length != fields.length then mismatch
    else (d.fields.zip fields).forM (fun (declared, (name, x)) => do
      if name != declared.name then mismatch
      else recurse declared.ty x)
  | .Enum eid, .aggregate vs =>
    let d ← match ctx.enums eid with
      | some d => pure d
      | none => throw (.unsupported .enumDefTable "closure capture enum definition is absent")
    let discs ← match enumEffectiveDiscriminants d with
      | some ds => pure ds
      | none => throw (.typeError "closure capture enum discriminants are invalid")
    let repr ← match enumCanonicalTagRepr d with
      | some r => pure r
      | none => throw (.typeError "closure capture enum tag representation is invalid")
    match vs with
    | [] => mismatch
    | tagValue :: payload => do
      -- The tag is a real child value, so its membership/poison checks use
      -- the same decremented structural fuel as every payload child.
      recurse repr.ty tagValue
      match tagValue with
      | .int _ tag => do
        -- Signed discriminants are carried by their canonical-width residue.
        -- Use the trusted declared width, never an unchecked runtime width.
        let residues := discs.map (fun disc => disc % ((2 : Int) ^ repr.bitWidth))
        let index ← match listIndexOf? residues tag with
          | some i => pure i
          | none => throw (.typeError "closure capture enum tag names no variant")
        let variant ← match trustIrListGet? d.variants index with
          | some variant => pure variant
          | none => throw (.typeError "closure capture enum tag names no variant")
        if variant.fields.length != payload.length then mismatch
        else (variant.fields.zip payload).forM (fun (t, x) => recurse t x)
      | _ => mismatch
  | .Closure cid, .typedClosure held _fn captures =>
    if held != cid then mismatch else
      let d ← match ctx.closures cid with
        | some d => pure d
        | none => throw (.unsupported .closureDefTable "closure definition is absent")
      if d.captures.length != captures.length then mismatch
      else (d.captures.zip captures).forM (fun (t, x) => recurse t x)
  | .FatPtr kind, .fatPtr _ _ metadata =>
    recurse (kind.metadataTyAtModel ctx.byteModel) metadata
  | _, _ => mismatch

theorem checkClosureValueAt_succ_step (ctx : EvalContext) (fuel : Nat) :
    checkClosureValueAt ctx (fuel + 1) = captureCheckStep ctx (checkClosureValueAt ctx fuel) := by rfl

theorem captureCheckStep_withLocalTypes (ctx : EvalContext) (types : Option LocalTypeTable)
    (recurse : Ty → Value → Except SemError Unit) (ty : Ty) (value : Value) :
    captureCheckStep {ctx with localTypes := types} recurse ty value =
      captureCheckStep ctx recurse ty value := by rfl

end TrustIr.GenericCoro.Prefix
