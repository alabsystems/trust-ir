-- Copyright 2026 Andrew Yates
-- Licensed under the Apache License, Version 2.0
import SemR
import TrustIr.Layout.Service

/-! Retained flat declarations use the existing canonical layout owner.

This adapter translates declaration types and original UTF-8 names only. It
does not calculate offsets, choose padding, repair incomplete declarations or
enable a SemR aggregate memory instruction.
-/

namespace SemR.CanonicalStructLayout

def scalarType : SemR.Ty → Option TrustIr.Ty
  | .bool => some .Bool
  | .int .i8 => some .I8 | .int .i16 => some .I16
  | .int .i32 => some .I32 | .int .i64 => some .I64
  | .int .i128 => some .I128 | .int .isize => some .Isize
  | .int .u8 => some .U8 | .int .u16 => some .U16
  | .int .u32 => some .U32 | .int .u64 => some .U64
  | .int .u128 => some .U128 | .int .usize => some .Usize
  | _ => none

def originalName (bytes : List Nat) : Except String String := do
  if !bytes.all (fun byte => byte < 256) then
    throw "struct name contains a non-byte"
  match String.fromUTF8? ⟨(bytes.map UInt8.ofNat).toArray⟩ with
  | some name => pure name
  | none => throw "struct name is not UTF-8"

def field (source : SemR.Ty × (List Nat × Option Nat)) : Except String TrustIr.FieldDef := do
  let some actual := scalarType source.1 | throw "struct field is outside the flat scalar fragment"
  let actualName ← originalName source.2.1
  pure { name := actualName, ty := actual, offset := source.2.2 }

def fields (types : List SemR.Ty) (metadata : List (List Nat × Option Nat)) :
    Except String (List TrustIr.FieldDef) :=
  if types.length = metadata.length then
    (types.zip metadata).mapM field
  else .error "struct field metadata differs from the original type inventory"

def declaration (source : SemR.StructDef) : Except String TrustIr.StructDef := do
  if source.repr != 0 then throw "struct representation is outside the retained Rust fragment"
  let name ← originalName source.name
  let actualFields ← fields source.fields source.fieldInfo
  pure { id := ⟨source.id⟩
         name := name
         fields := actualFields
         size := source.size
         align := source.align
         repr := .rust }

def environment (source : SemR.Module) : Except String TrustIr.SourceLayout.Environment := do
  let model ←
    if source.pointerBits == 32 then pure TrustIr.ByteModel.le32
    else if source.pointerBits == 64 then pure TrustIr.ByteModel.le64
    else throw "unsupported source pointer width"
  if !source.executableTarget then throw "unsupported source execution target"
  let declarations ← source.structs.mapM declaration
  pure { model := model
         canonicalScalars := true
         hasTargetInfo := source.target.isSome
         structs := declarations }

inductive Refusal where
  | declaration (message : String)
  | layout (error : TrustIr.SourceLayout.Error)
  deriving Repr

def query (source : SemR.Module) (mode : TrustIr.SourceLayout.Mode) (id : Nat) :
    Except Refusal TrustIr.SourceLayout.Summary :=
  match environment source with
  | .error message => .error (.declaration message)
  | .ok original =>
    match TrustIr.SourceLayout.query original mode (.Struct ⟨id⟩) with
    | .error error => .error (.layout error)
    | .ok value => .ok value

/-- Both successful geometry and contextual failures are the canonical
    service's exact answer, rather than a second layout validator. -/
theorem query_uses_canonical (source : SemR.Module)
    (original : TrustIr.SourceLayout.Environment)
    (adapted : environment source = .ok original)
    (mode : TrustIr.SourceLayout.Mode) (id : Nat) :
    query source mode id =
      match TrustIr.SourceLayout.query original mode (.Struct ⟨id⟩) with
      | .error error => .error (.layout error)
      | .ok value => .ok value := by
  simp only [query, adapted]

theorem fields_preserve_offsets (types : List SemR.Ty)
    (metadata : List (List Nat × Option Nat)) (actual : List TrustIr.FieldDef)
    (converted : fields types metadata = .ok actual) :
    actual.map TrustIr.FieldDef.offset = metadata.map Prod.snd := by
  induction types generalizing metadata actual with
  | nil =>
    cases metadata <;> simp_all [fields, pure, Except.pure, Except.bind]
  | cons ty types ih =>
    cases metadata with
    | nil => simp [fields] at converted
    | cons info metadata =>
      rcases info with ⟨name, offset⟩
      have equal : types.length = metadata.length := by
        by_cases same : types.length = metadata.length
        · exact same
        · simp [fields, same] at converted
      have head : fields (ty :: types) ((name, offset) :: metadata) = (do
          let first ← field (ty, (name, offset))
          let rest ← fields types metadata
          pure (first :: rest)) := by
        simp [fields, equal]
      rw [head] at converted
      cases typed : scalarType ty with
      | none => simp [field, typed, bind, pure, Except.bind, Except.pure] at converted
      | some actualType =>
        cases named : originalName name with
        | error message =>
          simp [field, typed, named, bind, pure, Except.bind, Except.pure] at converted
        | ok actualName =>
          cases rest : fields types metadata with
          | error message =>
            simp [field, typed, named, rest, bind, pure, Except.bind, Except.pure] at converted
          | ok actualRest =>
            have same : actual =
                { name := actualName, ty := actualType, offset := offset } :: actualRest := by
              simpa [field, typed, named, rest, bind, pure, Except.bind, Except.pure]
                using converted.symm
            rw [same]
            exact congrArg (List.cons offset) (ih metadata actualRest rest)

end SemR.CanonicalStructLayout
