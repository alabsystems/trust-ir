-- Copyright 2026 Andrew Yates | Apache-2.0
import TrustIrRuntime
import TrustIrEval.Run

/- Executable decoder controls, outside the axiom-audited library. These check
   source-field retention, not the validity of a producer's physical layout. -/
namespace TrustIrEval.DescriptorSchema

open Lean (Json toJson)
open TrustIr

private def object (fields : List (String × Json)) : Json := Json.mkObj fields
private def number (n : Nat) : Json := toJson n

private def require (checks : IO.Ref Nat) (label : String) (condition : Bool) : IO Unit := do
  unless condition do throw (IO.userError s!"descriptor-schema: {label}")
  checks.modify (· + 1)
  IO.println s!"descriptor-schema: control PASS {label}"

private def decoded {α : Type} (label : String) : D α → IO α
  | .ok value => pure value
  | .error error => throw (IO.userError s!"descriptor-schema {label}: {repr error}")

private def structJson (representation : Option Json) : Json :=
  object ([
    ("id", number 7), ("name", .str "SourceStruct"),
    ("fields", .arr #[object [
      ("name", .str "word"), ("ty", .str "U64"), ("offset", number 1)]]),
    ("size", number 9), ("align", number 1)] ++
    representation.toList.map (fun value => ("repr", value)))

private def directLayout : Json := object [
  ("encoding", object [("Direct", object [("tag_offset", number 4)])]),
  ("size", number 24), ("align", number 8),
  ("variant_field_offsets", .arr #[.arr #[], .arr #[number 8]])]

private def untaggedLayout : Json := object [
  ("encoding", .str "Untagged"), ("size", number 8), ("align", number 8),
  ("variant_field_offsets", .arr #[.arr #[number 0]])]

private def nicheLayout (start : Json) : Json := object [
  ("encoding", object [("Niche", object [
    ("untagged_variant", number 0), ("niche_variants_start", number 1),
    ("niche_variants_end", number 1), ("niche_start", start),
    ("niche_offset", number 0), ("niche_ty", .str "U128")])]),
  ("size", number 16), ("align", number 16),
  ("variant_field_offsets", .arr #[.arr #[number 0], .arr #[]])]

private def enumJson : Json := object [
  ("id", number 9), ("name", .str "SourceEnum"),
  ("variants", .arr #[object [("name", .str "Only"), ("fields", .arr #[.str "U64"]),
    ("field_names", .arr #[])]]),
  ("discriminants", .arr #[number 42]), ("repr", .str "U8"),
  ("layout", untaggedLayout)]

private def tupleJson : Json := object [
  ("tuple_type", number 0), ("size", number 16), ("align", number 8),
  ("field_offsets", .arr #[number 8, number 0, number 9])]

private def moduleJson : Json := object [
  ("functions", .arr #[]), ("func_types", .arr #[]), ("globals", .arr #[]),
  ("enums", .arr #[enumJson]), ("structs", .arr #[structJson (some (object [("Packed", number 1)]))]),
  ("types", .arr #[object [("Tuple", .arr #[.str "U8", .str "U64", .str "U8"])]]),
  ("tuple_layouts", .arr #[tupleJson])]

def run : IO Unit := do
  let checks ← IO.mkRef 0
  let require := require checks
  let representations : List (String × Json × StructRepr) := [
    ("Rust", .str "Rust", .rust), ("C", .str "C", .c),
    ("Transparent", .str "Transparent", .transparent),
    ("Packed1", object [("Packed", number 1)], .packed 1),
    ("Packed2", object [("Packed", number 2)], .packed 2),
    ("Packed4", object [("Packed", number 4)], .packed 4),
    ("Packed0 retained for refusal", object [("Packed", number 0)], .packed 0),
    ("Packed3 retained for refusal", object [("Packed", number 3)], .packed 3)]
  for (label, value, expected) in representations do
    let definition ← decoded label (structDef (structJson (some value)))
    require label (definition.repr == expected && definition.size == some 9 &&
      definition.align == some 1 && definition.fields.head?.bind (·.offset) == some 1)
  let absent ← decoded "absent serde default" (structDef (structJson none))
  require "absent serde default" (absent.repr == .rust)
  let direct ← decoded "direct" (enumLayoutDescriptor directLayout)
  require "direct" (direct.encoding == .direct 4 && direct.variantFieldOffsets == [[], [8]] &&
    direct.size == 24 && direct.align == 8)
  let untagged ← decoded "untagged" (enumLayoutDescriptor untaggedLayout)
  require "untagged" (untagged.encoding == .untagged && untagged.variantFieldOffsets == [[0]])
  let selected ← decoded "single-inhabited selector" (enumLayoutDescriptor (object [
    ("encoding", object [("SingleInhabited", object [("variant", number 1)])]),
    ("size", number 4), ("align", number 4),
    ("variant_field_offsets", .arr #[.arr #[], .arr #[number 0]])]))
  require "single-inhabited retained selector and rows"
    (selected.encoding == .singleInhabited 1 && selected.variantFieldOffsets == [[], [0]])
  let empty ← decoded "retained empty nominal declaration" (enumDef (object [
    ("id", number 10), ("name", .str "Empty"), ("variants", .arr #[]),
    ("discriminants", .arr #[]), ("repr", .null), ("layout", .null)]))
  require "empty nominal has no fabricated tag or layout" (empty.variants.isEmpty &&
    empty.discriminants.isEmpty && empty.tagRepr.isNone && empty.layout.isNone &&
    (SourceLayout.canonicalTag empty).isNone)
  let named ← decoded "retained field names" (enumDef (object [
    ("id", number 11), ("name", .str "Named"),
    ("variants", .arr #[object [("name", .str "Only"), ("fields", .arr #[.str "U32"]),
      ("field_names", .arr #[.str "word"])]]),
    ("discriminants", .arr #[number 23]), ("repr", .null), ("layout", .null)]))
  require "original variant field names retained"
    (named.variants.head?.map (·.fieldNames) == some ["word"] && named.discriminants == [some 23])
  let dead : EnumDef :=
    { id := ⟨0⟩, name := "BothNever", variants := [
        { name := "Inactive", fields := [.Never] }, { name := "Selected", fields := [.Never] }],
      layout := some { encoding := .singleInhabited 1, size := 4, align := 4, variantFieldOffsets := [[], [0]] } }
  require "selected Never exact full query refusal" (match
      SourceLayout.query { hasTargetInfo := true, enums := [dead] } .execution (.Enum ⟨0⟩) with
    | .error (.incoherent "enum" 0) => true
    | _ => false)
  let start := 340282366920938463463374607431768211455
  let niche ← decoded "wide niche" (enumLayoutDescriptor (nicheLayout (.str (toString start))))
  require "wide niche" (niche.encoding == .niche 0 1 1 start 0 .u128)
  require "negative niche refuses" (match enumLayoutDescriptor (nicheLayout (.str "-1")) with
    | .error (.malformed _) => true | _ => false)
  require "unknown representation refuses" (match structRepr (.str "Unknown") with
    | .error (.unsupported "struct_repr.Unknown") => true | _ => false)
  let tuple ← decoded "tuple" (tupleLayoutDescriptor tupleJson)
  require "tuple" (tuple.tupleType.index == 0 && tuple.size == 16 && tuple.align == 8 &&
    tuple.fieldOffsets == [8, 0, 9])
  let source ← decoded "module" (TrustIrEval.module moduleJson)
  let context ← decoded "context" (contextOf source 128)
  require "context" (context.tupleLayouts == [tuple] &&
    (match context.structs ⟨7⟩ with
      | some s => s.repr == .packed 1 && s.size == some 9 &&
        s.fields.head?.bind (·.offset) == some 1
      | none => false) &&
    (match context.enums ⟨9⟩ with
      | some e => e.discriminants == [some 42] && e.layout.map (·.encoding) == some .untagged
      | none => false))
  IO.println s!"descriptor-schema: {(← checks.get)} source-field controls PASS"

end TrustIrEval.DescriptorSchema

def main : IO Unit := TrustIrEval.DescriptorSchema.run
