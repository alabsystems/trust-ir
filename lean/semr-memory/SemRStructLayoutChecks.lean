-- Copyright 2026 Andrew Yates
-- Licensed under the Apache License, Version 2.0
import SemRStructLayout

-- Use the canonical owner's checked equation reduction on modern Lean.
-- This is local proof metadata, not a replacement executable or native eval.
run_cmd do
  let env ← Lean.getEnv
  let mut registered := 0
  for (name, _) in env.constants.map₁.toList do
    if name.toString.endsWith "TrustIr.SourceLayout.compileTy.eq_def" ||
       name.toString.endsWith "TrustIr.SourceLayout.compileTypes.eq_def" then
      Lean.Elab.Command.elabCommand
        (← `(command| attribute [local cbv_eval] $(Lean.mkIdent name):ident))
      registered := registered + 1
  unless registered == 2 do
    Lean.throwError "expected the two original layout compiler equations"

namespace SemR.CanonicalStructLayout.Checks

def pair : SemR.StructDef :=
  { id := 0
    fields := [.int .i64]
    name := "PairI64".toUTF8.data.toList.map UInt8.toNat
    fieldInfo := [("value".toUTF8.data.toList.map UInt8.toNat, some 0)]
    size := some 8
    align := some 8 }

def moduleWith (definition : SemR.StructDef) : SemR.Module :=
  { funcTys := [], enums := [], functions := [], structs := [definition] }

/-- The existing WP question's entire PairI64 declaration is retained,
    including the original name, field name and three explicit options. -/
theorem original_pair_declaration_decodes :
    SemR.flatStructDef 75 #["PairI64".toUTF8.data.toList.map UInt8.toNat,
      "value".toUTF8.data.toList.map UInt8.toNat]
      [0, 0, 1, 1, 3, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 8, 0, 0, 0, 0, 0, 0, 0, 1, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0] = .ok pair [] := rfl

theorem layout_u64_consumes_all_eight_original_bytes :
    SemR.optFixedU64 41 #[] [1, 8, 0, 0, 0, 0, 0, 0, 0] = .ok (some 8) [] := rfl

theorem layout_u64_preserves_the_unsigned_edge :
    SemR.optFixedU64 41 #[] [1, 255, 255, 255, 255, 255, 255, 255, 255] =
      .ok (some 18446744073709551615) [] := rfl

theorem layout_u64_does_not_accept_a_varint_instead :
    SemR.optFixedU64 41 #[] [1, 8] = .err (.malformed "unexpected end of input") := rfl

theorem instruction_alignment_keeps_its_existing_varint_reader :
    SemR.optU64 41 #[] [1, 128, 1] = .ok (some 128) [] := rfl

theorem original_pair_adapter :
    declaration pair = .ok {
      id := ⟨0⟩
      name := "PairI64"
      fields := [{ name := "value", ty := .I64, offset := some 0 }]
      size := some 8
      align := some 8
      repr := .rust } := rfl

theorem original_pair_execution_geometry :
    query (moduleWith pair) .execution 0 = .ok {
      size := 8
      align := some 8
      fields := [{ ty := .I64, offset := 0, size := 8, align := 8 }] } := by trustIrReduce

theorem original_pair_shape_geometry :
    query (moduleWith pair) .shape 0 = .ok {
      size := 8
      align := some 8
      fields := [{ ty := .I64, offset := 0, size := 8, align := 8 }] } := by trustIrReduce

/-- Presence is not permission to infer the other half of a descriptor. -/
theorem partial_descriptor_is_not_repaired :
    query (moduleWith { pair with align := none }) .execution 0 =
      .error (.layout (.incoherent "struct" 0)) := by trustIrReduce

def refused {α : Type} : Except Refusal α → Bool
  | .error _ => true
  | .ok _ => false

theorem misaligned_original_offset_refuses :
    refused (query (moduleWith { pair with
      fieldInfo := [("value".toUTF8.data.toList.map UInt8.toNat, some 1)] }) .execution 0) =
        true := by trustIrReduce

theorem field_outside_original_size_refuses :
    refused (query (moduleWith { pair with
      fieldInfo := [("value".toUTF8.data.toList.map UInt8.toNat, some 8)] }) .execution 0) =
        true := by trustIrReduce

theorem zero_alignment_refuses :
    refused (query (moduleWith { pair with align := some 0 }) .execution 0) = true := by
  trustIrReduce

theorem absent_field_metadata_is_not_inferred :
    query (moduleWith { pair with fieldInfo := [] }) .execution 0 =
      .error (.declaration "struct field metadata differs from the original type inventory") := rfl

theorem pointer_field_stays_outside_the_adapter :
    query (moduleWith { pair with fields := [.ptr] }) .execution 0 =
      .error (.declaration "struct field is outside the flat scalar fragment") := rfl

theorem original_invalid_name_is_not_normalized :
    originalName [255] = .error "struct name is not UTF-8" := by trustIrReduce

theorem original_nonbyte_name_is_not_truncated :
    originalName [256] = .error "struct name contains a non-byte" := rfl

theorem foreign_representation_is_not_reinterpreted :
    query (moduleWith { pair with repr := 1 }) .execution 0 =
      .error (.declaration "struct representation is outside the retained Rust fragment") := rfl

theorem original_geometry_does_not_enable_struct_allocation :
    SemR.layoutOf 64 (.struct 0) = SemR.unsupR "mem.layout" := rfl

theorem original_geometry_does_not_enable_struct_access :
    SemR.scalarLayout 64 (.struct 0) = SemR.unsupR "mem.access.ty" := rfl

theorem malformed_offset_option_refuses :
    SemR.flatStructDef 75 #[[]] [0,0,1,0,3,2] =
      .err (.malformed "invalid tag") := rfl

theorem truncated_offset_value_refuses :
    SemR.flatStructDef 75 #[[]] [0,0,1,0,3,1] =
      .err (.malformed "unexpected end of input") := rfl

theorem original_nominal_boundary_refuses :
    SemR.flatStructDef 75 #[[]] [0, 0, 1, 0, 3, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 8, 0, 0, 0, 0, 0, 0, 0, 1, 8, 0, 0, 0, 0, 0, 0, 0, 0, 1] =
      .err (.unsupported "struct.origin") := rfl

end SemR.CanonicalStructLayout.Checks
