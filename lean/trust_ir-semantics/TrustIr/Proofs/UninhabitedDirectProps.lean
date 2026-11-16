-- Copyright 2026 Andrew Yates | Apache-2.0
import TrustIr.Semantics.AggregateAccess

-- Closed controls use the actual source graph, fixed points and byte codec.
set_option smartUnfolding false
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

namespace TrustIr.UninhabitedDirectProps
open SourceLayout AggregateMemory

def deadTuple : Ty := .Tuple [.Never, .Array ⟨0⟩ 4096]
def profile : UninhabitedVariantLayout :=
  { variant := 0, size := 65552, align := 16, fields := [{ size := 65536, align := 16 }] }
def definition : EnumDef :=
  { id := ⟨0⟩, name := "NestedDirect"
    variants := [{ name := "Dead", fields := [deadTuple] },
      { name := "Live", fields := [.U32] }]
    tagRepr := some .u32
    layout := some { encoding := .directWithUninhabited 0 [profile], size := 65552, align := 16, variantFieldOffsets := [[16], [4]] } }
def source : Environment :=
  { hasTargetInfo := true, types := [some .U128], enums := [definition] }

private def view (result : SourceLayout.Result Summary) : Option (Nat × Option Nat) :=
  match result with | .ok summary => some (summary.size, summary.align) | .error _ => none

private def withProfiles (profiles : List UninhabitedVariantLayout) : Environment :=
  { source with enums := [{ definition with layout := some {
      encoding := .directWithUninhabited 0 profiles, size := 65552, align := 16, variantFieldOffsets := [[16], [4]] } }] }

private def cyclic : StructDef :=
  { id := ⟨0⟩, name := "Cycle", fields := [{ name := "next", ty := .Struct ⟨0⟩, offset := none }], size := none, align := none }

private def smallDefinition (dead : Ty) : EnumDef :=
  { definition with variants := [{ name := "Dead", fields := [dead] },
      { name := "Live", fields := [.U32] }], layout := some { encoding := .directWithUninhabited 0 [{ variant := 0, size := 8, align := 4, fields := [{ size := 0, align := 1 }] }], size := 8, align := 4, variantFieldOffsets := [[4], [4]] } }

private def nominalSource : Environment :=
  { source with structs := [{ id := ⟨0⟩, name := "DeadWrap", fields := [{ name := "never", ty := .Enum ⟨1⟩, offset := none }], size := none, align := none }], enums := [smallDefinition (.Struct ⟨0⟩), { id := ⟨1⟩, name := "Infallible", variants := [] }] }

private def selectedPlan : Plan :=
  .enumeration (.Enum ⟨0⟩) ⟨65552, 16⟩
    { tag := .u32, discriminants := [0, 1], encoding := .directWithUninhabited 0 [profile], variants := [[{ ty := deadTuple, offset := 16, size := 65536, align := 16 }],
        [{ ty := .U32, offset := 4, size := 4, align := 4 }]], uninhabited := [true, false] }
    [none, some [(4, .leaf .U32 ⟨4, 4⟩)]]

private def overwritten (image : ByteImage) (offset : Nat) (bytes : ByteImage) : ByteImage :=
  (image.slice 0 offset).append (bytes.append
    (image.slice (offset + bytes.size) (image.size - (offset + bytes.size))))

private def selectedImage : Image :=
  { bytes := overwritten
      (overwritten (ByteImage.fill 65552 none) 0
        (ByteImage.ofList [some 1, some 0, some 0, some 0])) 4
      (ByteImage.ofList [some 1, some 2, some 3, some 4]) }

private def logicalValue : Value := .aggregate [.int 32 1, .int 32 67305985]

private def signedSource : Environment :=
  { hasTargetInfo := true, enums := [{ (smallDefinition .Never) with
      discriminants := [some (-7), some 42], tagRepr := some .i32 }] }

-- Reduce the actual current source service and codec; no legacy builder facade.
macro "direct_source_compute" : tactic =>
  `(tactic| trustIrReduce)

private def selectedPrefix : ByteImage :=
  overwritten (ByteImage.fill 65552 none) 0
    (ByteImage.ofList [some 1, some 0, some 0, some 0])

private theorem selected_encode : encode .le64 none selectedPlan logicalValue = .ok selectedImage := by
  unfold selectedPlan logicalValue
  apply encode_enumeration_of_components .le64 none (.Enum ⟨0⟩) ⟨65552, 16⟩
    _ _ (.int 32 1) [.int 32 67305985] 1 false selectedPrefix selectedImage
  · rfl
  · rfl
  · apply VariantEncoded.of_fields .le64 none _ 1 _ _ _ [(4, .leaf .U32 ⟨4, 4⟩)]
    · rfl
    · trustIrReduce
  · rfl

private theorem selected_decode : decode .le64 none Memory.empty selectedPlan selectedImage.bytes = .ok logicalValue := by
  unfold selectedPlan logicalValue
  apply decode_enumeration_of_payload .le64 none Memory.empty (.Enum ⟨0⟩) ⟨65552, 16⟩
    _ _ selectedImage.bytes 1 1 [(4, .leaf .U32 ⟨4, 4⟩)] [.int 32 67305985]
  · rfl
  · rfl
  · rfl
  · rfl
  · apply FieldsDecoded.cons
    · trustIrReduce
    · exact (FieldsDecoded.nil_iff .le64 none Memory.empty selectedImage.bytes []).2 rfl

private theorem selected_observations :
    (selectedImage.bytes.size, (selectedImage.bytes.slice 0 8).toList) =
      (65552, [some 1, some 0, some 0, some 0, some 1, some 2, some 3, some 4]) := by rfl

private theorem selected_dead_decode :
    decode .le64 none Memory.empty selectedPlan (ByteImage.fill 65552 (some 0)) =
      .error (.ub "Load: uninhabited enum variant") := by
  unfold selectedPlan
  apply decode_enumeration_of_rejection .le64 none Memory.empty (.Enum ⟨0⟩) ⟨65552, 16⟩
    _ _ (ByteImage.fill 65552 (some 0)) (.ub "Load: uninhabited enum variant")
  · rfl
  · rfl

private theorem selected_dead_uninitialized_decode :
    decode .le64 none Memory.empty selectedPlan
      ((ByteImage.ofList [some 0, some 0, some 0, some 0]).append (ByteImage.fill 65548 none)) =
      .error (.ub "Load: uninhabited enum variant") := by
  unfold selectedPlan
  apply decode_enumeration_of_rejection .le64 none Memory.empty (.Enum ⟨0⟩) ⟨65552, 16⟩
    _ _ ((ByteImage.ofList [some 0, some 0, some 0, some 0]).append (ByteImage.fill 65548 none))
    (.ub "Load: uninhabited enum variant")
  · rfl
  · rfl

private theorem selected_dead_encode :
    encode .le64 none selectedPlan (.aggregate [.int 32 0, .uninit]) =
      .error (.typeError "memory image: uninhabited enum variant") := by
  unfold selectedPlan
  apply encode_enumeration_of_rejection .le64 none (.Enum ⟨0⟩) ⟨65552, 16⟩
    _ _ (.int 32 0) [.uninit] false (.typeError "memory image: uninhabited enum variant")
  rfl

private def roundtripProgram (result : Except SemError Plan) :
    Except SemError (Nat × List (Option UInt8) × Value) := do
  let plan ← result
  let image ← encode .le64 none plan logicalValue
  let decoded ← decode .le64 none Memory.empty plan image.bytes
  pure (image.bytes.size, (image.bytes.slice 0 8).toList, decoded)

private def finishRoundtrip (image : Image) (result : Except SemError Value) :
    Except SemError (Nat × List (Option UInt8) × Value) := do
  let decoded ← result
  pure (image.bytes.size, (image.bytes.slice 0 8).toList, decoded)

private def afterEncode (plan : Plan) (result : Except SemError Image) :
    Except SemError (Nat × List (Option UInt8) × Value) := do
  let image ← result
  let decoded ← decode .le64 none Memory.empty plan image.bytes
  pure (image.bytes.size, (image.bytes.slice 0 8).toList, decoded)

private theorem roundtripProgram_ok (plan : Plan) :
    roundtripProgram (.ok plan) = afterEncode plan (encode .le64 none plan logicalValue) := rfl

private theorem afterEncode_ok (plan : Plan) (image : Image) :
    afterEncode plan (.ok image) = finishRoundtrip image (decode .le64 none Memory.empty plan image.bytes) := rfl

private theorem finishRoundtrip_ok (image : Image) (value : Value) :
    finishRoundtrip image (.ok value) = .ok (image.bytes.size, (image.bytes.slice 0 8).toList, value) := rfl

private theorem selected_roundtrip : roundtripProgram (.ok selectedPlan) =
    .ok (65552, [some 1, some 0, some 0, some 0, some 1, some 2, some 3, some 4], logicalValue) := by
  have encoded : afterEncode selectedPlan (encode .le64 none selectedPlan logicalValue) =
      afterEncode selectedPlan (.ok selectedImage) :=
    congrArg (afterEncode selectedPlan) selected_encode
  have decoded : finishRoundtrip selectedImage (decode .le64 none Memory.empty selectedPlan selectedImage.bytes) =
      finishRoundtrip selectedImage (.ok logicalValue) :=
    congrArg (finishRoundtrip selectedImage) selected_decode
  have observed : (Except.ok (selectedImage.bytes.size, (selectedImage.bytes.slice 0 8).toList, logicalValue) :
      Except SemError (Nat × List (Option UInt8) × Value)) =
      .ok (65552, [some 1, some 0, some 0, some 0, some 1, some 2, some 3, some 4], logicalValue) :=
    congrArg (fun pair : Nat × List (Option UInt8) =>
      (Except.ok (pair.1, pair.2, logicalValue) : Except SemError (Nat × List (Option UInt8) × Value)))
      selected_observations
  exact (roundtripProgram_ok selectedPlan).trans
    (encoded.trans ((afterEncode_ok selectedPlan selectedImage).trans
      (decoded.trans ((finishRoundtrip_ok selectedImage logicalValue).trans observed))))

private def readProgram (image : ByteImage) (result : Except SemError Plan) : Except SemError Value := do
  let plan ← result
  decode .le64 none Memory.empty plan image

private theorem readProgram_ok (image : ByteImage) (plan : Plan) :
    readProgram image (.ok plan) = decode .le64 none Memory.empty plan image := rfl

private def impossibleStoreProgram (result : Except SemError Plan) : Except SemError Unit := do
  let plan ← result
  let _ ← encode .le64 none plan (.aggregate [.int 32 0, .uninit])
  pure ()

private def finishStore (result : Except SemError Image) : Except SemError Unit := do
  let _ ← result
  pure ()

private theorem impossibleStoreProgram_ok (plan : Plan) :
    impossibleStoreProgram (.ok plan) = finishStore (encode .le64 none plan (.aggregate [.int 32 0, .uninit])) := rfl

private theorem selected_impossible_store : impossibleStoreProgram (.ok selectedPlan) =
    .error (.typeError "memory image: uninhabited enum variant") :=
  (impossibleStoreProgram_ok selectedPlan).trans (congrArg finishStore selected_dead_encode)

/-- The true physical allocation survives although the dead tuple has no codec. -/
theorem nested_full_physical_extent_shape :
    view (SourceLayout.query source .shape (.Enum ⟨0⟩)) = some (65552, some 16) := by direct_source_compute

theorem nested_full_physical_extent_execution :
    view (SourceLayout.query source .execution (.Enum ⟨0⟩)) = some (65552, some 16) := by direct_source_compute

theorem old_direct_does_not_erase_the_dead_source_tuple :
    view (SourceLayout.query { source with enums := [{ definition with layout := some {
      encoding := .direct 0, size := 65552, align := 16, variantFieldOffsets := [[16], [4]] } }] } .execution (.Enum ⟨0⟩)) = none := by direct_source_compute

theorem missing_profile_refuses :
    view (SourceLayout.query (withProfiles []) .execution (.Enum ⟨0⟩)) = none := by direct_source_compute

theorem duplicate_profile_refuses :
    view (SourceLayout.query (withProfiles [profile, profile]) .execution (.Enum ⟨0⟩)) = none := by direct_source_compute

theorem live_profile_refuses :
    view (SourceLayout.query (withProfiles [{ profile with variant := 1 }])
      .execution (.Enum ⟨0⟩)) = none := by direct_source_compute

theorem zero_sized_array_is_not_a_dead_proof :
    view (SourceLayout.query { source with enums := [{ definition with variants :=
      [{ name := "EmptyArray", fields := [.Array ⟨0⟩ 0] },
       { name := "Live", fields := [.U32] }] }] }
      .execution (.Enum ⟨0⟩)) = none := by direct_source_compute

theorem out_of_range_profile_refuses :
    view (SourceLayout.query (withProfiles [{ profile with variant := 2 }])
      .execution (.Enum ⟨0⟩)) = none := by direct_source_compute

theorem profile_index_above_u32_refuses :
    view (SourceLayout.query (withProfiles [{ profile with variant := 2 ^ 32 }])
      .execution (.Enum ⟨0⟩)) = none := by direct_source_compute

theorem missing_field_storage_refuses :
    view (SourceLayout.query (withProfiles [{ profile with fields := [] }])
      .execution (.Enum ⟨0⟩)) = none := by direct_source_compute

theorem row_larger_than_outer_refuses :
    view (SourceLayout.query (withProfiles [{ profile with size := 65568 }])
      .execution (.Enum ⟨0⟩)) = none := by direct_source_compute

theorem field_outside_row_refuses :
    view (SourceLayout.query (withProfiles [{ profile with size := 65536 }])
      .execution (.Enum ⟨0⟩)) = none := by direct_source_compute

theorem row_alignment_cannot_exceed_outer :
    view (SourceLayout.query (withProfiles [{ profile with align := 32 }])
      .execution (.Enum ⟨0⟩)) = none := by direct_source_compute

theorem field_alignment_must_be_power_of_two :
    view (SourceLayout.query (withProfiles [{ profile with fields := [{ size := 65536, align := 3 }] }])
      .execution (.Enum ⟨0⟩)) = none := by direct_source_compute

theorem physical_field_size_must_be_alignment_rounded :
    view (SourceLayout.query (withProfiles [{ profile with fields := [{ size := 3, align := 2 }] }])
      .execution (.Enum ⟨0⟩)) = none := by direct_source_compute

theorem field_extent_above_u64_refuses :
    view (SourceLayout.query (withProfiles [{ profile with fields := [{ size := 2 ^ 64, align := 16 }] }])
      .execution (.Enum ⟨0⟩)) = none := by direct_source_compute

theorem tag_overlap_is_not_hidden_by_deadness :
    view (SourceLayout.query { source with enums := [{ definition with layout := some {
      encoding := .directWithUninhabited 0 [profile], size := 65552, align := 16, variantFieldOffsets := [[0], [4]] } }] } .execution (.Enum ⟨0⟩)) = none := by direct_source_compute

theorem live_tag_overlap_still_refuses :
    view (SourceLayout.query { source with enums := [{ definition with layout := some {
      encoding := .directWithUninhabited 0 [profile], size := 65552, align := 16, variantFieldOffsets := [[16], [0]] } }] } .execution (.Enum ⟨0⟩)) = none := by direct_source_compute

theorem impossible_field_ranges_must_not_overlap :
    view (SourceLayout.query { source with enums := [{ definition with
      variants := [{ name := "Dead", fields := [.Never, .Array ⟨0⟩ 4096] },
        { name := "Live", fields := [.U32] }], layout := some { encoding := .directWithUninhabited 0 [{ profile with fields := [{ size := 16, align := 16 }, { size := 16, align := 16 }] }], size := 65552, align := 16, variantFieldOffsets := [[16, 16], [4]] } }] }
      .execution (.Enum ⟨0⟩)) = none := by direct_source_compute

theorem missing_nominal_reference_still_refuses :
    view (SourceLayout.query { source with enums := [{ definition with variants :=
      [{ name := "Dead", fields := [.Tuple [.Never, .Ref (.Struct ⟨999⟩)]] },
       { name := "Live", fields := [.U32] }] }] }
      .execution (.Enum ⟨0⟩)) = none := by direct_source_compute

theorem never_does_not_hide_an_invalid_zero_array_reference :
    view (SourceLayout.query { source with enums := [{ definition with variants :=
      [{ name := "Dead", fields := [.Tuple [.Never, .Array ⟨999⟩ 0]] },
       { name := "Live", fields := [.U32] }] }] }
      .execution (.Enum ⟨0⟩)) = none := by direct_source_compute

theorem invalid_live_pointer_reference_still_refuses :
    view (SourceLayout.query { source with enums := [{ definition with variants :=
      [{ name := "Dead", fields := [deadTuple] },
       { name := "Live", fields := [.Ref (.Struct ⟨999⟩)] }] }] }
      .execution (.Enum ⟨0⟩)) = none := by direct_source_compute

theorem cycle_alone_is_not_a_dead_proof :
    view (SourceLayout.query { source with structs := [cyclic], enums :=
      [{ definition with variants := [{ name := "Unknown", fields := [.Struct ⟨0⟩] },
        { name := "Live", fields := [.U32] }] }] }
      .execution (.Enum ⟨0⟩)) = none := by direct_source_compute

theorem never_plus_valid_cycle_does_not_query_dead_storage :
    view (SourceLayout.query { source with structs := [cyclic], enums := [smallDefinition (.Tuple [.Never, .Struct ⟨0⟩])] }
      .execution (.Enum ⟨0⟩)) = some (8, some 4) := by direct_source_compute

theorem missing_dead_nominal_storage_is_not_needed :
    view (SourceLayout.query nominalSource .execution (.Enum ⟨0⟩)) = some (8, some 4) := by direct_source_compute

theorem standalone_empty_enum_has_no_value_layout :
    view (SourceLayout.query nominalSource .execution (.Enum ⟨1⟩)) = none := by direct_source_compute

theorem standalone_dead_wrapper_does_not_gain_a_value_layout :
    view (SourceLayout.query nominalSource .execution (.Struct ⟨0⟩)) = none := by direct_source_compute

theorem dead_profile_must_contain_its_direct_tag :
    view (SourceLayout.query { source with enums := [{ (smallDefinition .Never) with layout := some {
      encoding := .directWithUninhabited 0 [{ variant := 0, size := 0, align := 1, fields := [{ size := 0, align := 1 }] }], size := 8, align := 4, variantFieldOffsets := [[0], [4]] } }] }
      .execution (.Enum ⟨0⟩)) = none := by direct_source_compute

theorem sorted_coverage_is_required_even_when_every_index_is_dead :
    directProfilesCover
      { definition with variants := [{ name := "A", fields := [.Never] },
          { name := "B", fields := [.Never] }] }
      [true, true] [{ profile with variant := 1 }, profile] = false := by direct_source_compute

theorem source_identity_is_not_replaced_by_storage :
    (match SourceLayout.query source .execution (.Enum ⟨0⟩) with
      | .ok summary => summary.enumeration.map (fun info =>
          (info.variants.map (fun fields => fields.map (·.ty)), info.uninhabited))
      | .error _ => none) = some ([[deadTuple], [.U32]], [true, false]) := by direct_source_compute

/-- The full source declaration yields the executable plan, with no dead codec. -/
theorem source_prepares_physical_plan :
    (AggregateMemory.prepare source [.Enum ⟨0⟩]).query (.Enum ⟨0⟩) = .ok selectedPlan := by direct_source_compute

theorem source_plan_bytes_logical_value_roundtrip :
    (do
      let plan ← (AggregateMemory.prepare source [.Enum ⟨0⟩]).query (.Enum ⟨0⟩)
      let image ← encode .le64 none plan logicalValue
      let decoded ← decode .le64 none Memory.empty plan image.bytes
      pure (image.bytes.size, (image.bytes.slice 0 8).toList, decoded)) =
      .ok (65552, [some 1, some 0, some 0, some 0, some 1, some 2, some 3, some 4], logicalValue) := by
  exact (congrArg roundtripProgram source_prepares_physical_plan).trans selected_roundtrip

theorem raw_dead_tag_is_refused_before_payload_read :
    (do
      let plan ← (AggregateMemory.prepare source [.Enum ⟨0⟩]).query (.Enum ⟨0⟩)
      decode .le64 none Memory.empty plan (ByteImage.fill 65552 (some 0))) =
      .error (.ub "Load: uninhabited enum variant") := by
  exact (congrArg (readProgram (ByteImage.fill 65552 (some 0))) source_prepares_physical_plan).trans
    ((readProgram_ok _ selectedPlan).trans selected_dead_decode)

/-- Only the tag is initialized; selecting the dead row refuses before its payload. -/
theorem dead_tag_does_not_read_uninitialized_payload :
    (do
      let plan ← (AggregateMemory.prepare source [.Enum ⟨0⟩]).query (.Enum ⟨0⟩)
      decode .le64 none Memory.empty plan
        ((ByteImage.ofList [some 0, some 0, some 0, some 0]).append
          (ByteImage.fill 65548 none))) =
      .error (.ub "Load: uninhabited enum variant") := by
  exact (congrArg (readProgram ((ByteImage.ofList [some 0, some 0, some 0, some 0]).append
    (ByteImage.fill 65548 none))) source_prepares_physical_plan).trans
    ((readProgram_ok _ selectedPlan).trans selected_dead_uninitialized_decode)

theorem impossible_source_value_cannot_be_stored :
    (do
      let plan ← (AggregateMemory.prepare source [.Enum ⟨0⟩]).query (.Enum ⟨0⟩)
      let _ ← encode .le64 none plan (.aggregate [.int 32 0, .uninit])
      pure ()) = .error (.typeError "memory image: uninhabited enum variant") := by
  exact (congrArg impossibleStoreProgram source_prepares_physical_plan).trans selected_impossible_store

theorem explicit_discriminant_survives_the_new_direct_encoding :
    (do
      let plan ← (AggregateMemory.prepare signedSource [.Enum ⟨0⟩]).query (.Enum ⟨0⟩)
      let value := Value.aggregate [.int 32 42, .int 32 7]
      let image ← encode .le64 none plan value
      let decoded ← decode .le64 none Memory.empty plan image.bytes
      pure (image.bytes.toList, decoded)) =
      .ok ([some 42, some 0, some 0, some 0, some 7, some 0, some 0, some 0],
        .aggregate [.int 32 42, .int 32 7]) := by direct_source_compute

end TrustIr.UninhabitedDirectProps
