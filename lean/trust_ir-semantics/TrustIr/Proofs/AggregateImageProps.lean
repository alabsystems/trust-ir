-- Copyright 2026 Andrew Yates | Apache-2.0
import TrustIr.Proofs.AggregateMemoryFrames
import TrustIr.Proofs.ByteImageTraversalProps
import TrustIr.Semantics.Eval

run_cmd do
  if Lean.versionString == "4.30.0-rc2" then
    let env ← Lean.getEnv
    let mut registered := 0
    for (n, _) in env.constants.map₁.toList do
      if n.toString.endsWith "TrustIr.SourceLayout.compileTy.eq_def" ||
         n.toString.endsWith "TrustIr.SourceLayout.compileTypes.eq_def" then
        Lean.Elab.Command.elabCommand (← `(command| attribute [local cbv_eval] $(Lean.mkIdent n):ident))
        registered := registered + 1
    unless registered == 2 do
      Lean.throwError "expected the two original layout compiler equations"
  else if Lean.versionString != "4.8.0" then
    Lean.throwError "unsupported compiler for layout equation reduction"

namespace TrustIr.AggregateImageProps
open AggregateMemory

/-- Lane-record clipping never changes allocation metadata, stored bytes or
    allocator cursors, for arbitrary input states and byte ranges. -/
theorem forgetUnwritten_world (memory : Memory) (address length : Nat) :
    (memory.forgetUnwritten address length).allocations = memory.allocations ∧
    (memory.forgetUnwritten address length).bytes = memory.bytes ∧
    (memory.forgetUnwritten address length).nextAddr = memory.nextAddr ∧
    (memory.forgetUnwritten address length).nextAllocId = memory.nextAllocId := ⟨rfl, rfl, rfl, rfl⟩

theorem forgetUnwritten_zero (memory : Memory) (address : Nat) :
    memory.forgetUnwritten address 0 = memory := by
  cases memory with
  | mk allocations bytes nextAddr nextAllocId lanes => cases lanes <;> rfl

theorem recordUnwritten_empty (memory : Memory) (allocation : AllocId) (address : Nat) :
    memory.recordUnwritten allocation address [] = memory := rfl

theorem canonical_layout_ignores_aggregate_service (ctx : EvalContext) (ty : Ty)
    (canonical : ty.hasCanonicalMemoryLayout = true) : ctx.memoryServiceFor ty = none := by
  simp only [EvalContext.memoryServiceFor, canonical, if_true]

/-- Global initializer zeroing retains every defined byte and initializes
    every actual absent byte, across the complete logical image. -/
theorem zeroUninit_byte (image : Image) (index : Nat) (inside : index < image.bytes.size) :
    image.zeroUninit.get index = some ((image.bytes.get index).getD 0) :=
  ByteImage.get_map_inside image.bytes (fun byte => some (byte.getD 0)) index inside

theorem zeroUninit_extent (image : Image) : image.zeroUninit.size = image.bytes.size := rfl

private def coveredDense (plan : Plan) (bytes : List (Option UInt8)) :=
  AggregateMemory.covered plan (ByteImage.ofList bytes)
private def decodeDense (model : ByteModel) (order : FunctionAddressOrder) (memory : Memory)
    (plan : Plan) (bytes : List (Option UInt8)) :=
  AggregateMemory.decode model order memory plan (ByteImage.ofList bytes)
private def decodeUnwrittenDense (model : ByteModel) (order : FunctionAddressOrder) (memory : Memory)
    (plan : Plan) (bytes : List (Option UInt8)) :=
  AggregateMemory.decodeUnwritten model order memory plan (ByteImage.ofList bytes)

private def byte : Plan := .leaf .U8 ⟨1, 1⟩
private def word : Plan := .leaf .U64 ⟨8, 8⟩
private def padded : Plan := .fields (.Tuple [.U8, .U64]) ⟨16, 8⟩ [(0, byte), (8, word)]
private def packed : Plan := .fields (.Struct ⟨0⟩) ⟨9, 1⟩ [(0, byte), (1, word)]
private def rawChar : Plan := .fields (.Tuple [.Char]) ⟨4, 4⟩ [(0, .leaf .Char ⟨4, 4⟩)]
private def pair : Plan := .fields (.Tuple [.U8, .U8]) ⟨2, 1⟩ [(0, byte), (1, byte)]
private def noFunctions : FunctionAddressOrder := none
private def logicalPair : Value := .aggregate [.int 8 7, .int 64 42]
private def paddedBytes : List (Option UInt8) :=
  [some 7, none, none, none, none, none, none, none,
   some 42, some 0, some 0, some 0, some 0, some 0, some 0, some 0]

theorem padded_image_keeps_padding_absent :
    (encode .le64 noFunctions padded logicalPair).map (fun image => image.bytes.toList) = .ok paddedBytes := by
  trustIrCompilerProof {
    exact rfl
  } {
    exact by trustIrReduce
  }

theorem packed_image_has_no_synthesized_padding :
    (encode .le64 noFunctions packed logicalPair).map (fun image => image.bytes.toList) =
      .ok [some 7, some 42, some 0, some 0, some 0, some 0, some 0, some 0, some 0] := by
  trustIrCompilerProof {
    exact rfl
  } {
    exact by trustIrReduce
  }

theorem padding_is_not_covered : coveredDense padded paddedBytes = .ok none := by
  trustIrCompilerProof {
    exact rfl
  } {
    exact by trustIrReduce
  }

theorem missing_live_field_is_covered :
    coveredDense padded (paddedBytes.take 8 ++ List.replicate 8 none) = .ok (some 8) := by
  trustIrCompilerProof {
    exact rfl
  } {
    exact by trustIrReduce
  }

theorem padded_decode_ignores_padding :
    decodeDense .le64 noFunctions Memory.empty padded paddedBytes = .ok logicalPair := by
  trustIrCompilerProof {
    exact rfl
  } {
    exact by trustIrReduce
  }

theorem field_census_refuses :
    encode .le64 noFunctions padded (.aggregate [.int 8 7]) =
      .error (.typeError "memory image: field census mismatch") := by
  trustIrCompilerProof {
    exact rfl
  } {
    exact by trustIrReduce
  }

theorem integer_width_refuses :
    encode .le64 noFunctions pair (.aggregate [.int 16 7, .int 8 8]) =
      .error (.typeError "memory image: integer lane width does not match its source type") := by
  trustIrCompilerProof {
    exact rfl
  } {
    exact by trustIrReduce
  }

theorem unwritten_field_has_separate_record :
    (encode .le64 noFunctions pair (.aggregate [.uninit, .int 8 9]) true).map
      (fun image => (image.bytes.toList, image.unwritten)) = .ok ([none, some 9], [(0, 1)]) := by
  trustIrCompilerProof {
    exact rfl
  } {
    exact by trustIrReduce
  }

theorem unexplained_hole_refuses :
    decodeDense .le64 noFunctions Memory.empty pair [none, some 9] =
      .error (.ub "Load: reading uninitialized covered memory") := by
  trustIrCompilerProof {
    exact rfl
  } {
    exact by trustIrReduce
  }

theorem explained_whole_field_recovers_uninit :
    decodeUnwrittenDense .le64 noFunctions Memory.empty pair [none, some 9] =
      .ok (.aggregate [.uninit, .int 8 9]) := by
  trustIrCompilerProof {
    exact rfl
  } {
    exact by trustIrReduce
  }

theorem partial_scalar_field_cannot_recover_uninit :
    decodeUnwrittenDense .le64 noFunctions Memory.empty
      (.fields (.Tuple [.U16]) ⟨2, 2⟩ [(0, .leaf .U16 ⟨2, 2⟩)])
      [none, some 1] = .error (.ub "Load: partially written aggregate lane") := by
  trustIrCompilerProof {
    exact rfl
  } {
    exact by trustIrReduce
  }

theorem arrays_do_not_inherit_unwritten_permission :
    encode .le64 noFunctions (.array (.Array ⟨0⟩ 2) ⟨2, 1⟩ 2 byte)
      (.array (CompactArray.Packed.ofArray #[.uninit, .int 8 9])) true = .error (.ub "memory image: inspecting an unwritten lane") := by
  trustIrCompilerProof {
    exact rfl
  } {
    exact by trustIrReduce
  }

theorem nested_char_transports_raw_carrier :
    decodeDense .le64 noFunctions Memory.empty rawChar [some 0, some 216, some 0, some 0] =
      .ok (.aggregate [.int 32 55296]) := by
  trustIrCompilerProof {
    exact rfl
  } {
    exact by trustIrReduce
  }

theorem scalar_char_keeps_unicode_boundary :
    decodeDense .le64 noFunctions Memory.empty (.leaf .Char ⟨4, 4⟩)
      [some 0, some 216, some 0, some 0] = .error (.ub "memory decode: invalid Unicode scalar value") := by
  trustIrCompilerProof {
    exact rfl
  } {
    exact by trustIrReduce
  }

private def recorded : Memory := Memory.empty.recordUnwritten ⟨5⟩ 100 [(0, 8)]

theorem overwritten_low_record_is_clipped :
    ((recorded.forgetUnwritten 100 3).isUnwritten ⟨5⟩ 102,
      (recorded.forgetUnwritten 100 3).isUnwritten ⟨5⟩ 103) = (false, true) := rfl

theorem overwritten_middle_record_splits :
    ((recorded.forgetUnwritten 102 3).isUnwritten ⟨5⟩ 101,
      (recorded.forgetUnwritten 102 3).isUnwritten ⟨5⟩ 103,
      (recorded.forgetUnwritten 102 3).isUnwritten ⟨5⟩ 105) = (true, false, true) := rfl

theorem overwrite_clears_record :
    (recorded.forgetUnwritten 100 8).isUnwritten ⟨5⟩ 107 = false := rfl

theorem allocation_identity_is_required : recorded.isUnwritten ⟨6⟩ 100 = false := rfl

theorem copying_absent_bytes_creates_no_record :
    (Memory.empty.writeBytesMaybeUninit 200 (List.replicate 8 none)).isUnwritten ⟨5⟩ 200 = false := rfl

theorem zero_sized_unwritten_record_is_omitted :
    (Memory.empty.recordUnwritten ⟨5⟩ 100 [(0, 0)]).unwritten = [] := rfl

/-- Equal byte addresses do not erase distinct provenance at strong
    compare-exchange's typed aggregate comparison. -/
theorem equality_keeps_pointer_provenance :
    equal .le64 (.fields (.Tuple [.Ptr]) ⟨8, 8⟩ [(0, .leaf .Ptr ⟨8, 8⟩)])
      (.aggregate [.ptr 1024 (some ⟨0⟩)]) (.aggregate [.ptr 1024 (some ⟨1⟩)]) = .ok false := by
  trustIrCompilerProof {
    simp only [equal]
    rfl
  } {
    exact by trustIrReduce
  }

private def inhabitedAndDead : SourceLayout.Enumeration :=
  { tag := .u8, discriminants := [0, 1], encoding := .direct 0,
    variants := [[{ ty := .U64, offset := 8, size := 8, align := 8 }],
      [{ ty := .Never, offset := 8, size := 0, align := 1 }]],
    uninhabited := [false, true] }

private def variantPlan : Plan :=
  .enumeration (.Enum ⟨0⟩) ⟨16, 8⟩ inhabitedAndDead [some [(8, word)], none]

private def liveVariantBytes : List (Option UInt8) :=
  [some 0, none, none, none, none, none, none, none,
   some 42, some 0, some 0, some 0, some 0, some 0, some 0, some 0]

/-- An impossible inactive payload is explicitly absent, not an empty live
    payload and not a newly admitted standalone Never codec. -/
theorem inhabited_variant_ignores_dead_payload :
    decodeDense .le64 noFunctions Memory.empty variantPlan liveVariantBytes =
      .ok (.aggregate [.int 8 0, .int 64 42]) := by
  trustIrCompilerProof {
    exact rfl
  } {
    exact by trustIrReduce
  }

theorem inhabited_variant_encodes_with_dead_payload_absent :
    (encode .le64 noFunctions variantPlan (.aggregate [.int 8 0, .int 64 42])).map (fun image => image.bytes.toList) =
      .ok liveVariantBytes := by
  trustIrCompilerProof {
    exact rfl
  } {
    exact by trustIrReduce
  }

theorem covered_dead_tag_is_ub_before_missing_payload :
    coveredDense variantPlan (some 1 :: List.replicate 15 none) =
      .error (.ub "Load: uninhabited enum variant") := by
  trustIrCompilerProof {
    exact rfl
  } {
    exact by trustIrReduce
  }

theorem initialized_dead_tag_is_ub :
    decodeDense .le64 noFunctions Memory.empty variantPlan (some 1 :: List.replicate 15 (some 0)) =
      .error (.ub "Load: uninhabited enum variant") := by
  trustIrCompilerProof {
    exact rfl
  } {
    exact by trustIrReduce
  }

theorem dead_value_store_is_type_error :
    encode .le64 noFunctions variantPlan (.aggregate [.int 8 1, .uninit]) true =
      .error (.typeError "memory image: uninhabited enum variant") := by
  trustIrCompilerProof {
    exact rfl
  } {
    exact by trustIrReduce
  }

theorem unknown_tag_is_ub :
    coveredDense variantPlan (some 2 :: List.replicate 15 (some 0)) =
      .error (.ub "Load: enum tag does not name a variant") := by
  trustIrCompilerProof {
    exact rfl
  } {
    exact by trustIrReduce
  }

theorem missing_tag_remains_uninitialized :
    coveredDense variantPlan (List.replicate 16 none) = .ok (some 0) := by
  trustIrCompilerProof {
    exact rfl
  } {
    exact by trustIrReduce
  }

private def zeroDead : Plan :=
  .enumeration (.Enum ⟨1⟩) ⟨0, 1⟩
    { tag := .u8, discriminants := [0], encoding := .untagged,
      variants := [[{ ty := .Never, offset := 0, size := 0, align := 1 }]],
      uninhabited := [true] } [none]

theorem zero_byte_untagged_dead_is_ub :
    decodeDense .le64 noFunctions Memory.empty zeroDead [] =
      .error (.ub "Load: uninhabited enum variant") := by
  trustIrCompilerProof {
    exact rfl
  } {
    exact by trustIrReduce
  }

private def neverIsUnsupported (result : Except SemError Plan) : Bool :=
  match result with | .error (.unsupported .layout _) => true | _ => false

theorem standalone_never_image_query_remains_refused :
    neverIsUnsupported ((AggregateMemory.prepare { hasTargetInfo := true } [.Never]).query .Never) = true := by
  trustIrCompilerProof {
    exact rfl
  } {
    exact by trustIrReduce
  }

private def variantDefinition : EnumDef :=
  { id := ⟨0⟩
    name := "HasImpossible"
    variants := [{ name := "Good", fields := [.U64] }, { name := "Bad", fields := [.Never] }]
    layout := some { encoding := .direct 0, size := 16, align := 8, variantFieldOffsets := [[8], [8]] } }

private def variantSource : SourceLayout.Environment :=
  { hasTargetInfo := true, enums := [variantDefinition] }

private def variantEligibility (result : Except SemError Plan) : List Bool :=
  match result with
  | .ok (.enumeration _ _ _ variants) => variants.map Option.isSome
  | _ => []

theorem actual_preparation_keeps_only_executable_variant_payloads :
    variantEligibility ((AggregateMemory.prepare variantSource [.Enum ⟨0⟩]).query (.Enum ⟨0⟩)) =
      [true, false] := by
  trustIrCompilerProof {
    simp only [variantEligibility, AggregateMemory.prepare, AggregateMemory.Service.query,
      List.forIn, List.forIn.loop]
    rfl
  } {
    exact by trustIrReduce
  }

private def singlePlan : Plan :=
  .enumeration (.Enum ⟨0⟩) ⟨4, 4⟩
    { tag := .u8, discriminants := [7, 23], encoding := .singleInhabited 1,
      variants := [[], [{ ty := .U32, offset := 0, size := 4, align := 4 }]],
      uninhabited := [true, false] }
    [none, some [(0, .leaf .U32 ⟨4, 4⟩)]]
private def singleValue : Value := .aggregate [.int 8 23, .int 32 305419896]
private def singleBytes : List (Option UInt8) := [some 120, some 86, some 52, some 18]

theorem single_inhabited_image_contains_payload_without_stored_tag :
    (encode .le64 noFunctions singlePlan singleValue).map (fun image => image.bytes.toList) =
      .ok singleBytes := by
  trustIrCompilerProof {
    exact rfl
  } {
    exact by trustIrReduce
  }

theorem single_inhabited_decode_synthesizes_effective_discriminant_not_selector :
    decodeDense .le64 noFunctions Memory.empty singlePlan singleBytes = .ok singleValue := by
  trustIrCompilerProof {
    exact rfl
  } {
    exact by trustIrReduce
  }

theorem single_inhabited_dead_logical_variant_refuses :
    encode .le64 noFunctions singlePlan (.aggregate [.int 8 7]) =
      .error (.typeError "memory image: uninhabited enum variant") := by
  trustIrCompilerProof {
    exact rfl
  } {
    exact by trustIrReduce
  }

theorem single_inhabited_selector_is_not_a_logical_discriminant :
    encode .le64 noFunctions singlePlan (.aggregate [.int 8 1, .int 32 0]) =
      .error (.typeError "memory image: enum tag does not name a variant") := by
  trustIrCompilerProof {
    exact rfl
  } {
    exact by trustIrReduce
  }

end TrustIr.AggregateImageProps
