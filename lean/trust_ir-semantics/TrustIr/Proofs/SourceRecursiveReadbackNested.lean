-- Copyright 2026 Andrew Yates | Apache-2.0
import TrustIr.Proofs.SourceRecursiveReadbackFixtureData

/- Enable kernel reduction through the imported mutual compiler equations.
The metadata is local to these proofs; no executable definition is replaced. -/
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

namespace TrustIr.AggregateMemory.RecursiveReadbackControls
open SourceLayout
open FixtureData
set_option maxHeartbeats 4000000
set_option maxRecDepth 4096














private theorem except_success_projection {ε : Type _} {α : Type _}
    (result : Except ε α) (fallback : α) (success : ∃ value, result = .ok value) :
    result = .ok (result.toOption.getD fallback) := by
  obtain ⟨value, run⟩ := success
  cases run
  rfl

private theorem fieldsEncoded_cons_exists
    (offset : Nat) (plan : Plan) (fields : List (Nat × Plan))
    (value : Value) (values : List Value) (before child : Image)
    (encoded : encode .le64 none plan value false = .ok child)
    (fits : offset + child.bytes.size ≤ before.bytes.size)
    (later : ∀ next : Image, next.bytes.size = before.bytes.size →
      ∃ after, FieldsEncoded .le64 none fields values false next after) :
    ∃ after, FieldsEncoded .le64 none ((offset,plan) :: fields) (value :: values) false before after := by
  obtain ⟨bytes,written⟩ := ImageOverwrite.exists_of_fits before.bytes offset child.bytes fits
  let next : Image :=
    { bytes := bytes, unwritten := before.unwritten ++ child.unwritten.map (fun (start,count) => (offset + start,count)) }
  have nextExtent : next.bytes.size = before.bytes.size := written.extent
  obtain ⟨after,rest⟩ := later next nextExtent
  exact ⟨after,FieldsEncoded.cons_iff.mpr ⟨child,bytes,encoded,written,rest⟩⟩

private theorem element_encoding_success :
    ∃ image, encode .le64 none element elementInput false = .ok image := by
  let byteBytes : List UInt8 := encodeIntBytes (truncateUnsigned 513 8) (8 / 8)
  let byteImage : Image := { bytes := ByteImage.ofList (byteBytes.map some) }
  let boolImage : Image := { bytes := ByteImage.ofList (([0] : List UInt8).map some) }
  let pointerBytes : List UInt8 := encodeIntBytes (Int.ofNat 1025) (ByteModel.pointerBytes .le64)
  let pointerImage : Image := { bytes := ByteImage.ofList (pointerBytes.map some) }
  have byteRun : encode .le64 none byte (.int 8 513) false = .ok byteImage := by
    have size : byteBytes.length = 1 :=
      _root_.TrustIr.encodeIntBytes_length (truncateUnsigned 513 8) (8 / 8)
    exact encode_integer_leaf_of_memory .le64 none .U8 ⟨1,1⟩ 8 513 byteBytes rfl rfl size
      (_root_.TrustIr.encodeMemory_integer_residue .le64 none .U8 8 513 rfl)
  have boolRun : encode .le64 none boolean (.bool false) false = .ok boolImage := by
    exact encode_boolean_leaf_of_memory .le64 none ⟨1,1⟩ false [0] rfl
      (by trustIrCompilerProof { exact rfl } { exact by trustIrReduce })
  have pointerRun : encode .le64 none pointer (.ptr 1025 (some ⟨99⟩)) false = .ok pointerImage := by
    have bound : 1025 < ByteModel.addressLimit .le64 := by decide
    have size : pointerBytes.length = 8 :=
      _root_.TrustIr.encodeIntBytes_length (Int.ofNat 1025) (ByteModel.pointerBytes .le64)
    exact encode_pointer_leaf_of_memory .le64 none .Ptr ⟨8,8⟩ (.ptr 1025 (some ⟨99⟩))
      pointerBytes rfl (.inl ⟨1025,some ⟨99⟩,rfl⟩) size
      (_root_.TrustIr.encodeMemory_pointer_word .le64 none .Ptr 1025 (some ⟨99⟩) rfl bound)
  have byteExtent : byteImage.bytes.size = 1 := encode_extent .le64 none byte (.int 8 513) false byteImage byteRun
  have boolExtent : boolImage.bytes.size = 1 := encode_extent .le64 none boolean (.bool false) false boolImage boolRun
  have pointerExtent : pointerImage.bytes.size = 8 :=
    encode_extent .le64 none pointer (.ptr 1025 (some ⟨99⟩)) false pointerImage pointerRun
  let initial : Image := { bytes := ByteImage.fill 16 none }
  have initialExtent : initial.bytes.size = 16 := ByteImage.size_fill 16 none
  obtain ⟨image,row⟩ : ∃ image, FieldsEncoded .le64 none elementFields
      [.int 8 513,.bool false,.ptr 1025 (some ⟨99⟩)] false initial image := by
    change ∃ image, FieldsEncoded .le64 none [(0,byte),(1,boolean),(8,pointer)]
      [.int 8 513,.bool false,.ptr 1025 (some ⟨99⟩)] false initial image
    refine fieldsEncoded_cons_exists 0 byte [(1,boolean),(8,pointer)] (.int 8 513)
      [.bool false,.ptr 1025 (some ⟨99⟩)] initial byteImage byteRun (by omega) ?_
    intro first firstExtent
    refine fieldsEncoded_cons_exists 1 boolean [(8,pointer)] (.bool false)
      [.ptr 1025 (some ⟨99⟩)] first boolImage boolRun (by omega) ?_
    intro second secondExtent
    refine fieldsEncoded_cons_exists 8 pointer [] (.ptr 1025 (some ⟨99⟩)) []
      second pointerImage pointerRun (by omega) ?_
    intro third thirdExtent
    exact ⟨third,FieldsEncoded.nil_iff.mpr ⟨rfl,rfl⟩⟩
  exact ⟨image,encode_fields_of_components .le64 none elementTy ⟨16,8⟩ elementFields
    [.int 8 513,.bool false,.ptr 1025 (some ⟨99⟩)] false image row⟩

private theorem elementReady : ReadbackInput .le64 none memory element elementInput :=
  ReadbackInput.fields_of_pairs elementTy ⟨16,8⟩ elementFields _
    (.cons (.scalar (.integer .U8 ⟨1,1⟩ 8 513 rfl rfl rfl))
      (.cons (.scalar (.boolean false)) (.cons (.scalar (.pointer .Ptr ⟨8,8⟩ 1025 (some ⟨99⟩) rfl (by decide) rfl)) .nil)))

private def nestedTy : Ty := .Array ⟨1⟩ 2
private def nestedPlan : Plan := .array nestedTy ⟨96,8⟩ 2 array
private def nestedInput : Value := .array (CompactArray.Packed.uniform 2 (.array arrayValues))
private def nestedSource : Environment := { types := [some elementTy,some arrayTy] }
private def nestedStored : Image :=
  (encode .le64 none nestedPlan nestedInput false).toOption.getD { bytes := ByteImage.empty }
private theorem nestedPrepared : (prepare nestedSource []).query nestedTy = .ok nestedPlan := by
  trustIrCompilerProof {
    exact rfl
  } {
    exact by trustIrReduce
  }

private theorem nestedEncoded : encode .le64 none nestedPlan nestedInput false = .ok nestedStored := by
  obtain ⟨elementImage,elementRun⟩ := element_encoding_success
  have elementExtent : elementImage.bytes.size = 16 :=
    encode_extent .le64 none element elementInput false elementImage elementRun
  let arrayImage : Image := { bytes := elementImage.bytes.tile 3 }
  have arrayRun : encode .le64 none array (.array arrayValues) false = .ok arrayImage := by
    exact encode_uniform_array .le64 none arrayTy ⟨48,8⟩ 3 element elementInput elementImage
      (by decide) elementRun (by
        change 48 = elementImage.bytes.size * 3
        omega)
  have arrayExtent : arrayImage.bytes.size = 48 :=
    encode_extent .le64 none array (.array arrayValues) false arrayImage arrayRun
  let image : Image := { bytes := arrayImage.bytes.tile 2 }
  have run : encode .le64 none nestedPlan nestedInput false = .ok image := by
    exact encode_uniform_array .le64 none nestedTy ⟨96,8⟩ 2 array (.array arrayValues) arrayImage
      (by decide) arrayRun (by
        change 96 = arrayImage.bytes.size * 2
        omega)
  exact except_success_projection (encode .le64 none nestedPlan nestedInput false)
    { bytes := ByteImage.empty } ⟨image,run⟩

private theorem nestedReady : ReadbackInput .le64 none memory nestedPlan nestedInput :=
  ReadbackInput.array_uniform nestedTy ⟨96,8⟩ 2 array (.array arrayValues)
    (ReadbackInput.array_uniform arrayTy ⟨48,8⟩ 3 element elementInput elementReady)

theorem arrays_of_mixed_arrays_readback :
    ∃ output, decode .le64 none memory nestedPlan nestedStored.bytes = .ok output ∧ ValueReadback .le64 memory nestedInput output :=
  prepared_recursive_readback nestedSource [] nestedTy nestedPlan nestedPrepared .le64 none memory nestedInput nestedReady
    (by intro layout width raw impossible; cases impossible) nestedStored nestedEncoded
end TrustIr.AggregateMemory.RecursiveReadbackControls
