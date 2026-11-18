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

























private def source : Environment := { types := [some elementTy] }
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 4096 in
private theorem prepared : (prepare source []).query rootTy = .ok root := by
  trustIrCompilerProof {
    exact rfl
  } {
    exact by trustIrReduce
  }

private def stored : Image :=
  (encode .le64 none root input false).toOption.getD { bytes := ByteImage.empty }
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

private theorem tail_encoding_success :
    ∃ image, encode .le64 none tail tailInput false = .ok image := by
  let pointerBytes : List UInt8 := encodeIntBytes (Int.ofNat 0) (ByteModel.pointerBytes .le64)
  let pointerImage : Image := { bytes := ByteImage.ofList (pointerBytes.map some) }
  let charBytes : List UInt8 := encodeIntBytes (truncateUnsigned 55296 32) (32 / 8)
  let charImage : Image := { bytes := ByteImage.ofList (charBytes.map some) }
  have pointerRun : encode .le64 none pointer (.ptr 0 (some ⟨99⟩)) false = .ok pointerImage := by
    have bound : 0 < ByteModel.addressLimit .le64 := by decide
    have size : pointerBytes.length = 8 :=
      _root_.TrustIr.encodeIntBytes_length (Int.ofNat 0) (ByteModel.pointerBytes .le64)
    exact encode_pointer_leaf_of_memory .le64 none .Ptr ⟨8,8⟩ (.ptr 0 (some ⟨99⟩))
      pointerBytes rfl (.inl ⟨0,some ⟨99⟩,rfl⟩) size
      (_root_.TrustIr.encodeMemory_pointer_word .le64 none .Ptr 0 (some ⟨99⟩) rfl bound)
  have charRun : encode .le64 none character (.int 32 55296) false = .ok charImage := by
    have size : charBytes.length = 4 :=
      _root_.TrustIr.encodeIntBytes_length (truncateUnsigned 55296 32) (32 / 8)
    exact encode_integer_leaf_of_memory .le64 none .Char ⟨4,4⟩ 32 55296 charBytes rfl rfl size
      (_root_.TrustIr.encodeMemory_integer_residue .le64 none .Char 32 55296 rfl)
  have pointerExtent : pointerImage.bytes.size = 8 :=
    encode_extent .le64 none pointer (.ptr 0 (some ⟨99⟩)) false pointerImage pointerRun
  have charExtent : charImage.bytes.size = 4 :=
    encode_extent .le64 none character (.int 32 55296) false charImage charRun
  let initial : Image := { bytes := ByteImage.fill 16 none }
  have initialExtent : initial.bytes.size = 16 := ByteImage.size_fill 16 none
  obtain ⟨image,row⟩ : ∃ image, FieldsEncoded .le64 none tailFields
      [.ptr 0 (some ⟨99⟩),.int 32 55296] false initial image := by
    change ∃ image, FieldsEncoded .le64 none [(0,pointer),(8,character)]
      [.ptr 0 (some ⟨99⟩),.int 32 55296] false initial image
    refine fieldsEncoded_cons_exists 0 pointer [(8,character)] (.ptr 0 (some ⟨99⟩))
      [.int 32 55296] initial pointerImage pointerRun (by omega) ?_
    intro first firstExtent
    refine fieldsEncoded_cons_exists 8 character [] (.int 32 55296) []
      first charImage charRun (by omega) ?_
    intro second secondExtent
    exact ⟨second,FieldsEncoded.nil_iff.mpr ⟨rfl,rfl⟩⟩
  exact ⟨image,encode_fields_of_components .le64 none tailTy ⟨16,8⟩ tailFields
    [.ptr 0 (some ⟨99⟩),.int 32 55296] false image row⟩

set_option maxRecDepth 4096 in
private theorem encoded : encode .le64 none root input false = .ok stored := by
  obtain ⟨elementImage,elementRun⟩ := element_encoding_success
  have elementExtent : elementImage.bytes.size = 16 :=
    encode_extent .le64 none element elementInput false elementImage elementRun
  let arrayImage : Image := { bytes := elementImage.bytes.tile 3 }
  have arrayRun : encode .le64 none array (.array arrayValues) false = .ok arrayImage := by
    exact encode_uniform_array .le64 none arrayTy ⟨48,8⟩ 3 element elementInput elementImage
      (by decide) elementRun (by
        change 48 = elementImage.bytes.size * 3
        omega)
  obtain ⟨tailImage,tailRun⟩ := tail_encoding_success
  let boolImage : Image := { bytes := ByteImage.ofList (([1] : List UInt8).map some) }
  let fatBytes : List UInt8 :=
    encodeIntBytes (Int.ofNat 1034) (ByteModel.pointerBytes .le64) ++
      encodeIntBytes (truncateUnsigned (-1) (ByteModel.pointerBits .le64)) (ByteModel.pointerBytes .le64)
  let fatImage : Image := { bytes := ByteImage.ofList (fatBytes.map some) }
  have boolRun : encode .le64 none boolean (.bool true) false = .ok boolImage := by
    exact encode_boolean_leaf_of_memory .le64 none ⟨1,1⟩ true [1] rfl
      (by trustIrCompilerProof { exact rfl } { exact by trustIrReduce })
  have fatRun : encode .le64 none fat (.fatPtr 1034 (some ⟨99⟩) (.int 64 (-1))) false = .ok fatImage := by
    have bound : 1034 < ByteModel.addressLimit .le64 := by decide
    have size : fatBytes.length = 16 := by
      change (encodeIntBytes (Int.ofNat 1034) (ByteModel.pointerBytes .le64) ++
        encodeIntBytes (truncateUnsigned (-1) (ByteModel.pointerBits .le64)) (ByteModel.pointerBytes .le64)).length = 16
      simp only [List.length_append,_root_.TrustIr.encodeIntBytes_length]
      change 8 + 8 = 16
      rfl
    exact encode_fat_pointer_leaf_of_memory .le64 none kind ⟨16,8⟩ 1034 (some ⟨99⟩) (.int 64 (-1))
      fatBytes (_root_.TrustIr.fat_length_store_valid .le64 kind 1034 (some ⟨99⟩) (-1) rfl bound) size
      (_root_.TrustIr.encodeMemory_fat_length_words .le64 none kind 1034 (some ⟨99⟩) (-1) rfl bound)
  have boolExtent : boolImage.bytes.size = 1 := encode_extent .le64 none boolean (.bool true) false boolImage boolRun
  have arrayExtent : arrayImage.bytes.size = 48 :=
    encode_extent .le64 none array (.array arrayValues) false arrayImage arrayRun
  have fatExtent : fatImage.bytes.size = 16 :=
    encode_extent .le64 none fat (.fatPtr 1034 (some ⟨99⟩) (.int 64 (-1))) false fatImage fatRun
  have tailExtent : tailImage.bytes.size = 16 := encode_extent .le64 none tail tailInput false tailImage tailRun
  let initial : Image := { bytes := ByteImage.fill 88 none }
  have initialExtent : initial.bytes.size = 88 := ByteImage.size_fill 88 none
  obtain ⟨image,row⟩ : ∃ image, FieldsEncoded .le64 none rootFields
      [.bool true,.array arrayValues,.fatPtr 1034 (some ⟨99⟩) (.int 64 (-1)),tailInput] false initial image := by
    change ∃ image, FieldsEncoded .le64 none [(0,boolean),(8,array),(56,fat),(72,tail)]
      [.bool true,.array arrayValues,.fatPtr 1034 (some ⟨99⟩) (.int 64 (-1)),tailInput] false initial image
    refine fieldsEncoded_cons_exists 0 boolean [(8,array),(56,fat),(72,tail)] (.bool true)
      [.array arrayValues,.fatPtr 1034 (some ⟨99⟩) (.int 64 (-1)),tailInput] initial boolImage boolRun (by omega) ?_
    intro first firstExtent
    refine fieldsEncoded_cons_exists 8 array [(56,fat),(72,tail)] (.array arrayValues)
      [.fatPtr 1034 (some ⟨99⟩) (.int 64 (-1)),tailInput] first arrayImage arrayRun (by omega) ?_
    intro second secondExtent
    refine fieldsEncoded_cons_exists 56 fat [(72,tail)] (.fatPtr 1034 (some ⟨99⟩) (.int 64 (-1)))
      [tailInput] second fatImage fatRun (by omega) ?_
    intro third thirdExtent
    refine fieldsEncoded_cons_exists 72 tail [] tailInput [] third tailImage tailRun (by omega) ?_
    intro fourth fourthExtent
    exact ⟨fourth,FieldsEncoded.nil_iff.mpr ⟨rfl,rfl⟩⟩
  have run : encode .le64 none root input false = .ok image :=
    encode_fields_of_components .le64 none rootTy ⟨88,8⟩ rootFields
      [.bool true,.array arrayValues,.fatPtr 1034 (some ⟨99⟩) (.int 64 (-1)),tailInput] false image row
  exact except_success_projection (encode .le64 none root input false)
    { bytes := ByteImage.empty } ⟨image,run⟩

private theorem elementReady : ReadbackInput .le64 none memory element elementInput :=
  ReadbackInput.fields_of_pairs elementTy ⟨16,8⟩ elementFields _
    (.cons (.scalar (.integer .U8 ⟨1,1⟩ 8 513 rfl rfl rfl))
      (.cons (.scalar (.boolean false)) (.cons (.scalar (.pointer .Ptr ⟨8,8⟩ 1025 (some ⟨99⟩) rfl (by decide) rfl)) .nil)))
private theorem tailReady : ReadbackInput .le64 none memory tail tailInput :=
  ReadbackInput.fields_of_pairs tailTy ⟨16,8⟩ tailFields _
    (.cons (.scalar (.pointer .Ptr ⟨8,8⟩ 0 (some ⟨99⟩) rfl (by decide) rfl))
      (.cons (.scalar (.integer .Char ⟨4,4⟩ 32 55296 rfl rfl rfl)) .nil))
private theorem rootReady : ReadbackInput .le64 none memory root input :=
  ReadbackInput.fields_of_pairs rootTy ⟨88,8⟩ rootFields _
    (.cons (.scalar (.boolean true))
      (.cons (ReadbackInput.array_uniform arrayTy ⟨48,8⟩ 3 element elementInput elementReady)
        (.cons (.scalar (.fatLength kind ⟨16,8⟩ 1034 (some ⟨99⟩) (-1) rfl (by decide) rfl)) (.cons tailReady .nil))))
private theorem topReady : TopCharReady root input := by intro layout width raw impossible; cases impossible

theorem prepared_mixed_recursive_readback :
    ∃ output, decode .le64 none memory root stored.bytes = .ok output ∧ ValueReadback .le64 memory input output :=
  prepared_recursive_readback source [] rootTy root prepared .le64 none memory input rootReady topReady stored encoded

theorem mixed_nested_recursive_readback :
    ∃ output, ChildDecoded .le64 none memory root stored.bytes output ∧ ValueReadback .le64 memory input output :=
  prepared_recursive_child_readback source [] rootTy root prepared .le64 none memory input rootReady stored encoded

private def reconstructed : ByteImage := ByteImage.source stored.bytes.size stored.bytes.get
private theorem reconstructedBytes (index : Nat) : reconstructed.get index = stored.bytes.get index :=
  source_image_observations stored.bytes index

theorem distinct_byte_representation_readback :
    ∃ output, decode .le64 none memory root reconstructed = .ok output ∧ ValueReadback .le64 memory input output :=
  rootReady.top_readback source (prepared_plan_origin source [] rootTy root prepared).own stored encoded reconstructed
    (encode_extent .le64 none root input false stored encoded) reconstructedBytes topReady

private def project (rootPosition childPosition : Nat) : Except SemError (Option Value) := do
  let output ← decode .le64 none memory root stored.bytes
  match output with
  | .aggregate fields =>
    match (trustIrListGet? fields rootPosition) with
    | some (.array values) =>
      match values.get? 0 with
      | some (.aggregate fields) => pure ((trustIrListGet? fields childPosition))
      | _ => pure none
    | some (.aggregate fields) => pure ((trustIrListGet? fields childPosition))
    | some value => pure (some value)
    | _ => pure none
  | _ => pure none

-- Extract actual logical children; no compact representation identity or
-- global functionality of ValueReadback is assumed.
private theorem aggregate_readback_child {inputs : List Value} {output : Value}
    (related : ValueReadback .le64 memory (.aggregate inputs) output)
    (position : Nat) (input : Value) (inside : position < inputs.length)
    (selected : (trustIrListGet? inputs position) = some input) :
    ∃ outputs child, output = .aggregate outputs ∧
      (trustIrListGet? outputs position) = some child ∧ ValueReadback .le64 memory input child := by
  cases related with
  | aggregate inputs outputs census children =>
    have outputInside : position < outputs.length := by
      rw [← census]
      exact inside
    have found : (trustIrListGet? outputs position) = some (outputs.get ⟨position,outputInside⟩) :=
      TrustIr.CompilerCompat.listGet?_eq_get outputInside
    exact ⟨outputs,outputs.get ⟨position,outputInside⟩,rfl,found,
      children position input _ selected found⟩

private theorem array_readback_first {inputs : CompactArray.Packed Value} {output : Value}
    (related : ValueReadback .le64 memory (.array inputs) output) (input : Value)
    (inside : 0 < inputs.size) (selected : inputs.tree.get? 0 = some input) :
    ∃ outputs child, output = .array outputs ∧
      outputs.get? 0 = some child ∧ ValueReadback .le64 memory input child := by
  cases related with
  | array inputs outputs census children =>
    have outputInside : 0 < outputs.size := by
      rw [← census]
      exact inside
    obtain ⟨child,found⟩ := CompactArray.Packed.get_exists outputs 0 outputInside
    exact ⟨outputs,child,rfl,found,children 0 input child inside selected found⟩

set_option maxRecDepth 4096 in
theorem nested_pointer_uses_receiving_memory : project 1 2 = .ok (some (.ptr 1025 (some ⟨7⟩))) := by
  obtain ⟨output,run,related⟩ := prepared_mixed_recursive_readback
  obtain ⟨fields,arrayOutput,shape,arrayGet,arrayRelated⟩ :=
    aggregate_readback_child related 1 (.array arrayValues) (by decide) rfl
  obtain ⟨values,elementOutput,arrayShape,firstGet,elementRelated⟩ :=
    array_readback_first arrayRelated elementInput (by decide) rfl
  obtain ⟨elementFields,pointerOutput,elementShape,pointerGet,pointerRelated⟩ :=
    aggregate_readback_child elementRelated 2 (.ptr 1025 (some ⟨99⟩)) (by decide) rfl
  cases pointerRelated
  rewrite [project, run]
  dsimp only [Bind.bind, Except.bind, Pure.pure, Except.pure]
  rewrite [shape]
  dsimp only [Bind.bind, Except.bind, Pure.pure, Except.pure]
  rewrite [arrayGet,arrayShape]
  dsimp only [Bind.bind, Except.bind, Pure.pure, Except.pure]
  rewrite [firstGet,elementShape]
  dsimp only [Bind.bind, Except.bind, Pure.pure, Except.pure]
  rewrite [pointerGet]
  rfl

set_option maxRecDepth 4096 in
theorem fat_metadata_uses_declared_kind :
    project 2 0 = .ok (some (.fatPtr 1034 (some ⟨9⟩) (Value.intAt 64 (-1)))) := by
  obtain ⟨output,run,related⟩ := prepared_mixed_recursive_readback
  obtain ⟨fields,fatOutput,shape,fatGet,fatRelated⟩ :=
    aggregate_readback_child related 2 (.fatPtr 1034 (some ⟨99⟩) (.int 64 (-1))) (by decide) rfl
  cases fatRelated with
  | fat _ _ _ _ metadata =>
    cases metadata
    rewrite [project, run]
    dsimp only [Bind.bind, Except.bind, Pure.pure, Except.pure]
    rewrite [shape]
    dsimp only [Bind.bind, Except.bind, Pure.pure, Except.pure]
    rewrite [fatGet]
    rfl

set_option maxRecDepth 4096 in
theorem nested_zero_pointer_canonicalizes : project 3 0 = .ok (some .nullPtr) := by
  obtain ⟨output,run,related⟩ := prepared_mixed_recursive_readback
  obtain ⟨fields,tailOutput,shape,tailGet,tailRelated⟩ :=
    aggregate_readback_child related 3 tailInput (by decide) rfl
  obtain ⟨tailFields,pointerOutput,tailShape,pointerGet,pointerRelated⟩ :=
    aggregate_readback_child tailRelated 0 (.ptr 0 (some ⟨99⟩)) (by decide) rfl
  cases pointerRelated
  rewrite [project, run]
  dsimp only [Bind.bind, Except.bind, Pure.pure, Except.pure]
  rewrite [shape]
  dsimp only [Bind.bind, Except.bind, Pure.pure, Except.pure]
  rewrite [tailGet,tailShape]
  dsimp only [Bind.bind, Except.bind, Pure.pure, Except.pure]
  rewrite [pointerGet]
  rfl

set_option maxRecDepth 4096 in
theorem nested_surrogate_stays_raw : project 3 1 = .ok (some (.int 32 55296)) := by
  obtain ⟨output,run,related⟩ := prepared_mixed_recursive_readback
  obtain ⟨fields,tailOutput,shape,tailGet,tailRelated⟩ :=
    aggregate_readback_child related 3 tailInput (by decide) rfl
  obtain ⟨tailFields,integerOutput,tailShape,integerGet,integerRelated⟩ :=
    aggregate_readback_child tailRelated 1 (.int 32 55296) (by decide) rfl
  cases integerRelated
  rewrite [project, run]
  dsimp only [Bind.bind, Except.bind, Pure.pure, Except.pure]
  rewrite [shape]
  dsimp only [Bind.bind, Except.bind, Pure.pure, Except.pure]
  rewrite [tailGet,tailShape]
  dsimp only [Bind.bind, Except.bind, Pure.pure, Except.pure]
  rewrite [integerGet]
  rfl

set_option maxRecDepth 4096 in
theorem outer_padding_remains_absent : stored.bytes.get 1 = none ∧ stored.bytes.get 7 = none := by
  obtain ⟨values,same,row⟩ :=
    encode_fields_steps .le64 none rootTy ⟨88,8⟩ rootFields input stored encoded
  let laneBytes : ByteImage := ByteImage.fill 7 none
  have initialLane : ByteLane (ByteImage.fill 88 none) 1 laneBytes := by
    refine ⟨?_,?_⟩
    · change 1 + 7 ≤ 88
      decide
    · intro index inside
      change index < 7 at inside
      change (ByteImage.fill 88 none).get (1 + index) = (ByteImage.fill 7 none).get index
      rw [ByteImage.get_fill,ByteImage.get_fill,if_pos (by omega),if_pos inside]
  have separated : FieldsAvoidLane rootFields 1 laneBytes.size := by
    unfold FieldsAvoidLane
    intro field member
    simp only [rootFields,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl | rfl | rfl
    all_goals rfl
  have kept : ByteLane stored.bytes 1 laneBytes :=
    FieldsEncoded.preserves_lane row initialLane separated
  constructor
  · have observed := kept.2 0 (by change 0 < 7; decide)
    exact observed.trans (show laneBytes.get 0 = none from by
      change (ByteImage.fill 7 none).get 0 = none
      rw [ByteImage.get_fill,if_pos (by decide)])
  · have observed := kept.2 6 (by change 6 < 7; decide)
    exact observed.trans (show laneBytes.get 6 = none from by
      change (ByteImage.fill 7 none).get 6 = none
      rw [ByteImage.get_fill,if_pos (by decide)])

/-- Internal fixture certificate: actual root readiness and an actual successful encoding. -/
theorem mixed_root_fixture_support :
    ReadbackInput .le64 none memory root input ∧
    ∃ image : Image, encode .le64 none root input false = .ok image :=
  ⟨rootReady,stored,encoded⟩

end TrustIr.AggregateMemory.RecursiveReadbackControls
