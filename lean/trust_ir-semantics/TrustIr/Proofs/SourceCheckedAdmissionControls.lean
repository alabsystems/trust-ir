-- Copyright 2026 Andrew Yates | Apache-2.0
import TrustIr.Proofs.SourceCheckedAdmission

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

namespace TrustIr.AggregateMemory.SourceCheckedAdmissionControls
open SourceLayout

private def byte : Plan := .leaf .U8 ⟨1,1⟩
private def boolean : Plan := .leaf .Bool ⟨1,1⟩
private def pointer : Plan := .leaf .Ptr ⟨8,8⟩
private def elementTy : Ty := .Tuple [.U8,.Bool,.Ptr]
private def elementFields : List (Nat × Plan) := [(0,byte),(1,boolean),(8,pointer)]
private def element : Plan := .fields elementTy ⟨16,8⟩ elementFields
private def array : Plan := .array (.Array ⟨0⟩ 2) ⟨32,8⟩ 2 element
private def fat : Plan := .leaf (.FatPtr .ContainerLen) ⟨16,8⟩
private def character : Plan := .leaf .Char ⟨4,4⟩
private def function : Plan := .leaf (.Func ⟨0⟩) ⟨8,8⟩
private def unit : Plan := .leaf .Unit ⟨0,1⟩
private def rootTy : Ty := .Tuple [.Array ⟨0⟩ 2,.FatPtr .ContainerLen,.Char,.Func ⟨0⟩,.Unit]
private def fields : List (Nat × Plan) := [(0,array),(32,fat),(48,character),(56,function),(64,unit)]
private def root : Plan := .fields rootTy ⟨64,8⟩ fields
private def source : Environment := { types := [some elementTy], enums := [] }
private def order : FunctionAddressOrder := some [⟨42⟩,⟨7⟩]
private def context (base : EvalContext) : EvalContext :=
  { base with
    byteModel := .le64
    functionOrder := order
    valueSource := FunctionItemPresence.prepare { base.valueSource.source with types := [some elementTy] } }
private def elementInput : Value := .aggregate [.int 8 7,.bool true,.ptr 1025 (some ⟨99⟩)]
private def input : Value := .aggregate [.array (.uniform 2 elementInput),
  .fatPtr 1034 (some ⟨99⟩) (.int 64 3),.int 32 128512,.fnDef ⟨0⟩ ⟨42⟩,.aggregate []]
private def stored : Image :=
  (encode .le64 order root input false).toOption.getD { bytes := ByteImage.empty }
private theorem prepared : (prepare source []).query rootTy = .ok root := by
  trustIrCompilerProof {
    dsimp only [source,root,rootTy,fields,array,element,elementTy,elementFields,byte,boolean,pointer,fat,character,function,unit]
    rfl
  } {
    dsimp only [source,root,rootTy,fields,array,element,elementTy,elementFields,byte,boolean,pointer,fat,character,function,unit]
    trustIrReduce
  }

private theorem checkedSuccessProjection {ε : Type _} {α : Type _}
    (result : Except ε α) (fallback : α) (success : ∃ value, result = .ok value) :
    result = .ok (result.toOption.getD fallback) := by
  obtain ⟨value, run⟩ := success
  cases run
  rfl

private theorem checkedIntegerEncoding (model : ByteModel) (ty : Ty) (layout : MemoryTypeLayout)
    (width : Nat) (raw : Int) (integer : ty.isInteger = true)
    (typed : ty.bitWidthFor model = some width) (extent : width / 8 = layout.size) :
    ∃ image, encode model order (.leaf ty layout) (.int width raw) false = .ok image := by
  let bytes := encodeIntBytes (truncateUnsigned raw width) (width / 8)
  refine ⟨{ bytes := ByteImage.ofList (bytes.map some) }, ?_⟩
  exact encode_integer_leaf_of_memory model order ty layout width raw bytes integer typed
    ((_root_.TrustIr.encodeIntBytes_length _ _).trans extent)
    (_root_.TrustIr.encodeMemory_integer_residue model order ty width raw integer)

private theorem checkedPointerEncoding (model : ByteModel) (layout : MemoryTypeLayout)
    (extent : model.pointerBytes = layout.size) (bound : 1025 < model.addressLimit) :
    ∃ image, encode model order (.leaf .Ptr layout) (.ptr 1025 (some ⟨99⟩)) false = .ok image := by
  let bytes := encodeIntBytes (Int.ofNat 1025) model.pointerBytes
  refine ⟨{ bytes := ByteImage.ofList (bytes.map some) }, ?_⟩
  exact encode_pointer_leaf_of_memory model order .Ptr layout (.ptr 1025 (some ⟨99⟩)) bytes rfl
    (.inl ⟨1025, some ⟨99⟩, rfl⟩) ((_root_.TrustIr.encodeIntBytes_length _ _).trans extent)
    (_root_.TrustIr.encodeMemory_pointer_word model order .Ptr 1025 (some ⟨99⟩) rfl bound)

private theorem checkedBooleanEncoding (model : ByteModel) :
    ∃ image, encode model order boolean (.bool true) false = .ok image := by
  refine ⟨{ bytes := ByteImage.ofList (([1] : List UInt8).map some) }, ?_⟩
  exact encode_boolean_leaf_of_memory model order ⟨1,1⟩ true [1] rfl
    (by cases model <;> rfl)

private theorem checkedFatEncoding (model : ByteModel) (layout : MemoryTypeLayout)
    (extent : model.pointerBytes + model.pointerBytes = layout.size)
    (bound : 1034 < model.addressLimit)
    (valid : fatPtrStoreValueValidFor model (.FatPtr .ContainerLen)
      (.fatPtr 1034 (some ⟨99⟩) (.int model.pointerBits 3)) = true) :
    ∃ image, encode model order (.leaf (.FatPtr .ContainerLen) layout)
      (.fatPtr 1034 (some ⟨99⟩) (.int model.pointerBits 3)) false = .ok image := by
  let bytes := encodeIntBytes (Int.ofNat 1034) model.pointerBytes ++
    encodeIntBytes (truncateUnsigned 3 model.pointerBits) model.pointerBytes
  have size : bytes.length = layout.size := by
    dsimp only [bytes]
    rw [List.length_append, _root_.TrustIr.encodeIntBytes_length, _root_.TrustIr.encodeIntBytes_length]
    exact extent
  refine ⟨{ bytes := ByteImage.ofList (bytes.map some) }, ?_⟩
  exact encode_fat_pointer_leaf_of_memory model order .ContainerLen layout 1034 (some ⟨99⟩)
    (.int model.pointerBits 3) bytes valid size
    (_root_.TrustIr.encodeMemory_fat_length_words model order .ContainerLen 1034 (some ⟨99⟩) 3 rfl bound)

private theorem checkedFunctionEncoding (model : ByteModel) (layout : MemoryTypeLayout)
    (extent : model.pointerBytes = layout.size) (bound : 0 + 1 < model.addressLimit) :
    ∃ image, encode model order (.leaf (.Func ⟨0⟩) layout) (.fnDef ⟨0⟩ ⟨42⟩) false = .ok image := by
  let bytes := encodeIntBytes (Int.ofNat (0 + 1)) model.pointerBytes
  refine ⟨{ bytes := ByteImage.ofList (bytes.map some) }, ?_⟩
  exact encode_function_leaf_of_memory model order ⟨0⟩ layout (.fnDef ⟨0⟩ ⟨42⟩) bytes
    (.inl ⟨⟨42⟩, rfl⟩) ((_root_.TrustIr.encodeIntBytes_length _ _).trans extent)
    (_root_.TrustIr.encodeFunctionWord model [⟨42⟩,⟨7⟩] ⟨0⟩ ⟨42⟩ 0 rfl bound)

private theorem checkedUnitEncoding (model : ByteModel) :
    ∃ image, encode model order unit (.aggregate []) false = .ok image := by
  trustIrCompilerProof {
    cases model <;> exact ⟨{ bytes := ByteImage.ofList [] }, rfl⟩
  } {
    cases model <;> refine ⟨{ bytes := ByteImage.ofList [] }, ?_⟩ <;>
      (rw [encode.eq_def] <;> rfl)
  }

private theorem checkedFields3Encoding (model : ByteModel) (ty : Ty) (layout : MemoryTypeLayout)
    (offset0 : Nat) (plan0 : Plan) (value0 : Value)
    (offset1 : Nat) (plan1 : Plan) (value1 : Value)
    (offset2 : Nat) (plan2 : Plan) (value2 : Value)
    (child0 : ∃ image, encode model order plan0 value0 false = .ok image)
    (child1 : ∃ image, encode model order plan1 value1 false = .ok image)
    (child2 : ∃ image, encode model order plan2 value2 false = .ok image)
    (fit0 : offset0 + plan0.layout.size ≤ layout.size)
    (fit1 : offset1 + plan1.layout.size ≤ layout.size)
    (fit2 : offset2 + plan2.layout.size ≤ layout.size) :
    ∃ image, encode model order (.fields ty layout [(offset0,plan0),(offset1,plan1),(offset2,plan2)])
      (.aggregate [value0,value1,value2]) false = .ok image := by
  apply encode_fields_exists_of_children model order ty layout [(offset0,plan0),(offset1,plan1),(offset2,plan2)] [value0,value1,value2] false rfl
  · intro field value member
    simp only [List.zip_cons_cons, List.zip_nil_left, List.mem_cons, List.not_mem_nil,
      or_false, Prod.mk.injEq] at member
    rcases member with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · exact child0
    · exact child1
    · exact child2
  · intro field member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl
    · exact fit0
    · exact fit1
    · exact fit2

private theorem checkedFields5Encoding (model : ByteModel) (ty : Ty) (layout : MemoryTypeLayout)
    (offset0 : Nat) (plan0 : Plan) (value0 : Value)
    (offset1 : Nat) (plan1 : Plan) (value1 : Value)
    (offset2 : Nat) (plan2 : Plan) (value2 : Value)
    (offset3 : Nat) (plan3 : Plan) (value3 : Value)
    (offset4 : Nat) (plan4 : Plan) (value4 : Value)
    (child0 : ∃ image, encode model order plan0 value0 false = .ok image)
    (child1 : ∃ image, encode model order plan1 value1 false = .ok image)
    (child2 : ∃ image, encode model order plan2 value2 false = .ok image)
    (child3 : ∃ image, encode model order plan3 value3 false = .ok image)
    (child4 : ∃ image, encode model order plan4 value4 false = .ok image)
    (fit0 : offset0 + plan0.layout.size ≤ layout.size)
    (fit1 : offset1 + plan1.layout.size ≤ layout.size)
    (fit2 : offset2 + plan2.layout.size ≤ layout.size)
    (fit3 : offset3 + plan3.layout.size ≤ layout.size)
    (fit4 : offset4 + plan4.layout.size ≤ layout.size) :
    ∃ image, encode model order (.fields ty layout [(offset0,plan0),(offset1,plan1),(offset2,plan2),(offset3,plan3),(offset4,plan4)])
      (.aggregate [value0,value1,value2,value3,value4]) false = .ok image := by
  apply encode_fields_exists_of_children model order ty layout [(offset0,plan0),(offset1,plan1),(offset2,plan2),(offset3,plan3),(offset4,plan4)] [value0,value1,value2,value3,value4] false rfl
  · intro field value member
    simp only [List.zip_cons_cons, List.zip_nil_left, List.mem_cons, List.not_mem_nil,
      or_false, Prod.mk.injEq] at member
    rcases member with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · exact child0
    · exact child1
    · exact child2
    · exact child3
    · exact child4
  · intro field member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl
    · exact fit0
    · exact fit1
    · exact fit2
    · exact fit3
    · exact fit4

private theorem checkedRootEncoding :
    ∃ image, encode .le64 order root input false = .ok image := by
  have byteRun := checkedIntegerEncoding .le64 .U8 ⟨1,1⟩ 8 7 rfl rfl rfl
  have boolRun := checkedBooleanEncoding .le64
  have pointerRun := checkedPointerEncoding .le64 ⟨8,8⟩ rfl (by decide)
  obtain ⟨elementImage, elementRun⟩ : ∃ image, encode .le64 order element elementInput false = .ok image :=
    checkedFields3Encoding .le64 elementTy ⟨16,8⟩
      0 byte (.int 8 7) 1 boolean (.bool true) 8 pointer (.ptr 1025 (some ⟨99⟩))
      byteRun boolRun pointerRun (by decide) (by decide) (by decide)
  have elementExtent : elementImage.bytes.size = 16 :=
    encode_extent .le64 order element elementInput false elementImage elementRun
  have arrayRun : ∃ image, encode .le64 order array (.array (.uniform 2 elementInput)) false = .ok image := by
    refine ⟨{ bytes := elementImage.bytes.tile 2 }, ?_⟩
    exact encode_uniform_array .le64 order (.Array ⟨0⟩ 2) ⟨32,8⟩ 2 element elementInput elementImage
      (by decide) elementRun (by rw [elementExtent])
  have fatRun := checkedFatEncoding .le64 ⟨16,8⟩ rfl (by decide) (by decide)
  have charRun := checkedIntegerEncoding .le64 .Char ⟨4,4⟩ 32 128512 rfl rfl rfl
  have functionRun := checkedFunctionEncoding .le64 ⟨8,8⟩ rfl (by decide)
  have unitRun := checkedUnitEncoding .le64
  exact checkedFields5Encoding .le64 rootTy ⟨64,8⟩
    0 array (.array (.uniform 2 elementInput))
    32 fat (.fatPtr 1034 (some ⟨99⟩) (.int 64 3))
    48 character (.int 32 128512)
    56 function (.fnDef ⟨0⟩ ⟨42⟩)
    64 unit (.aggregate [])
    arrayRun fatRun charRun functionRun unitRun
    (by decide) (by decide) (by decide) (by decide) (by decide)

private theorem encoded : encode .le64 order root input false = .ok stored :=
  checkedSuccessProjection (encode .le64 order root input false)
    { bytes := ByteImage.empty } checkedRootEncoding

private theorem elementShape (base : EvalContext) : SourceReadbackShape (context base) element := by
  apply SourceReadbackShape.tuple [.U8,.Bool,.Ptr] ⟨16,8⟩ elementFields
  intro offset child member
  change (offset,child) ∈ [(0,byte),(1,boolean),(8,pointer)] at member
  simp only [List.mem_cons,List.not_mem_nil,or_false,Prod.mk.injEq] at member
  rcases member with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · exact .scalar (.integer .U8 ⟨1,1⟩ rfl)
  · exact .scalar .boolean
  · exact .scalar (.pointer .Ptr ⟨8,8⟩ rfl)
private theorem rootShape (base : EvalContext) : SourceReadbackShape (context base) root := by
  apply SourceReadbackShape.tuple _ ⟨64,8⟩ fields
  intro offset child member
  change (offset,child) ∈ [(0,array),(32,fat),(48,character),(56,function),(64,unit)] at member
  simp only [List.mem_cons,List.not_mem_nil,or_false,Prod.mk.injEq] at member
  rcases member with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · exact .array ⟨0⟩ ⟨32,8⟩ 2 element rfl (elementShape base)
  · exact .scalar (.fat .ContainerLen ⟨16,8⟩)
  · exact .scalar (.integer .Char ⟨4,4⟩ rfl)
  · exact .scalar (.function ⟨0⟩ ⟨8,8⟩)
  · exact .scalar .unit

private theorem inputDepth : input.depth = 4 := by
  trustIrCompilerProof {
    simp [Value.depth,input,elementInput,Value.depthSpec,valueListDepthSpec,arrayTreeDepthRangeSpec,CompactArray.Packed.uniform]
    rfl
  } {
    simp [Value.depth,input,elementInput,Value.depthSpec,valueListDepthSpec,arrayTreeDepthRangeSpec,CompactArray.Packed.uniform]
  }

private theorem checkedAt (base : EvalContext) : checkClosureValueAt (context base) 5 rootTy input = .ok () := by
  dsimp only [context,rootTy,input,elementInput,elementTy,order]
  rfl

theorem actual_recursive_checker_accepts_mixed_parent (base : EvalContext) :
    checkClosureValue (context base) rootTy input = .ok () := by
  unfold checkClosureValue
  rw [inputDepth]
  exact checkedAt base

theorem one_source_check_supplies_recursive_admission (base : EvalContext) :
    ReadbackInput .le64 order Memory.empty root input :=
  (rootShape base).admit order Memory.empty source (prepared_plan_origin source [] rootTy root prepared).own
    5 input stored (checkedAt base) encoded

theorem prepared_mixed_source_readback (base : EvalContext) :
    ∃ output, decode .le64 order Memory.empty root stored.bytes = .ok output ∧ ValueReadback .le64 Memory.empty input output :=
  prepared_checked_value_readback source [] rootTy root prepared (context base) (rootShape base) Memory.empty input stored
    (actual_recursive_checker_accepts_mixed_parent base) encoded

private theorem storedSize : stored.bytes.size = 64 := encode_extent .le64 order root input false stored encoded
private theorem reconstructedObservations (index : Nat) :
    (ByteImage.source 64 stored.bytes.get).get index = stored.bytes.get index := by
  have observed := source_image_observations stored.bytes index
  rw [storedSize] at observed
  exact observed

theorem reconstructed_source_image_readback (base : EvalContext) :
    ∃ output, decode .le64 order Memory.empty root (ByteImage.source 64 stored.bytes.get) = .ok output ∧
      ValueReadback .le64 Memory.empty input output :=
  source_checked_recursive_readback (rootShape base) source (prepared_plan_origin source [] rootTy root prepared).own
    5 order Memory.empty input stored (checkedAt base) encoded
    (ByteImage.source 64 stored.bytes.get) rfl reconstructedObservations

theorem recursive_checker_replaces_separate_scalar_lane_argument (base : EvalContext) :
    ReadbackInput .le64 order Memory.empty byte (.int 8 7) := by
  trustIrCompilerProof {
    exact (ScalarReadbackPlan.integer .U8 ⟨1,1⟩ rfl).admit_of_source_checked (context base) 1 order Memory.empty (.int 8 7)
      { bytes := ByteImage.ofList [some 7] } rfl rfl
  } {
    exact (ScalarReadbackPlan.integer .U8 ⟨1,1⟩ (by trustIrReduce)).admit_of_source_checked (context base) 1 order Memory.empty (.int 8 7)
      { bytes := ByteImage.ofList [some 7] } (by trustIrReduce) (by trustIrReduce)
  }

private def emptySource : Environment := { types := [some .F64], enums := [] }
private def emptyPlan : Plan := .array (.Array ⟨0⟩ 0) ⟨0,8⟩ 0 (.leaf .F64 ⟨8,8⟩)
private def emptyInput : Value := .array (.uniform 0 .uninit)
private def emptyContext (base : EvalContext) : EvalContext :=
  { context base with valueSource := FunctionItemPresence.prepare { (context base).valueSource.source with types := [some .U8] } }
private theorem emptyPrepared : (prepare emptySource []).query (.Array ⟨0⟩ 0) = .ok emptyPlan := by
  trustIrCompilerProof {
    exact rfl
  } {
    exact (by trustIrReduce)
  }

theorem empty_array_ignores_unsupported_unused_template_and_row (base : EvalContext) :
    ∃ output, decode .le64 order Memory.empty emptyPlan ByteImage.empty = .ok output ∧
      ValueReadback .le64 Memory.empty emptyInput output := by
  trustIrCompilerProof {
    exact prepared_checked_value_readback emptySource [] (.Array ⟨0⟩ 0) emptyPlan emptyPrepared (emptyContext base)
      (.emptyArray ⟨0⟩ ⟨0,8⟩ (.leaf .F64 ⟨8,8⟩)) Memory.empty emptyInput { bytes := ByteImage.empty } rfl rfl
  } {
    exact prepared_checked_value_readback emptySource [] (.Array ⟨0⟩ 0) emptyPlan emptyPrepared (emptyContext base)
      (.emptyArray ⟨0⟩ ⟨0,8⟩ (.leaf .F64 ⟨8,8⟩)) Memory.empty emptyInput { bytes := ByteImage.empty } (by trustIrReduce) (by trustIrReduce)
  }

private def byteTuple : Plan := .fields (.Tuple [.U8]) ⟨1,1⟩ [(0,byte)]

theorem tuple_transport_exception_does_not_supply_ordinary_store (base : EvalContext) :
    checkClosureValue (context base) (.Tuple [.U8]) (.aggregate [.uninit]) = .ok () ∧
    encode .le64 order byteTuple (.aggregate [.uninit]) false =
      .error (.ub "memory image: inspecting an unwritten lane") := by
  trustIrCompilerProof {
    exact ⟨rfl,rfl⟩
  } {
    exact ⟨(by trustIrReduce),(by trustIrReduce)⟩
  }

theorem partial_carriers_still_refuse_source_check_and_store (base : EvalContext) :
    checkClosureValue (context base) (.Tuple [.U8]) (.aggregate [.partial [none]]) =
      .error (.ub "closure boundary: uninitialized value") ∧
    encode .le64 order byteTuple (.aggregate [.partial [none]]) false =
      .error (.ub "memory image: inspecting poison") := by
  trustIrCompilerProof {
    exact ⟨rfl,rfl⟩
  } {
    exact ⟨(by trustIrReduce),(by trustIrReduce)⟩
  }

private def forged : Plan := .fields (.Tuple [.U8]) ⟨1,1⟩ [(0,.leaf .Ptr ⟨1,1⟩)]
private def forgedInput : Value := .aggregate [.int 8 7]
private def forgedImage : Image := { bytes := ByteImage.ofList [some 7] }

theorem byte_store_and_checker_do_not_authenticate_field_types (base : EvalContext) :
    checkClosureValue (context base) (.Tuple [.U8]) forgedInput = .ok () ∧
    encode .le64 order forged forgedInput false = .ok forgedImage := by
  trustIrCompilerProof {
    exact ⟨rfl,rfl⟩
  } {
    exact ⟨(by trustIrReduce),(by trustIrReduce)⟩
  }

theorem forged_field_types_have_no_source_origin (environment : Environment) :
    ¬ Plan.Origin (SourceElement environment) (ActualSummary environment) (.Tuple [.U8]) forged := by
  intro origin
  have typed := origin.tuple_types_and_children.1
  change [Ty.Ptr] = [Ty.U8] at typed
  cases typed

private def mismatchedArray : Plan := .array (.Array ⟨0⟩ 1) ⟨1,1⟩ 1 boolean
private def mismatchedInput : Value := .array (.uniform 1 (.int 8 1))
private def mismatchedImage : Image := match encode .le64 order mismatchedArray mismatchedInput false with
  | .ok image => image
  | .error _ => { bytes := ByteImage.empty }

theorem visible_array_row_disagreement_cannot_supply_shape (base : EvalContext) :
    ¬ SourceReadbackShape (emptyContext base) mismatchedArray := by
  intro shape
  cases shape with
  | scalar scalar => cases scalar
  | array id layout count element resolved child =>
    change some Ty.U8 = some Ty.Bool at resolved
    cases resolved

theorem actual_checks_and_storage_do_not_waive_visible_row_agreement (base : EvalContext) :
    checkClosureValue (emptyContext base) (.Array ⟨0⟩ 1) mismatchedInput = .ok () ∧
    encode .le64 order mismatchedArray mismatchedInput false = .ok mismatchedImage := by
  trustIrCompilerProof {
    exact ⟨rfl,rfl⟩
  } {
    exact ⟨(by trustIrReduce),(by trustIrReduce)⟩
  }

/-- A direct target-width scalar bridge; this does not claim native 32-bit ABI
    or a prepared 32-bit source-layout theorem. -/
theorem target32_source_checker_supplies_scalar_admission (base : EvalContext) :
    ReadbackInput .le32 order Memory.empty (.leaf .Usize ⟨4,4⟩) (.int 32 4294967295) := by
  trustIrCompilerProof {
    exact (ScalarReadbackPlan.integer .Usize ⟨4,4⟩ rfl).admit_of_source_checked
      { context base with byteModel := .le32 } 1 order Memory.empty (.int 32 4294967295)
      { bytes := ByteImage.ofList [some 255,some 255,some 255,some 255] } rfl rfl
  } {
    exact (ScalarReadbackPlan.integer .Usize ⟨4,4⟩ (by trustIrReduce)).admit_of_source_checked
      { context base with byteModel := .le32 } 1 order Memory.empty (.int 32 4294967295)
      { bytes := ByteImage.ofList [some 255,some 255,some 255,some 255] } (by trustIrReduce) (by trustIrReduce)
  }

private def context32 (base : EvalContext) : EvalContext := { context base with byteModel := .le32 }
private def source32 : Environment := { source with model := .le32 }
private def pointer32 : Plan := .leaf .Ptr ⟨4,4⟩
private def elementFields32 : List (Nat × Plan) := [(0,byte),(1,boolean),(4,pointer32)]
private def element32 : Plan := .fields elementTy ⟨8,4⟩ elementFields32
private def array32 : Plan := .array (.Array ⟨0⟩ 2) ⟨16,4⟩ 2 element32
private def fat32 : Plan := .leaf (.FatPtr .ContainerLen) ⟨8,4⟩
private def function32 : Plan := .leaf (.Func ⟨0⟩) ⟨4,4⟩
private def fields32 : List (Nat × Plan) := [(0,array32),(16,fat32),(24,character),(28,function32),(32,unit)]
private def root32 : Plan := .fields rootTy ⟨32,4⟩ fields32
private def input32 : Value := .aggregate [.array (.uniform 2 elementInput),
  .fatPtr 1034 (some ⟨99⟩) (.int 32 3),.int 32 128512,.fnDef ⟨0⟩ ⟨42⟩,.aggregate []]
private def stored32 : Image :=
  (encode .le32 order root32 input32 false).toOption.getD { bytes := ByteImage.empty }
private theorem prepared32 : (prepare source32 []).query rootTy = .ok root32 := by
  trustIrCompilerProof {
    dsimp only [source32,source,root32,rootTy,fields32,array32,element32,elementTy,elementFields32,byte,boolean,pointer32,
      fat32,character,function32,unit]
    rfl
  } {
    dsimp only [source32,source,root32,rootTy,fields32,array32,element32,elementTy,elementFields32,byte,boolean,pointer32,
      fat32,character,function32,unit]
    trustIrReduce
  }

private theorem checkedRootEncoding32 :
    ∃ image, encode .le32 order root32 input32 false = .ok image := by
  have byteRun := checkedIntegerEncoding .le32 .U8 ⟨1,1⟩ 8 7 rfl rfl rfl
  have boolRun := checkedBooleanEncoding .le32
  have pointerRun := checkedPointerEncoding .le32 ⟨4,4⟩ rfl (by decide)
  obtain ⟨elementImage, elementRun⟩ : ∃ image, encode .le32 order element32 elementInput false = .ok image :=
    checkedFields3Encoding .le32 elementTy ⟨8,4⟩
      0 byte (.int 8 7) 1 boolean (.bool true) 4 pointer32 (.ptr 1025 (some ⟨99⟩))
      byteRun boolRun pointerRun (by decide) (by decide) (by decide)
  have elementExtent : elementImage.bytes.size = 8 :=
    encode_extent .le32 order element32 elementInput false elementImage elementRun
  have arrayRun : ∃ image, encode .le32 order array32 (.array (.uniform 2 elementInput)) false = .ok image := by
    refine ⟨{ bytes := elementImage.bytes.tile 2 }, ?_⟩
    exact encode_uniform_array .le32 order (.Array ⟨0⟩ 2) ⟨16,4⟩ 2 element32 elementInput elementImage
      (by decide) elementRun (by rw [elementExtent])
  have fatRun := checkedFatEncoding .le32 ⟨8,4⟩ rfl (by decide) (by decide)
  have charRun := checkedIntegerEncoding .le32 .Char ⟨4,4⟩ 32 128512 rfl rfl rfl
  have functionRun := checkedFunctionEncoding .le32 ⟨4,4⟩ rfl (by decide)
  have unitRun := checkedUnitEncoding .le32
  exact checkedFields5Encoding .le32 rootTy ⟨32,4⟩
    0 array32 (.array (.uniform 2 elementInput))
    16 fat32 (.fatPtr 1034 (some ⟨99⟩) (.int 32 3))
    24 character (.int 32 128512)
    28 function32 (.fnDef ⟨0⟩ ⟨42⟩)
    32 unit (.aggregate [])
    arrayRun fatRun charRun functionRun unitRun
    (by decide) (by decide) (by decide) (by decide) (by decide)

private theorem encoded32 : encode .le32 order root32 input32 false = .ok stored32 :=
  checkedSuccessProjection (encode .le32 order root32 input32 false)
    { bytes := ByteImage.empty } checkedRootEncoding32

private theorem inputDepth32 : input32.depth = 4 := by
  trustIrCompilerProof {
    simp [Value.depth,input32,elementInput,Value.depthSpec,valueListDepthSpec,arrayTreeDepthRangeSpec,CompactArray.Packed.uniform]
    rfl
  } {
    simp [Value.depth,input32,elementInput,Value.depthSpec,valueListDepthSpec,arrayTreeDepthRangeSpec,CompactArray.Packed.uniform]
  }

private theorem checkedAt32 (base : EvalContext) : checkClosureValueAt (context32 base) 5 rootTy input32 = .ok () := by
  dsimp only [context32,context,rootTy,input32,elementInput,elementTy,order]
  rfl
private theorem elementShape32 (base : EvalContext) : SourceReadbackShape (context32 base) element32 := by
  apply SourceReadbackShape.tuple [.U8,.Bool,.Ptr] ⟨8,4⟩ elementFields32
  intro offset child member
  change (offset,child) ∈ [(0,byte),(1,boolean),(4,pointer32)] at member
  simp only [List.mem_cons,List.not_mem_nil,or_false,Prod.mk.injEq] at member
  rcases member with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · exact .scalar (.integer .U8 ⟨1,1⟩ rfl)
  · exact .scalar .boolean
  · exact .scalar (.pointer .Ptr ⟨4,4⟩ rfl)
private theorem rootShape32 (base : EvalContext) : SourceReadbackShape (context32 base) root32 := by
  apply SourceReadbackShape.tuple _ ⟨32,4⟩ fields32
  intro offset child member
  change (offset,child) ∈ [(0,array32),(16,fat32),(24,character),(28,function32),(32,unit)] at member
  simp only [List.mem_cons,List.not_mem_nil,or_false,Prod.mk.injEq] at member
  rcases member with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · exact .array ⟨0⟩ ⟨16,4⟩ 2 element32 rfl (elementShape32 base)
  · exact .scalar (.fat .ContainerLen ⟨8,4⟩)
  · exact .scalar (.integer .Char ⟨4,4⟩ rfl)
  · exact .scalar (.function ⟨0⟩ ⟨4,4⟩)
  · exact .scalar .unit

theorem actual_target32_recursive_checker_accepts_mixed_parent (base : EvalContext) :
    checkClosureValue (context32 base) rootTy input32 = .ok () := by
  unfold checkClosureValue
  rw [inputDepth32]
  exact checkedAt32 base

theorem prepared_target32_mixed_source_readback (base : EvalContext) :
    ∃ output, decode .le32 order Memory.empty root32 stored32.bytes = .ok output ∧ ValueReadback .le32 Memory.empty input32 output :=
  prepared_checked_value_readback source32 [] rootTy root32 prepared32 (context32 base) (rootShape32 base) Memory.empty input32 stored32
    (actual_target32_recursive_checker_accepts_mixed_parent base) encoded32

end TrustIr.AggregateMemory.SourceCheckedAdmissionControls
