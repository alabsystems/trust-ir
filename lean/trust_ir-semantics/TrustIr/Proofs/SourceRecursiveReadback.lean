-- Copyright 2026 Andrew Yates | Apache-2.0
import TrustIr.Proofs.SourceIntegerReadback
import TrustIr.Proofs.VectorAggregateReadback
import TrustIr.Proofs.PointerObservationProps
import TrustIr.Proofs.FunctionAggregateReadback

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

namespace TrustIr.AggregateMemory
open SourceLayout

/-- Readback observes logical values, canonical integer residues and receiving
    memory provenance. It never identifies compact storage representations.
    Unsupported leaf families have no implicit fallback constructor. -/
inductive ValueReadback (model : ByteModel) (memory : Memory) : Value → Value → Prop where
  | integer (width : Nat) (raw : Int) : ValueReadback model memory (.int width raw) (Value.intAt width raw)
  | boolean (value : Bool) : ValueReadback model memory (.bool value) (.bool value)
  | vector (inputs outputs : List Value) (census : inputs.length = outputs.length)
      (children : ∀ position input output, (trustIrListGet? inputs position) = some input → (trustIrListGet? outputs position) = some output →
        ValueReadback model memory input output) :
      ValueReadback model memory (.vector inputs) (.vector outputs)
  | pointer (address : Nat) (provenance : Option AllocId) :
      ValueReadback model memory (.ptr address provenance) (memory.resolveAddr address)
  | function (signature : FuncTyId) (target : FuncId) :
      ValueReadback model memory (.fnDef signature target) (.fnDef signature target)
  | null : ValueReadback model memory .nullPtr .nullPtr
  | fat (data : Nat) (provenance : Option AllocId) (input output : Value)
      (metadata : ValueReadback model memory input output) :
      ValueReadback model memory (.fatPtr data provenance input)
        (.fatPtr data (if data == 0 then none else memory.provenanceAt data) output)
  | aggregate (inputs outputs : List Value) (census : inputs.length = outputs.length)
      (children : ∀ position input output, (trustIrListGet? inputs position) = some input → (trustIrListGet? outputs position) = some output →
        ValueReadback model memory input output) :
      ValueReadback model memory (.aggregate inputs) (.aggregate outputs)
  | array (inputs outputs : CompactArray.Packed Value) (census : inputs.size = outputs.size)
      (children : ∀ position input output, position < inputs.size → inputs.tree.get? position = some input →
        outputs.tree.get? position = some output → ValueReadback model memory input output) :
      ValueReadback model memory (.array inputs) (.array outputs)

theorem vector_lane_value_readback (model : ByteModel) (memory : Memory) (ty : Ty) (input : Value)
    (ready : VectorLaneReady ty input) : ValueReadback model memory input (vectorLaneResult input) := by
  cases input with
  | int width raw => exact .integer width raw
  | bool value => exact .boolean value
  | _ => cases ty <;> cases ready

/-- Concrete scalar admission conditions, discharged by production codec laws.
    Integer, Bool, Unit and pointer families retain their actual width/overflow
    and metadata-kind guards. Packed integer/Bool vectors obtain their lane
    guards from actual storage; Float numerical refinement remains separate.
    Function words use the contextual certificate in ReadbackInput. -/
inductive ScalarReadbackInput (model : ByteModel) : Plan → Value → Prop where
  | integer (ty : Ty) (layout : MemoryTypeLayout) (width : Nat) (raw : Int)
      (integer : ty.isInteger = true) (typed : ty.bitWidthFor model = some width) (extent : layout.size = width / 8) :
      ScalarReadbackInput model (.leaf ty layout) (.int width raw)
  | boolean (value : Bool) : ScalarReadbackInput model (.leaf .Bool ⟨1,1⟩) (.bool value)
  | vector (count : Nat) (ty : Ty) (layout : MemoryTypeLayout) (inputs : List Value)
      (lane : VectorReadbackLane ty) (laneBytes : Nat) (typed : vectorScalarByteSize ty = some laneBytes)
      (nonzero : count ≠ 0) (census : inputs.length = count) (extent : layout.size = count * laneBytes)
      (ready : ∀ input ∈ inputs, VectorLaneReady ty input) :
      ScalarReadbackInput model (.leaf (.Vector count ty) layout) (.vector inputs)
  | unit : ScalarReadbackInput model (.leaf .Unit ⟨0,1⟩) (.aggregate [])
  | pointer (ty : Ty) (layout : MemoryTypeLayout) (address : Nat) (provenance : Option AllocId)
      (pointer : ty.isPointerLike = true) (bound : address < model.addressLimit) (extent : layout.size = model.pointerBytes) :
      ScalarReadbackInput model (.leaf ty layout) (.ptr address provenance)
  | null (ty : Ty) (layout : MemoryTypeLayout) (pointer : ty.isPointerLike = true) (extent : layout.size = model.pointerBytes) :
      ScalarReadbackInput model (.leaf ty layout) .nullPtr
  | fatLength (kind : FatPtrKind) (layout : MemoryTypeLayout) (data : Nat) (provenance : Option AllocId) (raw : Int)
      (lengthLane : kind.metadataTy = .U64) (bound : data < model.addressLimit) (extent : layout.size = 2 * model.pointerBytes) :
      ScalarReadbackInput model (.leaf (.FatPtr kind) layout) (.fatPtr data provenance (.int model.pointerBits raw))
  | fatVtable (kind : FatPtrKind) (layout : MemoryTypeLayout) (data metadata : Nat) (dataProv metadataProv : Option AllocId)
      (pointerLane : kind.metadataTy = .Ptr) (dataBound : data < model.addressLimit) (metaBound : metadata < model.addressLimit)
      (extent : layout.size = 2 * model.pointerBytes) :
      ScalarReadbackInput model (.leaf (.FatPtr kind) layout) (.fatPtr data dataProv (.ptr metadata metadataProv))
  | fatNull (kind : FatPtrKind) (layout : MemoryTypeLayout) (data : Nat) (provenance : Option AllocId)
      (pointerLane : kind.metadataTy = .Ptr) (bound : data < model.addressLimit) (extent : layout.size = 2 * model.pointerBytes) :
      ScalarReadbackInput model (.leaf (.FatPtr kind) layout) (.fatPtr data provenance .nullPtr)

private theorem leaf_stored_readback (model : ByteModel) (order : FunctionAddressOrder) (memory : Memory)
    (ty : Ty) (layout : MemoryTypeLayout) (input output : Value) (stored : Image) (loaded : ByteImage)
    (notChar : ty ≠ .Char)
    (codec : (encode model order (.leaf ty layout) input false).bind
      (fun image => decode model order memory (.leaf ty layout) image.bytes) = .ok output)
    (encoded : encode model order (.leaf ty layout) input false = .ok stored)
    (extent : loaded.size = layout.size) (bytes : ∀ index, loaded.get index = stored.bytes.get index) :
    ChildDecoded model order memory (.leaf ty layout) loaded output := by
  rw [encoded] at codec
  have run : decode model order memory (.leaf ty layout) stored.bytes = .ok output := codec
  have nested := (ChildDecoded.leaf_iff_decode model order memory ty layout stored.bytes output notChar).mpr run
  exact (ChildDecoded.leaf_iff_of_observations model order memory ty layout loaded stored.bytes
    (extent.trans (encode_extent model order (.leaf ty layout) input false stored encoded).symm) bytes output).mpr nested

/-- Concrete admitted scalar stores read through every complete byte-equivalent
    window. This proves the nested codec result, rather than taking it as a premise. -/
theorem ScalarReadbackInput.readback {model : ByteModel} {plan : Plan} {input : Value}
    (admitted : ScalarReadbackInput model plan input) (order : FunctionAddressOrder) (memory : Memory)
    (stored : Image) (loaded : ByteImage) (encoded : encode model order plan input false = .ok stored)
    (extent : loaded.size = plan.layout.size) (bytes : ∀ index, loaded.get index = stored.bytes.get index) :
    ∃ output, ChildDecoded model order memory plan loaded output ∧ ValueReadback model memory input output := by
  trustIrCompilerProof {
    cases admitted with
    | integer ty layout width raw integer typed size =>
      exact ⟨Value.intAt width raw,integer_child_readback_of_encoded model order memory ty layout width raw integer typed size
        stored loaded encoded extent bytes,.integer width raw⟩
    | boolean value =>
      exact ⟨.bool value,leaf_stored_readback model order memory .Bool ⟨1,1⟩ _ _ stored loaded (by intro impossible; cases impossible)
        (boolean_aggregate_leaf_roundtrip model order memory value) encoded extent bytes,.boolean value⟩
    | vector count ty layout inputs lane _laneBytes _typed _nonzero _census _sized ready =>
      obtain ⟨decoded,_storedReady⟩ := vector_child_readback_of_encoded model order memory count ty layout inputs lane stored loaded encoded extent bytes
      refine ⟨.vector (inputs.map vectorLaneResult),decoded,.vector inputs (inputs.map vectorLaneResult) (by simp) ?_⟩
      intro position input output found selected
      have same : vectorLaneResult input = output := by
        apply Option.some.inj
        simpa only [List.get?_map,found,Option.map_some] using selected
      subst output
      obtain ⟨inside,get⟩ := List.get?_eq_some.mp found
      exact vector_lane_value_readback model memory ty input (ready input (List.mem_iff_get.mpr ⟨⟨position,inside⟩,get⟩))
    | unit =>
      have codec : (encode model order (.leaf .Unit ⟨0,1⟩) (.aggregate []) false).bind
          (fun image => decode model order memory (.leaf .Unit ⟨0,1⟩) image.bytes) = .ok (.aggregate []) := by
        cases model <;> rfl
      exact ⟨.aggregate [],leaf_stored_readback model order memory .Unit ⟨0,1⟩ _ _ stored loaded (by intro impossible; cases impossible)
        codec encoded extent bytes,.aggregate [] [] rfl (by intro position input output impossible; cases impossible)⟩
    | pointer ty layout address provenance pointer bound size =>
      have notChar : ty ≠ .Char := by intro same; subst ty; cases pointer
      exact ⟨memory.resolveAddr address,leaf_stored_readback model order memory ty layout _ _ stored loaded notChar
        (pointer_aggregate_leaf_roundtrip model order memory ty layout address provenance pointer bound size) encoded extent bytes,
        .pointer address provenance⟩
    | null ty layout pointer size =>
      have notChar : ty ≠ .Char := by intro same; subst ty; cases pointer
      exact ⟨.nullPtr,leaf_stored_readback model order memory ty layout _ _ stored loaded notChar
        (null_pointer_aggregate_leaf_roundtrip model order memory ty layout pointer size) encoded extent bytes,.null⟩
    | fatLength kind layout data provenance raw lengthLane bound size =>
      exact ⟨_,leaf_stored_readback model order memory (.FatPtr kind) layout _ _ stored loaded (by intro impossible; cases impossible)
        (fat_length_aggregate_leaf_roundtrip model order memory kind layout data provenance raw lengthLane bound size) encoded extent bytes,
        .fat data provenance _ _ (.integer model.pointerBits raw)⟩
    | fatVtable kind layout data metadata dataProv metadataProv pointerLane dataBound metaBound size =>
      exact ⟨_,leaf_stored_readback model order memory (.FatPtr kind) layout _ _ stored loaded (by intro impossible; cases impossible)
        (fat_vtable_aggregate_leaf_roundtrip model order memory kind layout data metadata dataProv metadataProv pointerLane dataBound metaBound size)
        encoded extent bytes,.fat data dataProv _ _ (.pointer metadata metadataProv)⟩
    | fatNull kind layout data provenance pointerLane bound size =>
      exact ⟨_,leaf_stored_readback model order memory (.FatPtr kind) layout _ _ stored loaded (by intro impossible; cases impossible)
        (fat_null_vtable_aggregate_leaf_roundtrip model order memory kind layout data provenance pointerLane bound size) encoded extent bytes,
        .fat data provenance _ _ .null⟩
  } {
    cases admitted with
    | integer ty layout width raw integer typed size =>
      exact ⟨Value.intAt width raw,integer_child_readback_of_encoded model order memory ty layout width raw integer typed size
        stored loaded encoded extent bytes,.integer width raw⟩
    | boolean value =>
      exact ⟨.bool value,leaf_stored_readback model order memory .Bool ⟨1,1⟩ _ _ stored loaded (by intro impossible; cases impossible)
        (boolean_aggregate_leaf_roundtrip model order memory value) encoded extent bytes,.boolean value⟩
    | vector count ty layout inputs lane _laneBytes _typed _nonzero _census _sized ready =>
      obtain ⟨decoded,_storedReady⟩ := vector_child_readback_of_encoded model order memory count ty layout inputs lane stored loaded encoded extent bytes
      refine ⟨.vector (inputs.map vectorLaneResult),decoded,.vector inputs (inputs.map vectorLaneResult) (by simp) ?_⟩
      intro position input output found selected
      have same : vectorLaneResult input = output := by
        apply Option.some.inj
        simpa only [CompilerCompat.listGetConstructive_map,found,Option.map_some] using selected
      subst output
      exact vector_lane_value_readback model memory ty input (ready input (CompilerCompat.listGetConstructive_mem found))
    | unit =>
      have codec : (encode model order (.leaf .Unit ⟨0,1⟩) (.aggregate []) false).bind
          (fun image => decode model order memory (.leaf .Unit ⟨0,1⟩) image.bytes) = .ok (.aggregate []) := by
        cases model <;> trustIrReduce
      exact ⟨.aggregate [],leaf_stored_readback model order memory .Unit ⟨0,1⟩ _ _ stored loaded (by intro impossible; cases impossible)
        codec encoded extent bytes,.aggregate [] [] rfl (by intro position input output impossible; cases impossible)⟩
    | pointer ty layout address provenance pointer bound size =>
      have notChar : ty ≠ .Char := by intro same; subst ty; cases pointer
      exact ⟨memory.resolveAddr address,leaf_stored_readback model order memory ty layout _ _ stored loaded notChar
        (pointer_aggregate_leaf_roundtrip model order memory ty layout address provenance pointer bound size) encoded extent bytes,
        .pointer address provenance⟩
    | null ty layout pointer size =>
      have notChar : ty ≠ .Char := by intro same; subst ty; cases pointer
      exact ⟨.nullPtr,leaf_stored_readback model order memory ty layout _ _ stored loaded notChar
        (null_pointer_aggregate_leaf_roundtrip model order memory ty layout pointer size) encoded extent bytes,.null⟩
    | fatLength kind layout data provenance raw lengthLane bound size =>
      exact ⟨_,leaf_stored_readback model order memory (.FatPtr kind) layout _ _ stored loaded (by intro impossible; cases impossible)
        (fat_length_aggregate_leaf_roundtrip model order memory kind layout data provenance raw lengthLane bound size) encoded extent bytes,
        .fat data provenance _ _ (.integer model.pointerBits raw)⟩
    | fatVtable kind layout data metadata dataProv metadataProv pointerLane dataBound metaBound size =>
      exact ⟨_,leaf_stored_readback model order memory (.FatPtr kind) layout _ _ stored loaded (by intro impossible; cases impossible)
        (fat_vtable_aggregate_leaf_roundtrip model order memory kind layout data metadata dataProv metadataProv pointerLane dataBound metaBound size)
        encoded extent bytes,.fat data dataProv _ _ (.pointer metadata metadataProv)⟩
    | fatNull kind layout data provenance pointerLane bound size =>
      exact ⟨_,leaf_stored_readback model order memory (.FatPtr kind) layout _ _ stored loaded (by intro impossible; cases impossible)
        (fat_null_vtable_aggregate_leaf_roundtrip model order memory kind layout data provenance pointerLane bound size) encoded extent bytes,
        .fat data provenance _ _ .null⟩
  }

/-- Complete parent observations transport an existing bounded child lane. -/
theorem ByteLane.of_parent_observations {parent actual bytes : ByteImage} {offset : Nat}
    (lane : ByteLane parent offset bytes) (extent : actual.size = parent.size)
    (observed : ∀ index, actual.get index = parent.get index) : ByteLane actual offset bytes := by
  refine ⟨by rw [extent]; exact lane.1,?_⟩
  intro index inside
  exact (observed (offset + index)).trans (lane.2 index inside)

/-- Any complete window of a retained lane has all of the stored child's
    observations, including out-of-range absence. -/
theorem ByteLane.window_bytes {parent bytes part : ByteImage} {offset : Nat}
    (lane : ByteLane parent offset bytes) (extent : part.size = bytes.size)
    (observed : ∀ index, index < bytes.size → part.get index = parent.get (offset + index)) :
    ∀ index, part.get index = bytes.get index := by
  intro index
  by_cases inside : index < bytes.size
  · exact (observed index inside).trans (lane.2 index inside)
  · rw [ByteImage.get_outside part index (by rw [extent]; omega),ByteImage.get_outside bytes index (by omega)]

theorem ByteLane.slice_bytes {parent bytes : ByteImage} {offset : Nat} (lane : ByteLane parent offset bytes) :
    (parent.slice offset bytes.size).size = bytes.size ∧
      ∀ index, (parent.slice offset bytes.size).get index = bytes.get index := by
  have extent : (parent.slice offset bytes.size).size = bytes.size := by rw [ByteImage.size_slice]; have bound := lane.1; omega
  refine ⟨extent,lane.window_bytes extent ?_⟩
  intro index inside
  exact ByteImage.get_slice parent offset bytes.size index inside (by have bound := lane.1; omega)

theorem ValueReadback.aggregate_nil (model : ByteModel) (memory : Memory) : ValueReadback model memory (.aggregate []) (.aggregate []) :=
  .aggregate [] [] rfl (by intro position input output impossible; cases impossible)

theorem ValueReadback.aggregate_cons {model : ByteModel} {memory : Memory} {input output : Value} {inputs outputs : List Value}
    (first : ValueReadback model memory input output) (rest : ValueReadback model memory (.aggregate inputs) (.aggregate outputs)) :
    ValueReadback model memory (.aggregate (input :: inputs)) (.aggregate (output :: outputs)) := by
  cases rest with
  | aggregate _ _ census children =>
    refine .aggregate _ _ (congrArg Nat.succ census) ?_
    intro position actual expected found selected
    cases position with
    | zero => cases found; cases selected; exact first
    | succ position => exact children position actual expected found selected

/-- Finite recursive admission with concrete scalar guards and complete logical
    child coverage. Enum admission retains actual store-selection stability and
    logical tag normalization; neither is inferred from layout alone. -/
inductive ReadbackInput (model : ByteModel) (order : FunctionAddressOrder) (memory : Memory) : Plan → Value → Prop where
  | scalar {plan : Plan} {input : Value} (admitted : ScalarReadbackInput model plan input) : ReadbackInput model order memory plan input
  | function {plan : Plan} {input : Value} (admitted : FunctionReadbackInput model order plan input) :
      ReadbackInput model order memory plan input
  | fields (ty : Ty) (layout : MemoryTypeLayout) (fields : List (Nat × Plan)) (inputs : List Value)
      (census : fields.length = inputs.length)
      (children : ∀ position offset child input, (trustIrListGet? fields position) = some (offset,child) → (trustIrListGet? inputs position) = some input →
        ReadbackInput model order memory child input) :
      ReadbackInput model order memory (.fields ty layout fields) (.aggregate inputs)
  | array (ty : Ty) (layout : MemoryTypeLayout) (count : Nat) (element : Plan) (inputs : CompactArray.Packed Value)
      (census : inputs.size = count)
      (children : ∀ position input, position < count → inputs.tree.get? position = some input →
        ReadbackInput model order memory element input) :
      ReadbackInput model order memory (.array ty layout count element) (.array inputs)
  | enumeration (id : EnumId) (layout : MemoryTypeLayout) (info : Enumeration) (variants : List (Option (List (Nat × Plan))))
      (tag : Value) (inputs : List Value) (position : Nat) (discriminant : Int) (fields : List (Nat × Plan))
      (selected : EnumEncodingSelects info tag position) (live : (trustIrListGet? info.uninhabited position) = some false)
      (row : (trustIrListGet? variants position) = some (some fields)) (discriminantRow : (trustIrListGet? info.discriminants position) = some discriminant)
      (tagReadback : ValueReadback model memory tag (Value.intAt (tagBits info.tag) discriminant))
      (census : fields.length = inputs.length)
      (selection : ∀ stored, encode model order (.enumeration (.Enum id) layout info variants) (.aggregate (tag :: inputs)) false = .ok stored →
        EnumDecodingSelects info stored.bytes position)
      (children : ∀ fieldPosition offset child input, (trustIrListGet? fields fieldPosition) = some (offset,child) → (trustIrListGet? inputs fieldPosition) = some input →
        ReadbackInput model order memory child input) :
      ReadbackInput model order memory (.enumeration (.Enum id) layout info variants) (.aggregate (tag :: inputs))

private theorem fields_readback_of_children (model : ByteModel) (order : FunctionAddressOrder) (memory : Memory)
    (fields : List (Nat × Plan)) (inputs : List Value) (image : ByteImage) (census : fields.length = inputs.length)
    (children : ∀ position offset child input, (trustIrListGet? fields position) = some (offset,child) → (trustIrListGet? inputs position) = some input →
      ∃ output, ChildDecoded model order memory child (image.slice offset child.layout.size) output ∧ ValueReadback model memory input output) :
    ∃ outputs, FieldsDecoded model order memory fields image outputs ∧ ValueReadback model memory (.aggregate inputs) (.aggregate outputs) := by
  induction fields generalizing inputs with
  | nil =>
    cases inputs with
    | nil => exact ⟨[],(FieldsDecoded.nil_iff model order memory image []).mpr rfl,.aggregate_nil model memory⟩
    | cons input inputs => simp at census
  | cons field fields ih =>
    obtain ⟨offset,child⟩ := field
    cases inputs with
    | nil => simp at census
    | cons input inputs =>
      obtain ⟨output,first,related⟩ := children 0 offset child input rfl rfl
      obtain ⟨outputs,rest,later⟩ := ih inputs (Nat.succ.inj census)
        (fun position nextOffset nextChild nextInput found selected => children (position + 1) nextOffset nextChild nextInput found selected)
      exact ⟨output :: outputs,FieldsDecoded.cons first rest,related.aggregate_cons later⟩

private theorem origin_field_member (source : Environment) (ty : Ty) (layout : MemoryTypeLayout) (fields : List (Nat × Plan))
    (origin : Plan.Origin (SourceElement source) (ActualSummary source) ty (.fields ty layout fields))
    (position offset : Nat) (child : Plan) (found : (trustIrListGet? fields position) = some (offset,child)) :
    Plan.Origin (SourceElement source) (ActualSummary source) child.ty child := by
  trustIrCompilerProof {
    obtain ⟨_,_,_,children,_,_⟩ := origin.fields_metadata_view
    obtain ⟨inside,lookup⟩ := List.get?_eq_some.mp found
    exact children (offset,child) (List.mem_iff_get.mpr ⟨⟨position,inside⟩,lookup⟩)
  } {
    obtain ⟨_,_,_,children,_,_⟩ := origin.fields_metadata_view
    exact children (offset,child) (CompilerCompat.listGetConstructive_mem found)
  }

private theorem origin_array_child (source : Environment) (ty : Ty) (layout : MemoryTypeLayout) (count : Nat) (element : Plan)
    (origin : Plan.Origin (SourceElement source) (ActualSummary source) ty (.array ty layout count element)) :
    Plan.Origin (SourceElement source) (ActualSummary source) element.ty element := by
  cases origin with
  | array _ _ _ _ child _ _ _ _ => exact child

private theorem origin_enum_members (source : Environment) (id : EnumId) (layout : MemoryTypeLayout) (info : Enumeration)
    (variants : List (Option (List (Nat × Plan))))
    (origin : Plan.Origin (SourceElement source) (ActualSummary source) (.Enum id) (.enumeration (.Enum id) layout info variants))
    (position : Nat) (fields : List (Nat × Plan)) (live : (trustIrListGet? info.uninhabited position) = some false)
    (row : (trustIrListGet? variants position) = some (some fields)) :
    ∀ field ∈ fields, Plan.Origin (SourceElement source) (ActualSummary source) field.2.ty field.2 := by
  cases origin with
  | enumeration _ _ _ _ _ _ _ _ children _ _ =>
    obtain ⟨actual,actualRow,origins⟩ := children.live_at position live
    rw [row] at actualRow
    cases actualRow
    exact origins


/-- Recursive ordinary-storage readback through every complete observed window.
    Source origins supply child provenance/geometry; concrete scalar laws and
    actual enum selection certificates supply the nonrecursive obligations. -/
theorem ReadbackInput.readback {model : ByteModel} {order : FunctionAddressOrder} {memory : Memory}
    {plan : Plan} {input : Value} (admitted : ReadbackInput model order memory plan input) :
    ∀ source : Environment, Plan.Origin (SourceElement source) (ActualSummary source) plan.ty plan →
    ∀ stored : Image, encode model order plan input false = .ok stored →
    ∀ loaded : ByteImage, loaded.size = plan.layout.size → (∀ index, loaded.get index = stored.bytes.get index) →
    ∃ output, ChildDecoded model order memory plan loaded output ∧ ValueReadback model memory input output := by
  trustIrCompilerProof {
    induction admitted with
    | scalar scalar =>
      intro source origin stored encoded loaded extent bytes
      exact scalar.readback order memory stored loaded encoded extent bytes
    | function function =>
      intro source origin stored encoded loaded extent bytes
      have codec := function.codec memory
      cases function with
      | registered ids signature target index layout lookup bounded size =>
        exact ⟨_,leaf_stored_readback model (some ids) memory (.Func signature) layout _ _ stored loaded
          (by intro impossible; cases impossible) codec encoded extent bytes,.function signature target⟩
      | null order signature layout size =>
        exact ⟨_,leaf_stored_readback model order memory (.Func signature) layout _ _ stored loaded
          (by intro impossible; cases impossible) codec encoded extent bytes,.null⟩
    | fields ty layout fields inputs census children ih =>
      intro source origin stored encoded loaded extent bytes
      have parentSize := encode_extent model order (.fields ty layout fields) (.aggregate inputs) false stored encoded
      have sameSize : loaded.size = stored.bytes.size := extent.trans parentSize.symm
      obtain ⟨actual,same,fieldRun⟩ := encode_fields_steps model order ty layout fields (.aggregate inputs) stored encoded
      cases same
      have reads : ∀ position offset child input, (trustIrListGet? fields position) = some (offset,child) → (trustIrListGet? inputs position) = some input →
          ∃ output, ChildDecoded model order memory child (loaded.slice offset child.layout.size) output ∧ ValueReadback model memory input output := by
        intro position offset child input found selected
        obtain ⟨childImage,childEncoded,lane⟩ := fieldRun.child_lane position offset child found input selected
          (origin.fields_child_placement position offset child found).2
        have actualLane := lane.of_parent_observations sameSize bytes
        have childSize := encode_extent model order child input false childImage childEncoded
        obtain ⟨partSize,partBytes⟩ := actualLane.slice_bytes
        rw [childSize] at partSize partBytes
        exact ih position offset child input found selected source
          (origin_field_member source ty layout fields origin position offset child found) childImage childEncoded _ partSize partBytes
      obtain ⟨outputs,run,related⟩ := fields_readback_of_children model order memory fields inputs loaded census reads
      exact ⟨.aggregate outputs,ChildDecoded.fields_of_children model order memory ty layout fields loaded outputs extent run,related⟩
    | array ty layout count element inputs census children ih =>
      intro source origin stored encoded loaded extent bytes
      have parentSize := encode_extent model order (.array ty layout count element) (.array inputs) false stored encoded
      have sameSize : loaded.size = stored.bytes.size := extent.trans parentSize.symm
      obtain ⟨_actualCensus,layoutExtent⟩ := encode_array_geometry model order ty layout count element inputs stored encoded
      have childOrigin := origin_array_child source ty layout count element origin
      have reads : ∀ slot input, slot < count → inputs.tree.get? slot = some input →
          ∀ part, part.size = element.layout.size →
            (∀ index, index < element.layout.size → part.get index = loaded.get (slot * element.layout.size + index)) →
            ∃ output, ChildDecoded model order memory element part output ∧ ValueReadback model memory input output := by
        intro slot input inside found part partSize observed
        obtain ⟨childImage,childEncoded,lane⟩ := encode_array_slot model order ty layout count element inputs stored encoded slot input
          (by rw [census]; exact inside) found
        have actualLane := lane.of_parent_observations sameSize bytes
        have childSize := encode_extent model order element input false childImage childEncoded
        have exactBytes := actualLane.window_bytes (partSize.trans childSize.symm)
          (fun index inByte => observed index (by rw [← childSize]; exact inByte))
        exact ih slot input inside found source childOrigin childImage childEncoded part partSize exactBytes
      obtain ⟨outputs,outputSize,decoded⟩ := ChildDecoded.array_exists_of_children model order memory ty layout count element loaded
        layoutExtent extent (by
          intro slot inside part partSize observed
          obtain ⟨input,found⟩ := inputs.tree.get_exists slot (by rw [census]; exact inside)
          obtain ⟨output,run,_⟩ := reads slot input inside found part partSize observed
          exact ⟨output,run⟩)
      refine ⟨.array outputs,decoded,.array inputs outputs (census.trans outputSize.symm) ?_⟩
      intro slot input output inside inputFound outputFound
      have insideCount : slot < count := by rw [← census]; exact inside
      have ordinary := (ChildDecoded.array_iff_decode model order memory ty layout count element loaded (.array outputs)).mp decoded
      obtain ⟨part,partSize,actualRun,lane⟩ := decode_array_slot model order memory ty layout count element layoutExtent loaded outputs ordinary
        slot output insideCount outputFound
      obtain ⟨expected,expectedRun,related⟩ := reads slot input insideCount inputFound part partSize
        (fun index inByte => (lane.2 index (by rw [partSize]; exact inByte)).symm)
      have same := actualRun.functional expectedRun
      rw [same]
      exact related
    | enumeration id layout info variants tag inputs position discriminant fields selected live row discriminantRow tagRelated census selection children ih =>
      intro source origin stored encoded loaded extent bytes
      have parentSize := encode_extent model order (.enumeration (.Enum id) layout info variants) (.aggregate (tag :: inputs)) false stored encoded
      have sameSize : loaded.size = stored.bytes.size := extent.trans parentSize.symm
      have outputSelected := (EnumDecodingSelects.iff_of_observations info loaded stored.bytes sameSize bytes position).mpr (selection stored encoded)
      obtain ⟨actualPosition,_initialBytes,actualSelected,_,variantRun,_⟩ :=
        encode_enumeration_steps model order (.Enum id) layout info variants tag inputs false stored encoded
      have same := actualSelected.functional selected
      subst actualPosition
      obtain ⟨actualFields,actualRow,fieldRun⟩ := variantRun.fields
      rw [row] at actualRow
      cases actualRow
      have origins := origin_enum_members source id layout info variants origin position fields live row
      have reads : ∀ fieldPosition offset child input, (trustIrListGet? fields fieldPosition) = some (offset,child) → (trustIrListGet? inputs fieldPosition) = some input →
          ∃ output, ChildDecoded model order memory child (loaded.slice offset child.layout.size) output ∧ ValueReadback model memory input output := by
        intro fieldPosition offset child input found inputFound
        obtain ⟨childImage,childEncoded,lane⟩ := fieldRun.child_lane fieldPosition offset child found input inputFound
          (origin.enum_payload_child_placement position fields row fieldPosition offset child found).2
        have actualLane := lane.of_parent_observations sameSize bytes
        have childSize := encode_extent model order child input false childImage childEncoded
        obtain ⟨partSize,partBytes⟩ := actualLane.slice_bytes
        rw [childSize] at partSize partBytes
        obtain ⟨inside,lookup⟩ := List.get?_eq_some.mp found
        exact ih fieldPosition offset child input found inputFound source
          (origins (offset,child) (List.mem_iff_get.mpr ⟨⟨fieldPosition,inside⟩,lookup⟩)) childImage childEncoded _ partSize partBytes
      obtain ⟨outputs,payload,related⟩ := fields_readback_of_children model order memory fields inputs loaded census reads
      exact ⟨.aggregate (Value.intAt (tagBits info.tag) discriminant :: outputs),
        ChildDecoded.enumeration_of_payload model order memory (.Enum id) layout info variants loaded position discriminant fields outputs
          extent outputSelected discriminantRow row payload,tagRelated.aggregate_cons related⟩
  } {
    induction admitted with
    | scalar scalar =>
      intro source origin stored encoded loaded extent bytes
      exact scalar.readback order memory stored loaded encoded extent bytes
    | function function =>
      intro source origin stored encoded loaded extent bytes
      have codec := function.codec memory
      cases function with
      | registered ids signature target index layout lookup bounded size =>
        exact ⟨_,leaf_stored_readback model (some ids) memory (.Func signature) layout _ _ stored loaded
          (by intro impossible; cases impossible) codec encoded extent bytes,.function signature target⟩
      | null order signature layout size =>
        exact ⟨_,leaf_stored_readback model order memory (.Func signature) layout _ _ stored loaded
          (by intro impossible; cases impossible) codec encoded extent bytes,.null⟩
    | fields ty layout fields inputs census children ih =>
      intro source origin stored encoded loaded extent bytes
      have parentSize := encode_extent model order (.fields ty layout fields) (.aggregate inputs) false stored encoded
      have sameSize : loaded.size = stored.bytes.size := extent.trans parentSize.symm
      obtain ⟨actual,same,fieldRun⟩ := encode_fields_steps model order ty layout fields (.aggregate inputs) stored encoded
      cases same
      have reads : ∀ position offset child input, (trustIrListGet? fields position) = some (offset,child) → (trustIrListGet? inputs position) = some input →
          ∃ output, ChildDecoded model order memory child (loaded.slice offset child.layout.size) output ∧ ValueReadback model memory input output := by
        intro position offset child input found selected
        obtain ⟨childImage,childEncoded,lane⟩ := fieldRun.child_lane position offset child found input selected
          (origin.fields_child_placement position offset child found).2
        have actualLane := lane.of_parent_observations sameSize bytes
        have childSize := encode_extent model order child input false childImage childEncoded
        obtain ⟨partSize,partBytes⟩ := actualLane.slice_bytes
        rw [childSize] at partSize partBytes
        exact ih position offset child input found selected source
          (origin_field_member source ty layout fields origin position offset child found) childImage childEncoded _ partSize partBytes
      obtain ⟨outputs,run,related⟩ := fields_readback_of_children model order memory fields inputs loaded census reads
      exact ⟨.aggregate outputs,ChildDecoded.fields_of_children model order memory ty layout fields loaded outputs extent run,related⟩
    | array ty layout count element inputs census children ih =>
      intro source origin stored encoded loaded extent bytes
      have parentSize := encode_extent model order (.array ty layout count element) (.array inputs) false stored encoded
      have sameSize : loaded.size = stored.bytes.size := extent.trans parentSize.symm
      obtain ⟨_actualCensus,layoutExtent⟩ := encode_array_geometry model order ty layout count element inputs stored encoded
      have childOrigin := origin_array_child source ty layout count element origin
      have reads : ∀ slot input, slot < count → inputs.tree.get? slot = some input →
          ∀ part, part.size = element.layout.size →
            (∀ index, index < element.layout.size → part.get index = loaded.get (slot * element.layout.size + index)) →
            ∃ output, ChildDecoded model order memory element part output ∧ ValueReadback model memory input output := by
        intro slot input inside found part partSize observed
        obtain ⟨childImage,childEncoded,lane⟩ := encode_array_slot model order ty layout count element inputs stored encoded slot input
          (by rw [census]; exact inside) found
        have actualLane := lane.of_parent_observations sameSize bytes
        have childSize := encode_extent model order element input false childImage childEncoded
        have exactBytes := actualLane.window_bytes (partSize.trans childSize.symm)
          (fun index inByte => observed index (by rw [← childSize]; exact inByte))
        exact ih slot input inside found source childOrigin childImage childEncoded part partSize exactBytes
      obtain ⟨outputs,outputSize,decoded⟩ := ChildDecoded.array_exists_of_children model order memory ty layout count element loaded
        layoutExtent extent (by
          intro slot inside part partSize observed
          obtain ⟨input,found⟩ := inputs.tree.get_exists slot (by rw [census]; exact inside)
          obtain ⟨output,run,_⟩ := reads slot input inside found part partSize observed
          exact ⟨output,run⟩)
      refine ⟨.array outputs,decoded,.array inputs outputs (census.trans outputSize.symm) ?_⟩
      intro slot input output inside inputFound outputFound
      have insideCount : slot < count := by rw [← census]; exact inside
      have ordinary := (ChildDecoded.array_iff_decode model order memory ty layout count element loaded (.array outputs)).mp decoded
      obtain ⟨part,partSize,actualRun,lane⟩ := decode_array_slot model order memory ty layout count element layoutExtent loaded outputs ordinary
        slot output insideCount outputFound
      obtain ⟨expected,expectedRun,related⟩ := reads slot input insideCount inputFound part partSize
        (fun index inByte => (lane.2 index (by rw [partSize]; exact inByte)).symm)
      have same := actualRun.functional expectedRun
      rw [same]
      exact related
    | enumeration id layout info variants tag inputs position discriminant fields selected live row discriminantRow tagRelated census selection children ih =>
      intro source origin stored encoded loaded extent bytes
      have parentSize := encode_extent model order (.enumeration (.Enum id) layout info variants) (.aggregate (tag :: inputs)) false stored encoded
      have sameSize : loaded.size = stored.bytes.size := extent.trans parentSize.symm
      have outputSelected := (EnumDecodingSelects.iff_of_observations info loaded stored.bytes sameSize bytes position).mpr (selection stored encoded)
      obtain ⟨actualPosition,_initialBytes,actualSelected,_,variantRun,_⟩ :=
        encode_enumeration_steps model order (.Enum id) layout info variants tag inputs false stored encoded
      have same := actualSelected.functional selected
      subst actualPosition
      obtain ⟨actualFields,actualRow,fieldRun⟩ := variantRun.fields
      rw [row] at actualRow
      cases actualRow
      have origins := origin_enum_members source id layout info variants origin position fields live row
      have reads : ∀ fieldPosition offset child input, (trustIrListGet? fields fieldPosition) = some (offset,child) → (trustIrListGet? inputs fieldPosition) = some input →
          ∃ output, ChildDecoded model order memory child (loaded.slice offset child.layout.size) output ∧ ValueReadback model memory input output := by
        intro fieldPosition offset child input found inputFound
        obtain ⟨childImage,childEncoded,lane⟩ := fieldRun.child_lane fieldPosition offset child found input inputFound
          (origin.enum_payload_child_placement position fields row fieldPosition offset child found).2
        have actualLane := lane.of_parent_observations sameSize bytes
        have childSize := encode_extent model order child input false childImage childEncoded
        obtain ⟨partSize,partBytes⟩ := actualLane.slice_bytes
        rw [childSize] at partSize partBytes
        exact ih fieldPosition offset child input found inputFound source
          (origins (offset,child) (CompilerCompat.listGetConstructive_mem found)) childImage childEncoded _ partSize partBytes
      obtain ⟨outputs,payload,related⟩ := fields_readback_of_children model order memory fields inputs loaded census reads
      exact ⟨.aggregate (Value.intAt (tagBits info.tag) discriminant :: outputs),
        ChildDecoded.enumeration_of_payload model order memory (.Enum id) layout info variants loaded position discriminant fields outputs
          extent outputSelected discriminantRow row payload,tagRelated.aggregate_cons related⟩
  }

/-- The actual top-level Char rule remains a separate root condition. It is
    vacuous for other roots and never imposed on nested raw-word Char lanes. -/
def TopCharReady (plan : Plan) (input : Value) : Prop :=
  ∀ layout width raw, plan = .leaf .Char layout → input = .int width raw → validChar (truncateUnsigned raw width).toNat

theorem ScalarReadbackInput.character_view {model : ByteModel} {layout : MemoryTypeLayout} {input : Value}
    (admitted : ScalarReadbackInput model (.leaf .Char layout) input) :
    ∃ width raw, input = .int width raw ∧ Ty.Char.bitWidthFor model = some width ∧ layout.size = width / 8 := by
  cases admitted with
  | integer ty layout width raw integer typed extent => exact ⟨width,raw,rfl,typed,extent⟩
  | pointer ty layout address provenance pointer bound extent => cases pointer
  | null ty layout pointer extent => cases pointer

/-- Actual ordinary scalar readback retains Unicode validation exactly where
    production decoding performs it. -/
theorem ScalarReadbackInput.top_readback {model : ByteModel} {plan : Plan} {input : Value}
    (admitted : ScalarReadbackInput model plan input) (order : FunctionAddressOrder) (memory : Memory)
    (stored : Image) (loaded : ByteImage) (encoded : encode model order plan input false = .ok stored)
    (extent : loaded.size = plan.layout.size) (bytes : ∀ index, loaded.get index = stored.bytes.get index)
    (ready : TopCharReady plan input) :
    ∃ output, decode model order memory plan loaded = .ok output ∧ ValueReadback model memory input output := by
  by_cases character : ∃ layout, plan = .leaf .Char layout
  · obtain ⟨layout,shape⟩ := character
    subst plan
    obtain ⟨width,raw,inputShape,typed,size⟩ := admitted.character_view
    subst input
    have codec := integer_aggregate_leaf_roundtrip model order memory .Char layout width raw rfl typed size
    rw [encoded] at codec
    have run : decode model order memory (.leaf .Char layout) stored.bytes = .ok (Value.intAt width raw) := by
      simpa only [Except.bind,if_pos (ready layout width raw rfl rfl)] using codec
    refine ⟨Value.intAt width raw,?_,.integer width raw⟩
    exact (decode_leaf_eq_of_observations model order memory .Char layout loaded stored.bytes
      (extent.trans (encode_extent model order (.leaf .Char layout) (.int width raw) false stored encoded).symm) bytes).trans run
  · obtain ⟨output,run,related⟩ := admitted.readback order memory stored loaded encoded extent bytes
    refine ⟨output,?_,related⟩
    exact (ChildDecoded.ordinary_iff_decode model order memory plan loaded output
      (fun layout same => character ⟨layout,same⟩)).mp run

/-- The recursive ordinary entry retains top-level Char readiness and every
    actual source/byte premise, while parent success is the conclusion. -/
theorem ReadbackInput.top_readback {model : ByteModel} {order : FunctionAddressOrder} {memory : Memory}
    {plan : Plan} {input : Value} (admitted : ReadbackInput model order memory plan input)
    (source : Environment) (origin : Plan.Origin (SourceElement source) (ActualSummary source) plan.ty plan)
    (stored : Image) (encoded : encode model order plan input false = .ok stored)
    (loaded : ByteImage) (extent : loaded.size = plan.layout.size) (bytes : ∀ index, loaded.get index = stored.bytes.get index)
    (ready : TopCharReady plan input) :
    ∃ output, decode model order memory plan loaded = .ok output ∧ ValueReadback model memory input output := by
  by_cases character : ∃ layout, plan = .leaf .Char layout
  · obtain ⟨layout,shape⟩ := character
    subst plan
    cases admitted with
    | scalar scalar => exact scalar.top_readback order memory stored loaded encoded extent bytes ready
    | function function => cases function
  · obtain ⟨output,run,related⟩ := admitted.readback source origin stored encoded loaded extent bytes
    exact ⟨output,(ChildDecoded.ordinary_iff_decode model order memory plan loaded output
      (fun layout same => character ⟨layout,same⟩)).mp run,related⟩

/-- A successful real prepared query supplies all recursive source origins. -/
theorem prepared_recursive_readback (source : Environment) (roots : List Ty) (ty : Ty) (plan : Plan)
    (prepared : (prepare source roots).query ty = .ok plan)
    (model : ByteModel) (order : FunctionAddressOrder) (memory : Memory) (input : Value)
    (admitted : ReadbackInput model order memory plan input) (ready : TopCharReady plan input)
    (stored : Image) (encoded : encode model order plan input false = .ok stored) :
    ∃ output, decode model order memory plan stored.bytes = .ok output ∧ ValueReadback model memory input output :=
  admitted.top_readback source (prepared_plan_origin source roots ty plan prepared).own stored encoded stored.bytes
    (encode_extent model order plan input false stored encoded) (fun _ => rfl) ready

theorem prepared_recursive_child_readback (source : Environment) (roots : List Ty) (ty : Ty) (plan : Plan)
    (prepared : (prepare source roots).query ty = .ok plan)
    (model : ByteModel) (order : FunctionAddressOrder) (memory : Memory) (input : Value)
    (admitted : ReadbackInput model order memory plan input) (stored : Image)
    (encoded : encode model order plan input false = .ok stored) :
    ∃ output, ChildDecoded model order memory plan stored.bytes output ∧ ValueReadback model memory input output :=
  admitted.readback source (prepared_plan_origin source roots ty plan prepared).own stored encoded stored.bytes
    (encode_extent model order plan input false stored encoded) (fun _ => rfl)


/-- A complete ordered field-input certificate, convenient for concrete plans. -/
inductive FieldReadbackInputs (model : ByteModel) (order : FunctionAddressOrder) (memory : Memory) :
    List (Nat × Plan) → List Value → Prop where
  | nil : FieldReadbackInputs model order memory [] []
  | cons {offset : Nat} {child : Plan} {input : Value} {fields : List (Nat × Plan)} {inputs : List Value}
      (first : ReadbackInput model order memory child input) (rest : FieldReadbackInputs model order memory fields inputs) :
      FieldReadbackInputs model order memory ((offset,child) :: fields) (input :: inputs)

theorem FieldReadbackInputs.length {model : ByteModel} {order : FunctionAddressOrder} {memory : Memory}
    {fields : List (Nat × Plan)} {inputs : List Value} (pairs : FieldReadbackInputs model order memory fields inputs) :
    fields.length = inputs.length := by
  induction pairs with
  | nil => rfl
  | cons _ _ ih => exact congrArg Nat.succ ih

theorem FieldReadbackInputs.at {model : ByteModel} {order : FunctionAddressOrder} {memory : Memory}
    {fields : List (Nat × Plan)} {inputs : List Value} (pairs : FieldReadbackInputs model order memory fields inputs)
    (position offset : Nat) (child : Plan) (input : Value)
    (found : (trustIrListGet? fields position) = some (offset,child)) (selected : (trustIrListGet? inputs position) = some input) :
    ReadbackInput model order memory child input := by
  induction pairs generalizing position offset child input with
  | nil => cases found
  | cons first rest ih =>
    cases position with
    | zero => cases found; cases selected; exact first
    | succ position => exact ih position offset child input found selected

theorem ReadbackInput.fields_of_pairs {model : ByteModel} {order : FunctionAddressOrder} {memory : Memory}
    (ty : Ty) (layout : MemoryTypeLayout) (fields : List (Nat × Plan)) (inputs : List Value)
    (pairs : FieldReadbackInputs model order memory fields inputs) :
    ReadbackInput model order memory (.fields ty layout fields) (.aggregate inputs) :=
  .fields ty layout fields inputs pairs.length pairs.at

theorem ReadbackInput.array_uniform {model : ByteModel} {order : FunctionAddressOrder} {memory : Memory}
    (ty : Ty) (layout : MemoryTypeLayout) (count : Nat) (element : Plan) (input : Value)
    (child : ReadbackInput model order memory element input) :
    ReadbackInput model order memory (.array ty layout count element) (.array (CompactArray.Packed.uniform count input)) := by
  apply ReadbackInput.array ty layout count element (CompactArray.Packed.uniform count input) rfl
  intro position actual inside found
  simp only [CompactArray.Packed.uniform,CompactArray.Tree.get?,if_pos inside,Option.some.injEq] at found
  subst actual
  exact child


/-- Reifying an image's complete observations as an external source preserves
    all bytes, including outside lookup. It does not identify constructors. -/
theorem source_image_observations (image : ByteImage) (index : Nat) :
    (ByteImage.source image.size image.get).get index = image.get index := by
  by_cases inside : index < image.size
  · simp only [ByteImage.source,ByteImage.get,ByteImage.Tree.get,if_pos inside]
  · rw [ByteImage.get_outside _ index (by change image.size ≤ index; omega),ByteImage.get_outside image index (by omega)]


/-- Existing production prefix/selection laws construct the enum admission
    certificate. Default niche-carrier readiness remains an actual store obligation. -/
theorem ReadbackInput.enumeration_of_prefix {model : ByteModel} {order : FunctionAddressOrder} {memory : Memory}
    (id : EnumId) (layout : MemoryTypeLayout) (info : Enumeration) (variants : List (Option (List (Nat × Plan))))
    (tag : Value) (inputs : List Value) (position : Nat) (discriminant : Int) (fields : List (Nat × Plan))
    (selected : EnumEncodingSelects info tag position) (live : (trustIrListGet? info.uninhabited position) = some false)
    (row : (trustIrListGet? variants position) = some (some fields)) (discriminantRow : (trustIrListGet? info.discriminants position) = some discriminant)
    (tagRelated : ValueReadback model memory tag (Value.intAt (tagBits info.tag) discriminant))
    (pairs : FieldReadbackInputs model order memory fields inputs)
    (sound : EnumPrefixSound layout.size info position tag) (separated : EnumPayloadAvoidsTag info variants position)
    (carrier : ∀ stored, encode model order (.enumeration (.Enum id) layout info variants) (.aggregate (tag :: inputs)) false = .ok stored →
      EnumUntaggedCarrierReady info position stored.bytes) :
    ReadbackInput model order memory (.enumeration (.Enum id) layout info variants) (.aggregate (tag :: inputs)) :=
  .enumeration id layout info variants tag inputs position discriminant fields selected live row discriminantRow tagRelated pairs.length
    (fun stored encoded => (enum_encoded_selection model order (.Enum id) layout info variants tag inputs position false stored
      selected sound encoded separated (carrier stored encoded)).2) pairs.at

end TrustIr.AggregateMemory

namespace TrustIr.AggregateMemory.RecursiveReadbackControls
open SourceLayout
set_option maxHeartbeats 4000000
set_option maxRecDepth 4096

private def oldAllocation : Allocation :=
  { id := ⟨7⟩, base := 1024, size := 8, alive := false, origin := .cleanHeap, requested := 8 }
private def newAllocation : Allocation :=
  { id := ⟨9⟩, base := 1032, size := 8, alive := true, origin := .rustHeap, requested := 8 }
private def memory : Memory := { Memory.empty with allocations := [newAllocation,oldAllocation] }
private def byte : Plan := .leaf .U8 ⟨1,1⟩
private def boolean : Plan := .leaf .Bool ⟨1,1⟩
private def pointer : Plan := .leaf .Ptr ⟨8,8⟩
private def character : Plan := .leaf .Char ⟨4,4⟩
private def elementTy : Ty := .Tuple [.U8,.Bool,.Ptr]
private def elementFields : List (Nat × Plan) := [(0,byte),(1,boolean),(8,pointer)]
private def element : Plan := .fields elementTy ⟨16,8⟩ elementFields
private def elementInput : Value := .aggregate [.int 8 513,.bool false,.ptr 1025 (some ⟨99⟩)]
private def arrayTy : Ty := .Array ⟨0⟩ 3
private def array : Plan := .array arrayTy ⟨48,8⟩ 3 element
private def arrayValues : CompactArray.Packed Value := CompactArray.Packed.uniform 3 elementInput
private def tailTy : Ty := .Tuple [.Ptr,.Char]
private def tailFields : List (Nat × Plan) := [(0,pointer),(8,character)]
private def tail : Plan := .fields tailTy ⟨16,8⟩ tailFields
private def tailInput : Value := .aggregate [.ptr 0 (some ⟨99⟩),.int 32 55296]
private def kind : FatPtrKind := .Slice ⟨0⟩
private def fat : Plan := .leaf (.FatPtr kind) ⟨16,8⟩
private def rootTy : Ty := .Tuple [.Bool,arrayTy,.FatPtr kind,tailTy]
private def rootFields : List (Nat × Plan) := [(0,boolean),(8,array),(56,fat),(72,tail)]
private def root : Plan := .fields rootTy ⟨88,8⟩ rootFields
private def input : Value := .aggregate [.bool true,.array arrayValues,.fatPtr 1034 (some ⟨99⟩) (.int 64 (-1)),tailInput]
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
  match encode .le64 none root input false with
  | .ok image => image
  | .error _ => { bytes := ByteImage.empty }
set_option maxRecDepth 4096 in
private theorem encoded : encode .le64 none root input false = .ok stored := by
  trustIrCompilerProof {
    exact rfl
  } {
    exact by trustIrReduce
  }

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

set_option maxRecDepth 4096 in
theorem nested_pointer_uses_receiving_memory : project 1 2 = .ok (some (.ptr 1025 (some ⟨7⟩))) := by
  trustIrCompilerProof {
    exact rfl
  } {
    exact by trustIrReduce
  }

set_option maxRecDepth 4096 in
theorem fat_metadata_uses_declared_kind :
    project 2 0 = .ok (some (.fatPtr 1034 (some ⟨9⟩) (Value.intAt 64 (-1)))) := by
  trustIrCompilerProof {
    exact rfl
  } {
    exact by trustIrReduce
  }

set_option maxRecDepth 4096 in
theorem nested_zero_pointer_canonicalizes : project 3 0 = .ok (some .nullPtr) := by
  trustIrCompilerProof {
    exact rfl
  } {
    exact by trustIrReduce
  }

set_option maxRecDepth 4096 in
theorem nested_surrogate_stays_raw : project 3 1 = .ok (some (.int 32 55296)) := by
  trustIrCompilerProof {
    exact rfl
  } {
    exact by trustIrReduce
  }

set_option maxRecDepth 4096 in
theorem outer_padding_remains_absent : stored.bytes.get 1 = none ∧ stored.bytes.get 7 = none := by
  trustIrCompilerProof {
    exact ⟨rfl,rfl⟩
  } {
    exact ⟨by trustIrReduce,by trustIrReduce⟩
  }

private def nestedTy : Ty := .Array ⟨1⟩ 2
private def nestedPlan : Plan := .array nestedTy ⟨96,8⟩ 2 array
private def nestedInput : Value := .array (CompactArray.Packed.uniform 2 (.array arrayValues))
private def nestedSource : Environment := { types := [some elementTy,some arrayTy] }
private def nestedStored : Image :=
  match encode .le64 none nestedPlan nestedInput false with
  | .ok image => image
  | .error _ => { bytes := ByteImage.empty }
private theorem nestedPrepared : (prepare nestedSource []).query nestedTy = .ok nestedPlan := by
  trustIrCompilerProof {
    exact rfl
  } {
    exact by trustIrReduce
  }

private theorem nestedEncoded : encode .le64 none nestedPlan nestedInput false = .ok nestedStored := by
  trustIrCompilerProof {
    exact rfl
  } {
    exact by trustIrReduce
  }

private theorem nestedReady : ReadbackInput .le64 none memory nestedPlan nestedInput :=
  ReadbackInput.array_uniform nestedTy ⟨96,8⟩ 2 array (.array arrayValues)
    (ReadbackInput.array_uniform arrayTy ⟨48,8⟩ 3 element elementInput elementReady)

theorem arrays_of_mixed_arrays_readback :
    ∃ output, decode .le64 none memory nestedPlan nestedStored.bytes = .ok output ∧ ValueReadback .le64 memory nestedInput output :=
  prepared_recursive_readback nestedSource [] nestedTy nestedPlan nestedPrepared .le64 none memory nestedInput nestedReady
    (by intro layout width raw impossible; cases impossible) nestedStored nestedEncoded

private def enumInfo : Enumeration :=
  { tag := .u8, discriminants := [5], encoding := .untagged,
    variants := [[{ ty := rootTy, offset := 0, size := 88, align := 8 }]], uninhabited := [false] }
private def enumVariants : List (Option (List (Nat × Plan))) := [some [(0,root)]]
private def enumPlan : Plan := .enumeration (.Enum ⟨0⟩) ⟨88,8⟩ enumInfo enumVariants
private def enumInput : Value := .aggregate [.int 8 5,input]
private def definition : EnumDef :=
  { id := ⟨0⟩, name := "Mixed", variants := [{ name := "Mixed", fields := [rootTy] }], discriminants := [some 5], tagRepr := some .u8,
    layout := some { encoding := .untagged, size := 88, align := 8, variantFieldOffsets := [[0]] } }
private def enumSource : Environment := { types := [some elementTy], enums := [definition] }
private def enumStored : Image :=
  match encode .le64 none enumPlan enumInput false with
  | .ok image => image
  | .error _ => { bytes := ByteImage.empty }
private theorem enumPrepared : (prepare enumSource []).query (.Enum ⟨0⟩) = .ok enumPlan := by
  trustIrCompilerProof {
    dsimp only [enumSource,definition,enumPlan,enumInfo,enumVariants,root,rootTy,rootFields,fat,kind,tail,tailTy,tailFields,
      array,arrayTy,element,elementTy,elementFields,byte,boolean,pointer,character]
    rfl
  } {
    dsimp only [enumSource,definition,enumPlan,enumInfo,enumVariants,root,rootTy,rootFields,fat,kind,tail,tailTy,tailFields,
      array,arrayTy,element,elementTy,elementFields,byte,boolean,pointer,character]
    trustIrReduce
  }

private theorem enumEncoded : encode .le64 none enumPlan enumInput false = .ok enumStored := by
  trustIrCompilerProof {
    exact rfl
  } {
    exact by trustIrReduce
  }

private theorem prefixSound : EnumPrefixSound 88 enumInfo 0 (.int 8 5) := by
  refine ⟨⟨ByteImage.fill 88 none,rfl⟩,?_⟩
  intro initial built image
  exact EnumDecodingSelects.untagged enumInfo image rfl rfl (by decide)
private theorem enumReady : ReadbackInput .le64 none memory enumPlan enumInput :=
  ReadbackInput.enumeration_of_prefix ⟨0⟩ ⟨88,8⟩ enumInfo enumVariants (.int 8 5) [input] 0 5 [(0,root)]
    rfl rfl rfl rfl (.integer 8 5) (.cons rootReady .nil) prefixSound True.intro (fun _ _ => True.intro)

theorem recursive_enum_payload_readback :
    ∃ output, decode .le64 none memory enumPlan enumStored.bytes = .ok output ∧ ValueReadback .le64 memory enumInput output :=
  prepared_recursive_readback enumSource [] (.Enum ⟨0⟩) enumPlan enumPrepared .le64 none memory enumInput enumReady
    (by intro layout width raw impossible; cases impossible) enumStored enumEncoded

private def charSource : Environment := { types := [] }
private def charInput : Value := .int 32 128512
private def charStored : Image :=
  { bytes := ByteImage.ofList ((encodeIntBytes (truncateUnsigned 128512 32) 4).map some) }
private theorem charAdmitted : ReadbackInput .le64 none memory character charInput :=
  .scalar (.integer .Char ⟨4,4⟩ 32 128512 rfl rfl rfl)
private theorem charReady : TopCharReady character charInput := by
  intro layout width raw shape inputShape
  cases shape
  cases inputShape
  decide

theorem valid_top_character_readback :
    ∃ output, decode .le64 none memory character charStored.bytes = .ok output ∧ ValueReadback .le64 memory charInput output := by
  trustIrCompilerProof {
    exact prepared_recursive_readback charSource [] .Char character rfl .le64 none memory charInput charAdmitted charReady charStored rfl
  } {
    exact prepared_recursive_readback charSource [] .Char character (by trustIrReduce) .le64 none memory charInput charAdmitted charReady charStored (by trustIrReduce)
  }

theorem invalid_top_character_has_no_ready_certificate : ¬ TopCharReady character (.int 32 55296) := by
  intro ready
  have invalid : ¬ validChar (truncateUnsigned 55296 32).toNat := by decide
  exact invalid (ready ⟨4,4⟩ 32 55296 rfl rfl)

theorem invalid_top_character_still_refuses :
    decode .le64 none memory character (ByteImage.ofList [some 0,some 216,some 0,some 0]) =
      .error (.ub "memory decode: invalid Unicode scalar value") := by
  trustIrCompilerProof {
    exact rfl
  } {
    exact by trustIrReduce
  }

theorem float_is_not_implicitly_admitted (value : Float) : ¬ ScalarReadbackInput .le64 (.leaf .F64 ⟨8,8⟩) (.float value) := by
  intro admitted
  cases admitted

theorem unwritten_is_not_implicitly_admitted : ¬ ReadbackInput .le64 none memory byte .uninit := by
  intro admitted
  cases admitted with
  | scalar scalar => cases scalar
  | function function => cases function

theorem target32_overflow_has_no_scalar_certificate :
    ¬ ScalarReadbackInput .le32 (.leaf .Ptr ⟨4,4⟩) (.ptr 4294967296 none) := by
  intro admitted
  cases admitted with
  | pointer ty layout address provenance pointer bound extent =>
    have impossible : ¬ 4294967296 < ByteModel.le32.addressLimit := by decide
    exact impossible bound

private def badInfo : Enumeration :=
  { tag := .u8, discriminants := [10,20], encoding := .niche 0 1 1 1 0 .u8, variants := [[],[]], uninhabited := [false,false] }
private def badVariants : List (Option (List (Nat × Plan))) := [some [],some []]
private def badPlan : Plan := .enumeration (.Enum ⟨0⟩) ⟨1,1⟩ badInfo badVariants

theorem uninitialized_carrier_has_no_selection_certificate :
    ¬ (∀ image, encode .le64 none badPlan (.aggregate [.int 8 10]) false = .ok image → EnumDecodingSelects badInfo image.bytes 0) := by
  trustIrCompilerProof {
    intro certificate
    have selected := certificate { bytes := ByteImage.fill 1 none } rfl
    cases selected
  } {
    intro certificate
    have selected := certificate { bytes := ByteImage.fill 1 none } (by trustIrReduce)
    cases selected
  }

private def overlappingFields : List (Nat × Plan) := [(0,byte),(0,byte)]
private def overlapping : Plan := .fields (.Tuple [.U8,.U8]) ⟨1,1⟩ overlappingFields

theorem overlapping_plan_has_no_source_origin (environment : Environment) :
    ¬ Plan.Origin (SourceElement environment) (ActualSummary environment) (.Tuple [.U8,.U8]) overlapping := by
  intro origin
  have separated := (origin.fields_child_placement 0 0 byte rfl).2
  have impossible := separated (0,byte) (by change (0,byte) ∈ [(0,byte)]; exact .head [])
  change true = false at impossible
  cases impossible

end TrustIr.AggregateMemory.RecursiveReadbackControls
