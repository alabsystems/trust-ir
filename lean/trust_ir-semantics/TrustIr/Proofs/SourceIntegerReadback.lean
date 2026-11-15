-- Copyright 2026 Andrew Yates | Apache-2.0
import TrustIr.Proofs.SourceSiblingGeometry
import TrustIr.Proofs.IntResidue

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

/-- A successful field run retains each actual encoded child over the entire
    final lane when later writes are disjoint. No parent decoder is assumed. -/
theorem FieldsEncoded.child_lane {model : ByteModel} {order : FunctionAddressOrder}
    {fields : List (Nat × Plan)} {values : List Value} {before after : Image}
    (run : FieldsEncoded model order fields values false before after)
    (position offset : Nat) (child : Plan) (found : (trustIrListGet? fields position) = some (offset,child))
    (value : Value) (selected : (trustIrListGet? values position) = some value)
    (separated : FieldsAvoidLane (fields.drop (position + 1)) offset child.layout.size) :
    ∃ stored, encode model order child value false = .ok stored ∧ ByteLane after.bytes offset stored.bytes := by
  obtain ⟨actualValue,earlier,stored,placed,actual,_,encoded,written,suffix⟩ := run.at position offset child found
  rw [selected] at actual
  cases actual
  have size := encode_extent model order child value false stored encoded
  exact ⟨stored,encoded,suffix.preserves_lane written.lane (by simpa only [size] using separated)⟩

/-- An intact integer lane from its actual store is readable in strict nested
    mode. Padding outside the lane imposes no initialization premise. -/
theorem ByteLane.integer_child_readback (model : ByteModel) (order : FunctionAddressOrder) (memory : Memory)
    (ty : Ty) (layout : MemoryTypeLayout) (width : Nat) (raw : Int)
    (integer : ty.isInteger = true) (typed : ty.bitWidthFor model = some width)
    (extent : layout.size = width / 8) (stored : Image) (parent : ByteImage) (offset : Nat)
    (encoded : encode model order (.leaf ty layout) (.int width raw) false = .ok stored)
    (lane : ByteLane parent offset stored.bytes) :
    ChildDecoded model order memory (.leaf ty layout) (parent.slice offset layout.size) (Value.intAt width raw) := by
  have storedSize := encode_extent model order (.leaf ty layout) (.int width raw) false stored encoded
  change stored.bytes.size = layout.size at storedSize
  have bounded : offset + layout.size ≤ parent.size := by rw [← storedSize]; exact lane.1
  have loadedSize : (parent.slice offset layout.size).size = layout.size := by
    rw [ByteImage.size_slice]; omega
  apply integer_child_readback_of_encoded model order memory ty layout width raw integer typed extent stored _ encoded loadedSize
  intro index
  by_cases inside : index < layout.size
  · rw [ByteImage.get_slice parent offset layout.size index inside (by omega)]
    exact lane.2 index (by rw [storedSize]; exact inside)
  · rw [ByteImage.get_outside _ index (by rw [loadedSize]; omega),
      ByteImage.get_outside _ index (by rw [storedSize]; omega)]

/-- A selected integer field is readable after an actual successful parent
    store with later-write separation. Parent load success is not a premise. -/
theorem field_integer_child_readback (model : ByteModel) (order : FunctionAddressOrder) (memory : Memory)
    (ty : Ty) (layout : MemoryTypeLayout) (fields : List (Nat × Plan)) (values : List Value) (image : Image)
    (encoded : encode model order (.fields ty layout fields) (.aggregate values) false = .ok image)
    (position offset : Nat) (childTy : Ty) (childLayout : MemoryTypeLayout)
    (found : (trustIrListGet? fields position) = some (offset,.leaf childTy childLayout))
    (width : Nat) (raw : Int) (selected : (trustIrListGet? values position) = some (.int width raw))
    (integer : childTy.isInteger = true) (typed : childTy.bitWidthFor model = some width)
    (extent : childLayout.size = width / 8)
    (separated : FieldsAvoidLane (fields.drop (position + 1)) offset childLayout.size) :
    ChildDecoded model order memory (.leaf childTy childLayout)
      (image.bytes.slice offset childLayout.size) (Value.intAt width raw) := by
  obtain ⟨actual,same,run⟩ := encode_fields_steps model order ty layout fields (.aggregate values) image encoded
  cases same
  obtain ⟨stored,storedRun,lane⟩ := run.child_lane position offset (.leaf childTy childLayout) found
    (.int width raw) selected separated
  exact lane.integer_child_readback model order memory childTy childLayout width raw integer typed extent stored image.bytes offset storedRun

/-- Actual prepared source metadata discharges the later-write condition for
    integer field readback, including target-width integers and nested Char. -/
theorem prepared_field_integer_child_readback (source : Environment) (roots : List Ty)
    (model : ByteModel) (order : FunctionAddressOrder) (memory : Memory)
    (ty : Ty) (layout : MemoryTypeLayout) (fields : List (Nat × Plan))
    (prepared : (prepare source roots).query ty = .ok (.fields ty layout fields))
    (values : List Value) (image : Image)
    (encoded : encode model order (.fields ty layout fields) (.aggregate values) false = .ok image)
    (position offset : Nat) (childTy : Ty) (childLayout : MemoryTypeLayout)
    (found : (trustIrListGet? fields position) = some (offset,.leaf childTy childLayout))
    (width : Nat) (raw : Int) (selected : (trustIrListGet? values position) = some (.int width raw))
    (integer : childTy.isInteger = true) (typed : childTy.bitWidthFor model = some width)
    (extent : childLayout.size = width / 8) :
    ChildDecoded model order memory (.leaf childTy childLayout)
      (image.bytes.slice offset childLayout.size) (Value.intAt width raw) :=
  field_integer_child_readback model order memory ty layout fields values image encoded position offset childTy childLayout found
    width raw selected integer typed extent
    ((prepared_plan_origin source roots ty _ prepared).fields_child_placement position offset (.leaf childTy childLayout) found).2

/-- Every retained integer array slot is readable after successful encoding,
    across all compact representations. No array decoder success is assumed. -/
theorem array_integer_child_readback (model : ByteModel) (order : FunctionAddressOrder) (memory : Memory)
    (ty : Ty) (layout : MemoryTypeLayout) (count : Nat) (childTy : Ty) (childLayout : MemoryTypeLayout)
    (values : CompactArray.Packed Value) (image : Image)
    (encoded : encode model order (.array ty layout count (.leaf childTy childLayout)) (.array values) false = .ok image)
    (slot : Nat) (width : Nat) (raw : Int) (inside : slot < values.size)
    (selected : values.tree.get? slot = some (.int width raw))
    (integer : childTy.isInteger = true) (typed : childTy.bitWidthFor model = some width)
    (extent : childLayout.size = width / 8) :
    ChildDecoded model order memory (.leaf childTy childLayout)
      (image.bytes.slice (slot * childLayout.size) childLayout.size) (Value.intAt width raw) := by
  obtain ⟨stored,storedRun,lane⟩ := encode_array_slot model order ty layout count (.leaf childTy childLayout)
    values image encoded slot (.int width raw) inside selected
  exact lane.integer_child_readback model order memory childTy childLayout width raw integer typed extent stored image.bytes
    (slot * childLayout.size) storedRun

/-- An actual selected enum payload store makes its integer child readable.
    This proves the child call, without asserting parent selector/read success. -/
theorem enum_integer_child_readback (model : ByteModel) (order : FunctionAddressOrder) (memory : Memory)
    (ty : Ty) (layout : MemoryTypeLayout) (info : Enumeration)
    (variants : List (Option (List (Nat × Plan)))) (tag : Value) (values : List Value) (image : Image)
    (encoded : encode model order (.enumeration ty layout info variants) (.aggregate (tag :: values)) false = .ok image)
    (position : Nat) (selectedVariant : EnumEncodingSelects info tag position)
    (fields : List (Nat × Plan)) (row : (trustIrListGet? variants position) = some (some fields))
    (fieldPosition offset : Nat) (childTy : Ty) (childLayout : MemoryTypeLayout)
    (found : (trustIrListGet? fields fieldPosition) = some (offset,.leaf childTy childLayout))
    (width : Nat) (raw : Int) (selected : (trustIrListGet? values fieldPosition) = some (.int width raw))
    (integer : childTy.isInteger = true) (typed : childTy.bitWidthFor model = some width)
    (extent : childLayout.size = width / 8)
    (separated : FieldsAvoidLane (fields.drop (fieldPosition + 1)) offset childLayout.size) :
    ChildDecoded model order memory (.leaf childTy childLayout)
      (image.bytes.slice offset childLayout.size) (Value.intAt width raw) := by
  obtain ⟨actualPosition,_initialBytes,actualSelected,_,variantRun,_⟩ :=
    encode_enumeration_steps model order ty layout info variants tag values false image encoded
  have same := actualSelected.functional selectedVariant
  subst actualPosition
  obtain ⟨actualFields,actualRow,run⟩ := variantRun.fields
  rw [row] at actualRow
  cases actualRow
  obtain ⟨stored,storedRun,lane⟩ := run.child_lane fieldPosition offset (.leaf childTy childLayout) found
    (.int width raw) selected separated
  exact lane.integer_child_readback model order memory childTy childLayout width raw integer typed extent stored image.bytes offset storedRun

/-- Prepared enum metadata supplies later-payload-write separation. Default
    niche carrier readiness remains a separate parent-selection obligation. -/
theorem prepared_enum_integer_child_readback (source : Environment) (roots : List Ty) (id : EnumId)
    (model : ByteModel) (order : FunctionAddressOrder) (memory : Memory)
    (layout : MemoryTypeLayout) (info : Enumeration) (variants : List (Option (List (Nat × Plan))))
    (prepared : (prepare source roots).query (.Enum id) = .ok (.enumeration (.Enum id) layout info variants))
    (tag : Value) (values : List Value) (image : Image)
    (encoded : encode model order (.enumeration (.Enum id) layout info variants) (.aggregate (tag :: values)) false = .ok image)
    (position : Nat) (selectedVariant : EnumEncodingSelects info tag position)
    (fields : List (Nat × Plan)) (row : (trustIrListGet? variants position) = some (some fields))
    (fieldPosition offset : Nat) (childTy : Ty) (childLayout : MemoryTypeLayout)
    (found : (trustIrListGet? fields fieldPosition) = some (offset,.leaf childTy childLayout))
    (width : Nat) (raw : Int) (selected : (trustIrListGet? values fieldPosition) = some (.int width raw))
    (integer : childTy.isInteger = true) (typed : childTy.bitWidthFor model = some width)
    (extent : childLayout.size = width / 8) :
    ChildDecoded model order memory (.leaf childTy childLayout)
      (image.bytes.slice offset childLayout.size) (Value.intAt width raw) :=
  enum_integer_child_readback model order memory (.Enum id) layout info variants tag values image encoded position selectedVariant
    fields row fieldPosition offset childTy childLayout found width raw selected integer typed extent
    ((prepared_plan_origin source roots (.Enum id) _ prepared).enum_payload_child_placement position fields row
      fieldPosition offset (.leaf childTy childLayout) found).2


/-- Exact typed integer payload inputs and their canonical readback outputs.
    Every field is retained; there is no constructor for an uncovered family. -/
inductive IntegerFieldReadback (model : ByteModel) : List (Nat × Plan) → List Value → List Value → Prop where
  | nil : IntegerFieldReadback model [] [] []
  | cons (offset : Nat) (ty : Ty) (layout : MemoryTypeLayout) (width : Nat) (raw : Int)
      (integer : ty.isInteger = true) (typed : ty.bitWidthFor model = some width)
      (extent : layout.size = width / 8) {fields : List (Nat × Plan)} {inputs outputs : List Value}
      (rest : IntegerFieldReadback model fields inputs outputs) :
      IntegerFieldReadback model ((offset,.leaf ty layout) :: fields) (.int width raw :: inputs)
        (Value.intAt width raw :: outputs)

theorem IntegerFieldReadback.length {model : ByteModel} {fields : List (Nat × Plan)} {inputs outputs : List Value}
    (typed : IntegerFieldReadback model fields inputs outputs) : fields.length = outputs.length := by
  induction typed with
  | nil => rfl
  | cons _ _ _ _ _ _ _ _ _ ih => exact congrArg Nat.succ ih

/-- Every logical field/output occurrence has an actual typed input witness. -/
theorem IntegerFieldReadback.at {model : ByteModel} {fields : List (Nat × Plan)} {inputs outputs : List Value}
    (typed : IntegerFieldReadback model fields inputs outputs) (position offset : Nat) (child : Plan) (output : Value)
    (found : (trustIrListGet? fields position) = some (offset,child)) (selected : (trustIrListGet? outputs position) = some output) :
    ∃ ty layout width raw, child = .leaf ty layout ∧ (trustIrListGet? inputs position) = some (.int width raw) ∧
      output = Value.intAt width raw ∧ ty.isInteger = true ∧ ty.bitWidthFor model = some width ∧ layout.size = width / 8 := by
  induction typed generalizing position offset child output with
  | nil => cases found
  | cons firstOffset ty layout width raw integer scalar extent rest ih =>
    cases position with
    | zero =>
      cases found
      cases selected
      exact ⟨ty,layout,width,raw,rfl,rfl,rfl,integer,scalar,extent⟩
    | succ position => exact ih position offset child output found selected

/-- All typed integer children of a stored field product compose into its
    complete strict field run. No parent load success is assumed. -/
theorem IntegerFieldReadback.fields_decoded {model : ByteModel} {fields : List (Nat × Plan)} {inputs outputs : List Value}
    (typed : IntegerFieldReadback model fields inputs outputs) (order : FunctionAddressOrder) (memory : Memory)
    (ty : Ty) (layout : MemoryTypeLayout) (image : Image)
    (encoded : encode model order (.fields ty layout fields) (.aggregate inputs) false = .ok image)
    (separated : ∀ position offset child, (trustIrListGet? fields position) = some (offset,child) →
      FieldsAvoidLane (fields.drop (position + 1)) offset child.layout.size) :
    FieldsDecoded model order memory fields image.bytes outputs := by
  apply FieldsDecoded.of_get model order memory fields image.bytes outputs typed.length
  intro position offset child output found selected
  obtain ⟨childTy,childLayout,width,raw,shape,inputFound,outputShape,integer,scalar,extent⟩ :=
    typed.at position offset child output found selected
  subst child
  subst output
  exact field_integer_child_readback model order memory ty layout fields inputs image encoded position offset childTy childLayout
    found width raw inputFound integer scalar extent (separated position offset (.leaf childTy childLayout) found)

/-- Whole ordinary field-product decoding follows from an actual successful
    store and complete typed integer readback, with real suffix separation. -/
theorem integer_fields_decode (model : ByteModel) (order : FunctionAddressOrder) (memory : Memory)
    (ty : Ty) (layout : MemoryTypeLayout) (fields : List (Nat × Plan)) (inputs outputs : List Value)
    (typed : IntegerFieldReadback model fields inputs outputs) (image : Image)
    (encoded : encode model order (.fields ty layout fields) (.aggregate inputs) false = .ok image)
    (separated : ∀ position offset child, (trustIrListGet? fields position) = some (offset,child) →
      FieldsAvoidLane (fields.drop (position + 1)) offset child.layout.size) :
    decode model order memory (.fields ty layout fields) image.bytes = .ok (.aggregate outputs) :=
  decode_fields_of_children model order memory ty layout fields image.bytes outputs
    (encode_extent model order (.fields ty layout fields) (.aggregate inputs) false image encoded)
    (typed.fields_decoded order memory ty layout image encoded separated)

/-- Prepared source geometry closes all later-write premises for whole integer
    field-product decoding; padding need not be initialized. -/
theorem prepared_integer_fields_decode (source : Environment) (roots : List Ty)
    (model : ByteModel) (order : FunctionAddressOrder) (memory : Memory)
    (ty : Ty) (layout : MemoryTypeLayout) (fields : List (Nat × Plan))
    (prepared : (prepare source roots).query ty = .ok (.fields ty layout fields))
    (inputs outputs : List Value) (typed : IntegerFieldReadback model fields inputs outputs) (image : Image)
    (encoded : encode model order (.fields ty layout fields) (.aggregate inputs) false = .ok image) :
    decode model order memory (.fields ty layout fields) image.bytes = .ok (.aggregate outputs) :=
  integer_fields_decode model order memory ty layout fields inputs outputs typed image encoded (fun position offset child found =>
    ((prepared_plan_origin source roots ty _ prepared).fields_child_placement position offset child found).2)

/-- Successful selected enum stores supply every actual typed integer payload
    read, hence the complete strict payload run, independently of parent load. -/
theorem IntegerFieldReadback.enum_payload_decoded {model : ByteModel} {fields : List (Nat × Plan)} {inputs outputs : List Value}
    (typed : IntegerFieldReadback model fields inputs outputs) (order : FunctionAddressOrder) (memory : Memory)
    (ty : Ty) (layout : MemoryTypeLayout) (info : Enumeration) (variants : List (Option (List (Nat × Plan))))
    (tag : Value) (image : Image)
    (encoded : encode model order (.enumeration ty layout info variants) (.aggregate (tag :: inputs)) false = .ok image)
    (position : Nat) (selectedVariant : EnumEncodingSelects info tag position)
    (row : (trustIrListGet? variants position) = some (some fields))
    (separated : ∀ fieldPosition offset child, (trustIrListGet? fields fieldPosition) = some (offset,child) →
      FieldsAvoidLane (fields.drop (fieldPosition + 1)) offset child.layout.size) :
    FieldsDecoded model order memory fields image.bytes outputs := by
  apply FieldsDecoded.of_get model order memory fields image.bytes outputs typed.length
  intro fieldPosition offset child output found selected
  obtain ⟨childTy,childLayout,width,raw,shape,inputFound,outputShape,integer,scalar,extent⟩ :=
    typed.at fieldPosition offset child output found selected
  subst child
  subst output
  exact enum_integer_child_readback model order memory ty layout info variants tag inputs image encoded position selectedVariant
    fields row fieldPosition offset childTy childLayout found width raw inputFound integer scalar extent
    (separated fieldPosition offset (.leaf childTy childLayout) found)

/-- The checked capture chain now concludes whole enum decoding for complete
    integer payloads. Actual niche carrier readiness remains an explicit premise. -/
theorem prepared_enum_capture_integer_decode (source : Environment) (ctx : EvalContext)
    (associated : CaptureSource source ctx) (admitted : enumIdsAdmitted source.enums = true)
    (roots : List Ty) (id : EnumId) (definition : EnumDef) (resolved : ctx.enums id = some definition)
    (plan : Plan) (prepared : (prepare source roots).query (.Enum id) = .ok plan)
    (fuel : Nat) (values : List Value) (initialized : (Value.aggregate values).Initialized)
    (checked : checkClosureValueAt ctx (fuel + 1) (.Enum id) (.aggregate values) = .ok ()) :
    ∃ layout info variants tag inputs position variant fields,
      plan = .enumeration (.Enum id) layout info variants ∧ values = tag :: inputs ∧
      EnumTagSelects definition tag position ∧ (trustIrListGet? definition.variants position) = some variant ∧
      EnumEncodingSelects info tag position ∧ (trustIrListGet? info.uninhabited position) = some false ∧
      (trustIrListGet? variants position) = some (some fields) ∧
      ∀ model order memory image outputs,
        encode model order plan (.aggregate values) false = .ok image →
        EnumUntaggedCarrierReady info position image.bytes → IntegerFieldReadback model fields inputs outputs →
        ∃ discriminant, (trustIrListGet? info.discriminants position) = some discriminant ∧
          decode model order memory plan image.bytes = .ok (.aggregate (Value.intAt (tagBits info.tag) discriminant :: outputs)) := by
  obtain ⟨layout,info,variants,tag,inputs,position,variant,fields,
    shape,valuesShape,sourceSelected,definitionRow,inputSelected,live,row,_origins,finish⟩ :=
    prepared_enum_capture_coherent_encoded_selection source ctx associated admitted roots id definition resolved plan prepared
      fuel values initialized checked
  refine ⟨layout,info,variants,tag,inputs,position,variant,fields,
    shape,valuesShape,sourceSelected,definitionRow,inputSelected,live,row,?_⟩
  intro model order memory image outputs encoded carrier typed
  obtain ⟨extent,selected⟩ := finish model order false image encoded carrier
  obtain ⟨discriminant,discriminantRow⟩ := selected.discriminant
  have encodedRoot : encode model order (.enumeration (.Enum id) layout info variants) (.aggregate (tag :: inputs)) false = .ok image := by
    simpa only [shape,valuesShape] using encoded
  have preparedRoot : (prepare source roots).query (.Enum id) = .ok (.enumeration (.Enum id) layout info variants) := by
    simpa only [shape] using prepared
  have origin := prepared_plan_origin source roots (.Enum id) _ preparedRoot
  have payload := typed.enum_payload_decoded order memory (.Enum id) layout info variants tag image encodedRoot position inputSelected row
    (fun fieldPosition offset child found => (origin.enum_payload_child_placement position fields row fieldPosition offset child found).2)
  refine ⟨discriminant,discriminantRow,?_⟩
  simpa only [shape] using decode_enumeration_of_payload model order memory (.Enum id) layout info variants image.bytes
    position discriminant fields outputs extent selected discriminantRow row payload


/-- Integer field-product readback also constructs a nested aggregate call,
    preserving strict child mode throughout. -/
theorem integer_fields_child_decode (model : ByteModel) (order : FunctionAddressOrder) (memory : Memory)
    (ty : Ty) (layout : MemoryTypeLayout) (fields : List (Nat × Plan)) (inputs outputs : List Value)
    (typed : IntegerFieldReadback model fields inputs outputs) (image : Image)
    (encoded : encode model order (.fields ty layout fields) (.aggregate inputs) false = .ok image)
    (separated : ∀ position offset child, (trustIrListGet? fields position) = some (offset,child) →
      FieldsAvoidLane (fields.drop (position + 1)) offset child.layout.size) :
    ChildDecoded model order memory (.fields ty layout fields) image.bytes (.aggregate outputs) :=
  ChildDecoded.fields_of_children model order memory ty layout fields image.bytes outputs
    (encode_extent model order (.fields ty layout fields) (.aggregate inputs) false image encoded)
    (typed.fields_decoded order memory ty layout image encoded separated)


/-- Any actual callback window with the stored lane's complete observations
    reads the same canonical integer; no storage-constructor equality is used. -/
theorem ByteLane.integer_window_readback (model : ByteModel) (order : FunctionAddressOrder) (memory : Memory)
    (ty : Ty) (layout : MemoryTypeLayout) (width : Nat) (raw : Int)
    (integer : ty.isInteger = true) (typed : ty.bitWidthFor model = some width)
    (extent : layout.size = width / 8) (stored : Image) (parent part : ByteImage) (offset : Nat)
    (encoded : encode model order (.leaf ty layout) (.int width raw) false = .ok stored)
    (lane : ByteLane parent offset stored.bytes) (partSize : part.size = layout.size)
    (bytes : ∀ index, index < layout.size → part.get index = parent.get (offset + index)) :
    ChildDecoded model order memory (.leaf ty layout) part (Value.intAt width raw) := by
  have storedSize := encode_extent model order (.leaf ty layout) (.int width raw) false stored encoded
  change stored.bytes.size = layout.size at storedSize
  apply integer_child_readback_of_encoded model order memory ty layout width raw integer typed extent stored part encoded partSize
  intro index
  by_cases inside : index < layout.size
  · exact (bytes index inside).trans (lane.2 index (by rw [storedSize]; exact inside))
  · rw [ByteImage.get_outside part index (by rw [partSize]; omega),
      ByteImage.get_outside stored.bytes index (by rw [storedSize]; omega)]

/-- All visible typed integer slots of an actual successful array store decode
    as a whole array. The result is pointwise, independent of compact shapes;
    neither parent decoder success nor callback extensionality is a premise. -/
theorem integer_array_decode (model : ByteModel) (order : FunctionAddressOrder) (memory : Memory)
    (ty : Ty) (layout : MemoryTypeLayout) (count : Nat) (childTy : Ty) (childLayout : MemoryTypeLayout)
    (width : Nat) (values : CompactArray.Packed Value) (image : Image)
    (encoded : encode model order (.array ty layout count (.leaf childTy childLayout)) (.array values) false = .ok image)
    (integer : childTy.isInteger = true) (typed : childTy.bitWidthFor model = some width)
    (extent : childLayout.size = width / 8)
    (inputs : ∀ slot value, slot < values.size → values.tree.get? slot = some value → ∃ raw, value = .int width raw) :
    ∃ outputs : CompactArray.Packed Value, outputs.size = values.size ∧
      decode model order memory (.array ty layout count (.leaf childTy childLayout)) image.bytes = .ok (.array outputs) ∧
      ∀ slot, slot < values.size → ∃ raw,
        values.tree.get? slot = some (.int width raw) ∧ outputs.tree.get? slot = some (Value.intAt width raw) := by
  obtain ⟨census,layoutExtent⟩ := encode_array_geometry model order ty layout count (.leaf childTy childLayout) values image encoded
  have reads : ∀ slot, slot < count → ∀ part, part.size = childLayout.size →
      (∀ index, index < childLayout.size → part.get index = image.bytes.get (slot * childLayout.size + index)) →
      ∃ value, ChildDecoded model order memory (.leaf childTy childLayout) part value := by
    intro slot inside part partSize bytes
    have sourceInside : slot < values.size := by rw [census]; exact inside
    obtain ⟨value,found⟩ := values.tree.get_exists slot sourceInside
    obtain ⟨raw,shape⟩ := inputs slot value sourceInside found
    subst value
    obtain ⟨stored,storedRun,lane⟩ := encode_array_slot model order ty layout count (.leaf childTy childLayout)
      values image encoded slot (.int width raw) sourceInside found
    exact ⟨Value.intAt width raw,lane.integer_window_readback model order memory childTy childLayout width raw integer typed extent
      stored image.bytes part (slot * childLayout.size) storedRun partSize bytes⟩
  obtain ⟨outputs,outputSize,decoded⟩ := decode_array_exists_of_mapper
    ByteImage.mapBlocks_exists_of_windows model order memory ty layout count (.leaf childTy childLayout) image.bytes
    layoutExtent (encode_extent model order (.array ty layout count (.leaf childTy childLayout)) (.array values) false image encoded) reads
  refine ⟨outputs,outputSize.trans census.symm,decoded,?_⟩
  intro slot inside
  have slotCount : slot < count := by rw [← census]; exact inside
  obtain ⟨input,inputFound⟩ := values.tree.get_exists slot inside
  obtain ⟨raw,shape⟩ := inputs slot input inside inputFound
  subst input
  obtain ⟨output,outputFound⟩ := outputs.tree.get_exists slot (by rw [outputSize]; exact slotCount)
  obtain ⟨part,partSize,actualRun,loadedLane⟩ := decode_array_slot model order memory ty layout count (.leaf childTy childLayout)
    layoutExtent image.bytes outputs decoded slot output slotCount outputFound
  obtain ⟨stored,storedRun,lane⟩ := encode_array_slot model order ty layout count (.leaf childTy childLayout)
    values image encoded slot (.int width raw) inside inputFound
  have expectedRun := lane.integer_window_readback model order memory childTy childLayout width raw integer typed extent
    stored image.bytes part (slot * childLayout.size) storedRun partSize
    (fun index inByte => (loadedLane.2 index (by rw [partSize]; exact inByte)).symm)
  have same := actualRun.functional expectedRun
  refine ⟨raw,inputFound,?_⟩
  rw [← same]
  exact outputFound


/-- Whole integer-array readback also supplies the strict nested parent call
    and the same pointwise normalized result, ready for aggregate recursion. -/
theorem integer_array_child_decode (model : ByteModel) (order : FunctionAddressOrder) (memory : Memory)
    (ty : Ty) (layout : MemoryTypeLayout) (count : Nat) (childTy : Ty) (childLayout : MemoryTypeLayout)
    (width : Nat) (values : CompactArray.Packed Value) (image : Image)
    (encoded : encode model order (.array ty layout count (.leaf childTy childLayout)) (.array values) false = .ok image)
    (integer : childTy.isInteger = true) (typed : childTy.bitWidthFor model = some width)
    (extent : childLayout.size = width / 8)
    (inputs : ∀ slot value, slot < values.size → values.tree.get? slot = some value → ∃ raw, value = .int width raw) :
    ∃ outputs : CompactArray.Packed Value, outputs.size = values.size ∧
      ChildDecoded model order memory (.array ty layout count (.leaf childTy childLayout)) image.bytes (.array outputs) ∧
      ∀ slot, slot < values.size → ∃ raw,
        values.tree.get? slot = some (.int width raw) ∧ outputs.tree.get? slot = some (Value.intAt width raw) := by
  obtain ⟨outputs,census,decoded,slots⟩ := integer_array_decode model order memory ty layout count childTy childLayout width values image
    encoded integer typed extent inputs
  exact ⟨outputs,census,(ChildDecoded.array_iff_decode model order memory ty layout count (.leaf childTy childLayout) image.bytes
    (.array outputs)).mpr decoded,slots⟩

end TrustIr.AggregateMemory

namespace TrustIr.AggregateMemory.IntegerReadbackControls

private def byte : Plan := .leaf .U8 ⟨1,1⟩
private def fields : List (Nat × Plan) := [(0,byte),(2,byte)]
private def parent : Plan := .fields (.Tuple [.U8,.U8]) ⟨4,1⟩ fields
private def image : Image :=
  match encode .le64 none parent (.aggregate [.int 8 513,.int 8 7]) false with
  | .ok result => result
  | .error _ => { bytes := ByteImage.empty }

private theorem one_observations (value : Option UInt8) (index : Nat) :
    (ByteImage.fill 1 value).get index = (ByteImage.ofList [value]).get index := by
  by_cases zero : index = 0
  · subst index; rfl
  · rw [ByteImage.get_outside _ index (by change 1 ≤ index; omega),
      ByteImage.get_outside _ index (by change 1 ≤ index; omega)]

theorem actual_parent_store : encode .le64 none parent (.aggregate [.int 8 513,.int 8 7]) false = .ok image := by
  trustIrCompilerProof {
    exact rfl
  } {
    exact by trustIrReduce
  }

theorem stored_field_readback_without_parent_load :
    ChildDecoded .le64 none Memory.empty byte (image.bytes.slice 0 1) (Value.intAt 8 513) :=
  field_integer_child_readback .le64 none Memory.empty _ ⟨4,1⟩ fields _ image actual_parent_store
    0 0 .U8 ⟨1,1⟩ rfl 8 513 rfl rfl rfl rfl (by
      intro field member
      cases member with
      | head => rfl
      | tail _ impossible => cases impossible)

theorem negative_target32_child (order : FunctionAddressOrder) (memory : Memory) :
    ChildDecoded .le32 order memory (.leaf .Isize ⟨4,4⟩)
      (ByteImage.ofList ((encodeIntBytes (truncateUnsigned (-1) 32) 4).map some)) (Value.intAt 32 (-1)) :=
  integer_child_leaf_bytes .le32 order memory .Isize ⟨4,4⟩ 32 (-1) rfl rfl rfl

theorem nested_surrogate_is_raw (model : ByteModel) (order : FunctionAddressOrder) (memory : Memory) :
    ChildDecoded model order memory (.leaf .Char ⟨4,4⟩)
      (ByteImage.ofList ((encodeIntBytes (truncateUnsigned 55296 32) 4).map some)) (Value.intAt 32 55296) :=
  integer_child_leaf_bytes model order memory .Char ⟨4,4⟩ 32 55296 rfl (by cases model <;> rfl) rfl

theorem top_surrogate_still_refuses :
    decode .le64 none Memory.empty (.leaf .Char ⟨4,4⟩)
      (ByteImage.ofList [some 0,some 216,some 0,some 0]) =
      .error (.ub "memory decode: invalid Unicode scalar value") := by
  trustIrCompilerProof {
    exact rfl
  } {
    exact by trustIrReduce
  }

theorem scalar_storage_shape_does_not_change_result (value : Option UInt8) :
    decode .le64 none Memory.empty byte (ByteImage.fill 1 value) =
      decode .le64 none Memory.empty byte (ByteImage.ofList [value]) :=
  decode_leaf_eq_of_observations .le64 none Memory.empty .U8 ⟨1,1⟩ _ _ rfl (one_observations value)

theorem missing_scalar_byte_still_refuses :
    decode .le64 none Memory.empty byte (ByteImage.fill 1 none) =
      .error (.ub "Load: reading uninitialized covered memory") := by
  trustIrCompilerProof {
    exact rfl
  } {
    exact by trustIrReduce
  }

theorem extent_is_independent_of_total_byte_reads :
    (∀ index, ByteImage.empty.get index = (ByteImage.fill 1 none).get index) ∧
      ByteImage.empty.size ≠ (ByteImage.fill 1 none).size := by
  refine ⟨?_,by decide⟩
  intro index
  by_cases zero : index = 0
  · subst index; rfl
  · rw [ByteImage.get_outside _ index (by change 0 ≤ index; omega),
      ByteImage.get_outside _ index (by change 1 ≤ index; omega)]

theorem clipped_empty_windows_keep_observations (value : Option UInt8) (index : Nat) :
    ((ByteImage.fill 1 value).slice 9 3).get index = ((ByteImage.ofList [value]).slice 9 3).get index :=
  ByteImage.slice_get_eq_of_observations (ByteImage.fill 1 value) (ByteImage.ofList [value]) rfl (one_observations value) 9 3 index

private def arrayValues : CompactArray.Packed Value := CompactArray.Packed.uniform 1000000 (.int 8 513)
private def arrayImage : Image := { bytes := (ByteImage.ofList [some 1]).tile 1000000 }
private theorem arrayEncoded : encode .le64 none (.array (.Array ⟨0⟩ 1000000) ⟨1000000,1⟩ 1000000 byte)
    (.array arrayValues) false = .ok arrayImage := by
  trustIrCompilerProof {
    exact encode_uniform_array .le64 none (.Array ⟨0⟩ 1000000) ⟨1000000,1⟩ 1000000 byte (.int 8 513)
      { bytes := ByteImage.ofList [some 1] } (by decide) rfl rfl
  } {
    exact encode_uniform_array .le64 none (.Array ⟨0⟩ 1000000) ⟨1000000,1⟩ 1000000 byte (.int 8 513)
      { bytes := ByteImage.ofList [some 1] } (by decide) (by trustIrReduce) rfl
  }

set_option maxRecDepth 4096 in
theorem million_uniform_slot_readback :
    ChildDecoded .le64 none Memory.empty byte (arrayImage.bytes.slice 999999 1) (Value.intAt 8 513) :=
  array_integer_child_readback .le64 none Memory.empty (.Array ⟨0⟩ 1000000) ⟨1000000,1⟩ 1000000 .U8 ⟨1,1⟩
    arrayValues arrayImage arrayEncoded 999999 8 513 (by decide) rfl rfl rfl rfl

end TrustIr.AggregateMemory.IntegerReadbackControls

namespace TrustIr.AggregateMemory.ParentDecoderControls
open SourceLayout

private def byte : Plan := .leaf .U8 ⟨1,1⟩
private def character : Plan := .leaf .Char ⟨4,4⟩
private def fields : List (Nat × Plan) := [(0,byte),(4,character)]
private def ty : Ty := .Tuple [.U8,.Char]
private def plan : Plan := .fields ty ⟨8,4⟩ fields
private def inputs : List Value := [.int 8 513,.int 32 55296]
private def outputs : List Value := [Value.intAt 8 513,Value.intAt 32 55296]
private def source : Environment := { types := [] }
private theorem prepared : (prepare source []).query ty = .ok plan := by
  trustIrCompilerProof {
    exact rfl
  } {
    exact by trustIrReduce
  }

private def image : Image :=
  match encode .le64 none plan (.aggregate inputs) false with
  | .ok result => result
  | .error _ => { bytes := ByteImage.empty }
private theorem typed : IntegerFieldReadback .le64 fields inputs outputs :=
  .cons (model := .le64) 0 .U8 ⟨1,1⟩ 8 513 rfl rfl rfl (.cons (model := .le64) 4 .Char ⟨4,4⟩ 32 55296 rfl rfl rfl .nil)

theorem actual_parent_store : encode .le64 none plan (.aggregate inputs) false = .ok image := by
  trustIrCompilerProof {
    exact rfl
  } {
    exact by trustIrReduce
  }

theorem whole_prepared_parent_load : decode .le64 none Memory.empty plan image.bytes = .ok (.aggregate outputs) :=
  prepared_integer_fields_decode source [] .le64 none Memory.empty ty ⟨8,4⟩ fields prepared inputs outputs typed image actual_parent_store

theorem parent_padding_stays_absent : image.bytes.get 1 = none ∧ image.bytes.get 2 = none ∧ image.bytes.get 3 = none := by
  trustIrCompilerProof {
    exact ⟨rfl,rfl,rfl⟩
  } {
    exact ⟨by trustIrReduce,by trustIrReduce,by trustIrReduce⟩
  }

theorem strict_nested_parent_load : ChildDecoded .le64 none Memory.empty plan image.bytes (.aggregate outputs) :=
  integer_fields_child_decode .le64 none Memory.empty ty ⟨8,4⟩ fields inputs outputs typed image actual_parent_store
    (fun position offset child found =>
      ((prepared_plan_origin source [] ty plan prepared).fields_child_placement position offset child found).2)

theorem logical_outputs_are_normalized : outputs = [.int 8 1,.int 32 55296] := by
  trustIrCompilerProof {
    exact rfl
  } {
    exact by trustIrReduce
  }

theorem empty_product_parent_load :
    decode .le64 none Memory.empty (.fields (.Tuple []) ⟨0,1⟩ []) ByteImage.empty = .ok (.aggregate []) := by
  trustIrCompilerProof {
    exact integer_fields_decode .le64 none Memory.empty (.Tuple []) ⟨0,1⟩ [] [] [] .nil { bytes := ByteImage.empty }
      rfl (by intro position offset child impossible; cases impossible)
  } {
    exact integer_fields_decode .le64 none Memory.empty (.Tuple []) ⟨0,1⟩ [] [] [] .nil { bytes := ByteImage.empty }
      (by trustIrReduce) (by intro position offset child impossible; cases impossible)
  }

theorem integer_relation_has_no_missing_outputs : ¬ IntegerFieldReadback .le64 fields inputs [] := by
  intro relation
  have census := relation.length
  change 2 = 0 at census
  cases census

theorem bool_is_not_silently_covered : ¬ IntegerFieldReadback .le64 [(0,.leaf .Bool ⟨1,1⟩)] [.bool true] [.bool true] := by
  intro relation
  cases relation

theorem successful_child_does_not_erase_parent_extent_check :
    FieldsDecoded .le64 none Memory.empty [(0,byte)] (ByteImage.ofList [some 7]) [.int 8 7] ∧
    decode .le64 none Memory.empty (.fields (.Tuple [.U8]) ⟨2,1⟩ [(0,byte)]) (ByteImage.ofList [some 7]) =
      .error (.typeError "Load: image size does not match source layout") := by
  trustIrCompilerProof {
    exact ⟨rfl,rfl⟩
  } {
    exact ⟨by trustIrReduce,by trustIrReduce⟩
  }

theorem selection_cannot_invent_discriminant (info : Enumeration) (image : ByteImage)
    (empty : info.discriminants = []) (position : Nat) : ¬ EnumDecodingSelects info image position := by
  intro selected
  have bound := selected.bound
  rw [empty] at bound
  change position < 0 at bound
  omega

private def enumInfo : Enumeration :=
  { tag := .u8, discriminants := [10,20], encoding := .direct 0,
    variants := [[{ ty := .Char, offset := 4, size := 4, align := 4 }],[]], uninhabited := [false,false] }
private def enumVariants : List (Option (List (Nat × Plan))) := [some [(4,character)],some []]
private def enumPlan : Plan := .enumeration (.Enum ⟨0⟩) ⟨8,4⟩ enumInfo enumVariants
private def enumInput : List Value := [.int 8 10,.int 32 128512]
private def enumImage : Image :=
  match encode .le64 none enumPlan (.aggregate enumInput) false with
  | .ok result => result
  | .error _ => { bytes := ByteImage.empty }
private theorem enumStored : encode .le64 none enumPlan (.aggregate enumInput) false = .ok enumImage := by
  trustIrCompilerProof {
    exact rfl
  } {
    exact by trustIrReduce
  }

private theorem enumTyped : IntegerFieldReadback .le64 [(4,character)] [.int 32 128512] [Value.intAt 32 128512] :=
  .cons (model := .le64) 4 .Char ⟨4,4⟩ 32 128512 rfl rfl rfl .nil

theorem actual_enum_payload_run : FieldsDecoded .le64 none Memory.empty [(4,character)] enumImage.bytes [Value.intAt 32 128512] :=
  enumTyped.enum_payload_decoded none Memory.empty (.Enum ⟨0⟩) ⟨8,4⟩ enumInfo enumVariants (.int 8 10) enumImage enumStored
    0 rfl rfl (by
      intro position offset child found
      cases position with
      | zero => cases found; intro field impossible; cases impossible
      | succ position => cases found)

theorem whole_enum_load_from_payload_success : decode .le64 none Memory.empty enumPlan enumImage.bytes =
    .ok (.aggregate [Value.intAt 8 10,Value.intAt 32 128512]) := by
  trustIrCompilerProof {
    exact decode_enumeration_of_payload .le64 none Memory.empty (.Enum ⟨0⟩) ⟨8,4⟩ enumInfo enumVariants enumImage.bytes 0 10
      [(4,character)] [Value.intAt 32 128512]
      (encode_extent .le64 none enumPlan (.aggregate enumInput) false enumImage enumStored) rfl rfl rfl actual_enum_payload_run
  } {
    exact decode_enumeration_of_payload .le64 none Memory.empty (.Enum ⟨0⟩) ⟨8,4⟩ enumInfo enumVariants enumImage.bytes 0 10
      [(4,character)] [Value.intAt 32 128512]
      (encode_extent .le64 none enumPlan (.aggregate enumInput) false enumImage enumStored) (by trustIrReduce) rfl rfl actual_enum_payload_run
  }

theorem strict_nested_enum_load : ChildDecoded .le64 none Memory.empty enumPlan enumImage.bytes
    (.aggregate [Value.intAt 8 10,Value.intAt 32 128512]) := by
  trustIrCompilerProof {
    exact ChildDecoded.enumeration_of_payload .le64 none Memory.empty (.Enum ⟨0⟩) ⟨8,4⟩ enumInfo enumVariants enumImage.bytes 0 10
      [(4,character)] [Value.intAt 32 128512]
      (encode_extent .le64 none enumPlan (.aggregate enumInput) false enumImage enumStored) rfl rfl rfl actual_enum_payload_run
  } {
    exact ChildDecoded.enumeration_of_payload .le64 none Memory.empty (.Enum ⟨0⟩) ⟨8,4⟩ enumInfo enumVariants enumImage.bytes 0 10
      [(4,character)] [Value.intAt 32 128512]
      (encode_extent .le64 none enumPlan (.aggregate enumInput) false enumImage enumStored) (by trustIrReduce) rfl rfl actual_enum_payload_run
  }

private def enumDefinition : EnumDef :=
  { id := ⟨0⟩, name := "CharacterOrUnit", variants := [{ name := "Character", fields := [.Char] },{ name := "Unit", fields := [] }],
    discriminants := [some 10,some 20], tagRepr := some .u8,
    layout := some { encoding := .direct 0, size := 8, align := 4, variantFieldOffsets := [[4],[]] } }
private def enumModule : TrustIrEval.Module :=
  { hasTargetInfo := true, functions := [], funcTys := [], globals := [], enums := [enumDefinition], structs := [], records := [], types := [] }
private def enumContext : EvalContext :=
  match TrustIrEval.contextOf enumModule 0 with
  | .ok context => context
  | .error _ => EvalContext.empty
private def enumSource : Environment := decodedCaptureSource enumModule enumContext.byteModel
private theorem contextReady : TrustIrEval.contextOf enumModule 0 = .ok enumContext := by
  trustIrCompilerProof {
    exact rfl
  } {
    exact by trustIrReduce
  }

private theorem associated : CaptureSource enumSource enumContext :=
  contextOf_capture_source enumModule 0 enumContext contextReady (by
    intro id definition member
    change (id,some definition) ∈ ([] : List (RecordId × Option RecordDef)) at member
    cases member)
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 4096 in
private theorem enumPrepared : (prepare enumSource []).query (.Enum ⟨0⟩) = .ok enumPlan := by
  trustIrCompilerProof {
    exact rfl
  } {
    exact by trustIrReduce
  }

private theorem enumInitialized : (Value.aggregate enumInput).Initialized :=
  .aggregate _ (by
    intro value member
    cases member with
    | head => exact .int 8 10
    | tail _ member =>
      cases member with
      | head => exact .int 32 128512
      | tail _ impossible => cases impossible)
set_option maxRecDepth 4096 in
private theorem enumChecked : checkClosureValueAt enumContext 4 (.Enum ⟨0⟩) (.aggregate enumInput) = .ok () := by
  trustIrCompilerProof {
    exact rfl
  } {
    exact by trustIrReduce
  }

/-- The full checked capture application concludes parent success without
    assuming a decoder result, with a real source plan and admitted payload. -/
theorem checked_capture_whole_enum_load : decode .le64 none Memory.empty enumPlan enumImage.bytes =
    .ok (.aggregate [Value.intAt 8 10,Value.intAt 32 128512]) := by
  trustIrCompilerProof {
    obtain ⟨layout,info,variants,tag,inputs,position,variant,fields,
      shape,valuesShape,_sourceSelected,_definitionRow,inputSelected,_live,row,finish⟩ :=
      prepared_enum_capture_integer_decode enumSource enumContext associated (by rfl) [] ⟨0⟩ enumDefinition (by rfl)
        enumPlan enumPrepared 3 enumInput enumInitialized enumChecked
    change Plan.enumeration (.Enum ⟨0⟩) ⟨8,4⟩ enumInfo enumVariants =
      Plan.enumeration (.Enum ⟨0⟩) layout info variants at shape
    obtain ⟨_,layoutEq,infoEq,variantsEq⟩ := Plan.enumeration.inj shape
    subst layout
    subst info
    subst variants
    change (.int 8 10 :: [.int 32 128512]) = tag :: inputs at valuesShape
    obtain ⟨tagEq,inputsEq⟩ := List.cons.inj valuesShape
    subst tag
    subst inputs
    have zero : EnumEncodingSelects enumInfo (.int 8 10) 0 := rfl
    have same := inputSelected.functional zero
    subst position
    have sameFields : [(4,character)] = fields := Option.some.inj (Option.some.inj row)
    subst fields
    obtain ⟨discriminant,discriminantRow,decoded⟩ :=
      finish .le64 none Memory.empty enumImage [Value.intAt 32 128512] enumStored (by trivial) enumTyped
    have sameDiscriminant : 10 = discriminant := Option.some.inj discriminantRow
    subst discriminant
    exact decoded
  } {
    obtain ⟨layout,info,variants,tag,inputs,position,variant,fields,
      shape,valuesShape,_sourceSelected,_definitionRow,inputSelected,_live,row,finish⟩ :=
      prepared_enum_capture_integer_decode enumSource enumContext associated (by rfl) [] ⟨0⟩ enumDefinition (by rfl)
        enumPlan enumPrepared 3 enumInput enumInitialized enumChecked
    change Plan.enumeration (.Enum ⟨0⟩) ⟨8,4⟩ enumInfo enumVariants =
      Plan.enumeration (.Enum ⟨0⟩) layout info variants at shape
    obtain ⟨_,layoutEq,infoEq,variantsEq⟩ := Plan.enumeration.inj shape
    subst layout
    subst info
    subst variants
    change (.int 8 10 :: [.int 32 128512]) = tag :: inputs at valuesShape
    obtain ⟨tagEq,inputsEq⟩ := List.cons.inj valuesShape
    subst tag
    subst inputs
    have zero : EnumEncodingSelects enumInfo (.int 8 10) 0 := by trustIrReduce
    have same := inputSelected.functional zero
    subst position
    have sameFields : [(4,character)] = fields := Option.some.inj (Option.some.inj row)
    subst fields
    obtain ⟨discriminant,discriminantRow,decoded⟩ :=
      finish .le64 none Memory.empty enumImage [Value.intAt 32 128512] enumStored (by trivial) enumTyped
    have sameDiscriminant : 10 = discriminant := Option.some.inj discriminantRow
    subst discriminant
    exact decoded
  }

end TrustIr.AggregateMemory.ParentDecoderControls

namespace TrustIr.AggregateMemory.ArrayParentControls

private def byte : Plan := .leaf .U8 ⟨1,1⟩
private def a : Value := .int 8 513
private def b : Value := .int 8 (-1)
private def uniform : CompactArray.Packed Value := CompactArray.Packed.uniform 1000000 a
private def dense : CompactArray.Packed Value := ⟨3,.dense (by decide) (.cons a (.cons b (.cons a .nil)))⟩
private def split : CompactArray.Packed Value := ⟨4,.split (by decide) (.uniform 2 a) (.uniform 2 b)⟩
private def periodic : CompactArray.Packed Value :=
  ⟨5,.periodic (.dense (by decide) (.cons a (.cons b .nil))) (by decide) 1 5⟩
private def plan (values : CompactArray.Packed Value) : Plan :=
  .array (.Array ⟨0⟩ values.size) ⟨values.size,1⟩ values.size byte
private def stored (values : CompactArray.Packed Value) : Image :=
  match encode .le64 none (plan values) (.array values) false with
  | .ok image => image
  | .error _ => { bytes := ByteImage.empty }
private def checkInteger : Value → Except Unit Unit
  | .int width _ => if width == 8 then .ok () else .error ()
  | _ => .error ()
private theorem checkInteger_sound (value : Value) (accepted : checkInteger value = .ok ()) :
    ∃ raw, value = .int 8 raw := by
  cases value <;> simp only [checkInteger] at accepted <;> try cases accepted
  rename_i width raw
  split at accepted
  · rename_i typed
    have same : width = 8 := by simpa only [beq_iff_eq] using typed
    subst width
    exact ⟨raw,rfl⟩
  · cases accepted
private def Readback (values : CompactArray.Packed Value) (image : Image) : Prop :=
  ∃ outputs : CompactArray.Packed Value, outputs.size = values.size ∧
    decode .le64 none Memory.empty (plan values) image.bytes = .ok (.array outputs) ∧
    ∀ slot, slot < values.size → ∃ raw,
      values.tree.get? slot = some (.int 8 raw) ∧ outputs.tree.get? slot = some (Value.intAt 8 raw)
private theorem readback (values : CompactArray.Packed Value) (image : Image)
    (encoded : encode .le64 none (plan values) (.array values) false = .ok image)
    (checked : values.tree.checkStored checkInteger = .ok ()) : Readback values image :=
  integer_array_decode .le64 none Memory.empty (.Array ⟨0⟩ values.size) ⟨values.size,1⟩ values.size .U8 ⟨1,1⟩ 8 values image
    encoded rfl rfl rfl (fun slot value _inside found =>
      checkInteger_sound value (CompactArray.Tree.checkStored_get checkInteger values.tree slot value checked found))
private def uniformImage : Image := { bytes := (ByteImage.ofList [some 1]).tile 1000000 }
private theorem uniformStored : encode .le64 none (plan uniform) (.array uniform) false = .ok uniformImage := by
  trustIrCompilerProof {
    exact encode_uniform_array .le64 none (.Array ⟨0⟩ 1000000) ⟨1000000,1⟩ 1000000 byte a
      { bytes := ByteImage.ofList [some 1] } (by decide) rfl rfl
  } {
    exact encode_uniform_array .le64 none (.Array ⟨0⟩ 1000000) ⟨1000000,1⟩ 1000000 byte a
      { bytes := ByteImage.ofList [some 1] } (by decide) (by trustIrReduce) rfl
  }

theorem million_uniform_parent_decode : Readback uniform uniformImage := readback uniform uniformImage uniformStored rfl

theorem dense_parent_decode : Readback dense (stored dense) := by
  trustIrCompilerProof {
    exact readback dense (stored dense) rfl rfl
  } {
    exact readback dense (stored dense) (by trustIrReduce) rfl
  }

theorem split_parent_decode : Readback split (stored split) := by
  trustIrCompilerProof {
    exact readback split (stored split) rfl rfl
  } {
    exact readback split (stored split) (by trustIrReduce) rfl
  }

theorem shifted_periodic_parent_decode : Readback periodic (stored periodic) := by
  trustIrCompilerProof {
    exact readback periodic (stored periodic) rfl rfl
  } {
    exact readback periodic (stored periodic) (by trustIrReduce) rfl
  }

private def emptyPoison : CompactArray.Packed Value := ⟨0,.uniform 0 .uninit⟩

theorem empty_array_does_not_force_hidden_poison : Readback emptyPoison { bytes := ByteImage.empty } := by
  trustIrCompilerProof {
    apply integer_array_decode .le64 none Memory.empty (.Array ⟨0⟩ 0) ⟨0,1⟩ 0 .U8 ⟨1,1⟩ 8 emptyPoison { bytes := ByteImage.empty }
      rfl rfl rfl rfl
    intro slot value inside
    change slot < 0 at inside
    omega
  } {
    apply integer_array_decode .le64 none Memory.empty (.Array ⟨0⟩ 0) ⟨0,1⟩ 0 .U8 ⟨1,1⟩ 8 emptyPoison { bytes := ByteImage.empty }
      (by trustIrReduce) rfl rfl rfl
    intro slot value inside
    change slot < 0 at inside
    omega
  }

private def zero : Plan := .fields (.Tuple []) ⟨0,1⟩ []
private theorem zeroReads (slot : Nat) (_inside : slot < 3) (part : ByteImage) (partSize : part.size = 0)
    (_bytes : ∀ index, index < 0 → part.get index = ByteImage.empty.get (slot * 0 + index)) :
    ∃ value, ChildDecoded .le64 none Memory.empty zero part value :=
  ⟨.aggregate [],ChildDecoded.fields_of_children .le64 none Memory.empty (.Tuple []) ⟨0,1⟩ [] part [] partSize
    ((FieldsDecoded.nil_iff .le64 none Memory.empty part []).mpr rfl)⟩

theorem zero_stride_parent_keeps_logical_count :
    ∃ values : CompactArray.Packed Value, values.size = 3 ∧
      decode .le64 none Memory.empty (.array (.Array ⟨0⟩ 3) ⟨0,1⟩ 3 zero) ByteImage.empty = .ok (.array values) :=
  decode_array_exists_of_children .le64 none Memory.empty (.Array ⟨0⟩ 3) ⟨0,1⟩ 3 zero ByteImage.empty rfl rfl zeroReads

theorem nested_zero_stride_parent_keeps_mode :
    ∃ values : CompactArray.Packed Value, values.size = 3 ∧
      ChildDecoded .le64 none Memory.empty (.array (.Array ⟨0⟩ 3) ⟨0,1⟩ 3 zero) ByteImage.empty (.array values) :=
  ChildDecoded.array_exists_of_children .le64 none Memory.empty (.Array ⟨0⟩ 3) ⟨0,1⟩ 3 zero ByteImage.empty rfl rfl zeroReads


private def hiddenPoison : CompactArray.Packed Value :=
  ⟨1,.periodic (.dense (by decide) (.cons a (.cons .uninit .nil))) (by decide) 0 1⟩

theorem clipped_periodic_array_does_not_force_hidden_poison : Readback hiddenPoison (stored hiddenPoison) := by
  trustIrCompilerProof {
    apply integer_array_decode .le64 none Memory.empty (.Array ⟨0⟩ 1) ⟨1,1⟩ 1 .U8 ⟨1,1⟩ 8 hiddenPoison (stored hiddenPoison)
      rfl rfl rfl rfl
    intro slot value inside found
    have zero : slot = 0 := by change slot < 1 at inside; omega
    subst slot
    have same : a = value := Option.some.inj found
    subst value
    exact ⟨513,rfl⟩
  } {
    apply integer_array_decode .le64 none Memory.empty (.Array ⟨0⟩ 1) ⟨1,1⟩ 1 .U8 ⟨1,1⟩ 8 hiddenPoison (stored hiddenPoison)
      (by trustIrReduce) rfl rfl rfl
    intro slot value inside found
    have zero : slot = 0 := by change slot < 1 at inside; omega
    subst slot
    have same : a = value := Option.some.inj found
    subst value
    exact ⟨513,rfl⟩
  }

end TrustIr.AggregateMemory.ArrayParentControls
