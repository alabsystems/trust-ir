-- Copyright 2026 Andrew Yates | Apache-2.0
import TrustIr.Proofs.SourceLeafCoverage
import TrustIr.Proofs.SourceArrayLanes

namespace TrustIr.AggregateMemory
open SourceLayout

/-- Strict field decoding preserves the logical field census. -/
theorem FieldsDecoded.length {model : ByteModel} {order : FunctionAddressOrder} {memory : Memory}
    {fields : List (Nat × Plan)} {image : ByteImage} {values : List Value}
    (run : FieldsDecoded model order memory fields image values) : fields.length = values.length := by
  induction fields generalizing values with
  | nil =>
    have empty := (FieldsDecoded.nil_iff model order memory image values).mp run
    simp [empty]
  | cons field fields ih =>
    obtain ⟨offset,child⟩ := field
    obtain ⟨value,later,shape,_,rest⟩ := run.head
    rw [shape]
    simp only [List.length_cons,ih rest]

/-- Select an actual strict child call by logical field position. The callback
    reads the production slice of the immutable parent, not a byte sidecar. -/
theorem FieldsDecoded.at {model : ByteModel} {order : FunctionAddressOrder} {memory : Memory}
    {fields : List (Nat × Plan)} {image : ByteImage} {values : List Value}
    (run : FieldsDecoded model order memory fields image values)
    (position offset : Nat) (child : Plan) (found : (trustIrListGet? fields position) = some (offset,child)) :
    ∃ value, (trustIrListGet? values position) = some value ∧
      ChildDecoded model order memory child (image.slice offset child.layout.size) value := by
  induction fields generalizing position values with
  | nil => cases position <;> cases found
  | cons field fields ih =>
    obtain ⟨base,plan⟩ := field
    obtain ⟨value,later,shape,decoded,rest⟩ := run.head
    subst values
    cases position with
    | zero =>
      change some (base,plan) = some (offset,child) at found
      obtain ⟨sameOffset,sameChild⟩ := Prod.mk.inj (Option.some.inj found)
      subst base
      subst plan
      exact ⟨value,rfl,decoded⟩
    | succ position =>
      change (trustIrListGet? fields position) = some (offset,child) at found
      exact ih rest position found

/-- A bounded source slice retains its entire child image, including padding. -/
theorem ByteLane.slice (image : ByteImage) (offset count : Nat) (bounded : offset + count ≤ image.size) :
    ByteLane image offset (image.slice offset count) := by
  have size : (image.slice offset count).size = count := by rw [ByteImage.size_slice]; omega
  refine ⟨by rw [size]; exact bounded,?_⟩
  intro index inside
  have inCount : index < count := by rw [size] at inside; exact inside
  exact (ByteImage.get_slice image offset count index inCount (by omega)).symm

/-- A real ordinary tuple/struct load authenticates the selected child call and
    complete byte lane. The bound includes zero-size field offsets. -/
theorem decode_field_slot (model : ByteModel) (order : FunctionAddressOrder) (memory : Memory)
    (ty : Ty) (layout : MemoryTypeLayout) (fields : List (Nat × Plan))
    (image : ByteImage) (values : List Value)
    (run : decode model order memory (.fields ty layout fields) image = .ok (.aggregate values))
    (position offset : Nat) (child : Plan) (found : (trustIrListGet? fields position) = some (offset,child))
    (bounded : offset + child.layout.size ≤ layout.size) (value : Value)
    (valueFound : (trustIrListGet? values position) = some value) :
    ∃ part, part.size = child.layout.size ∧ ChildDecoded model order memory child part value ∧
      ByteLane image offset part := by
  obtain ⟨imageSize,actual,same,decoded⟩ := decode_fields_steps model order memory ty layout fields image (.aggregate values) run
  cases same
  obtain ⟨actualValue,selected,childRun⟩ := decoded.at position offset child found
  rw [valueFound] at selected
  cases selected
  exact ⟨image.slice offset child.layout.size,childRun.extent,childRun,
    ByteLane.slice image offset child.layout.size (by rw [imageSize]; exact bounded)⟩

theorem FieldsEncoded.length {model : ByteModel} {order : FunctionAddressOrder}
    {fields : List (Nat × Plan)} {values : List Value} {allow : Bool} {before after : Image}
    (run : FieldsEncoded model order fields values allow before after) : fields.length = values.length := by
  induction fields generalizing values before with
  | nil =>
    have empty := (FieldsEncoded.nil_iff.mp run).1
    simp [empty]
  | cons field fields ih =>
    obtain ⟨offset,plan⟩ := field
    obtain ⟨value,later,child,bytes,shape,encoded,written,rest⟩ := run.head
    rw [shape]
    simp only [List.length_cons,ih rest]

/-- Extract a positional child from the actual successful field encoder.
    Both the prefix and suffix remain actual runs with full image metadata. -/
theorem FieldsEncoded.at {model : ByteModel} {order : FunctionAddressOrder}
    {fields : List (Nat × Plan)} {values : List Value} {allow : Bool} {before after : Image}
    (run : FieldsEncoded model order fields values allow before after)
    (position offset : Nat) (plan : Plan) (found : (trustIrListGet? fields position) = some (offset,plan)) :
    ∃ value earlier child bytes, (trustIrListGet? values position) = some value ∧
      FieldsEncoded model order (fields.take position) (values.take position) allow before earlier ∧
      encode model order plan value allow = .ok child ∧
      ImageOverwrite earlier.bytes offset child.bytes bytes ∧
      FieldsEncoded model order (fields.drop (position + 1)) (values.drop (position + 1)) allow
        { bytes, unwritten := earlier.unwritten ++
          child.unwritten.map (fun (start,count) => (offset + start,count)) } after := by
  induction fields generalizing position values before with
  | nil => cases position <;> cases found
  | cons field fields ih =>
    obtain ⟨firstOffset,firstPlan⟩ := field
    obtain ⟨firstValue,later,firstChild,nextBytes,shape,headEncoded,headWritten,rest⟩ := run.head
    subst values
    cases position with
    | zero =>
      change some (firstOffset,firstPlan) = some (offset,plan) at found
      obtain ⟨offsetEq,planEq⟩ := Prod.mk.inj (Option.some.inj found)
      subst firstOffset
      subst firstPlan
      refine ⟨firstValue,before,firstChild,nextBytes,rfl,?_,headEncoded,headWritten,?_⟩
      · exact FieldsEncoded.nil_iff.mpr ⟨rfl,rfl⟩
      · exact rest
    | succ position =>
      change (trustIrListGet? fields position) = some (offset,plan) at found
      obtain ⟨value,earlier,child,bytes,valueAt,prefixRun,encoded,written,suffix⟩ := ih rest position found
      have earlierPrefix : FieldsEncoded model order
          ((firstOffset,firstPlan) :: fields.take position) (firstValue :: later.take position)
          allow before earlier :=
        FieldsEncoded.cons_iff.mpr ⟨firstChild,nextBytes,headEncoded,headWritten,prefixRun⟩
      exact ⟨value,earlier,child,bytes,valueAt,earlierPrefix,encoded,written,suffix⟩

/-- A successful ordinary tuple/struct call supplies the actual full field run. -/
theorem encode_fields_steps (model : ByteModel) (order : FunctionAddressOrder)
    (ty : Ty) (layout : MemoryTypeLayout) (fields : List (Nat × Plan))
    (value : Value) (image : Image)
    (run : encode model order (.fields ty layout fields) value false = .ok image) :
    ∃ values, value = .aggregate values ∧
      FieldsEncoded model order fields values false { bytes := ByteImage.fill layout.size none } image := by
  rw [encode] at run
  cases value <;> simp only [Value.isUninit,Bool.false_eq_true,ite_false,ite_true,
    Bind.bind,Except.bind,Pure.pure,Except.pure] at run
  all_goals first | exact ⟨_,rfl,run⟩ | cases run

/-- Successful field encoding/decoding agree on complete child bytes when
    later writes are disjoint. No recursive child-value readback is assumed. -/
theorem field_slot_codec_bytes (model : ByteModel) (order : FunctionAddressOrder) (memory : Memory)
    (ty : Ty) (layout : MemoryTypeLayout) (fields : List (Nat × Plan))
    (inputs outputs : List Value) (image : Image)
    (encoded : encode model order (.fields ty layout fields) (.aggregate inputs) false = .ok image)
    (decoded : decode model order memory (.fields ty layout fields) image.bytes = .ok (.aggregate outputs))
    (position offset : Nat) (child : Plan) (found : (trustIrListGet? fields position) = some (offset,child))
    (bounded : offset + child.layout.size ≤ layout.size)
    (separated : FieldsAvoidLane (fields.drop (position + 1)) offset child.layout.size)
    (input output : Value) (inputFound : (trustIrListGet? inputs position) = some input) (outputFound : (trustIrListGet? outputs position) = some output) :
    ∃ stored : Image, ∃ loaded : ByteImage,
      encode model order child input false = .ok stored ∧ ChildDecoded model order memory child loaded output ∧
      stored.bytes.size = child.layout.size ∧ loaded.size = child.layout.size ∧
      ∀ index, loaded.get index = stored.bytes.get index := by
  obtain ⟨actual,same,fieldRun⟩ := encode_fields_steps model order ty layout fields (.aggregate inputs) image encoded
  cases same
  obtain ⟨actualValue,earlier,stored,placed,selected,_,storedRun,written,suffix⟩ := fieldRun.at position offset child found
  rw [inputFound] at selected
  cases selected
  have storedSize := encode_extent model order child input false stored storedRun
  have storedLane : ByteLane image.bytes offset stored.bytes :=
    suffix.preserves_lane written.lane (by simpa only [storedSize] using separated)
  obtain ⟨loaded,loadedSize,loadedRun,loadedLane⟩ := decode_field_slot model order memory ty layout fields
    image.bytes outputs decoded position offset child found bounded output outputFound
  refine ⟨stored,loaded,storedRun,loadedRun,storedSize,loadedSize,?_⟩
  intro index
  by_cases inside : index < child.layout.size
  · exact (loadedLane.2 index (by rw [loadedSize]; exact inside)).symm.trans
      (storedLane.2 index (by rw [storedSize]; exact inside))
  · rw [ByteImage.get_outside loaded index (by rw [loadedSize]; omega),
      ByteImage.get_outside stored.bytes index (by rw [storedSize]; omega)]

/-- A known real enum selection identifies the exact discriminant row and
    strict payload run. Payload positions exclude the prepended logical tag. -/
theorem decode_enum_selected_fields (model : ByteModel) (order : FunctionAddressOrder) (memory : Memory)
    (ty : Ty) (layout : MemoryTypeLayout) (info : Enumeration)
    (variants : List (Option (List (Nat × Plan)))) (image : ByteImage)
    (tag : Value) (values : List Value)
    (run : decode model order memory (.enumeration ty layout info variants) image = .ok (.aggregate (tag :: values)))
    (position : Nat) (selected : EnumDecodingSelects info image position)
    (fields : List (Nat × Plan)) (row : (trustIrListGet? variants position) = some (some fields)) :
    image.size = layout.size ∧ ∃ discriminant, (trustIrListGet? info.discriminants position) = some discriminant ∧
      tag = Value.intAt (tagBits info.tag) discriminant ∧ FieldsDecoded model order memory fields image values := by
  obtain ⟨imageSize,actualPosition,discriminant,actualFields,actualValues,
    actualSelected,discriminantRow,actualRow,shape,decoded⟩ :=
    decode_enumeration_steps model order memory ty layout info variants image (.aggregate (tag :: values)) run
  have samePosition := actualSelected.functional selected
  subst actualPosition
  rw [row] at actualRow
  cases actualRow
  have sameValues := List.cons.inj (Value.aggregate.inj shape)
  refine ⟨imageSize,discriminant,discriminantRow,sameValues.1,?_⟩
  rw [sameValues.2]
  exact decoded

/-- A selected enum payload field comes from its actual strict decoder call
    and a bounded complete parent lane, including absent padding. -/
theorem decode_enum_payload_slot (model : ByteModel) (order : FunctionAddressOrder) (memory : Memory)
    (ty : Ty) (layout : MemoryTypeLayout) (info : Enumeration)
    (variants : List (Option (List (Nat × Plan)))) (image : ByteImage)
    (tag : Value) (values : List Value)
    (run : decode model order memory (.enumeration ty layout info variants) image = .ok (.aggregate (tag :: values)))
    (position : Nat) (selected : EnumDecodingSelects info image position)
    (fields : List (Nat × Plan)) (row : (trustIrListGet? variants position) = some (some fields))
    (fieldPosition offset : Nat) (child : Plan) (found : (trustIrListGet? fields fieldPosition) = some (offset,child))
    (bounded : offset + child.layout.size ≤ layout.size) (value : Value)
    (valueFound : (trustIrListGet? values fieldPosition) = some value) :
    ∃ part, part.size = child.layout.size ∧ ChildDecoded model order memory child part value ∧ ByteLane image offset part := by
  obtain ⟨imageSize,_,_,_,decoded⟩ := decode_enum_selected_fields model order memory ty layout info variants
    image tag values run position selected fields row
  obtain ⟨actualValue,actualFound,childRun⟩ := decoded.at fieldPosition offset child found
  rw [valueFound] at actualFound
  cases actualFound
  exact ⟨image.slice offset child.layout.size,childRun.extent,childRun,
    ByteLane.slice image offset child.layout.size (by rw [imageSize]; exact bounded)⟩

/-- Actual enum stores/loads with the same selected variant meet at identical
    child bytes. The tag prefix precedes payload writes; suffix separation
    protects the selected payload child's entire extent. -/
theorem enum_payload_slot_codec_bytes (model : ByteModel) (order : FunctionAddressOrder) (memory : Memory)
    (ty : Ty) (layout : MemoryTypeLayout) (info : Enumeration)
    (variants : List (Option (List (Nat × Plan)))) (inputTag outputTag : Value)
    (inputs outputs : List Value) (image : Image)
    (encoded : encode model order (.enumeration ty layout info variants) (.aggregate (inputTag :: inputs)) false = .ok image)
    (decoded : decode model order memory (.enumeration ty layout info variants) image.bytes = .ok (.aggregate (outputTag :: outputs)))
    (position : Nat) (inputSelected : EnumEncodingSelects info inputTag position)
    (outputSelected : EnumDecodingSelects info image.bytes position)
    (fields : List (Nat × Plan)) (row : (trustIrListGet? variants position) = some (some fields))
    (fieldPosition offset : Nat) (child : Plan) (found : (trustIrListGet? fields fieldPosition) = some (offset,child))
    (bounded : offset + child.layout.size ≤ layout.size)
    (separated : FieldsAvoidLane (fields.drop (fieldPosition + 1)) offset child.layout.size)
    (input output : Value) (inputFound : (trustIrListGet? inputs fieldPosition) = some input) (outputFound : (trustIrListGet? outputs fieldPosition) = some output) :
    ∃ stored : Image, ∃ loaded : ByteImage,
      encode model order child input false = .ok stored ∧ ChildDecoded model order memory child loaded output ∧
      stored.bytes.size = child.layout.size ∧ loaded.size = child.layout.size ∧
      ∀ index, loaded.get index = stored.bytes.get index := by
  obtain ⟨actualPosition,_initialBytes,actualSelected,_,variantRun,_⟩ :=
    encode_enumeration_steps model order ty layout info variants inputTag inputs false image encoded
  have samePosition := actualSelected.functional inputSelected
  subst actualPosition
  obtain ⟨actualFields,actualRow,fieldRun⟩ := variantRun.fields
  rw [row] at actualRow
  cases actualRow
  obtain ⟨actualValue,earlier,stored,placed,selected,_,storedRun,written,suffix⟩ :=
    fieldRun.at fieldPosition offset child found
  rw [inputFound] at selected
  cases selected
  have storedSize := encode_extent model order child input false stored storedRun
  have storedLane : ByteLane image.bytes offset stored.bytes :=
    suffix.preserves_lane written.lane (by simpa only [storedSize] using separated)
  obtain ⟨loaded,loadedSize,loadedRun,loadedLane⟩ := decode_enum_payload_slot model order memory ty layout info variants
    image.bytes outputTag outputs decoded position outputSelected fields row fieldPosition offset child found bounded output outputFound
  refine ⟨stored,loaded,storedRun,loadedRun,storedSize,loadedSize,?_⟩
  intro index
  by_cases inside : index < child.layout.size
  · exact (loadedLane.2 index (by rw [loadedSize]; exact inside)).symm.trans
      (storedLane.2 index (by rw [storedSize]; exact inside))
  · rw [ByteImage.get_outside loaded index (by rw [loadedSize]; omega),
      ByteImage.get_outside stored.bytes index (by rw [storedSize]; omega)]

/-- A static initialized lane path through leaves and tuple/struct fields.
    Bounds and later-write separation are part of the checked path; padding
    is not a constructor. Array and enum recursion require separate laws. -/
inductive Plan.CoversLane : Plan → Nat → Nat → Prop where
  | leaf {ty : Ty} {layout : MemoryTypeLayout} {offset count : Nat}
      (bounded : offset + count ≤ layout.size) :
      CoversLane (.leaf ty layout) offset count
  | fields {ty : Ty} {layout : MemoryTypeLayout} {fields : List (Nat × Plan)}
      {position base offset count : Nat} {child : Plan}
      (found : (trustIrListGet? fields position) = some (base,child))
      (bounded : base + offset + count ≤ layout.size)
      (covered : CoversLane child offset count)
      (separated : FieldsAvoidLane (fields.drop (position + 1)) (base + offset) count) :
      CoversLane (.fields ty layout fields) (base + offset) count
  | array {ty : Ty} {layout : MemoryTypeLayout} {length : Nat} {element : Plan}
      {slot offset count : Nat} (inside : slot < length)
      (bounded : slot * element.layout.size + offset + count ≤ layout.size)
      (covered : CoversLane element offset count) :
      CoversLane (.array ty layout length element) (slot * element.layout.size + offset) count

theorem Plan.CoversLane.bounds {plan : Plan} {offset count : Nat}
    (covered : plan.CoversLane offset count) : offset + count ≤ plan.layout.size := by
  cases covered with
  | leaf bounded => exact bounded
  | fields found bounded covered separated => exact bounded
  | array inside bounded covered => exact bounded

/-- Derive initialized bytes from actual successful encoding along any finite
    certified field/array path ending at a leaf. Array steps retain logical slot
    membership and physical bounds. No child read is assumed. -/
theorem Plan.CoversLane.initialized {plan : Plan} {offset count : Nat}
    (covered : plan.CoversLane offset count) (model : ByteModel) (order : FunctionAddressOrder)
    (value : Value) (image : Image) (run : encode model order plan value false = .ok image) :
    ∃ bytes : List UInt8, bytes.length = count ∧ InitializedLane image.bytes offset count bytes := by
  induction covered generalizing value image with
  | leaf bounded => exact encode_leaf_range_initialized model order _ _ value image run _ _ bounded
  | @fields ty layout fields position base offset count child found bounded covered separated ih =>
    obtain ⟨values,shape,fieldRun⟩ := encode_fields_steps model order ty layout fields value image run
    obtain ⟨fieldValue,earlier,childImage,placedBytes,valueAt,prefixRun,encoded,written,suffix⟩ :=
      fieldRun.at position base child found
    obtain ⟨bytes,length,read⟩ := ih fieldValue childImage encoded
    have extent := encode_extent model order child fieldValue false childImage encoded
    let placed : Image := { bytes := placedBytes, unwritten := earlier.unwritten ++
      childImage.unwritten.map (fun (start,count) => (base + start,count)) }
    refine ⟨bytes,length,?_⟩
    exact FieldsEncoded.retains_initialized_child (placed := placed)
      written (by rw [extent]; exact covered.bounds) read suffix separated
  | @array ty layout length element slot offset count _inside bounded covered ih =>
    exact encode_array_initialized_slot model order ty layout length element offset count covered.bounds
      (fun value image encoded => ih value image encoded) slot bounded value image run

/-- Actual whole-field encoding supplies the selected nested carrier's calls,
    placements and suffix; the static path supplies only layout facts. -/
theorem FieldsEncoded.covered_at_initialized {model : ByteModel} {order : FunctionAddressOrder}
    {fields : List (Nat × Plan)} {values : List Value} {before after : Image}
    (run : FieldsEncoded model order fields values false before after)
    (position base : Nat) (child : Plan)
    (found : (trustIrListGet? fields position) = some (base,child))
    (offset count : Nat) (covered : child.CoversLane offset count)
    (separated : FieldsAvoidLane (fields.drop (position + 1)) (base + offset) count) :
    ∃ value bytes, (trustIrListGet? values position) = some value ∧ bytes.length = count ∧
      InitializedLane after.bytes (base + offset) count bytes := by
  obtain ⟨value,earlier,childImage,placedBytes,valueAt,prefixRun,encoded,written,suffix⟩ :=
    run.at position base child found
  obtain ⟨bytes,length,read⟩ := covered.initialized model order value childImage encoded
  have extent := encode_extent model order child value false childImage encoded
  let placed : Image := { bytes := placedBytes, unwritten := earlier.unwritten ++
    childImage.unwritten.map (fun (start,count) => (base + start,count)) }
  refine ⟨value,bytes,valueAt,length,?_⟩
  exact FieldsEncoded.retains_initialized_child (placed := placed)
    written (by rw [extent]; exact covered.bounds) read suffix separated

/-- A selected nested field in the actual payload run establishes niche readiness. -/
theorem EnumUntaggedCarrierReady.of_covered_field_run
    {model : ByteModel} {order : FunctionAddressOrder}
    {fields : List (Nat × Plan)} {values : List Value} {before after : Image}
    (run : FieldsEncoded model order fields values false before after)
    (fieldPosition base : Nat) (child : Plan)
    (found : (trustIrListGet? fields fieldPosition) = some (base,child))
    (offset : Nat) (info : Enumeration) (position untagged start stop first : Nat) (repr : EnumTagRepr)
    (encoding : info.encoding = .niche untagged start stop first (base + offset) repr)
    (covered : child.CoversLane offset (tagBits repr / 8))
    (separated : FieldsAvoidLane (fields.drop (fieldPosition + 1)) (base + offset) (tagBits repr / 8)) :
    EnumUntaggedCarrierReady info position after.bytes := by
  obtain ⟨value,bytes,valueAt,length,read⟩ :=
    run.covered_at_initialized fieldPosition base child found offset (tagBits repr / 8) covered separated
  rw [EnumUntaggedCarrierReady,encoding]
  intro _
  exact ⟨bytes,read⟩

/-- The actual successful enum encoder supplies the selected payload run used
    by the nested carrier proof. -/
theorem enum_encoded_covered_carrier_ready (model : ByteModel) (order : FunctionAddressOrder)
    (ty : Ty) (layout : MemoryTypeLayout) (info : Enumeration)
    (variants : List (Option (List (Nat × Plan)))) (tag : Value) (values : List Value)
    (position : Nat) (allowUnwritten : Bool) (image : Image)
    (selected : EnumEncodingSelects info tag position)
    (encoded : encode model order (.enumeration ty layout info variants)
      (.aggregate (tag :: values)) allowUnwritten = .ok image)
    (fields : List (Nat × Plan)) (row : (trustIrListGet? variants position) = some (some fields))
    (fieldPosition base : Nat) (child : Plan) (found : (trustIrListGet? fields fieldPosition) = some (base,child))
    (offset untagged start stop first : Nat) (repr : EnumTagRepr)
    (encoding : info.encoding = .niche untagged start stop first (base + offset) repr)
    (covered : child.CoversLane offset (tagBits repr / 8))
    (separated : FieldsAvoidLane (fields.drop (fieldPosition + 1)) (base + offset) (tagBits repr / 8)) :
    EnumUntaggedCarrierReady info position image.bytes := by
  obtain ⟨actual,bytes,actualSelected,built,payload,guarded⟩ :=
    encode_enumeration_steps model order ty layout info variants tag values allowUnwritten image encoded
  have same := selected.functional actualSelected
  subst actual
  obtain ⟨actualFields,actualRow,fieldRun⟩ := payload.fields
  have sameFields := Option.some.inj (Option.some.inj (actualRow.symm.trans row))
  subst actualFields
  exact EnumUntaggedCarrierReady.of_covered_field_run fieldRun fieldPosition base child found offset
    info position untagged start stop first repr encoding covered separated

/-- Source-bound admitted captures obtain final-image selection from a static
    nested carrier path, with no initialized-read premise. -/
theorem prepared_enum_capture_covered_encoded_selection (source : Environment) (ctx : EvalContext)
    (associated : CaptureSource source ctx) (admitted : enumIdsAdmitted source.enums = true)
    (roots : List Ty) (id : EnumId) (definition : EnumDef) (resolved : ctx.enums id = some definition)
    (plan : Plan) (run : (prepare source roots).query (.Enum id) = .ok plan)
    (fuel : Nat) (values : List Value) (initialized : (Value.aggregate values).Initialized)
    (checked : checkClosureValueAt ctx (fuel + 1) (.Enum id) (.aggregate values) = .ok ()) :
    ∃ layout info variants tag payload position variant fields,
      plan = .enumeration (.Enum id) layout info variants ∧ values = tag :: payload ∧
      EnumTagSelects definition tag position ∧ (trustIrListGet? definition.variants position) = some variant ∧
      EnumEncodingSelects info tag position ∧ (trustIrListGet? info.uninhabited position) = some false ∧
      (trustIrListGet? variants position) = some (some fields) ∧
      (∀ field ∈ fields, Plan.Origin (SourceElement source) (ActualSummary source) field.2.ty field.2) ∧
      ∀ model order allowUnwritten image,
        encode model order plan (.aggregate values) allowUnwritten = .ok image →
        (∃ fieldPosition base child offset untagged start stop first repr,
          info.encoding = .niche untagged start stop first (base + offset) repr ∧
          (trustIrListGet? fields fieldPosition) = some (base,child) ∧
          child.CoversLane offset (tagBits repr / 8) ∧
          FieldsAvoidLane (fields.drop (fieldPosition + 1)) (base + offset) (tagBits repr / 8)) →
        image.bytes.size = layout.size ∧ EnumDecodingSelects info image.bytes position := by
  obtain ⟨layout,info,variants,tag,payload,position,variant,fields,
    shape,valuesShape,sourceSelected,row,selected,live,found,origins,finish⟩ :=
    prepared_enum_capture_coherent_encoded_selection source ctx associated admitted roots id definition resolved
      plan run fuel values initialized checked
  refine ⟨layout,info,variants,tag,payload,position,variant,fields,
    shape,valuesShape,sourceSelected,row,selected,live,found,origins,?_⟩
  intro model order allowUnwritten image encoded certificate
  obtain ⟨fieldPosition,base,child,offset,untagged,start,stop,first,repr,
    encoding,fieldFound,covered,separated⟩ := certificate
  have actualEncoded := encoded
  rw [shape,valuesShape] at actualEncoded
  have ready := enum_encoded_covered_carrier_ready model order (.Enum id) layout info variants
    tag payload position allowUnwritten image selected actualEncoded fields found
    fieldPosition base child fieldFound offset untagged start stop first repr encoding covered separated
  exact finish model order allowUnwritten image encoded ready

end TrustIr.AggregateMemory

namespace TrustIr.AggregateMemory.FieldStepControls

private def bytePlan : Plan := .leaf .U8 ⟨1,1⟩
private def inner : Plan := .fields (.Struct ⟨1⟩) ⟨2,1⟩ [(1,bytePlan)]
private def fields : List (Nat × Plan) := [(0,bytePlan),(2,inner),(6,bytePlan)]
private def outer : Plan := .fields (.Tuple [.U8,.Struct ⟨1⟩,.U8]) ⟨8,1⟩ fields
private def values : List Value := [.int 8 11,.aggregate [.int 8 7],.int 8 42]
private def before : Image := { bytes := ByteImage.fill 8 none }
private def childBytes : ByteImage :=
  ((ByteImage.fill 2 none).slice 0 1).append
    ((ByteImage.ofList [some 7]).append ((ByteImage.fill 2 none).slice 2 0))
private def first : Image :=
  { bytes := (before.bytes.slice 0 0).append
      ((ByteImage.ofList [some 11]).append (before.bytes.slice 1 7)) }
private def middle : Image :=
  { bytes := (first.bytes.slice 0 2).append (childBytes.append (first.bytes.slice 4 4)) }
private def final : Image :=
  { bytes := (middle.bytes.slice 0 6).append
      ((ByteImage.ofList [some 42]).append (middle.bytes.slice 7 1)) }

theorem nested_coverage_path : outer.CoversLane 3 1 := by
  apply Plan.CoversLane.fields (position := 1) (base := 2) (offset := 1)
    (child := inner) (by rfl) (by decide)
  · apply Plan.CoversLane.fields (position := 0) (base := 1) (offset := 0)
      (child := bytePlan) (by rfl) (by decide) (.leaf (by decide))
    intro field member
    cases member
  · intro field member
    change field ∈ [(6,bytePlan)] at member
    cases member with
    | head => rfl
    | tail _ impossible => cases impossible

theorem actual_nested_encoding :
    encode .le64 none outer (.aggregate values) false = .ok final := by
  trustIrCompilerProof {
    exact rfl
  } {
    exact by trustIrReduce
  }

theorem actual_full_field_run : FieldsEncoded .le64 none fields values false before final := by
  trustIrCompilerProof {
    exact rfl
  } {
    exact by trustIrReduce
  }

theorem nested_read_from_actual_encoding :
    ∃ bytes : List UInt8, bytes.length = 1 ∧ InitializedLane final.bytes 3 1 bytes :=
  nested_coverage_path.initialized .le64 none (.aggregate values) final actual_nested_encoding

theorem adjacent_padding_has_no_coverage_path : ¬ outer.CoversLane 2 1 := by
  intro covered
  obtain ⟨bytes,length,read⟩ := covered.initialized .le64 none (.aggregate values) final actual_nested_encoding
  cases read

/-- The selected carrier is the middle field, with real earlier and later writes. -/
theorem selected_middle_field_coverage :
    ∃ value bytes, (trustIrListGet? values 1) = some value ∧ bytes.length = 1 ∧
      InitializedLane final.bytes 3 1 bytes := by
  apply actual_full_field_run.covered_at_initialized 1 2 inner (by rfl) 1 1
  · apply Plan.CoversLane.fields (position := 0) (base := 1) (offset := 0)
      (child := bytePlan) (by rfl) (by decide) (.leaf (by decide))
    intro field member
    cases member
  · intro field member
    change field ∈ [(6,bytePlan)] at member
    cases member with
    | head => rfl
    | tail _ impossible => cases impossible

private def unwrittenBefore : Image := { bytes := ByteImage.fill 8 none, unwritten := [(1,2)] }
private def unwrittenAfter : Image :=
  { bytes := (unwrittenBefore.bytes.slice 0 3).append
      ((ByteImage.fill 1 none).append (unwrittenBefore.bytes.slice 4 4)),
    unwritten := [(1,2),(3,1)] }

theorem unwritten_step_retains_shifted_metadata :
    FieldsEncoded .le64 none [(3,bytePlan)] [.uninit] true unwrittenBefore unwrittenAfter := by
  trustIrCompilerProof {
    exact rfl
  } {
    exact by trustIrReduce
  }

theorem extra_values_refuse (start finish : Image) :
    ¬ FieldsEncoded .le64 none [] [.int 8 7] false start finish := by
  intro run
  have impossible := (FieldsEncoded.nil_iff.mp run).1
  cases impossible

theorem missing_values_refuse (start finish : Image) :
    ¬ FieldsEncoded .le64 none [(0,bytePlan)] [] false start finish := by
  intro run
  obtain ⟨value,later,child,bytes,impossible,encoded,written,rest⟩ := run.head
  cases impossible

end TrustIr.AggregateMemory.FieldStepControls
