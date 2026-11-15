-- Copyright 2026 Andrew Yates | Apache-2.0
import TrustIr.Proofs.SourceFieldSteps

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

namespace TrustIr.SourceLayout

theorem Field.Separated.subrange {field other : Field} (separated : field.Separated other)
    (offset count : Nat) (bounded : offset + count ≤ field.size) :
    overlap (field.offset + offset) count other.offset other.size = false := by
  apply (overlap_false_iff_separated
    { ty := .U8, offset := field.offset + offset, size := count, align := 1 } other).mpr
  change count = 0 ∨ other.size = 0 ∨ field.offset + offset + count ≤ other.offset ∨
    other.offset + other.size ≤ field.offset + offset
  rcases separated with empty | empty | before | after
  · exact .inl (by omega)
  · exact .inr (.inl empty)
  · exact .inr (.inr (.inl (by omega)))
  · exact .inr (.inr (.inr (by omega)))

/-- Separation is positional, so equal zero-sized field occurrences remain valid. -/
theorem FieldsSeparated.later_at {metadata : List Field} (safe : FieldsSeparated metadata)
    (position : Nat) (field : Field) (found : (trustIrListGet? metadata position) = some field) :
    ∀ other ∈ metadata.drop (position + 1), field.Separated other := by
  induction metadata generalizing position with
  | nil => cases position <;> cases found
  | cons first rest ih =>
    cases position with
    | zero =>
      change some first = some field at found
      cases found
      exact safe.1
    | succ position => exact ih safe.2 position found

end TrustIr.SourceLayout

namespace TrustIr.AggregateMemory
open SourceLayout

private theorem map_drop {α β : Type} (f : α → β) (rows : List α) (count : Nat) :
    (rows.map f).drop count = (rows.drop count).map f := by
  induction rows generalizing count with
  | nil => cases count <;> rfl
  | cons first rest ih => cases count with
    | zero => rfl
    | succ count => exact ih count

theorem FieldBindings.drop_metadata {metadata : List Field} {fields : List (Nat × Plan)}
    (bindings : FieldBindings (metadata.map (·.ty)) (metadata.map (·.offset)) fields) (count : Nat) :
    FieldBindings ((metadata.drop count).map (·.ty)) ((metadata.drop count).map (·.offset))
      (fields.drop count) := by
  constructor
  · have same := congrArg (fun rows : List Ty => rows.drop count) bindings.1
    simpa only [map_drop] using same
  · have same := congrArg (fun rows : List Nat => rows.drop count) bindings.2
    simpa only [map_drop] using same

theorem FieldExtents.drop_metadata {metadata : List Field} {fields : List (Nat × Plan)}
    (extents : FieldExtents metadata fields) (count : Nat) :
    FieldExtents (metadata.drop count) (fields.drop count) := by
  have same := congrArg (fun rows : List Nat => rows.drop count) extents
  simpa only [map_drop] using same

/-- Source field separation and checked actual child sizes discharge every later
    sibling's nonoverlap with a bounded interior child lane. -/
theorem FieldBindings.later_avoids_subrange {metadata : List Field} {fields : List (Nat × Plan)}
    (bindings : FieldBindings (metadata.map (·.ty)) (metadata.map (·.offset)) fields)
    (extents : FieldExtents metadata fields) (safe : FieldsSeparated metadata)
    (position base : Nat) (child : Plan) (found : (trustIrListGet? fields position) = some (base,child))
    (offset count : Nat) (bounded : offset + count ≤ child.layout.size) :
    FieldsAvoidLane (fields.drop (position + 1)) (base + offset) count := by
  obtain ⟨field,row,typed,placed⟩ := bindings.source_child position base child found
  have sized := extents.at position field base child row found
  apply (bindings.drop_metadata (position + 1)).avoids_lane (extents.drop_metadata (position + 1))
  intro other member
  rw [placed]
  exact (safe.later_at position field row other member).subrange offset count (by omega)

/-- The fields constructor retains source metadata, checked extents and actual
    child origins from successful compilation. -/
theorem Plan.Origin.fields_metadata_view {source : Environment} {ty : Ty}
    {layout : MemoryTypeLayout} {fields : List (Nat × Plan)}
    (origin : Plan.Origin (SourceElement source) (ActualSummary source) ty (.fields ty layout fields)) :
    ∃ value, ActualSummary source ty value ∧ layout.size = value.size ∧
      (∀ field ∈ fields, Plan.Origin (SourceElement source) (ActualSummary source) field.2.ty field.2) ∧
      FieldBindings (value.fields.map (·.ty)) (value.fields.map (·.offset)) fields ∧
      FieldExtents value.fields fields := by
  cases origin with
  | fields ty layout fields kind children value summary extent bindings metadata sizes =>
    exact ⟨value,summary,extent.1,children,metadata,sizes⟩

/-- Actual source geometry supplies the parent bound and later-write separation. -/
theorem Plan.Origin.covers_fields_child {source : Environment} {ty : Ty}
    {layout : MemoryTypeLayout} {fields : List (Nat × Plan)}
    (origin : Plan.Origin (SourceElement source) (ActualSummary source) ty (.fields ty layout fields))
    (position base : Nat) (child : Plan) (found : (trustIrListGet? fields position) = some (base,child))
    (offset count : Nat) (covered : child.CoversLane offset count) :
    (.fields ty layout fields : Plan).CoversLane (base + offset) count := by
  trustIrCompilerProof {
    obtain ⟨value,actual,extent,children,bindings,sizes⟩ := origin.fields_metadata_view
    obtain ⟨before,next,history,queried⟩ := actual
    have geometry := (history.query_storage_geometry .execution ty value queried).1
    obtain ⟨field,row,typed,placed⟩ := bindings.source_child position base child found
    have sized := sizes.at position field base child row found
    obtain ⟨inside,get⟩ := List.get?_eq_some.mp row
    have member : field ∈ value.fields := List.mem_iff_get.mpr ⟨⟨position,inside⟩,get⟩
    apply Plan.CoversLane.fields found
    · have contained := geometry.2 field member
      have bound := covered.bounds
      rw [extent]
      omega
    · exact covered
    · exact bindings.later_avoids_subrange sizes geometry.1 position base child found offset count covered.bounds
  } {
    obtain ⟨value,actual,extent,children,bindings,sizes⟩ := origin.fields_metadata_view
    obtain ⟨before,next,history,queried⟩ := actual
    have geometry := (history.query_storage_geometry .execution ty value queried).1
    obtain ⟨field,row,typed,placed⟩ := bindings.source_child position base child found
    have sized := sizes.at position field base child row found
    have member : field ∈ value.fields := CompilerCompat.listGetConstructive_mem row
    apply Plan.CoversLane.fields found
    · have contained := geometry.2 field member
      have bound := covered.bounds
      rw [extent]
      omega
    · exact covered
    · exact bindings.later_avoids_subrange sizes geometry.1 position base child found offset count covered.bounds
  }

/-- Source metadata authenticates the entire child extent, including padding
    and zero-size offsets, and protects it from every later sibling write. -/
theorem Plan.Origin.fields_child_placement {source : Environment} {ty : Ty}
    {layout : MemoryTypeLayout} {fields : List (Nat × Plan)}
    (origin : Plan.Origin (SourceElement source) (ActualSummary source) ty (.fields ty layout fields))
    (position offset : Nat) (child : Plan) (found : (trustIrListGet? fields position) = some (offset,child)) :
    offset + child.layout.size ≤ layout.size ∧
      FieldsAvoidLane (fields.drop (position + 1)) offset child.layout.size := by
  trustIrCompilerProof {
    obtain ⟨value,actual,extent,_,bindings,sizes⟩ := origin.fields_metadata_view
    obtain ⟨_,_,history,queried⟩ := actual
    have geometry := (history.query_storage_geometry .execution ty value queried).1
    obtain ⟨field,row,_,placed⟩ := bindings.source_child position offset child found
    have sized := sizes.at position field offset child row found
    obtain ⟨inside,get⟩ := List.get?_eq_some.mp row
    have member : field ∈ value.fields := List.mem_iff_get.mpr ⟨⟨position,inside⟩,get⟩
    refine ⟨?_,?_⟩
    · have contained := geometry.2 field member
      rw [extent]
      omega
    · simpa only [Nat.add_zero] using
        bindings.later_avoids_subrange sizes geometry.1 position offset child found 0 child.layout.size (by omega)
  } {
    obtain ⟨value,actual,extent,_,bindings,sizes⟩ := origin.fields_metadata_view
    obtain ⟨_,_,history,queried⟩ := actual
    have geometry := (history.query_storage_geometry .execution ty value queried).1
    obtain ⟨field,row,_,placed⟩ := bindings.source_child position offset child found
    have sized := sizes.at position field offset child row found
    have member : field ∈ value.fields := CompilerCompat.listGetConstructive_mem row
    refine ⟨?_,?_⟩
    · have contained := geometry.2 field member
      rw [extent]
      omega
    · simpa only [Nat.add_zero] using
        bindings.later_avoids_subrange sizes geometry.1 position offset child found 0 child.layout.size (by omega)
  }

/-- An authentic source-plan origin supplies the physical field bound required
    by strict decoder custody. No initialized-padding assertion is needed. -/
theorem decode_source_field_slot (source : Environment) (model : ByteModel)
    (order : FunctionAddressOrder) (memory : Memory) (ty : Ty) (layout : MemoryTypeLayout)
    (fields : List (Nat × Plan))
    (origin : Plan.Origin (SourceElement source) (ActualSummary source) ty (.fields ty layout fields))
    (image : ByteImage) (values : List Value)
    (run : decode model order memory (.fields ty layout fields) image = .ok (.aggregate values))
    (position offset : Nat) (child : Plan) (found : (trustIrListGet? fields position) = some (offset,child))
    (value : Value) (valueFound : (trustIrListGet? values position) = some value) :
    ∃ part, part.size = child.layout.size ∧ ChildDecoded model order memory child part value ∧ ByteLane image offset part :=
  decode_field_slot model order memory ty layout fields image values run position offset child found
    (origin.fields_child_placement position offset child found).1 value valueFound

/-- Actual preparation discharges the field decoder's source geometry. -/
theorem prepared_field_decoded_slot (source : Environment) (roots : List Ty) (model : ByteModel)
    (order : FunctionAddressOrder) (memory : Memory) (ty : Ty) (layout : MemoryTypeLayout)
    (fields : List (Nat × Plan))
    (prepared : (prepare source roots).query ty = .ok (.fields ty layout fields))
    (image : ByteImage) (values : List Value)
    (run : decode model order memory (.fields ty layout fields) image = .ok (.aggregate values))
    (position offset : Nat) (child : Plan) (found : (trustIrListGet? fields position) = some (offset,child))
    (value : Value) (valueFound : (trustIrListGet? values position) = some value) :
    ∃ part, part.size = child.layout.size ∧ ChildDecoded model order memory child part value ∧ ByteLane image offset part :=
  decode_source_field_slot source model order memory ty layout fields
    (prepared_plan_origin source roots ty _ prepared) image values run position offset child found value valueFound

/-- Source geometry supplies both the bound and suffix separation for complete
    child-byte correspondence between successful ordinary field stores/loads. -/
theorem field_slot_codec_bytes_of_origin (source : Environment) (model : ByteModel)
    (order : FunctionAddressOrder) (memory : Memory) (ty : Ty) (layout : MemoryTypeLayout)
    (fields : List (Nat × Plan))
    (origin : Plan.Origin (SourceElement source) (ActualSummary source) ty (.fields ty layout fields))
    (inputs outputs : List Value) (image : Image)
    (encoded : encode model order (.fields ty layout fields) (.aggregate inputs) false = .ok image)
    (decoded : decode model order memory (.fields ty layout fields) image.bytes = .ok (.aggregate outputs))
    (position offset : Nat) (child : Plan) (found : (trustIrListGet? fields position) = some (offset,child))
    (input output : Value) (inputFound : (trustIrListGet? inputs position) = some input) (outputFound : (trustIrListGet? outputs position) = some output) :
    ∃ stored : Image, ∃ loaded : ByteImage,
      encode model order child input false = .ok stored ∧ ChildDecoded model order memory child loaded output ∧
      stored.bytes.size = child.layout.size ∧ loaded.size = child.layout.size ∧
      ∀ index, loaded.get index = stored.bytes.get index := by
  obtain ⟨bound,separated⟩ := origin.fields_child_placement position offset child found
  exact field_slot_codec_bytes model order memory ty layout fields inputs outputs image encoded decoded
    position offset child found bound separated input output inputFound outputFound

/-- Actual prepared queries remove all caller field-bound and separation
    premises from the successful child-byte codec bridge. -/
theorem prepared_field_slot_codec_bytes (source : Environment) (roots : List Ty) (model : ByteModel)
    (order : FunctionAddressOrder) (memory : Memory) (ty : Ty) (layout : MemoryTypeLayout)
    (fields : List (Nat × Plan))
    (prepared : (prepare source roots).query ty = .ok (.fields ty layout fields))
    (inputs outputs : List Value) (image : Image)
    (encoded : encode model order (.fields ty layout fields) (.aggregate inputs) false = .ok image)
    (decoded : decode model order memory (.fields ty layout fields) image.bytes = .ok (.aggregate outputs))
    (position offset : Nat) (child : Plan) (found : (trustIrListGet? fields position) = some (offset,child))
    (input output : Value) (inputFound : (trustIrListGet? inputs position) = some input) (outputFound : (trustIrListGet? outputs position) = some output) :
    ∃ stored : Image, ∃ loaded : ByteImage,
      encode model order child input false = .ok stored ∧ ChildDecoded model order memory child loaded output ∧
      stored.bytes.size = child.layout.size ∧ loaded.size = child.layout.size ∧
      ∀ index, loaded.get index = stored.bytes.get index :=
  field_slot_codec_bytes_of_origin source model order memory ty layout fields
    (prepared_plan_origin source roots ty _ prepared) inputs outputs image encoded decoded
    position offset child found input output inputFound outputFound

/-- Syntactic field/array steps and a final leaf bound. Array steps carry
only logical index membership; physical bounds come from the actual source origin. -/
inductive Plan.LanePath : Plan → Nat → Nat → Prop where
  | leaf {ty : Ty} {layout : MemoryTypeLayout} {offset count : Nat}
      (bounded : offset + count ≤ layout.size) : LanePath (.leaf ty layout) offset count
  | fields {ty : Ty} {layout : MemoryTypeLayout} {fields : List (Nat × Plan)}
      {position base offset count : Nat} {child : Plan}
      (found : (trustIrListGet? fields position) = some (base,child)) (path : LanePath child offset count) :
      LanePath (.fields ty layout fields) (base + offset) count
  | array {ty : Ty} {layout : MemoryTypeLayout} {length : Nat} {element : Plan}
      {slot offset count : Nat} (inside : slot < length) (path : LanePath element offset count) :
      LanePath (.array ty layout length element) (slot * element.layout.size + offset) count

theorem Plan.Origin.lane_path_covers {source : Environment} {plan : Plan} {offset count : Nat}
    (origin : Plan.Origin (SourceElement source) (ActualSummary source) plan.ty plan) (path : plan.LanePath offset count) :
    plan.CoversLane offset count := by
  trustIrCompilerProof {
    induction path with
    | leaf bounded => exact .leaf bounded
    | @fields ty layout fields position base offset count child found path ih =>
      obtain ⟨value,actual,extent,children,bindings,sizes⟩ := origin.fields_metadata_view
      obtain ⟨inside,get⟩ := List.get?_eq_some.mp found
      have member : (base,child) ∈ fields := List.mem_iff_get.mpr ⟨⟨position,inside⟩,get⟩
      exact origin.covers_fields_child position base child found offset count (ih (children (base,child) member))
    | @array ty layout length element slot offset count inside path ih =>
      obtain ⟨id,same,_,_,childOrigin,_,_,_,_⟩ := origin.array_binding_view
      cases same
      have extent := origin.source_array_extent
      have covered := ih childOrigin
      apply Plan.CoversLane.array inside _ covered
      rw [extent.1]
      have childBound := covered.bounds
      have slotBound : slot + 1 ≤ length := by omega
      calc
        slot * element.layout.size + offset + count ≤ slot * element.layout.size + element.layout.size := by omega
        _ = (slot + 1) * element.layout.size := by rw [Nat.add_mul,Nat.one_mul]
        _ ≤ length * element.layout.size := Nat.mul_le_mul_right _ slotBound
        _ = element.layout.size * length := Nat.mul_comm _ _
  } {
    induction path with
    | leaf bounded => exact .leaf bounded
    | @fields ty layout fields position base offset count child found path ih =>
      obtain ⟨value,actual,extent,children,bindings,sizes⟩ := origin.fields_metadata_view
      have member : (base,child) ∈ fields := CompilerCompat.listGetConstructive_mem found
      exact origin.covers_fields_child position base child found offset count (ih (children (base,child) member))
    | @array ty layout length element slot offset count inside path ih =>
      obtain ⟨id,same,_,_,childOrigin,_,_,_,_⟩ := origin.array_binding_view
      cases same
      have extent := origin.source_array_extent
      have covered := ih childOrigin
      apply Plan.CoversLane.array inside _ covered
      rw [extent.1]
      have childBound := covered.bounds
      have slotBound : slot + 1 ≤ length := by omega
      calc
        slot * element.layout.size + offset + count ≤ slot * element.layout.size + element.layout.size := by omega
        _ = (slot + 1) * element.layout.size := by rw [Nat.add_mul,Nat.one_mul]
        _ ≤ length * element.layout.size := Nat.mul_le_mul_right _ slotBound
        _ = element.layout.size * length := Nat.mul_comm _ _
  }

theorem prepared_lane_path_covers (source : Environment) (roots : List Ty) (ty : Ty) (plan : Plan)
    (run : (prepare source roots).query ty = .ok plan) (offset count : Nat)
    (path : plan.LanePath offset count) : plan.CoversLane offset count :=
  (prepared_plan_origin source roots ty plan run).own.lane_path_covers path

/-- Actual enum source geometry authenticates a complete payload child lane
    and all later sibling writes, including padding and zero-size offsets. -/
theorem Plan.Origin.enum_payload_child_placement {source : Environment} {id : EnumId}
    {layout : MemoryTypeLayout} {info : Enumeration} {variants : List (Option (List (Nat × Plan)))}
    (origin : Plan.Origin (SourceElement source) (ActualSummary source) (.Enum id)
      (.enumeration (.Enum id) layout info variants))
    (position : Nat) (fields : List (Nat × Plan)) (row : (trustIrListGet? variants position) = some (some fields))
    (fieldPosition offset : Nat) (child : Plan) (found : (trustIrListGet? fields fieldPosition) = some (offset,child)) :
    offset + child.layout.size ≤ layout.size ∧
      FieldsAvoidLane (fields.drop (fieldPosition + 1)) offset child.layout.size := by
  trustIrCompilerProof {
    obtain ⟨actualLayout,actualInfo,actualVariants,value,shape,actual,present,extent,_,bindings,sizes⟩ := origin.enum_extent_view
    obtain ⟨_,layoutEq,infoEq,variantsEq⟩ := Plan.enumeration.inj shape
    subst actualLayout
    subst actualInfo
    subst actualVariants
    obtain ⟨metadata,sourceRow,tied⟩ := bindings.source_at position fields row
    obtain ⟨other,otherRow,sized⟩ := sizes position fields row
    have same := Option.some.inj (sourceRow.symm.trans otherRow)
    subst other
    obtain ⟨variantInside,variantGet⟩ := List.get?_eq_some.mp sourceRow
    have variantMember : metadata ∈ info.variants := List.mem_iff_get.mpr ⟨⟨position,variantInside⟩,variantGet⟩
    obtain ⟨_,_,history,queried⟩ := actual
    have geometry := (history.query_storage_geometry .execution (.Enum id) value queried).2 info present metadata variantMember
    obtain ⟨field,fieldRow,_,placed⟩ := tied.source_child fieldPosition offset child found
    have fieldSize := sized.at fieldPosition field offset child fieldRow found
    obtain ⟨fieldInside,fieldGet⟩ := List.get?_eq_some.mp fieldRow
    have fieldMember : field ∈ metadata := List.mem_iff_get.mpr ⟨⟨fieldPosition,fieldInside⟩,fieldGet⟩
    refine ⟨?_,?_⟩
    · have contained := geometry.2 field fieldMember
      rw [extent.1]
      omega
    · simpa only [Nat.add_zero] using tied.later_avoids_subrange sized geometry.1
        fieldPosition offset child found 0 child.layout.size (by omega)
  } {
    obtain ⟨actualLayout,actualInfo,actualVariants,value,shape,actual,present,extent,_,bindings,sizes⟩ := origin.enum_extent_view
    obtain ⟨_,layoutEq,infoEq,variantsEq⟩ := Plan.enumeration.inj shape
    subst actualLayout
    subst actualInfo
    subst actualVariants
    obtain ⟨metadata,sourceRow,tied⟩ := bindings.source_at position fields row
    obtain ⟨other,otherRow,sized⟩ := sizes position fields row
    have same := Option.some.inj (sourceRow.symm.trans otherRow)
    subst other
    have variantMember : metadata ∈ info.variants := CompilerCompat.listGetConstructive_mem sourceRow
    obtain ⟨_,_,history,queried⟩ := actual
    have geometry := (history.query_storage_geometry .execution (.Enum id) value queried).2 info present metadata variantMember
    obtain ⟨field,fieldRow,_,placed⟩ := tied.source_child fieldPosition offset child found
    have fieldSize := sized.at fieldPosition field offset child fieldRow found
    have fieldMember : field ∈ metadata := CompilerCompat.listGetConstructive_mem fieldRow
    refine ⟨?_,?_⟩
    · have contained := geometry.2 field fieldMember
      rw [extent.1]
      omega
    · simpa only [Nat.add_zero] using tied.later_avoids_subrange sized geometry.1
        fieldPosition offset child found 0 child.layout.size (by omega)
  }

/-- Source origins discharge the physical payload child bound for actual enum
    decoder custody, without asserting that padding is initialized. -/
theorem decode_source_enum_payload_slot (source : Environment) (id : EnumId) (model : ByteModel)
    (order : FunctionAddressOrder) (memory : Memory) (layout : MemoryTypeLayout) (info : Enumeration)
    (variants : List (Option (List (Nat × Plan))))
    (origin : Plan.Origin (SourceElement source) (ActualSummary source) (.Enum id)
      (.enumeration (.Enum id) layout info variants))
    (image : ByteImage) (tag : Value) (values : List Value)
    (run : decode model order memory (.enumeration (.Enum id) layout info variants) image = .ok (.aggregate (tag :: values)))
    (position : Nat) (selected : EnumDecodingSelects info image position)
    (fields : List (Nat × Plan)) (row : (trustIrListGet? variants position) = some (some fields))
    (fieldPosition offset : Nat) (child : Plan) (found : (trustIrListGet? fields fieldPosition) = some (offset,child))
    (value : Value) (valueFound : (trustIrListGet? values fieldPosition) = some value) :
    ∃ part, part.size = child.layout.size ∧ ChildDecoded model order memory child part value ∧ ByteLane image offset part :=
  decode_enum_payload_slot model order memory (.Enum id) layout info variants image tag values run position selected fields row
    fieldPosition offset child found (origin.enum_payload_child_placement position fields row fieldPosition offset child found).1
    value valueFound

/-- Actual prepared enum queries provide complete selected payload geometry. -/
theorem prepared_enum_decoded_payload_slot (source : Environment) (roots : List Ty) (id : EnumId) (model : ByteModel)
    (order : FunctionAddressOrder) (memory : Memory) (layout : MemoryTypeLayout) (info : Enumeration)
    (variants : List (Option (List (Nat × Plan))))
    (prepared : (prepare source roots).query (.Enum id) = .ok (.enumeration (.Enum id) layout info variants))
    (image : ByteImage) (tag : Value) (values : List Value)
    (run : decode model order memory (.enumeration (.Enum id) layout info variants) image = .ok (.aggregate (tag :: values)))
    (position : Nat) (selected : EnumDecodingSelects info image position)
    (fields : List (Nat × Plan)) (row : (trustIrListGet? variants position) = some (some fields))
    (fieldPosition offset : Nat) (child : Plan) (found : (trustIrListGet? fields fieldPosition) = some (offset,child))
    (value : Value) (valueFound : (trustIrListGet? values fieldPosition) = some value) :
    ∃ part, part.size = child.layout.size ∧ ChildDecoded model order memory child part value ∧ ByteLane image offset part :=
  decode_source_enum_payload_slot source id model order memory layout info variants
    (prepared_plan_origin source roots (.Enum id) _ prepared) image tag values run position selected fields row
    fieldPosition offset child found value valueFound

/-- Successful same-variant stores/loads retain identical payload child bytes;
    actual source metadata supplies bounds and suffix separation. -/
theorem enum_payload_slot_codec_bytes_of_origin (source : Environment) (id : EnumId) (model : ByteModel)
    (order : FunctionAddressOrder) (memory : Memory) (layout : MemoryTypeLayout) (info : Enumeration)
    (variants : List (Option (List (Nat × Plan))))
    (origin : Plan.Origin (SourceElement source) (ActualSummary source) (.Enum id)
      (.enumeration (.Enum id) layout info variants))
    (inputTag outputTag : Value) (inputs outputs : List Value) (image : Image)
    (encoded : encode model order (.enumeration (.Enum id) layout info variants) (.aggregate (inputTag :: inputs)) false = .ok image)
    (decoded : decode model order memory (.enumeration (.Enum id) layout info variants) image.bytes = .ok (.aggregate (outputTag :: outputs)))
    (position : Nat) (inputSelected : EnumEncodingSelects info inputTag position)
    (outputSelected : EnumDecodingSelects info image.bytes position)
    (fields : List (Nat × Plan)) (row : (trustIrListGet? variants position) = some (some fields))
    (fieldPosition offset : Nat) (child : Plan) (found : (trustIrListGet? fields fieldPosition) = some (offset,child))
    (input output : Value) (inputFound : (trustIrListGet? inputs fieldPosition) = some input) (outputFound : (trustIrListGet? outputs fieldPosition) = some output) :
    ∃ stored : Image, ∃ loaded : ByteImage,
      encode model order child input false = .ok stored ∧ ChildDecoded model order memory child loaded output ∧
      stored.bytes.size = child.layout.size ∧ loaded.size = child.layout.size ∧
      ∀ index, loaded.get index = stored.bytes.get index := by
  obtain ⟨bound,separated⟩ := origin.enum_payload_child_placement position fields row fieldPosition offset child found
  exact enum_payload_slot_codec_bytes model order memory (.Enum id) layout info variants inputTag outputTag inputs outputs
    image encoded decoded position inputSelected outputSelected fields row fieldPosition offset child found bound separated
    input output inputFound outputFound

/-- Prepared source queries remove all caller payload-bound/separation premises.
    Selector agreement remains explicit here and is discharged by capture below. -/
theorem prepared_enum_payload_slot_codec_bytes (source : Environment) (roots : List Ty) (id : EnumId) (model : ByteModel)
    (order : FunctionAddressOrder) (memory : Memory) (layout : MemoryTypeLayout) (info : Enumeration)
    (variants : List (Option (List (Nat × Plan))))
    (prepared : (prepare source roots).query (.Enum id) = .ok (.enumeration (.Enum id) layout info variants))
    (inputTag outputTag : Value) (inputs outputs : List Value) (image : Image)
    (encoded : encode model order (.enumeration (.Enum id) layout info variants) (.aggregate (inputTag :: inputs)) false = .ok image)
    (decoded : decode model order memory (.enumeration (.Enum id) layout info variants) image.bytes = .ok (.aggregate (outputTag :: outputs)))
    (position : Nat) (inputSelected : EnumEncodingSelects info inputTag position)
    (outputSelected : EnumDecodingSelects info image.bytes position)
    (fields : List (Nat × Plan)) (row : (trustIrListGet? variants position) = some (some fields))
    (fieldPosition offset : Nat) (child : Plan) (found : (trustIrListGet? fields fieldPosition) = some (offset,child))
    (input output : Value) (inputFound : (trustIrListGet? inputs fieldPosition) = some input) (outputFound : (trustIrListGet? outputs fieldPosition) = some output) :
    ∃ stored : Image, ∃ loaded : ByteImage,
      encode model order child input false = .ok stored ∧ ChildDecoded model order memory child loaded output ∧
      stored.bytes.size = child.layout.size ∧ loaded.size = child.layout.size ∧
      ∀ index, loaded.get index = stored.bytes.get index :=
  enum_payload_slot_codec_bytes_of_origin source id model order memory layout info variants
    (prepared_plan_origin source roots (.Enum id) _ prepared) inputTag outputTag inputs outputs image encoded decoded position
    inputSelected outputSelected fields row fieldPosition offset child found input output inputFound outputFound

/-- Actual enum-row metadata discharges separation from later outer payload fields. -/
theorem prepared_enum_field_siblings_avoid (source : Environment) (roots : List Ty)
    (id : EnumId) (plan : Plan) (run : (prepare source roots).query (.Enum id) = .ok plan)
    (layout : MemoryTypeLayout) (info : Enumeration) (variants : List (Option (List (Nat × Plan))))
    (shape : plan = .enumeration (.Enum id) layout info variants)
    (variantPosition : Nat) (fields : List (Nat × Plan))
    (row : (trustIrListGet? variants variantPosition) = some (some fields))
    (fieldPosition base : Nat) (child : Plan) (found : (trustIrListGet? fields fieldPosition) = some (base,child))
    (offset count : Nat) (bounded : offset + count ≤ child.layout.size) :
    FieldsAvoidLane (fields.drop (fieldPosition + 1)) (base + offset) count := by
  trustIrCompilerProof {
    obtain ⟨actualLayout,actualInfo,actualVariants,value,actualShape,actual,present,
      extent,children,bindings,sizes⟩ :=
      (prepared_plan_origin source roots (.Enum id) plan run).enum_extent_view
    obtain ⟨_,layoutEq,infoEq,variantsEq⟩ := Plan.enumeration.inj (actualShape.symm.trans shape)
    subst actualLayout
    subst actualInfo
    subst actualVariants
    obtain ⟨metadata,sourceRow,tied⟩ := bindings.source_at variantPosition fields row
    obtain ⟨other,otherRow,sized⟩ := sizes variantPosition fields row
    have same := Option.some.inj (sourceRow.symm.trans otherRow)
    subst other
    obtain ⟨inside,get⟩ := List.get?_eq_some.mp sourceRow
    have member : metadata ∈ info.variants := List.mem_iff_get.mpr ⟨⟨variantPosition,inside⟩,get⟩
    obtain ⟨before,next,history,queried⟩ := actual
    have geometry := (history.query_storage_geometry .execution (.Enum id) value queried).2
    exact tied.later_avoids_subrange sized (geometry info present metadata member).1
      fieldPosition base child found offset count bounded
  } {
    obtain ⟨actualLayout,actualInfo,actualVariants,value,actualShape,actual,present,
      extent,children,bindings,sizes⟩ :=
      (prepared_plan_origin source roots (.Enum id) plan run).enum_extent_view
    obtain ⟨_,layoutEq,infoEq,variantsEq⟩ := Plan.enumeration.inj (actualShape.symm.trans shape)
    subst actualLayout
    subst actualInfo
    subst actualVariants
    obtain ⟨metadata,sourceRow,tied⟩ := bindings.source_at variantPosition fields row
    obtain ⟨other,otherRow,sized⟩ := sizes variantPosition fields row
    have same := Option.some.inj (sourceRow.symm.trans otherRow)
    subst other
    have member : metadata ∈ info.variants := CompilerCompat.listGetConstructive_mem sourceRow
    obtain ⟨before,next,history,queried⟩ := actual
    have geometry := (history.query_storage_geometry .execution (.Enum id) value queried).2
    exact tied.later_avoids_subrange sized (geometry info present metadata member).1
      fieldPosition base child found offset count bounded
  }

/-- Source-bound final selection needs only the selected nested field path;
    actual checked source geometry supplies all sibling separation. -/
theorem prepared_enum_capture_path_encoded_selection (source : Environment) (ctx : EvalContext)
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
          child.LanePath offset (tagBits repr / 8)) →
        image.bytes.size = layout.size ∧ EnumDecodingSelects info image.bytes position := by
  trustIrCompilerProof {
    obtain ⟨layout,info,variants,tag,payload,position,variant,fields,
      shape,valuesShape,sourceSelected,row,selected,live,found,origins,finish⟩ :=
      prepared_enum_capture_covered_encoded_selection source ctx associated admitted roots id definition resolved
        plan run fuel values initialized checked
    refine ⟨layout,info,variants,tag,payload,position,variant,fields,
      shape,valuesShape,sourceSelected,row,selected,live,found,origins,?_⟩
    intro model order allowUnwritten image encoded certificate
    obtain ⟨fieldPosition,base,child,offset,untagged,start,stop,first,repr,
      encoding,fieldFound,path⟩ := certificate
    obtain ⟨inside,get⟩ := List.get?_eq_some.mp fieldFound
    have member : (base,child) ∈ fields := List.mem_iff_get.mpr ⟨⟨fieldPosition,inside⟩,get⟩
    have covered := (origins (base,child) member).lane_path_covers path
    have siblings := prepared_enum_field_siblings_avoid source roots id plan run layout info variants shape
      position fields found fieldPosition base child fieldFound offset (tagBits repr / 8) covered.bounds
    exact finish model order allowUnwritten image encoded
      ⟨fieldPosition,base,child,offset,untagged,start,stop,first,repr,encoding,fieldFound,covered,siblings⟩
  } {
    obtain ⟨layout,info,variants,tag,payload,position,variant,fields,
      shape,valuesShape,sourceSelected,row,selected,live,found,origins,finish⟩ :=
      prepared_enum_capture_covered_encoded_selection source ctx associated admitted roots id definition resolved
        plan run fuel values initialized checked
    refine ⟨layout,info,variants,tag,payload,position,variant,fields,
      shape,valuesShape,sourceSelected,row,selected,live,found,origins,?_⟩
    intro model order allowUnwritten image encoded certificate
    obtain ⟨fieldPosition,base,child,offset,untagged,start,stop,first,repr,
      encoding,fieldFound,path⟩ := certificate
    have member : (base,child) ∈ fields := CompilerCompat.listGetConstructive_mem fieldFound
    have covered := (origins (base,child) member).lane_path_covers path
    have siblings := prepared_enum_field_siblings_avoid source roots id plan run layout info variants shape
      position fields found fieldPosition base child fieldFound offset (tagBits repr / 8) covered.bounds
    exact finish model order allowUnwritten image encoded
      ⟨fieldPosition,base,child,offset,untagged,start,stop,first,repr,encoding,fieldFound,covered,siblings⟩
  }

/-- Checked source capture plus actual prepared encoding/decoding supplies
    selector agreement, strict payload runs and complete child-byte custody.
    Default-niche carrier readiness is the existing explicit premise. -/
theorem prepared_enum_capture_payload_codec_bytes (source : Environment) (ctx : EvalContext)
    (associated : CaptureSource source ctx) (admitted : enumIdsAdmitted source.enums = true)
    (roots : List Ty) (id : EnumId) (definition : EnumDef) (resolved : ctx.enums id = some definition)
    (plan : Plan) (prepared : (prepare source roots).query (.Enum id) = .ok plan)
    (fuel : Nat) (values : List Value) (initialized : (Value.aggregate values).Initialized)
    (checked : checkClosureValueAt ctx (fuel + 1) (.Enum id) (.aggregate values) = .ok ()) :
    ∃ layout info variants inputTag inputs position variant fields,
      plan = .enumeration (.Enum id) layout info variants ∧ values = inputTag :: inputs ∧
      EnumTagSelects definition inputTag position ∧ (trustIrListGet? definition.variants position) = some variant ∧
      EnumEncodingSelects info inputTag position ∧ (trustIrListGet? info.uninhabited position) = some false ∧
      (trustIrListGet? variants position) = some (some fields) ∧
      (∀ field ∈ fields, Plan.Origin (SourceElement source) (ActualSummary source) field.2.ty field.2) ∧
      ∀ model order memory image result,
        encode model order plan (.aggregate values) false = .ok image →
        EnumUntaggedCarrierReady info position image.bytes →
        decode model order memory plan image.bytes = .ok result →
        ∃ discriminant outputs, (trustIrListGet? info.discriminants position) = some discriminant ∧
          result = .aggregate (Value.intAt (tagBits info.tag) discriminant :: outputs) ∧
          FieldsDecoded model order memory fields image.bytes outputs ∧
          ∀ fieldPosition offset child, (trustIrListGet? fields fieldPosition) = some (offset,child) →
            ∀ input output, (trustIrListGet? inputs fieldPosition) = some input → (trustIrListGet? outputs fieldPosition) = some output →
              ∃ stored : Image, ∃ loaded : ByteImage,
                encode model order child input false = .ok stored ∧ ChildDecoded model order memory child loaded output ∧
                stored.bytes.size = child.layout.size ∧ loaded.size = child.layout.size ∧
                ∀ index, loaded.get index = stored.bytes.get index := by
  obtain ⟨layout,info,variants,inputTag,inputs,position,variant,fields,
    shape,valuesShape,sourceSelected,definitionRow,inputSelected,live,row,origins,finish⟩ :=
    prepared_enum_capture_coherent_encoded_selection source ctx associated admitted roots id definition resolved plan prepared
      fuel values initialized checked
  refine ⟨layout,info,variants,inputTag,inputs,position,variant,fields,
    shape,valuesShape,sourceSelected,definitionRow,inputSelected,live,row,origins,?_⟩
  intro model order memory image result encoded carrier decoded
  have outputSelected := (finish model order false image encoded carrier).2
  have encodedRoot : encode model order (.enumeration (.Enum id) layout info variants)
      (.aggregate (inputTag :: inputs)) false = .ok image := by
    simpa only [shape,valuesShape] using encoded
  have decodedRoot : decode model order memory (.enumeration (.Enum id) layout info variants) image.bytes = .ok result := by
    simpa only [shape] using decoded
  obtain ⟨_,actualPosition,discriminant,actualFields,outputs,actualSelected,discriminantRow,actualRow,resultShape,payloadRun⟩ :=
    decode_enumeration_steps model order memory (.Enum id) layout info variants image.bytes result decodedRoot
  have samePosition := actualSelected.functional outputSelected
  subst actualPosition
  rw [row] at actualRow
  cases actualRow
  refine ⟨discriminant,outputs,discriminantRow,resultShape,payloadRun,?_⟩
  intro fieldPosition offset child found input output inputFound outputFound
  have preparedRoot : (prepare source roots).query (.Enum id) = .ok (.enumeration (.Enum id) layout info variants) := by
    simpa only [shape] using prepared
  have decodedResult : decode model order memory (.enumeration (.Enum id) layout info variants) image.bytes =
      .ok (.aggregate (Value.intAt (tagBits info.tag) discriminant :: outputs)) := by
    rw [← resultShape]
    exact decodedRoot
  exact prepared_enum_payload_slot_codec_bytes source roots id model order memory layout info variants preparedRoot
    inputTag (Value.intAt (tagBits info.tag) discriminant) inputs outputs image encodedRoot decodedResult
    position inputSelected outputSelected fields row fieldPosition offset child found input output inputFound outputFound

end TrustIr.AggregateMemory

namespace TrustIr.AggregateMemory.SiblingGeometryControls
open SourceLayout

private def word : Field := { ty := .U16, offset := 4, size := 2, align := 1 }
private def byte : Field := { ty := .U8, offset := 0, size := 1, align := 1 }
private def empty : Field := { ty := .Tuple [], offset := 5, size := 0, align := 1 }
private def metadata : List Field := [word,byte,empty,empty]
private def wordPlan : Plan := .leaf .U16 ⟨2,2⟩
private def bytePlan : Plan := .leaf .U8 ⟨1,1⟩
private def emptyPlan : Plan := .fields (.Tuple []) ⟨0,1⟩ []
private def fields : List (Nat × Plan) := [(4,wordPlan),(0,bytePlan),(5,emptyPlan),(5,emptyPlan)]

/-- Logical order need not be increasing physical order; equal empty rows are valid. -/
theorem checked_row_separated : FieldsSeparated metadata := by
  simp [FieldsSeparated,Field.Separated,metadata,word,byte,empty]

/-- A zero-sized later write may lie inside the selected word's storage. -/
theorem actual_siblings_avoid_interior_lane : FieldsAvoidLane (fields.drop 1) 5 1 := by
  trustIrCompilerProof {
    have bindings : FieldBindings (metadata.map (fun f : Field => f.ty))
        (metadata.map (fun f : Field => f.offset)) fields := ⟨rfl,rfl⟩
    have extents : FieldExtents metadata fields := rfl
    exact bindings.later_avoids_subrange extents checked_row_separated 0 4 wordPlan rfl 1 1 (by decide)
  } {
    have bindings : FieldBindings (metadata.map (fun f : Field => f.ty))
        (metadata.map (fun f : Field => f.offset)) fields := ⟨by trustIrReduce,by trustIrReduce⟩
    have extents : FieldExtents metadata fields := by trustIrReduce
    exact bindings.later_avoids_subrange extents checked_row_separated 0 4 wordPlan rfl 1 1 (by decide)
  }

theorem path_needs_no_parent_layout_premises :
    (Plan.fields (.Struct ⟨1⟩) ⟨8,1⟩ fields).LanePath 5 1 :=
  .fields (position := 0) (base := 4) (offset := 1) (by rfl) (.leaf (by decide))

theorem nonempty_overlap_refuses_separation :
    ¬ FieldsSeparated [{ ty := .U16, offset := 0, size := 2, align := 1 },
      { ty := .U8, offset := 1, size := 1, align := 1 }] := by
  intro safe
  have impossible := safe.1 _ ((trustIrListMemConsSelf _ _))
  change 2 = 0 ∨ 1 = 0 ∨ 2 ≤ 1 ∨ 2 ≤ 0 at impossible
  omega

theorem type_and_offset_do_not_replace_extent_check :
    ¬ FieldExtents [byte] [(0,.leaf .U8 ⟨2,1⟩)] := by
  intro impossible
  cases impossible

theorem empty_selected_subrange_is_disjoint :
    overlap 5 0 word.offset word.size = false :=
  (show empty.Separated word from .inl rfl).subrange 0 0 (by decide)

end TrustIr.AggregateMemory.SiblingGeometryControls

namespace TrustIr.AggregateMemory.FieldDecoderControls
open SourceLayout

private def byte : Plan := .leaf .U8 ⟨1,1⟩
private def word : Plan := .leaf .U16 ⟨2,2⟩
private def zero : Plan := .fields (.Tuple []) ⟨0,1⟩ []
private def childTy : Ty := .Tuple [.U8,.U16]
private def child : Plan := .fields childTy ⟨4,2⟩ [(0,byte),(2,word)]
private def parentTy : Ty := .Tuple [.U8,childTy,.U8]
private def parent : Plan := .fields parentTy ⟨8,2⟩ [(0,byte),(2,child),(6,byte)]
private def input : Value := .aggregate [.int 8 5,.aggregate [.int 8 7,.int 16 4660],.int 8 9]
private def padded : ByteImage := ByteImage.ofList [some 5,none,some 7,none,some 52,some 18,some 9,none]
private def source : Environment := { types := [] }
private theorem prepared : (prepare source []).query parentTy = .ok parent := by
  trustIrCompilerProof {
    exact rfl
  } {
    exact by trustIrReduce
  }

private def loadAt (model : ByteModel) (plan : Plan) (image : ByteImage) (position : Nat) :
    Except SemError (Option Value) := do
  let value ← decode model none Memory.empty plan image
  match value with
  | .aggregate values => pure ((trustIrListGet? values position))
  | _ => pure none
private def roundtripAt (plan : Plan) (value : Value) (position : Nat) : Except SemError (Option Value) := do
  let image ← encode .le64 none plan value false
  loadAt .le64 plan image.bytes position
private def storedByte (index : Nat) : Except SemError (Option UInt8) := do
  let image ← encode .le64 none parent input false
  pure (image.bytes.get index)
private def refused (result : Except SemError Value) : Bool :=
  match result with
  | .error _ => true
  | .ok _ => false

theorem nested_padded_child_roundtrip :
    roundtripAt parent input 1 = .ok (some (.aggregate [.int 8 7,.int 16 4660])) := by
  trustIrCompilerProof {
    exact rfl
  } {
    exact by trustIrReduce
  }

theorem padding_survives_later_field :
    storedByte 1 = .ok none ∧ storedByte 3 = .ok none ∧ storedByte 7 = .ok none := by
  trustIrCompilerProof {
    exact ⟨rfl,rfl,rfl⟩
  } {
    exact ⟨by trustIrReduce,by trustIrReduce,by trustIrReduce⟩
  }

theorem field_positions_are_logical :
    loadAt .le64 parent padded 2 = .ok (some (.int 8 9)) ∧ loadAt .le64 parent padded 3 = .ok none := by
  trustIrCompilerProof {
    exact ⟨rfl,rfl⟩
  } {
    exact ⟨by trustIrReduce,by trustIrReduce⟩
  }

private def zeroParent : Plan := .fields (.Tuple [.U8,.Tuple [],.U8]) ⟨2,1⟩ [(0,byte),(1,zero),(1,byte)]

theorem zero_size_fields_keep_positions :
    loadAt .le32 zeroParent (ByteImage.ofList [some 5,some 9]) 1 = .ok (some (.aggregate [])) ∧
      loadAt .le32 zeroParent (ByteImage.ofList [some 5,some 9]) 2 = .ok (some (.int 8 9)) := by
  trustIrCompilerProof {
    exact ⟨rfl,rfl⟩
  } {
    exact ⟨by trustIrReduce,by trustIrReduce⟩
  }

private def forgedZero : Plan := .fields (.Tuple [.Tuple []]) ⟨0,1⟩ [(3,zero)]

theorem clipped_empty_child_does_not_prove_parent_bounds :
    decode .le64 none Memory.empty forgedZero ByteImage.empty = .ok (.aggregate [.aggregate []]) := by
  trustIrCompilerProof {
    exact rfl
  } {
    exact by trustIrReduce
  }

theorem forged_empty_offset_has_no_lane : ¬ ByteLane ByteImage.empty 3 ByteImage.empty := by
  intro lane
  have impossible := lane.1
  change 3 + 0 ≤ 0 at impossible
  omega

theorem forged_empty_offset_has_no_origin (environment : Environment) :
    ¬ Plan.Origin (SourceElement environment) (ActualSummary environment) (.Tuple [.Tuple []]) forgedZero := by
  intro origin
  have impossible := (origin.fields_child_placement 0 3 zero rfl).1
  change 3 + 0 ≤ 0 at impossible
  omega

private def overlapping : Plan := .fields (.Tuple [.U16,.U8]) ⟨2,2⟩ [(0,word),(1,byte)]

theorem overlapping_suffix_changes_earlier_value :
    roundtripAt overlapping (.aggregate [.int 16 4660,.int 8 255]) 0 = .ok (some (.int 16 65332)) := by
  trustIrCompilerProof {
    exact rfl
  } {
    exact by trustIrReduce
  }

theorem overlapping_fields_have_no_origin (environment : Environment) :
    ¬ Plan.Origin (SourceElement environment) (ActualSummary environment) (.Tuple [.U16,.U8]) overlapping := by
  intro origin
  have separated := (origin.fields_child_placement 0 0 word rfl).2
  have impossible := separated (1,byte) ((trustIrListMemConsSelf _ _))
  change true = false at impossible
  cases impossible

theorem nested_char_keeps_strict_raw_rule :
    loadAt .le64 (.fields (.Tuple [.Char]) ⟨4,4⟩ [(0,.leaf .Char ⟨4,4⟩)])
      (ByteImage.ofList [some 0,some 216,some 0,some 0]) 0 = .ok (some (.int 32 55296)) := by
  trustIrCompilerProof {
    exact rfl
  } {
    exact by trustIrReduce
  }

theorem missing_covered_byte_refuses :
    refused (decode .le64 none Memory.empty parent
      (ByteImage.ofList [some 5,none,some 7,none,some 52,none,some 9,none])) = true := by
  trustIrCompilerProof {
    exact rfl
  } {
    exact by trustIrReduce
  }

theorem parent_extent_mismatch_refuses :
    refused (decode .le64 none Memory.empty parent (ByteImage.fill 7 (some 0))) = true := by
  trustIrCompilerProof {
    exact rfl
  } {
    exact by trustIrReduce
  }

private def arrayChild : Plan := .array (.Array ⟨0⟩ 3) ⟨3,1⟩ 3 byte
private def arrayParent : Plan := .fields (.Tuple [.Array ⟨0⟩ 3,.U8]) ⟨4,1⟩ [(0,arrayChild),(3,byte)]
private def arrayInput : Value := .aggregate [
  .array ⟨3,.periodic (.dense (by decide) (.cons (.int 8 1) (.cons (.int 8 2) .nil))) (by decide) 1 3⟩,.int 8 9]
private def arraySlot : Except SemError (Option Value) := do
  let image ← encode .le64 none arrayParent arrayInput false
  let value ← loadAt .le64 arrayParent image.bytes 0
  match value with
  | some (.array values) => pure (values.tree.get? 1)
  | _ => pure none

theorem array_child_is_observed_pointwise : arraySlot = .ok (some (.int 8 1)) := by
  trustIrCompilerProof {
    exact rfl
  } {
    exact by trustIrReduce
  }

theorem prepared_child_geometry_includes_padding :
    2 + child.layout.size ≤ parent.layout.size ∧ FieldsAvoidLane [(6,byte)] 2 child.layout.size :=
  (prepared_plan_origin source [] parentTy parent prepared).fields_child_placement 1 2 child rfl

theorem prepared_child_callback_retains_padding (values : List Value)
    (run : decode .le64 none Memory.empty parent padded = .ok (.aggregate values))
    (found : (trustIrListGet? values 1) = some (.aggregate [.int 8 7,.int 16 4660])) :
    ∃ part, ChildDecoded .le64 none Memory.empty child part (.aggregate [.int 8 7,.int 16 4660]) ∧ part.get 1 = none := by
  trustIrCompilerProof {
    obtain ⟨part,partSize,decoded,lane⟩ := prepared_field_decoded_slot source [] .le64 none Memory.empty
      parentTy ⟨8,2⟩ [(0,byte),(2,child),(6,byte)] prepared padded values run 1 2 child rfl _ found
    refine ⟨part,decoded,?_⟩
    have byte := lane.2 1 (by rw [partSize]; decide)
    have absent : padded.get (2 + 1) = none := rfl
    rw [absent] at byte
    exact byte.symm
  } {
    obtain ⟨part,partSize,decoded,lane⟩ := prepared_field_decoded_slot source [] .le64 none Memory.empty
      parentTy ⟨8,2⟩ [(0,byte),(2,child),(6,byte)] prepared padded values run 1 2 child rfl _ found
    refine ⟨part,decoded,?_⟩
    have byte := lane.2 1 (by rw [partSize]; decide)
    have absent : padded.get (2 + 1) = none := by trustIrReduce
    rw [absent] at byte
    exact byte.symm
  }

end TrustIr.AggregateMemory.FieldDecoderControls

namespace TrustIr.AggregateMemory.EnumDecoderControls
open SourceLayout

private def byte : Plan := .leaf .U8 ⟨1,1⟩
private def childTy : Ty := .Tuple [.U8,.U16]
private def child : Plan := .fields childTy ⟨4,2⟩ [(0,byte),(2,.leaf .U16 ⟨2,2⟩)]
private def childValue : Value := .aggregate [.int 8 7,.int 16 4660]
private def metadata : List (List Field) :=
  [[{ ty := childTy, offset := 2, size := 4, align := 2 },{ ty := .U8, offset := 6, size := 1, align := 1 }],[]]
private def info : Enumeration :=
  { tag := .u8, discriminants := [10,20], encoding := .direct 0, variants := metadata, uninhabited := [false,false] }
private def variants : List (Option (List (Nat × Plan))) := [some [(2,child),(6,byte)],some []]
private def plan : Plan := .enumeration (.Enum ⟨0⟩) ⟨8,2⟩ info variants
private def inputValues : List Value := [.int 8 10,childValue,.int 8 9]
private def padded : ByteImage := ByteImage.ofList [some 10,none,some 7,none,some 52,some 18,some 9,none]
private def observe (plan : Plan) (image : ByteImage) : Except SemError (List Value) := do
  let value ← decode .le64 none Memory.empty plan image
  match value with
  | .aggregate values => pure values
  | _ => pure []
private def roundtrip (plan : Plan) (values : List Value) : Except SemError (List Value) := do
  let image ← encode .le64 none plan (.aggregate values) false
  observe plan image.bytes
private def refused (result : Except SemError Value) : Bool :=
  match result with
  | .error _ => true
  | .ok _ => false

theorem direct_payload_roundtrip : roundtrip plan inputValues = .ok inputValues := by
  trustIrCompilerProof {
    exact rfl
  } {
    exact by trustIrReduce
  }

theorem tag_and_payload_positions_are_distinct :
    observe plan padded = .ok [.int 8 10,childValue,.int 8 9] := by
  trustIrCompilerProof {
    exact rfl
  } {
    exact by trustIrReduce
  }

theorem live_empty_payload_keeps_logical_discriminant :
    roundtrip plan [.int 8 20] = .ok [.int 8 20] := by
  trustIrCompilerProof {
    exact rfl
  } {
    exact by trustIrReduce
  }

private def zero : Plan := .fields (.Tuple []) ⟨0,1⟩ []
private def untaggedInfo : Enumeration :=
  { tag := .u8, discriminants := [99], encoding := .untagged,
    variants := [[{ ty := .Tuple [], offset := 0, size := 0, align := 1 }]], uninhabited := [false] }
private def untagged : Plan := .enumeration (.Enum ⟨0⟩) ⟨0,1⟩ untaggedInfo [some [(0,zero)]]

theorem untagged_zero_size_payload_is_present :
    roundtrip untagged [.int 8 99,.aggregate []] = .ok [.int 8 99,.aggregate []] := by
  trustIrCompilerProof {
    exact rfl
  } {
    exact by trustIrReduce
  }

private def singleInfo : Enumeration :=
  { tag := .u8, discriminants := [0,99], encoding := .singleInhabited 1,
    variants := [[],[{ ty := .U8, offset := 0, size := 1, align := 1 }]], uninhabited := [true,false] }
private def single : Plan := .enumeration (.Enum ⟨0⟩) ⟨1,1⟩ singleInfo [none,some [(0,byte)]]

theorem single_inhabited_uses_source_position :
    roundtrip single [.int 8 99,.int 8 7] = .ok [.int 8 99,.int 8 7] := by
  trustIrCompilerProof {
    exact rfl
  } {
    exact by trustIrReduce
  }

private def nicheInfo : Enumeration :=
  { tag := .u8, discriminants := [10,20], encoding := .niche 0 1 1 1 0 .u8,
    variants := [[{ ty := .U8, offset := 0, size := 1, align := 1 }],[]], uninhabited := [false,false] }
private def niche : Plan := .enumeration (.Enum ⟨0⟩) ⟨1,1⟩ nicheInfo [some [(0,byte)],some []]

theorem default_niche_reads_real_payload :
    roundtrip niche [.int 8 10,.int 8 7] = .ok [.int 8 10,.int 8 7] := by
  trustIrCompilerProof {
    exact rfl
  } {
    exact by trustIrReduce
  }

theorem tagged_niche_maps_to_logical_discriminant : roundtrip niche [.int 8 20] = .ok [.int 8 20] := by
  trustIrCompilerProof {
    exact rfl
  } {
    exact by trustIrReduce
  }

private def missingInfo : Enumeration :=
  { tag := .u8, discriminants := [10,20], encoding := .niche 0 1 1 1 0 .u8,
    variants := [[],[]], uninhabited := [false,false] }
private def missing : Plan := .enumeration (.Enum ⟨0⟩) ⟨1,1⟩ missingInfo [some [],some []]

theorem default_niche_carrier_is_not_initialized_by_successful_store :
    encode .le64 none missing (.aggregate [.int 8 10]) false = .ok ⟨ByteImage.fill 1 none,[]⟩ ∧
      refused (decode .le64 none Memory.empty missing (ByteImage.fill 1 none)) = true := by
  trustIrCompilerProof {
    exact ⟨rfl,rfl⟩
  } {
    exact ⟨by trustIrReduce,by trustIrReduce⟩
  }

theorem absent_payload_row_refuses :
    refused (decode .le64 none Memory.empty (.enumeration (.Enum ⟨0⟩) ⟨8,2⟩ info [some [(2,child),(6,byte)],none])
      (ByteImage.ofList [some 20,none,none,none,none,none,none,none])) = true := by
  trustIrCompilerProof {
    exact rfl
  } {
    exact by trustIrReduce
  }

theorem uninhabited_flag_refuses_present_row :
    refused (decode .le64 none Memory.empty (.enumeration (.Enum ⟨0⟩) ⟨8,2⟩
      { info with uninhabited := [false,true] } variants)
      (ByteImage.ofList [some 20,none,none,none,none,none,none,none])) = true := by
  trustIrCompilerProof {
    exact rfl
  } {
    exact by trustIrReduce
  }

private def signedInfo : Enumeration :=
  { tag := .i8, discriminants := [-1,1], encoding := .direct 0, variants := [[],[]], uninhabited := [false,false] }
private def signed : Plan := .enumeration (.Enum ⟨0⟩) ⟨1,1⟩ signedInfo [some [],some []]

theorem signed_tag_uses_logical_table_value :
    roundtrip signed [Value.intAt 8 (-1)] = .ok [Value.intAt 8 (-1)] := by
  trustIrCompilerProof {
    exact rfl
  } {
    exact by trustIrReduce
  }

theorem missing_covered_payload_byte_refuses :
    refused (decode .le64 none Memory.empty plan
      (ByteImage.ofList [some 10,none,some 7,none,some 52,none,some 9,none])) = true := by
  trustIrCompilerProof {
    exact rfl
  } {
    exact by trustIrReduce
  }

theorem parent_extent_mismatch_refuses :
    refused (decode .le64 none Memory.empty plan (ByteImage.fill 7 (some 0))) = true := by
  trustIrCompilerProof {
    exact rfl
  } {
    exact by trustIrReduce
  }

theorem payload_census_mismatch_refuses :
    (match encode .le64 none plan (.aggregate [.int 8 10,childValue]) false with
     | .error _ => true | .ok _ => false) = true := by
  trustIrCompilerProof {
    exact rfl
  } {
    exact by trustIrReduce
  }

private def definition : EnumDef :=
  { id := ⟨0⟩, name := "PayloadOrUnit", variants := [{ name := "Payload", fields := [childTy,.U8] },
      { name := "Unit", fields := [] }], discriminants := [some 10,some 20], tagRepr := some .u8,
    layout := some { encoding := .direct 0, size := 8, align := 2, variantFieldOffsets := [[2,6],[]] } }
private def module : TrustIrEval.Module :=
  { hasTargetInfo := true, functions := [], funcTys := [], globals := [], enums := [definition],
    structs := [], records := [], types := [] }
private def ctx : EvalContext :=
  match TrustIrEval.contextOf module 0 with
  | .ok context => context
  | .error _ => EvalContext.empty
private def source : Environment := decodedCaptureSource module ctx.byteModel
private theorem contextReady : TrustIrEval.contextOf module 0 = .ok ctx := by
  trustIrCompilerProof {
    exact rfl
  } {
    exact by trustIrReduce
  }

private theorem associated : CaptureSource source ctx :=
  contextOf_capture_source module 0 ctx contextReady (by
    intro id definition member
    change (id,some definition) ∈ ([] : List (RecordId × Option RecordDef)) at member
    cases member)
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 4096 in
private theorem prepared : (prepare source []).query (.Enum ⟨0⟩) = .ok plan := by
  trustIrCompilerProof {
    exact rfl
  } {
    exact by trustIrReduce
  }

theorem prepared_payload_geometry_includes_padding :
    2 + child.layout.size ≤ (8 : Nat) ∧ FieldsAvoidLane [(6,byte)] 2 child.layout.size :=
  (prepared_plan_origin source [] (.Enum ⟨0⟩) plan prepared).enum_payload_child_placement 0 [(2,child),(6,byte)] rfl 0 2 child rfl

theorem selected_payload_callback_keeps_padding (tag : Value) (values : List Value)
    (run : decode .le64 none Memory.empty plan padded = .ok (.aggregate (tag :: values)))
    (found : (trustIrListGet? values 0) = some childValue) :
    ∃ part, ChildDecoded .le64 none Memory.empty child part childValue ∧ part.get 1 = none := by
  trustIrCompilerProof {
    obtain ⟨part,partSize,decoded,lane⟩ := prepared_enum_decoded_payload_slot source [] ⟨0⟩ .le64 none Memory.empty
      ⟨8,2⟩ info variants prepared padded tag values run 0 (by rfl) [(2,child),(6,byte)] rfl 0 2 child rfl childValue found
    refine ⟨part,decoded,?_⟩
    have byte := lane.2 1 (by rw [partSize]; decide)
    have absent : padded.get (2 + 1) = none := rfl
    rw [absent] at byte
    exact byte.symm
  } {
    obtain ⟨part,partSize,decoded,lane⟩ := prepared_enum_decoded_payload_slot source [] ⟨0⟩ .le64 none Memory.empty
      ⟨8,2⟩ info variants prepared padded tag values run 0 (by rfl) [(2,child),(6,byte)] rfl 0 2 child rfl childValue found
    refine ⟨part,decoded,?_⟩
    have byte := lane.2 1 (by rw [partSize]; decide)
    have absent : padded.get (2 + 1) = none := by trustIrReduce
    rw [absent] at byte
    exact byte.symm
  }

private theorem childInitialized : childValue.Initialized :=
  .aggregate _ (by
    intro value member
    cases member with
    | head => exact .int 8 7
    | tail _ member =>
      cases member with
      | head => exact .int 16 4660
      | tail _ impossible => cases impossible)
private theorem inputInitialized : (Value.aggregate inputValues).Initialized :=
  .aggregate _ (by
    intro value member
    cases member with
    | head => exact .int 8 10
    | tail _ member =>
      cases member with
      | head => exact childInitialized
      | tail _ member =>
        cases member with
        | head => exact .int 8 9
        | tail _ impossible => cases impossible)

set_option maxRecDepth 4096 in
private theorem checkedInput : checkClosureValueAt ctx 4 (.Enum ⟨0⟩) (.aggregate inputValues) = .ok () := by
  trustIrCompilerProof {
    exact rfl
  } {
    exact by trustIrReduce
  }

end TrustIr.AggregateMemory.EnumDecoderControls
