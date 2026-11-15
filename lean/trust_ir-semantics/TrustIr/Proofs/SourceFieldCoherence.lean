-- Copyright 2026 Andrew Yates | Apache-2.0
import TrustIr.Proofs.SourceFieldBindings

namespace TrustIr.AggregateMemory
open SourceLayout

private theorem member_of_lookup {α : Type} (rows : List α) (position : Nat) (value : α)
    (found : (trustIrListGet? rows position) = some value) : value ∈ rows := by
  trustIrCompilerProof {
    obtain ⟨inside,get⟩ := List.get?_eq_some.mp found
    exact List.mem_iff_get.mpr ⟨⟨position,inside⟩,get⟩
  } {
    exact CompilerCompat.listGetConstructive_mem found
  }

/-- Checked extents transport physical source separation to actual child writes. -/
theorem FieldBindings.avoids_lane {metadata : List Field} {fields : List (Nat × Plan)}
    (bindings : FieldBindings (metadata.map (·.ty)) (metadata.map (·.offset)) fields)
    (extents : FieldExtents metadata fields) (offset count : Nat)
    (separated : ∀ field ∈ metadata, overlap offset count field.offset field.size = false) :
    FieldsAvoidLane fields offset count := by
  trustIrCompilerProof {
    intro actual member
    obtain ⟨position,get⟩ := List.mem_iff_get.mp member
    have found : (trustIrListGet? fields position.val) = some actual := List.get?_eq_some.mpr ⟨position.isLt,get⟩
    obtain ⟨field,sourceRow,typed,placed⟩ := bindings.source_child position.val actual.1 actual.2 found
    have sized := extents.at position.val field actual.1 actual.2 sourceRow found
    change overlap offset count actual.1 actual.2.layout.size = false
    rw [placed,sized]
    exact separated field (member_of_lookup metadata position.val field sourceRow)
  } {
    intro actual member
    obtain ⟨position,get⟩ := List.mem_iff_get.mp member
    change fields[position.val] = actual at get
    have found : (trustIrListGet? fields position.val) = some actual := CompilerCompat.listGet?_eq_some.mpr ⟨position.isLt,get⟩
    obtain ⟨field,sourceRow,typed,placed⟩ := bindings.source_child position.val actual.1 actual.2 found
    have sized := extents.at position.val field actual.1 actual.2 sourceRow found
    change overlap offset count actual.1 actual.2.layout.size = false
    rw [placed,sized]
    exact separated field (member_of_lookup metadata position.val field sourceRow)
  }

private theorem variant_avoids {info : Enumeration} {variants : List (Option (List (Nat × Plan)))}
    (bindings : VariantBindings (info.variants.map (fun fields => fields.map (·.ty)))
      (info.variants.map (fun fields => fields.map (·.offset))) info.uninhabited variants)
    (extents : VariantExtents info.variants variants) (position offset count : Nat)
    (separated : ∀ metadata, (trustIrListGet? info.variants position) = some metadata →
      ∀ field ∈ metadata, overlap offset count field.offset field.size = false) :
    ∀ fields, (trustIrListGet? variants position) = some (some fields) → FieldsAvoidLane fields offset count := by
  intro fields found
  obtain ⟨metadata,row,tied⟩ := bindings.source_at position fields found
  obtain ⟨other,otherRow,sized⟩ := extents position fields found
  have same := Option.some.inj (row.symm.trans otherRow)
  subst other
  exact tied.avoids_lane sized offset count (separated metadata row)

/-- Actual compiler checks discharge tag/payload separation for every encoding. -/
theorem enum_checked_fields_avoid_tag (value : Summary) (info : Enumeration)
    (present : value.enumeration = some info) (geometry : EnumEncodingGeometry value)
    (variants : List (Option (List (Nat × Plan))))
    (bindings : VariantBindings (info.variants.map (fun fields => fields.map (·.ty)))
      (info.variants.map (fun fields => fields.map (·.offset))) info.uninhabited variants)
    (extents : VariantExtents info.variants variants) (position : Nat)
    (live : (trustIrListGet? info.uninhabited position) = some false) : EnumPayloadAvoidsTag info variants position := by
  have guarded := geometry info present
  cases encoding : info.encoding with
  | untagged => simp [EnumPayloadAvoidsTag,encoding]
  | singleInhabited chosen => simp [EnumPayloadAvoidsTag,encoding]
  | direct offset =>
    rw [encoding] at guarded
    obtain ⟨align,aligned,laneBounds,separated⟩ := guarded
    rw [EnumPayloadAvoidsTag,encoding]
    apply variant_avoids bindings extents position offset (tagBits info.tag / 8)
    intro metadata row field member
    exact separated metadata (member_of_lookup info.variants position metadata row) field member
  | niche untagged start stop first offset repr =>
    rw [encoding] at guarded
    obtain ⟨align,aligned,laneBounds,cardinality,untaggedBound,ordered,endBound,firstFits,rangeFits,allowed,carrier,separated⟩ := guarded
    rw [EnumPayloadAvoidsTag,encoding]
    intro other
    have range : start ≤ position ∧ position ≤ stop := by
      have admitted := List.all_eq_true.mp allowed (false,position) ((numbered_member_iff_get _ _ _).2 live)
      simpa [other] using admitted
    apply variant_avoids bindings extents position offset (tagBits repr / 8)
    intro metadata row field member
    exact separated metadata position ((numbered_member_iff_get _ _ _).2 row) other range.1 range.2 field member

/-- Actual prepared plans discharge physical separation from source geometry and
    the compiler's checked child extents. -/
theorem prepared_enum_payload_avoids_tag (source : Environment) (roots : List Ty)
    (id : EnumId) (plan : Plan) (run : (prepare source roots).query (.Enum id) = .ok plan)
    (layout : MemoryTypeLayout) (info : Enumeration)
    (variants : List (Option (List (Nat × Plan))))
    (shape : plan = .enumeration (.Enum id) layout info variants)
    (position : Nat) (live : (trustIrListGet? info.uninhabited position) = some false) :
    EnumPayloadAvoidsTag info variants position := by
  obtain ⟨actualLayout,actualInfo,actualVariants,value,actualShape,actual,present,
    extent,children,bindings,sizes⟩ :=
    (prepared_plan_origin source roots (.Enum id) plan run).enum_extent_view
  have same := Plan.enumeration.inj (actualShape.symm.trans shape)
  obtain ⟨_,layoutEq,infoEq,variantsEq⟩ := same
  subst actualLayout
  subst actualInfo
  subst actualVariants
  obtain ⟨before,next,history,queried⟩ := actual
  exact enum_checked_fields_avoid_tag value info present
    (history.query_encoding_geometry .execution (.Enum id) value queried)
    variants bindings sizes position live

/-- Source-bound successful encoding preserves selection using compiler-checked
    separation; default niche carrier initialization remains explicit. -/
theorem prepared_enum_capture_coherent_encoded_selection (source : Environment) (ctx : EvalContext)
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
        EnumUntaggedCarrierReady info position image.bytes →
        image.bytes.size = layout.size ∧ EnumDecodingSelects info image.bytes position := by
  obtain ⟨layout,info,variants,tag,payload,position,variant,fields,
    shape,valuesShape,sourceSelected,row,selected,live,found,origins,finish⟩ :=
    prepared_enum_capture_encoded_selection source ctx associated admitted roots id definition resolved
      plan run fuel values initialized checked
  refine ⟨layout,info,variants,tag,payload,position,variant,fields,
    shape,valuesShape,sourceSelected,row,selected,live,found,origins,?_⟩
  intro model order allowUnwritten image encoded carrier
  exact finish model order allowUnwritten image encoded
    (prepared_enum_payload_avoids_tag source roots id plan run layout info variants shape position live) carrier

end TrustIr.AggregateMemory
