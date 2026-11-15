-- Copyright 2026 Andrew Yates | Apache-2.0
import TrustIr.Proofs.SourceEnumDecode

namespace TrustIr.AggregateMemory
open SourceLayout

/-- A retained plan's selected payload must avoid its direct/tagged-niche lane.
    Authenticating this from source field layouts remains an explicit obligation. -/
def EnumPayloadAvoidsTag (info : Enumeration) (variants : List (Option (List (Nat × Plan))))
    (position : Nat) : Prop :=
  match info.encoding with
  | .untagged | .singleInhabited _ => True
  | .direct offset => ∀ fields, (trustIrListGet? variants position) = some (some fields) →
      FieldsAvoidLane fields offset (tagBits info.tag / 8)
  | .niche untagged _ _ _ offset repr => position ≠ untagged →
      ∀ fields, (trustIrListGet? variants position) = some (some fields) →
        FieldsAvoidLane fields offset (tagBits repr / 8)

/-- The real decoder read is required for the default niche payload. -/
def EnumUntaggedCarrierReady (info : Enumeration) (position : Nat) (image : ByteImage) : Prop :=
  match info.encoding with
  | .niche untagged _ _ _ offset repr => position = untagged →
      ∃ bytes, InitializedLane image offset (tagBits repr / 8) bytes
  | _ => True

/-- Prefix authority survives actual successful payload encoding under explicit
    retained-field separation and default-carrier initialization obligations. -/
theorem enum_encoded_selection (model : ByteModel) (order : FunctionAddressOrder)
    (ty : Ty) (layout : MemoryTypeLayout) (info : Enumeration)
    (variants : List (Option (List (Nat × Plan)))) (tag : Value) (values : List Value)
    (position : Nat) (allowUnwritten : Bool) (image : Image)
    (selected : EnumEncodingSelects info tag position)
    (sound : EnumPrefixSound layout.size info position tag)
    (encoded : encode model order (.enumeration ty layout info variants)
      (.aggregate (tag :: values)) allowUnwritten = .ok image)
    (separated : EnumPayloadAvoidsTag info variants position)
    (carrier : EnumUntaggedCarrierReady info position image.bytes) :
    image.bytes.size = layout.size ∧ EnumDecodingSelects info image.bytes position := by
  obtain ⟨actual,bytes,actualSelected,built,payload,guarded⟩ :=
    encode_enumeration_steps model order ty layout info variants tag values allowUnwritten image encoded
  have same := selected.functional actualSelected
  subst actual
  refine ⟨encode_enumeration_extent model order ty layout info variants tag values allowUnwritten image encoded,?_⟩
  have prefixSelected := sound.2 bytes built
  cases encoding : info.encoding with
  | untagged =>
    rw [encoding] at prefixSelected
    exact prefixSelected image.bytes
  | singleInhabited chosen =>
    rw [encoding] at prefixSelected
    exact prefixSelected image.bytes
  | direct offset =>
    rw [encoding] at prefixSelected
    obtain ⟨width,raw,shape⟩ := built.direct_tag encoding
    subst tag
    let tagBytes := encodeIntBytes raw (tagBits info.tag / 8)
    have lane := built.direct_lane layout.size info position width raw bytes offset encoding
    have finalLane := payload.preserves_lane lane (by
      intro fields found
      have avoids := separated
      rw [EnumPayloadAvoidsTag,encoding] at avoids
      simpa only [ByteImage.size_ofList,List.length_map,encodeIntBytes_length] using avoids fields found)
    have initialRead := lane.initialized tagBytes
    have finalRead := finalLane.initialized tagBytes
    have count : tagBytes.length = tagBits info.tag / 8 := encodeIntBytes_length _ _
    rw [count] at initialRead finalRead
    exact EnumDecodingSelects.transfer_direct encoding initialRead finalRead prefixSelected
  | niche untagged start stop first offset repr =>
    rw [encoding] at prefixSelected
    dsimp only at prefixSelected
    by_cases isDefault : position = untagged
    · rw [if_pos isDefault] at prefixSelected
      have ready := carrier
      rw [EnumUntaggedCarrierReady,encoding] at ready
      obtain ⟨tagBytes,read⟩ := ready isDefault
      exact prefixSelected image.bytes tagBytes read guarded
    · rw [if_neg isDefault] at prefixSelected
      let word := truncateUnsigned (Int.ofNat first + Int.ofNat position - Int.ofNat start) (tagBits repr)
      let tagBytes := encodeIntBytes word (tagBits repr / 8)
      have lane := built.niche_lane layout.size info position tag bytes untagged start stop first offset repr encoding isDefault
      have finalLane := payload.preserves_lane lane (by
        intro fields found
        have avoids := separated
        rw [EnumPayloadAvoidsTag,encoding] at avoids
        simpa only [ByteImage.size_ofList,List.length_map,encodeIntBytes_length] using avoids isDefault fields found)
      have initialRead := lane.initialized tagBytes
      have finalRead := finalLane.initialized tagBytes
      have count : tagBytes.length = tagBits repr / 8 := encodeIntBytes_length _ _
      rw [count] at initialRead finalRead
      exact EnumDecodingSelects.transfer_niche encoding initialRead finalRead prefixSelected

/-- Source-bound admitted captures retain final-image selection whenever the
    actual encoding succeeds and the remaining lane obligations are established. -/
theorem prepared_enum_capture_encoded_selection (source : Environment) (ctx : EvalContext)
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
        EnumPayloadAvoidsTag info variants position →
        EnumUntaggedCarrierReady info position image.bytes →
        image.bytes.size = layout.size ∧ EnumDecodingSelects info image.bytes position := by
  obtain ⟨layout,info,variants,tag,payload,position,variant,fields,
    shape,valuesShape,sourceSelected,row,selected,live,found,origins,sound⟩ :=
    prepared_enum_capture_prefix source ctx associated admitted roots id definition resolved plan run
      fuel values initialized checked
  refine ⟨layout,info,variants,tag,payload,position,variant,fields,
    shape,valuesShape,sourceSelected,row,selected,live,found,origins,?_⟩
  intro model order allowUnwritten image encoded separated carrier
  rw [shape,valuesShape] at encoded
  exact enum_encoded_selection model order (.Enum id) layout info variants tag payload position
    allowUnwritten image selected sound encoded separated carrier

end TrustIr.AggregateMemory

namespace TrustIr.AggregateMemory.EnumImageControls
open SourceLayout

private def bytePlan : Plan := .leaf .U8 ⟨1,1⟩
private def direct : Enumeration :=
  { tag := .u8, discriminants := [0,1], encoding := .direct 0,
    variants := [[],[]], uninhabited := [false,false] }
private def one : Image := { bytes := ByteImage.ofList [some 1] }
private def disjointPrefix : ByteImage :=
  (ByteImage.fill 2 none).slice 0 0 |>.append
    ((ByteImage.ofList [some 0]).append ((ByteImage.fill 2 none).slice 1 1))
private def disjointImage : Image :=
  { bytes := (disjointPrefix.slice 0 1).append
      ((ByteImage.ofList [some 1]).append (disjointPrefix.slice 2 0)) }

/-- A malformed retained plan can overwrite its own prefix; separation is essential. -/
theorem overlapping_payload_changes_selection :
    encode .le64 none (.enumeration (.Enum ⟨0⟩) ⟨1,1⟩ direct
      [some [(0,bytePlan)],some []]) (.aggregate [.int 8 0,.int 8 1]) false = .ok one ∧
    EnumDecodingSelects direct one.bytes 1 := by
  trustIrCompilerProof {
    exact ⟨rfl,rfl⟩
  } {
    constructor <;> trustIrReduce
  }

theorem overlapping_retained_range_is_not_separated : ¬ FieldsAvoidLane [(0,bytePlan)] 0 1 := by
  intro separated
  have bad := separated (0,bytePlan) ((trustIrListMemConsSelf _ _))
  change (true : Bool) = false at bad
  cases bad

theorem disjoint_payload_keeps_selection :
    encode .le64 none (.enumeration (.Enum ⟨0⟩) ⟨2,1⟩ direct
      [some [(1,bytePlan)],some []]) (.aggregate [.int 8 0,.int 8 1]) false = .ok disjointImage ∧
    EnumDecodingSelects direct disjointImage.bytes 0 := by
  trustIrCompilerProof {
    exact ⟨rfl,rfl⟩
  } {
    constructor <;> trustIrReduce
  }

theorem wrong_child_extent_refuses :
    encode .le64 none (.leaf .U8 ⟨2,1⟩) (.int 8 1) false =
      .error (.typeError "memory image: leaf byte count mismatch") := by
  trustIrCompilerProof {
    exact rfl
  } {
    trustIrReduce
  }

theorem wrong_payload_census_refuses :
    encode .le64 none (.fields (.Tuple []) ⟨0,1⟩ []) (.aggregate [.int 8 1]) false =
      .error (.typeError "memory image: field census mismatch") := by
  trustIrCompilerProof {
    exact rfl
  } {
    trustIrReduce
  }

theorem unwritten_transport_retains_extent :
    encode .le64 none (.leaf .U8 ⟨2,1⟩) .uninit true =
      .ok { bytes := ByteImage.fill 2 none, unwritten := [(0,2)] } := by
  trustIrCompilerProof {
    exact rfl
  } {
    trustIrReduce
  }

theorem forbidden_unwritten_refuses :
    encode .le64 none bytePlan .uninit false =
      .error (.ub "memory image: inspecting an unwritten lane") := by
  trustIrCompilerProof {
    exact rfl
  } {
    trustIrReduce
  }

private def niche : Enumeration :=
  { tag := .u8, discriminants := [0,1], encoding := .niche 0 1 1 1 0 .u8,
    variants := [[],[]], uninhabited := [false,false] }
private def missing : Image := { bytes := ByteImage.fill 1 none }

theorem successful_encoding_does_not_imply_carrier_initialization :
    encode .le64 none (.enumeration (.Enum ⟨0⟩) ⟨1,1⟩ niche [some [],some []])
      (.aggregate [.int 8 0]) false = .ok missing ∧
    ¬ EnumUntaggedCarrierReady niche 0 missing.bytes := by
  trustIrCompilerProof {
    refine ⟨rfl,?_⟩
    intro ready
    obtain ⟨bytes,read⟩ := ready rfl
    cases read
  } {
    refine ⟨(by trustIrReduce),?_⟩
    intro ready
    obtain ⟨bytes,read⟩ := ready rfl
    cases read
  }

theorem reserved_default_payload_refuses :
    encode .le64 none (.enumeration (.Enum ⟨0⟩) ⟨1,1⟩ niche
      [some [(0,bytePlan)],some []]) (.aggregate [.int 8 0,.int 8 1]) false =
      .error (.typeError "memory image: untagged payload occupies a reserved niche") := by
  trustIrCompilerProof {
    exact rfl
  } {
    trustIrReduce
  }

end TrustIr.AggregateMemory.EnumImageControls
