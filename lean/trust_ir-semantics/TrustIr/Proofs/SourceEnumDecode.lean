-- Copyright 2026 Andrew Yates | Apache-2.0
import TrustIr.Proofs.SourceEnumCodec
import TrustIr.Proofs.ByteMemory

namespace TrustIr.AggregateMemory
open SourceLayout

theorem image_materialized_length (image : ByteImage) : image.toList.length = image.size := by
  simp only [ByteImage.toList,List.length_map,metadata_range_length]

theorem image_materialized_lookup (image : ByteImage) (position : Nat) :
    (trustIrListGet? image.toList position) = if position < image.size then some (image.get position) else none := by
  trustIrCompilerProof {
    unfold ByteImage.toList
    rw [List.get?_map,numbered_range_lookup]
    split <;> rfl
  } {
    unfold ByteImage.toList
    rw [CompilerCompat.listGetConstructive_map,numbered_range_lookup]
    split <;> rfl
  }

/-- An actual overwritten window yields the actual initialized decoder lane. -/
theorem ByteLane.initialized {image : ByteImage} {offset : Nat} (bytes : List UInt8)
    (lane : ByteLane image offset (ByteImage.ofList (bytes.map some))) :
    InitializedLane image offset bytes.length bytes := by
  trustIrCompilerProof {
    apply InitializedLane.of_materialized
    apply List.ext
    intro position
    have extent : (image.slice offset bytes.length).size = bytes.length := by
      rw [ByteImage.size_slice]
      have bound := lane.1
      simp only [ByteImage.size_ofList,List.length_map] at bound
      omega
    rw [image_materialized_lookup,extent]
    by_cases inside : position < bytes.length
    · rw [if_pos inside,ByteImage.get_slice image offset bytes.length position inside (by
        have bound := lane.1
        simp only [ByteImage.size_ofList,List.length_map] at bound
        omega)]
      rw [lane.2 position (by simpa using inside),ByteImage.get_ofList]
      simp only [List.get?_map,List.get?_eq_get inside,Option.map,Option.getD]
    · rw [if_neg inside,List.get?_eq_none.mpr (by simp only [List.length_map]; omega)]
  } {
    apply InitializedLane.of_materialized
    apply CompilerCompat.listGetConstructive_ext
    intro position
    have extent : (image.slice offset bytes.length).size = bytes.length := by
      rw [ByteImage.size_slice]
      have bound := lane.1
      simp only [ByteImage.size_ofList,List.length_map] at bound
      omega
    rw [image_materialized_lookup,extent]
    by_cases inside : position < bytes.length
    · rw [if_pos inside,ByteImage.get_slice image offset bytes.length position inside (by
        have bound := lane.1
        simp only [ByteImage.size_ofList,List.length_map] at bound
        omega)]
      rw [lane.2 position (by simpa using inside),ByteImage.get_ofList]
      simp only [CompilerCompat.listGetConstructive_map,CompilerCompat.listGet?_eq_get inside,Option.map,Option.getD]
    · rw [if_neg inside,CompilerCompat.listGet?_outside _ _ (by simp only [List.length_map]; omega)]
  }

/-- Actual byte encoding and decoding agree for every nonnegative in-range lane. -/
theorem decode_encode_integer (raw : Int) (count : Nat) (nonnegative : 0 ≤ raw)
    (bound : raw < (256 : Int) ^ count) : Int.ofNat (decodeIntBytes (encodeIntBytes raw count)) = raw := by
  have cast : (Int.ofNat raw.toNat) = raw := Int.toNat_of_nonneg nonnegative
  have capacity : Int.ofNat ((256 : Nat) ^ count) = (256 : Int) ^ count := Int.natCast_pow _ _
  have small : raw.toNat < (256 : Nat) ^ count := by
    apply Int.ofNat_lt.mp
    change Int.ofNat raw.toNat < Int.ofNat ((256 : Nat) ^ count)
    rw [cast,capacity]
    exact bound
  change Int.ofNat (decodeIntBytes.go (encodeIntBytes.go count raw.toNat) 0) = raw
  rw [decode_encode_go]
  simp only [Nat.pow_zero,Nat.one_mul,Nat.mod_eq_of_lt small]
  exact cast

theorem tag_byte_capacity (tag : EnumTagRepr) : (256 : Int) ^ (tagBits tag / 8) = (2 : Int) ^ tagBits tag := by
  cases tag <;> decide

/-- The actual direct tag built supplies exactly the bytes read by selection. -/
theorem direct_prefix_decoding_agrees (size : Nat) (info : Enumeration) (position width : Nat) (raw : Int)
    (image : ByteImage) (offset : Nat) (encoding : info.encoding = .direct offset)
    (built : EnumTagPrefix size info position (.int width raw) image)
    (selected : EnumEncodingSelects info (.int width raw) position)
    (nonnegative : 0 ≤ raw) (canonical : raw < (2 : Int) ^ tagBits info.tag)
    (live : (trustIrListGet? info.uninhabited position) = some false) (bound : position < info.discriminants.length) :
    EnumDecodingSelects info image position := by
  let bytes := encodeIntBytes raw (tagBits info.tag / 8)
  have lane := EnumTagPrefix.direct_lane size info position width raw image offset encoding built
  have read := lane.initialized bytes
  have sized : bytes.length = tagBits info.tag / 8 := encodeIntBytes_length _ _
  rw [sized] at read
  have decoded : Int.ofNat (decodeIntBytes bytes) = raw :=
    decode_encode_integer raw _ nonnegative (by rw [tag_byte_capacity]; exact canonical)
  apply EnumDecodingSelects.direct info image offset position bytes encoding read ?_ live bound
  rw [decoded]
  have normalization : (if tagSigned info.tag then toSigned raw (tagBits info.tag) else raw) = enumTagValue info.tag raw := by
    unfold enumTagValue
    split
    · rfl
    · rw [truncateUnsigned,Int.emod_eq_of_lt nonnegative canonical]
  rw [normalization]
  exact (selected.lookup info width raw position).2

theorem profiled_direct_prefix_decoding_agrees (size : Nat) (info : Enumeration) (position width : Nat) (raw : Int)
    (image : ByteImage) (offset : Nat) {profiles : List UninhabitedVariantLayout} (encoding : info.encoding = .directWithUninhabited offset profiles)
    (built : EnumTagPrefix size info position (.int width raw) image)
    (selected : EnumEncodingSelects info (.int width raw) position)
    (nonnegative : 0 ≤ raw) (canonical : raw < (2 : Int) ^ tagBits info.tag)
    (live : (trustIrListGet? info.uninhabited position) = some false) (bound : position < info.discriminants.length) :
    EnumDecodingSelects info image position := by
  let bytes := encodeIntBytes raw (tagBits info.tag / 8)
  have lane := EnumTagPrefix.profiled_direct_lane size info position width raw image offset encoding built
  have read := lane.initialized bytes
  have sized : bytes.length = tagBits info.tag / 8 := encodeIntBytes_length _ _
  rw [sized] at read
  have decoded : Int.ofNat (decodeIntBytes bytes) = raw :=
    decode_encode_integer raw _ nonnegative (by rw [tag_byte_capacity]; exact canonical)
  apply EnumDecodingSelects.profiled_direct info image offset position bytes encoding read ?_ live bound
  rw [decoded]
  have normalization : (if tagSigned info.tag then toSigned raw (tagBits info.tag) else raw) = enumTagValue info.tag raw := by
    unfold enumTagValue
    split
    · rfl
    · rw [truncateUnsigned,Int.emod_eq_of_lt nonnegative canonical]
  rw [normalization]
  exact (selected.lookup info width raw position).2


/-- Payload bytes cannot change untagged selection after its actual built guard. -/
theorem untagged_prefix_decoding_agrees (size : Nat) (info : Enumeration) (position : Nat) (tag : Value)
    (prefixImage image : ByteImage) (encoding : info.encoding = .untagged)
    (built : EnumTagPrefix size info position tag prefixImage)
    (live : (trustIrListGet? info.uninhabited position) = some false) (bound : position < info.discriminants.length) :
    EnumDecodingSelects info image position := by
  have selected := built.untagged_index size info position tag prefixImage encoding
  subst position
  exact EnumDecodingSelects.untagged info image encoding live bound

/-- Payload bytes cannot change single-inhabited selection after its real guard. -/
theorem single_prefix_decoding_agrees (size : Nat) (info : Enumeration) (position chosen : Nat) (tag : Value)
    (prefixImage image : ByteImage) (encoding : info.encoding = .singleInhabited chosen)
    (built : EnumTagPrefix size info position tag prefixImage)
    (live : (trustIrListGet? info.uninhabited position) = some false) (bound : position < info.discriminants.length) :
    EnumDecodingSelects info image position := by
  have selected := built.single_index size info position chosen tag prefixImage encoding
  subst position
  exact EnumDecodingSelects.single info image chosen encoding live bound

/-- The modular niche numbering is invertible across its wraparound boundary. -/
theorem niche_relative_roundtrip (first relative modulus : Nat) (firstBound : first < modulus)
    (relativeBound : relative < modulus) :
    (((first + relative) % modulus) + modulus - first) % modulus = relative := by
  by_cases small : first + relative < modulus
  · rw [Nat.mod_eq_of_lt small]
    have sum : first + relative + modulus - first = relative + modulus := by omega
    rw [sum,Nat.add_mod_right,Nat.mod_eq_of_lt relativeBound]
  · have large : modulus ≤ first + relative := by omega
    rw [Nat.mod_eq_sub_mod large,Nat.mod_eq_of_lt (show first + relative - modulus < modulus from by omega)]
    have sum : first + relative - modulus + modulus - first = relative := by omega
    rw [sum,Nat.mod_eq_of_lt relativeBound]

/-- Actual tagged niche bytes decode to the original numbered variant. -/
theorem niche_prefix_decoding_agrees (size : Nat) (info : Enumeration) (position : Nat) (tag : Value)
    (image : ByteImage) (untagged start stop first offset : Nat) (repr : EnumTagRepr)
    (encoding : info.encoding = .niche untagged start stop first offset repr)
    (built : EnumTagPrefix size info position tag image) (other : position ≠ untagged)
    (lower : start ≤ position) (upper : position ≤ stop)
    (firstBound : first < 2 ^ tagBits repr) (rangeBound : stop - start < 2 ^ tagBits repr)
    (live : (trustIrListGet? info.uninhabited position) = some false) (bound : position < info.discriminants.length) :
    EnumDecodingSelects info image position := by
  let word := truncateUnsigned (Int.ofNat first + Int.ofNat position - Int.ofNat start) (tagBits repr)
  let bytes := encodeIntBytes word (tagBits repr / 8)
  have lane := built.niche_lane size info position tag image untagged start stop first offset repr encoding other
  have read := lane.initialized bytes
  have sized : bytes.length = tagBits repr / 8 := encodeIntBytes_length _ _
  rw [sized] at read
  have positive : (0 : Int) < 2 ^ tagBits repr := by cases repr <;> decide
  have nonnegative : 0 ≤ word := Int.emod_nonneg _ (Int.ne_of_gt positive)
  have canonical : word < (2 : Int) ^ tagBits repr := Int.emod_lt_of_pos _ positive
  have decoded := decode_encode_integer word (tagBits repr / 8) nonnegative (by rw [tag_byte_capacity]; exact canonical)
  have argument : Int.ofNat first + Int.ofNat position - Int.ofNat start = Int.ofNat (first + (position - start)) := by
    have sumCast : Int.ofNat (first + (position - start)) = Int.ofNat first + Int.ofNat (position - start) := rfl
    have subCast : Int.ofNat (position - start) = Int.ofNat position - Int.ofNat start := Int.ofNat_sub lower
    rw [sumCast,subCast]
    omega
  have representation : word = Int.ofNat ((first + (position - start)) % (2 ^ tagBits repr)) := by
    dsimp only [word,truncateUnsigned]
    have modulusCast : (2 : Int) ^ tagBits repr = Int.ofNat ((2 : Nat) ^ tagBits repr) :=
      (Int.natCast_pow 2 (tagBits repr)).symm
    rw [argument,modulusCast]
    rfl
  have wordEq := Int.ofNat.inj (decoded.trans representation)
  have relative : (decodeIntBytes bytes + 2 ^ tagBits repr - first) % (2 ^ tagBits repr) = position - start := by
    rw [wordEq]
    exact niche_relative_roundtrip first (position - start) _ firstBound (by omega)
  apply EnumDecodingSelects.niche_tagged info image untagged start stop first offset position repr bytes encoding read
    (by rw [relative]; omega) (by rw [relative]; omega) other live bound

/-- The real untagged-payload guard and actual initialized bytes agree with
    the decoder's default niche branch, rather than treating absent bytes as zero. -/
theorem niche_payload_decoding_agrees (info : Enumeration) (image : ByteImage)
    (untagged start stop first offset : Nat) (repr : EnumTagRepr) (bytes : List UInt8)
    (encoding : info.encoding = .niche untagged start stop first offset repr)
    (checked : NichePayloadChecked info untagged image)
    (read : InitializedLane image offset (tagBits repr / 8) bytes)
    (live : (trustIrListGet? info.uninhabited untagged) = some false) (bound : untagged < info.discriminants.length) :
    EnumDecodingSelects info image untagged := by
  have outside := checked.untagged_outside info image untagged start stop first offset repr encoding
  rw [read.defaulted] at outside
  exact EnumDecodingSelects.niche_untagged info image untagged start stop first offset repr bytes encoding read outside live bound

/-- Prefix selection authority for every physical encoding. Untagged niche
    payloads additionally retain the actual encoder guard and initialized carrier. -/
def EnumPrefixSound (size : Nat) (info : Enumeration) (position : Nat) (tag : Value) : Prop :=
  (∃ image, EnumTagPrefix size info position tag image) ∧
  ∀ initial, EnumTagPrefix size info position tag initial →
    match info.encoding with
    | .untagged | .singleInhabited _ => ∀ image, EnumDecodingSelects info image position
    | .direct _ | .directWithUninhabited _ _ => EnumDecodingSelects info initial position
    | .niche untagged _ _ _ offset repr =>
      if position = untagged then
        ∀ image bytes, InitializedLane image offset (tagBits repr / 8) bytes →
          NichePayloadChecked info position image → EnumDecodingSelects info image position
      else EnumDecodingSelects info initial position

private theorem live_discriminant_bound (value : Summary) (info : Enumeration)
    (present : value.enumeration = some info) (metadata : EnumMetadata value) (position : Nat)
    (live : (trustIrListGet? info.uninhabited position) = some false) : position < info.discriminants.length := by
  trustIrCompilerProof {
    have counts := metadata info present
    by_cases inside : position < info.uninhabited.length
    · omega
    · rw [List.get?_eq_none.mpr (by omega)] at live
      cases live
  } {
    have counts := metadata info present
    by_cases inside : position < info.uninhabited.length
    · omega
    · rw [CompilerCompat.listGet?_outside _ _ (by omega)] at live
      cases live
  }

/-- Genuine finalizer geometry and checked tag data construct a real prefix
    and discharge the selector laws for all encoding constructors. -/
theorem enum_prefix_sound (value : Summary) (info : Enumeration) (present : value.enumeration = some info)
    (metadata : EnumMetadata value) (geometry : EnumEncodingGeometry value) (size : Nat) (extent : size = value.size)
    (position width : Nat) (raw : Int) (selected : EnumEncodingSelects info (.int width raw) position)
    (nonnegative : 0 ≤ raw) (canonical : raw < (2 : Int) ^ tagBits info.tag)
    (live : (trustIrListGet? info.uninhabited position) = some false) : EnumPrefixSound size info position (.int width raw) := by
  have counts := metadata info present
  have bound := live_discriminant_bound value info present metadata position live
  have guarded := geometry info present
  cases encoding : info.encoding with
  | untagged =>
    rw [encoding] at guarded
    have only : position = 0 := by omega
    subst position
    refine ⟨⟨ByteImage.fill size none,EnumTagPrefix.untagged_exists size info _ encoding⟩,?_⟩
    intro initial built
    rw [encoding]
    intro image
    exact EnumDecodingSelects.untagged info image encoding live bound
  | singleInhabited chosen =>
    rw [encoding] at guarded
    have same : position = chosen := by
      by_cases matched : position = chosen
      · exact matched
      · have admitted := List.all_eq_true.mp guarded.2.2.2 (false,position)
          ((numbered_member_iff_get _ _ _).2 live)
        simp [matched] at admitted
    subst position
    refine ⟨⟨ByteImage.fill size none,EnumTagPrefix.single_exists size info chosen _ encoding⟩,?_⟩
    intro initial built
    rw [encoding]
    intro image
    exact EnumDecodingSelects.single info image chosen encoding live bound
  | direct offset =>
    rw [encoding] at guarded
    obtain ⟨align,aligned,laneBounds,separated⟩ := guarded
    have fits : offset + (ByteImage.ofList ((encodeIntBytes raw (tagBits info.tag / 8)).map some)).size ≤ size := by
      simp only [ByteImage.size_ofList,List.length_map,encodeIntBytes_length]
      rw [extent]
      exact laneBounds.2.2.1
    refine ⟨EnumTagPrefix.direct_exists size info position width raw offset encoding fits,?_⟩
    intro initial built
    rw [encoding]
    exact direct_prefix_decoding_agrees size info position width raw initial offset encoding built selected nonnegative canonical live bound
  | directWithUninhabited offset profiles =>
    rw [encoding] at guarded
    obtain ⟨align,aligned,laneBounds,profileLanes,separated⟩ := guarded
    have fits : offset + (ByteImage.ofList ((encodeIntBytes raw (tagBits info.tag / 8)).map some)).size ≤ size := by
      simp only [ByteImage.size_ofList,List.length_map,encodeIntBytes_length]
      rw [extent]
      exact laneBounds.2.2.1
    refine ⟨EnumTagPrefix.profiled_direct_exists size info position width raw offset encoding fits,?_⟩
    intro initial built
    rw [encoding]
    exact profiled_direct_prefix_decoding_agrees size info position width raw initial offset encoding built selected nonnegative canonical live bound
  | niche untagged start stop first offset repr =>
    rw [encoding] at guarded
    obtain ⟨align,aligned,laneBounds,cardinality,untaggedBound,ordered,endBound,firstFits,rangeFits,allowed,carrier,separated⟩ := guarded
    by_cases same : position = untagged
    · subst position
      refine ⟨⟨ByteImage.fill size none,EnumTagPrefix.niche_untagged_exists size info _ untagged start stop first offset repr encoding⟩,?_⟩
      intro initial built
      rw [encoding]
      simp only [ite_true]
      intro image bytes read checked
      exact niche_payload_decoding_agrees info image untagged start stop first offset repr bytes encoding checked read live bound
    · have range : start ≤ position ∧ position ≤ stop := by
        have admitted := List.all_eq_true.mp allowed (false,position) ((numbered_member_iff_get _ _ _).2 live)
        simpa [same] using admitted
      have positive : 0 < 2 ^ tagBits repr := by cases repr <;> decide
      have firstBound : first < 2 ^ tagBits repr := by omega
      have rangeBound : stop - start < 2 ^ tagBits repr := by omega
      have fits : offset + (ByteImage.ofList ((encodeIntBytes
          (truncateUnsigned (Int.ofNat first + Int.ofNat position - Int.ofNat start) (tagBits repr))
          (tagBits repr / 8)).map some)).size ≤ size := by
        simp only [ByteImage.size_ofList,List.length_map,encodeIntBytes_length]
        rw [extent]
        exact laneBounds.2.2.1
      refine ⟨EnumTagPrefix.niche_tagged_exists size info position _ untagged start stop first offset repr encoding same fits,?_⟩
      intro initial built
      rw [encoding]
      simp only [if_neg same]
      exact niche_prefix_decoding_agrees size info position _ initial untagged start stop first offset repr encoding built same
        range.1 range.2 firstBound rangeBound live bound

/-- The actual prepared plan's checked initialized active capture has real
    prefix selection authority, with its exact actual extent retained. -/
theorem prepared_enum_capture_prefix (source : Environment) (ctx : EvalContext)
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
      EnumPrefixSound layout.size info position tag := by
  obtain ⟨layout,info,variants,value,planShape,actual,present,extent,children⟩ :=
    (prepared_plan_origin source roots (.Enum id) plan run).enum_layout_view
  obtain ⟨before,next,history,queried⟩ := actual
  obtain ⟨sourcePosition,actualDefinition,sourceRow,identity,origin⟩ := history.query_enum_origin .execution id value queried
  have member := numbered_source_member source.enums actualDefinition sourcePosition ((numbered_member_iff_get _ _ _).2 sourceRow)
  have same := enum_lookup_agrees_of_admission source ctx associated admitted id definition resolved actualDefinition member identity
  subst actualDefinition
  obtain ⟨width,number,payload,position,variant,repr,valuesShape,selected,row,tagged,tagChecked⟩ :=
    enum_checked_tag_contract ctx fuel id definition resolved values checked
  have actualTag := (origin.tag_data info present).1
  rw [canonicalTag_eval] at actualTag
  have sameTag := Option.some.inj (tagged.symm.trans actualTag)
  subst repr
  obtain ⟨otherTag,otherPayload,otherPosition,otherVariant,otherShape,otherSelected,_otherRow,flag⟩ :=
    history.query_enum_capture_active_flag_false ctx associated admitted .execution id definition resolved
      value info present queried fuel values initialized checked
  have tags := (List.cons.inj (otherShape.symm.trans valuesShape)).1
  rw [tags] at otherSelected
  have positions := EnumTagSelects.functional definition (.int width number) otherPosition position otherSelected selected
  subst otherPosition
  have encoding := enum_encoding_of_checked_selection origin info present ctx fuel (.int width number) position selected tagChecked flag
  obtain ⟨fields,found,fieldOrigins⟩ := children.live_at position flag
  have integer := enum_tag_integer_contract ctx fuel info.tag width number tagChecked
  have canonical : number < (2 : Int) ^ tagBits info.tag := by rw [← integer.1]; exact integer.2.2
  have sound := enum_prefix_sound value info present (history.query_metadata .execution (.Enum id) value queried)
    (history.query_encoding_geometry .execution (.Enum id) value queried) layout.size extent.1 position width number encoding integer.2.1 canonical flag
  exact ⟨layout,info,variants,.int width number,payload,position,variant,fields,
    planShape,valuesShape,selected,row,encoding,flag,found,fieldOrigins,sound⟩

end TrustIr.AggregateMemory

namespace TrustIr.AggregateMemory.DecoderPrefixControls
open SourceLayout

theorem initialized_empty_slice_is_not_a_full_lane : InitializedLane ByteImage.empty 0 1 [] := rfl

theorem empty_image_cannot_contain_byte : ¬ ByteLane ByteImage.empty 0 (ByteImage.ofList [some 7]) := by
  intro lane
  have bound := lane.1
  change 1 ≤ 0 at bound
  omega

private def zero : ByteImage := ByteImage.ofList [some 0]
private def one : ByteImage := ByteImage.ofList [some 1]

private theorem zero_lane : ByteLane zero 0 zero := by
  constructor
  · decide
  · intro index inside; simp only [Nat.zero_add]

theorem overlapping_write_changes_tag :
    ByteLane zero 0 zero ∧ ImageOverwrite zero 0 one one ∧ ¬ ByteLane one 0 zero := by
  refine ⟨zero_lane,rfl,?_⟩
  intro lane
  have wrong := lane.2 0 (by decide)
  have values := congrArg (fun value : Option UInt8 => value.map UInt8.toNat) wrong
  change some 1 = some 0 at values
  cases values

theorem disjoint_write_preserves_actual_tag : ∃ after,
    ImageOverwrite (ByteImage.ofList [some 0,some 2]) 1 one after ∧ ByteLane after 0 zero := by
  let before := ByteImage.ofList [some 0,some 2]
  let after := (before.slice 0 1).append (one.append (before.slice 2 0))
  have run : ImageOverwrite before 1 one after := rfl
  have lane : ByteLane before 0 zero := by
    constructor
    · decide
    · intro index inside
      have same : index = 0 := by change index < 1 at inside; omega
      subst index
      rfl
  exact ⟨after,run,lane.after_write run (Or.inr (by decide))⟩

theorem niche_wraparound_reconstructs_position : (((255 + 1) % 256) + 256 - 255) % 256 = (1 : Nat) := rfl

theorem out_of_range_first_breaks_inverse :
    (((512 + 1) % 256) + 256 - 512) % 256 = (0 : Nat) ∧ (1 : Nat) ≠ 0 := ⟨rfl,by decide⟩

theorem out_of_range_relative_breaks_inverse :
    (((0 + 256) % 256) + 256 - 0) % 256 = (0 : Nat) ∧ (256 : Nat) ≠ 0 := ⟨rfl,by decide⟩

private def info : Enumeration :=
  { tag := .u8, discriminants := [0,1], encoding := .niche 0 1 1 1 0 .u8,
    variants := [[{ ty := .U8, offset := 0, size := 1, align := 1 }],[]], uninhabited := [false,false] }
private def missing : ByteImage := ByteImage.fill 1 none

theorem missing_carrier_can_pass_encoder_guard : NichePayloadChecked info 0 missing := by
  trustIrCompilerProof {
    exact rfl
  } {
    trustIrReduce
  }

theorem missing_carrier_refuses_decoder : ¬ EnumDecodingSelects info missing 0 := by
  intro impossible
  cases impossible

private def summary : Summary := { size := 1, align := some 1, enumeration := some info }

theorem wrong_extent_has_no_origin :
    ¬ Plan.Origin (fun _ _ => True) (fun _ actual => actual = summary) (.Enum ⟨0⟩)
      (.enumeration (.Enum ⟨0⟩) ⟨2,1⟩ info [some [],some []]) := by
  intro origin
  obtain ⟨layout,enumeration,variants,value,shape,actual,present,extent,children⟩ := origin.enum_layout_view
  cases shape
  subst value
  have wrong : 2 = 1 := extent.1
  cases wrong

theorem wrong_alignment_has_no_origin :
    ¬ Plan.Origin (fun _ _ => True) (fun _ actual => actual = summary) (.Enum ⟨0⟩)
      (.enumeration (.Enum ⟨0⟩) ⟨1,2⟩ info [some [],some []]) := by
  intro origin
  obtain ⟨layout,enumeration,variants,value,shape,actual,present,extent,children⟩ := origin.enum_layout_view
  cases shape
  subst value
  have wrong : (some 1 : Option Nat) = some 2 := extent.2
  cases wrong

end TrustIr.AggregateMemory.DecoderPrefixControls
