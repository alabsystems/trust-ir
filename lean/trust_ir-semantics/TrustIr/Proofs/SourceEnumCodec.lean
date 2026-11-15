-- Copyright 2026 Andrew Yates | Apache-2.0
import TrustIr.Proofs.SourceEnumTag
import TrustIr.Proofs.SourceEnumPlan

namespace TrustIr.AggregateMemory
open SourceLayout

private theorem signed_residue_roundtrip (half modulus value : Int) (positive : 0 < half)
    (twice : modulus = 2 * half) (lower : -half ≤ value) (upper : value < half) :
    (if (value % modulus) % modulus ≥ half then (value % modulus) % modulus - modulus
      else (value % modulus) % modulus) = value := by
  trustIrCompilerProof {
    rw [Int.emod_emod]
    by_cases nonnegative : 0 ≤ value
    · have small : value < modulus := by omega
      rw [Int.emod_eq_of_lt nonnegative small]
      simp only [show ¬ value ≥ half from by omega,ite_false]
    · have low : 0 ≤ value + modulus := by omega
      have high : value + modulus < modulus := by omega
      have residue : value % modulus = value + modulus := by
        have same := Int.emod_eq_of_lt low high
        simpa only [Int.add_emod_self] using same
      rw [residue]
      simp only [show value + modulus ≥ half from by omega,ite_true]
      omega
  } {
    rw [Int.emod_emod]
    by_cases nonnegative : 0 ≤ value
    · have small : value < modulus := by omega
      rw [Int.emod_eq_of_lt nonnegative small]
      simp only [show ¬ value ≥ half from by omega,ite_false]
    · have low : 0 ≤ value + modulus := by omega
      have high : value + modulus < modulus := by omega
      have residue : value % modulus = value + modulus := by
        have same := Int.emod_eq_of_lt low high
        simpa only [Int.add_emod_right] using same
      rw [residue]
      simp only [show value + modulus ≥ half from by omega,ite_true]
      omega
  }

/-- Fitting source discriminants round-trip through the encoder's actual
    signed/unsigned normalization, including explicit 128-bit tags. -/
theorem enumTagValue_fitted (tag : EnumTagRepr) (value : Int) (fits : tagFits tag value = true) :
    enumTagValue tag (value % ((2 : Int) ^ tagBits tag)) = value := by
  unfold enumTagValue
  cases signed : tagSigned tag with
  | false =>
    have bounds : 0 ≤ value ∧ value < (2 : Int) ^ tagBits tag := by
      cases tag <;> simp [tagSigned,tagFits,tagBits] at * <;> omega
    simp only [signed,Bool.false_eq_true,ite_false,truncateUnsigned,Int.emod_emod]
    exact Int.emod_eq_of_lt bounds.1 bounds.2
  | true =>
    have bounds : -((2 : Int) ^ (tagBits tag - 1)) ≤ value ∧ value < (2 : Int) ^ (tagBits tag - 1) := by
      simpa only [tagFits,signed,ite_true,Bool.and_eq_true,decide_eq_true_eq] using fits
    have positive : 0 < (2 : Int) ^ (tagBits tag - 1) := by
      cases tag <;> decide
    have twice : (2 : Int) ^ tagBits tag = 2 * ((2 : Int) ^ (tagBits tag - 1)) := by
      cases tag <;> decide
    simp only [signed,ite_true,toSigned]
    exact signed_residue_roundtrip _ _ value positive twice bounds.1 bounds.2

/-- Integer normalization preserves the original residue. -/
theorem enumTagValue_residue (tag : EnumTagRepr) (raw : Int) :
    enumTagValue tag raw % ((2 : Int) ^ tagBits tag) = raw % ((2 : Int) ^ tagBits tag) := by
  unfold enumTagValue
  split
  · unfold toSigned
    dsimp only
    split <;> simp [Int.sub_emod]
  · simp [truncateUnsigned]

private theorem fitted_residue_eq (tag : EnumTagRepr) (value raw : Int) (fits : tagFits tag value = true)
    (canonical : raw % ((2 : Int) ^ tagBits tag) = raw) :
    value % ((2 : Int) ^ tagBits tag) = raw ↔ value = enumTagValue tag raw := by
  constructor
  · intro same
    rw [← same,enumTagValue_fitted tag value fits]
  · intro same
    rw [same,enumTagValue_residue,canonical]

/-- First-match lookup commutes with residue normalization on the complete
    fitting discriminant table, so order and duplicate precedence are retained. -/
theorem discriminantIndex_residue (tag : EnumTagRepr) (values : List Int) (raw : Int)
    (fits : values.all (tagFits tag) = true) (canonical : raw % ((2 : Int) ^ tagBits tag) = raw) :
    discriminantIndex (values.map (fun value => value % ((2 : Int) ^ tagBits tag))) raw =
      discriminantIndex values (enumTagValue tag raw) := by
  induction values with
  | nil => rfl
  | cons first rest ih =>
    have firstFits := List.all_eq_true.mp fits first (.head _)
    have restFits : rest.all (tagFits tag) = true := by
      apply List.all_eq_true.mpr
      intro value member
      exact List.all_eq_true.mp fits value (.tail _ member)
    have same : ((first % ((2 : Int) ^ tagBits tag)) == raw) = (first == enumTagValue tag raw) := by
      apply Bool.eq_iff_iff.mpr
      simp only [beq_iff_eq]
      exact fitted_residue_eq tag first raw firstFits canonical
    simp only [List.map_cons,discriminantIndex,same]
    split
    · rfl
    · rw [ih restFits]

private theorem list_index_offset (values : List Int) (number : Int) (start : Nat) :
    listIndexOf?.go number values start = (discriminantIndex values number).map (fun position => start + position) := by
  induction values generalizing start with
  | nil => rfl
  | cons first rest ih =>
    simp only [listIndexOf?.go,discriminantIndex]
    split
    · simp
    · rw [ih]
      cases found : discriminantIndex rest number <;> simp [found,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]

/-- The shared real codec lookup is the checker's first-match lookup. -/
theorem discriminantIndex_eval (values : List Int) (number : Int) :
    discriminantIndex values number = listIndexOf? values number := by
  unfold listIndexOf?
  rw [list_index_offset]
  cases discriminantIndex values number <;> simp

theorem enum_checked_tag_contract (ctx : EvalContext) (fuel : Nat) (id : EnumId) (definition : EnumDef)
    (resolved : ctx.enums id = some definition) (values : List Value)
    (checked : checkClosureValueAt ctx (fuel + 1) (.Enum id) (.aggregate values) = .ok ()) :
    ∃ width number payload position variant repr,
      values = Value.int width number :: payload ∧ EnumTagSelects definition (.int width number) position ∧
      (trustIrListGet? definition.variants position) = some variant ∧ enumCanonicalTagRepr definition = some repr ∧
      checkClosureValueAt ctx fuel repr.ty (.int width number) = .ok () := by
  trustIrCompilerProof {
    rw [checkClosureValueAt.eq_2] at checked
    simp only [Value.isPoison, Value.isUninit, Bool.false_or, Bool.false_eq_true, ite_false,
      resolved, Except.bind, Except.pure, Bind.bind, Pure.pure] at checked
    split at checked
    · rename_i discs discsEq
      split at checked
      · rename_i repr reprEq
        cases values with
        | nil => cases checked
        | cons tag payload =>
          dsimp only at checked
          split at checked
          · cases checked
          · rename_i unit tagChecked
            cases unit
            cases tag with
            | int width number =>
              dsimp only at checked
              split at checked
              · rename_i position selected
                split at checked
                · rename_i variant found
                  by_cases same : variant.fields.length = payload.length
                  · exact ⟨width,number,payload,position,variant,repr,rfl,
                      ⟨discs,repr,width,number,rfl,discsEq,reprEq,selected⟩,found,reprEq,tagChecked⟩
                  · have different : (variant.fields.length != payload.length) = true := by simp [same]
                    simp [different] at checked
                · cases checked
              · cases checked
            | _ => cases checked
      · cases checked
    · cases checked
  } {
    rw [checkClosureValueAt] at checked
    simp only [Value.isPoison, Value.isUninit, Bool.false_or, Bool.false_eq_true, ite_false,
      resolved, Except.bind, Except.pure, Bind.bind, Pure.pure] at checked
    split at checked
    · rename_i discs discsEq
      split at checked
      · rename_i repr reprEq
        cases values with
        | nil => cases checked
        | cons tag payload =>
          dsimp only at checked
          split at checked
          · cases checked
          · rename_i unit tagChecked
            cases unit
            cases tag with
            | int width number =>
              dsimp only at checked
              split at checked
              · rename_i position selected
                split at checked
                · rename_i variant found
                  by_cases same : variant.fields.length = payload.length
                  · exact ⟨width,number,payload,position,variant,repr,rfl,
                      ⟨discs,repr,width,number,rfl,discsEq,reprEq,selected⟩,found,reprEq,tagChecked⟩
                  · have different : (variant.fields.length != payload.length) = true := by simp [same]
                    simp [different] at checked
                · cases checked
              · cases checked
            | _ => cases checked
      · cases checked
    · cases checked
  }

theorem enum_tag_integer_contract (ctx : EvalContext) (fuel : Nat) (tag : EnumTagRepr)
    (width : Nat) (number : Int) (checked : checkClosureValueAt ctx fuel tag.ty (.int width number) = .ok ()) :
    width = tagBits tag ∧ 0 ≤ number ∧ number < (2 : Int) ^ width := by
  cases fuel with
  | zero => cases checked
  | succ fuel =>
    cases model : ctx.byteModel <;> cases tag <;> simp [model,checkClosureValueAt,EnumTagRepr.ty,Ty.isInteger,Ty.bitWidthFor,Ty.bitWidth,Ty.bitWidthAtModel,Ty.bitWidthAtPointerBits,ByteModel.pointerBits,beq_iff_eq,
      Value.isPoison,Value.isUninit,tagBits] at checked ⊢
    all_goals split at checked <;> simp_all [Pure.pure,Except.pure]
    all_goals split at checked <;> simp_all [Pure.pure,Except.pure]

/-- The actual encoder chooses the checker's exact position when the real
    source metadata, checked integer tag and live flag are all retained. -/
theorem enum_encoding_of_checked_selection {index : Index} {facts : NatIndexTree Unit} {definition : EnumDef}
    {value : Summary} (origin : EnumOrigin index facts .execution definition value)
    (info : Enumeration) (present : value.enumeration = some info) (ctx : EvalContext) (fuel : Nat)
    (tag : Value) (position : Nat) (selected : EnumTagSelects definition tag position)
    (checked : checkClosureValueAt ctx fuel info.tag.ty tag = .ok ())
    (live : (trustIrListGet? info.uninhabited position) = some false) : EnumEncodingSelects info tag position := by
  obtain ⟨discs,repr,width,number,shape,numbered,tagged,selection⟩ := selected
  have data := origin.tag_data info present
  have actualTag := data.1
  rw [canonicalTag_eval] at actualTag
  have sameTag := Option.some.inj (tagged.symm.trans actualTag)
  have actualDiscs := data.2
  rw [discriminants_eval] at actualDiscs
  have sameDiscs := Option.some.inj (numbered.symm.trans actualDiscs)
  subst repr
  subst discs
  rw [shape] at checked ⊢
  have contract := enum_tag_integer_contract ctx fuel info.tag width number checked
  have canonical : number % ((2 : Int) ^ tagBits info.tag) = number := by
    rw [← contract.1]
    exact Int.emod_eq_of_lt contract.2.1 contract.2.2
  have fits := canonicalTag_fits definition info.tag info.discriminants data.1 data.2
  have found : discriminantIndex info.discriminants (enumTagValue info.tag number) = some position := by
    rw [← discriminantIndex_residue info.tag info.discriminants number fits canonical,discriminantIndex_eval]
    simpa only [tagBits_eval] using selection
  exact EnumEncodingSelects.of_lookup info width number position contract.1 found live

/-- The actual memory-plan encoder selects the accepted initialized capture's
    active position and that position has a present payload plan. This proves
    selection authority, not success of every child codec or final store. -/
theorem prepared_enum_capture_encoding (source : Environment) (ctx : EvalContext)
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
      ∀ field ∈ fields, Plan.Origin (SourceElement source) (ActualSummary source) field.2.ty field.2 := by
  obtain ⟨layout,info,variants,value,planShape,actual,present,children⟩ := prepared_enum_plan_view source roots id plan run
  obtain ⟨before,next,history,queried⟩ := actual
  obtain ⟨sourcePosition,actualDefinition,sourceRow,identity,origin⟩ := history.query_enum_origin .execution id value queried
  have member := numbered_source_member source.enums actualDefinition sourcePosition
    ((numbered_member_iff_get _ _ _).2 sourceRow)
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
  exact ⟨layout,info,variants,.int width number,payload,position,variant,fields,
    planShape,valuesShape,selected,row,encoding,flag,found,fieldOrigins⟩

end TrustIr.AggregateMemory

namespace TrustIr.AggregateMemory.CodecSelectionControls
open SourceLayout

-- Elaboration depth for closed 128-bit arithmetic controls, not model fuel.
set_option maxRecDepth 10000

private def definition : EnumDef :=
  { id := ⟨0⟩, name := "TwoUnits", variants := [{ name := "A", fields := [] }, { name := "B", fields := [] }] }
private def info : Enumeration :=
  { tag := .u8, discriminants := [0,1], encoding := .direct 0, variants := [[],[]], uninhabited := [false,false] }

theorem wrong_width_has_selector_witness : EnumTagSelects definition (.int 16 1) 1 :=
  ⟨[0,1],.u8,16,1,rfl,rfl,rfl,rfl⟩

theorem wrong_width_refuses_encoding : ¬ EnumEncodingSelects info (.int 16 1) 1 := by
  intro impossible
  cases impossible

theorem wrong_width_refuses_checker (ctx : EvalContext) (fuel : Nat) :
    checkClosureValueAt ctx fuel .U8 (.int 16 1) ≠ .ok () := by
  intro checked
  have wrong := (enum_tag_integer_contract ctx fuel .u8 16 1 checked).1
  cases wrong

theorem encoder_alone_accepts_oversized_raw : EnumEncodingSelects info (.int 8 257) 1 := rfl

theorem oversized_raw_refuses_checker (ctx : EvalContext) (fuel : Nat) :
    checkClosureValueAt ctx fuel .U8 (.int 8 257) ≠ .ok () := by
  intro checked
  have bounds := (enum_tag_integer_contract ctx fuel .u8 8 257 checked).2
  omega

theorem oversized_raw_has_no_selector (position : Nat) : ¬ EnumTagSelects definition (.int 8 257) position := by
  intro selected
  obtain ⟨discs,repr,width,number,shape,numbered,tagged,selection⟩ := selected
  change some [0,1] = some discs at numbered
  cases numbered
  change some .u8 = some repr at tagged
  cases tagged
  cases shape
  change (none : Option Nat) = some position at selection
  cases selection

theorem signed_residue_reads_negative : enumTagValue .i8 255 = -1 := rfl

theorem unsigned_residue_stays_positive : enumTagValue .u8 255 = 255 := rfl

theorem signed_128_residue_reads_negative : enumTagValue .i128 ((2 : Int) ^ 128 - 1) = -1 := rfl

theorem nonfitting_table_breaks_residue_lookup :
    discriminantIndex ([255,-1].map (fun value : Int => value % 256)) 255 = some 0 ∧
    discriminantIndex [255,-1] (enumTagValue .i8 255) = some 1 ∧
    [255,-1].all (tagFits .i8) = false := ⟨rfl,rfl,rfl⟩

private def wrongInfo : Enumeration := { info with tag := .u16 }
private def wrongSummary : Summary := { size := 2, align := some 2, enumeration := some wrongInfo }
private def source : Environment := { enums := [definition] }

theorem wrong_tag_has_no_source_origin :
    ¬ EnumOrigin (Index.ofEnvironment source) (uninhabitedFacts (Index.ofEnvironment source)) .execution definition wrongSummary := by
  intro origin
  have actual := (origin.tag_data wrongInfo rfl).1
  change some EnumTagRepr.u8 = some EnumTagRepr.u16 at actual
  cases actual

end TrustIr.AggregateMemory.CodecSelectionControls
