-- Copyright 2026 Andrew Yates | Apache-2.0
import TrustIrEval.DecodeEnumCodec
import TrustIr.Proofs.SourceFieldSteps

namespace TrustIrEval
open TrustIr SourceLayout AggregateMemory

/-- Actual decoded captures retain final-image selection from static nested carrier coverage and actual encoding. -/
theorem decoded_enum_plan_covered_encoded_selection (document : Lean.Json) (decoded : Module)
    (parsed : module document = .ok decoded) (maxDepth : Nat) (ctx : EvalContext)
    (prepared : contextOf decoded maxDepth = .ok ctx) (admitted : enumAdmission document = .ok true)
    (roots : List Ty) (id : EnumId) (definition : EnumDef) (resolved : ctx.enums id = some definition)
    (plan : Plan)
    (run : (AggregateMemory.prepare (decodedCaptureSource decoded ctx.byteModel) roots).query (.Enum id) = .ok plan)
    (fuel : Nat) (values : List Value) (initialized : (Value.aggregate values).Initialized)
    (checked : checkClosureValueAt ctx (fuel + 1) (.Enum id) (.aggregate values) = .ok ()) :
    ∃ layout info variants tag payload position variant fields,
      plan = .enumeration (.Enum id) layout info variants ∧ values = tag :: payload ∧
      EnumTagSelects definition tag position ∧ (trustIrListGet? definition.variants position) = some variant ∧
      EnumEncodingSelects info tag position ∧ (trustIrListGet? info.uninhabited position) = some false ∧
      (trustIrListGet? variants position) = some (some fields) ∧
      (∀ field ∈ fields, Plan.Origin (SourceElement (decodedCaptureSource decoded ctx.byteModel)) (ActualSummary (decodedCaptureSource decoded ctx.byteModel)) field.2.ty field.2) ∧
      ∀ model order allowUnwritten image,
        encode model order plan (.aggregate values) allowUnwritten = .ok image →
        (∃ fieldPosition base child offset untagged start stop first repr,
          info.encoding = .niche untagged start stop first (base + offset) repr ∧
          (trustIrListGet? fields fieldPosition) = some (base,child) ∧
          child.CoversLane offset (tagBits repr / 8) ∧
          FieldsAvoidLane (fields.drop (fieldPosition + 1)) (base + offset) (tagBits repr / 8)) →
        image.bytes.size = layout.size ∧ EnumDecodingSelects info image.bytes position :=
  prepared_enum_capture_covered_encoded_selection _ ctx
    (decoded_context_capture_source document decoded parsed maxDepth ctx prepared)
    (enumAdmission_decoded_true document decoded parsed admitted) roots id definition resolved plan run
    fuel values initialized checked

end TrustIrEval

/- Historical legacy printer record, preserved verbatim:
/-- info: 'TrustIrEval.decoded_enum_plan_covered_encoded_selection' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIrEval.decoded_enum_plan_covered_encoded_selection
-/
#print axioms TrustIrEval.decoded_enum_plan_covered_encoded_selection
#trustIrAxiomsPinned TrustIrEval.decoded_enum_plan_covered_encoded_selection == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]
