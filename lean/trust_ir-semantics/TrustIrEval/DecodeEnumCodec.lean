-- Copyright 2026 Andrew Yates | Apache-2.0
import TrustIrEval.DecodeEnumPlan
import TrustIr.Proofs.SourceEnumCodec

namespace TrustIrEval
open TrustIr SourceLayout AggregateMemory

/-- Source-bound wire admission and actual initialized checking agree with
    the actual plan encoder's selection and present active payload. -/
theorem decoded_enum_plan_encoder_selection (document : Lean.Json) (decoded : Module)
    (parsed : module document = .ok decoded) (maxDepth : Nat) (ctx : EvalContext)
    (prepared : contextOf decoded maxDepth = .ok ctx) (admitted : enumAdmission document = .ok true)
    (roots : List Ty) (id : EnumId) (definition : EnumDef) (resolved : ctx.enums id = some definition)
    (plan : Plan)
    (run : (AggregateMemory.prepare (decodedCaptureSource decoded ctx.byteModel) roots).query (.Enum id) = .ok plan)
    (fuel : Nat) (values : List Value) (initialized : (Value.aggregate values).Initialized)
    (checked : checkClosureValueAt ctx (fuel + 1) (.Enum id) (.aggregate values) = .ok ()) :
    ∃ layout info variants tag payload position variant fields,
      plan = .enumeration (.Enum id) layout info variants ∧ values = tag :: payload ∧
      EnumTagSelects definition tag position ∧ definition.variants.get? position = some variant ∧
      EnumEncodingSelects info tag position ∧ info.uninhabited.get? position = some false ∧
      variants.get? position = some (some fields) ∧
      ∀ field ∈ fields, Plan.Origin (SourceElement (decodedCaptureSource decoded ctx.byteModel)) (ActualSummary (decodedCaptureSource decoded ctx.byteModel)) field.2.ty field.2 :=
  prepared_enum_capture_encoding _ ctx
    (decoded_context_capture_source document decoded parsed maxDepth ctx prepared)
    (enumAdmission_decoded_true document decoded parsed admitted) roots id definition resolved plan run
    fuel values initialized checked

end TrustIrEval

/-- info: 'TrustIrEval.decoded_enum_plan_encoder_selection' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIrEval.decoded_enum_plan_encoder_selection
