-- Copyright 2026 Andrew Yates | Apache-2.0
import TrustIrEval.DecodeEnumImage
import TrustIr.Proofs.SourceFieldBindings

namespace TrustIrEval
open TrustIr SourceLayout AggregateMemory

/-- Actual decoded contexts retain their source association and each compiled
    field's exact type/offset and actual typed child-query extent. -/
theorem decoded_enum_field_queries (document : Lean.Json) (decoded : Module)
    (parsed : module document = .ok decoded) (maxDepth : Nat) (ctx : EvalContext)
    (prepared : contextOf decoded maxDepth = .ok ctx) (roots : List Ty) (id : EnumId)
    (plan : Plan)
    (run : (AggregateMemory.prepare (decodedCaptureSource decoded ctx.byteModel) roots).query (.Enum id) = .ok plan) :
    CaptureSource (decodedCaptureSource decoded ctx.byteModel) ctx ∧
    ∃ layout info variants value,
      plan = .enumeration (.Enum id) layout info variants ∧
      ActualSummary (decodedCaptureSource decoded ctx.byteModel) (.Enum id) value ∧ value.enumeration = some info ∧
      (layout.size = value.size ∧ value.align = some layout.alignment) ∧
      ∀ position fields, (trustIrListGet? variants position) = some (some fields) →
        ∃ sourceFields, (trustIrListGet? info.variants position) = some sourceFields ∧
          FieldBindings (sourceFields.map (·.ty)) (sourceFields.map (·.offset)) fields ∧
          ∀ fieldPosition offset child, (trustIrListGet? fields fieldPosition) = some (offset,child) →
            ∃ sourceField childValue, (trustIrListGet? sourceFields fieldPosition) = some sourceField ∧
              child.ty = sourceField.ty ∧ offset = sourceField.offset ∧
              ActualSummary (decodedCaptureSource decoded ctx.byteModel) sourceField.ty childValue ∧
              child.layout.size = childValue.size ∧ childValue.align = some child.layout.alignment :=
  ⟨decoded_context_capture_source document decoded parsed maxDepth ctx prepared,
   prepared_enum_field_queries _ roots id plan run⟩

end TrustIrEval

/- Historical legacy printer record, preserved verbatim:
/-- info: 'TrustIrEval.decoded_enum_field_queries' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIrEval.decoded_enum_field_queries
-/
#print axioms TrustIrEval.decoded_enum_field_queries
#trustIrAxiomsPinned TrustIrEval.decoded_enum_field_queries == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]
