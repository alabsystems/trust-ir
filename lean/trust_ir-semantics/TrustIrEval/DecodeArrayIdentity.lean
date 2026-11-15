-- Copyright 2026 Andrew Yates | Apache-2.0
import TrustIrEval.DecodeEnumCodec
import TrustIr.Proofs.SourceArrayIdentity

namespace TrustIrEval
open TrustIr SourceLayout AggregateMemory

/-- Actual decoded contexts retain source association and the source array's
logical count through checked planning and successful compact encoding. -/
theorem decoded_array_plan_encoded_census (document : Lean.Json) (decoded : Module)
    (parsed : module document = .ok decoded) (maxDepth : Nat) (ctx : EvalContext)
    (prepared : contextOf decoded maxDepth = .ok ctx) (roots : List Ty)
    (id : TyId) (sourceCount : Nat) (planTy : Ty) (layout : MemoryTypeLayout)
    (count : Nat) (element : Plan)
    (planned : (AggregateMemory.prepare (decodedCaptureSource decoded ctx.byteModel) roots).query
      (.Array id sourceCount) = .ok (.array planTy layout count element))
    (model : ByteModel) (order : FunctionAddressOrder) (value : Value) (image : Image)
    (encoded : encode model order (.array planTy layout count element) value false = .ok image) :
    CaptureSource (decodedCaptureSource decoded ctx.byteModel) ctx ∧
    ∃ values, value = .array values ∧ values.size = sourceCount ∧
      ArrayImageEncoded (fun child => do
        pure (← encode model order element child false).bytes) values.tree image.bytes :=
  ⟨decoded_context_capture_source document decoded parsed maxDepth ctx prepared,
   prepared_array_encoded_census _ roots id sourceCount planTy layout count element planned
     model order value image encoded⟩

/-- Actual decoder/context resolution and checked source planning agree on
an array element's exact type and its typed child-layout query. -/
theorem decoded_array_plan_element (document : Lean.Json) (decoded : Module)
    (parsed : module document = .ok decoded) (maxDepth : Nat) (ctx : EvalContext)
    (prepared : contextOf decoded maxDepth = .ok ctx) (roots : List Ty)
    (id : TyId) (sourceCount : Nat) (expected : Ty) (resolved : ctx.types id = some expected)
    (planTy : Ty) (layout : MemoryTypeLayout) (count : Nat) (element : Plan)
    (planned : (AggregateMemory.prepare (decodedCaptureSource decoded ctx.byteModel) roots).query
      (.Array id sourceCount) = .ok (.array planTy layout count element)) :
    element.ty = expected ∧
      ∃ value, ActualSummary (decodedCaptureSource decoded ctx.byteModel) expected value ∧
        element.layout.size = value.size ∧ value.align = some element.layout.alignment := by
  have associated := decoded_context_capture_source document decoded parsed maxDepth ctx prepared
  have typed := prepared_array_context_element _ ctx associated roots id sourceCount expected resolved
    planTy layout count element planned
  obtain ⟨_,value,actual,size,align⟩ := prepared_array_element_query _ roots id sourceCount planTy layout count element planned
  exact ⟨typed,value,typed ▸ actual,size,align⟩

end TrustIrEval

/-- info: 'TrustIrEval.decoded_array_plan_encoded_census' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIrEval.decoded_array_plan_encoded_census

/-- info: 'TrustIrEval.decoded_array_plan_element' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIrEval.decoded_array_plan_element
