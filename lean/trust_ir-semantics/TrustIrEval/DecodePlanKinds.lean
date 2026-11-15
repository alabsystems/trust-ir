-- Copyright 2026 Andrew Yates | Apache-2.0
import TrustIrEval.DecodeArrayIdentity
import TrustIr.Proofs.SourcePlanKinds

namespace TrustIrEval
open TrustIr SourceLayout AggregateMemory

/-- Successful checked planning from an actual decoded source preserves exact
source-kind dispatch for every type, including empty aggregates. -/
theorem decoded_plan_source_shape (document : Lean.Json) (decoded : Module)
    (parsed : module document = .ok decoded) (maxDepth : Nat) (ctx : EvalContext)
    (prepared : contextOf decoded maxDepth = .ok ctx) (roots : List Ty) (ty : Ty) (plan : Plan)
    (planned : (AggregateMemory.prepare (decodedCaptureSource decoded ctx.byteModel) roots).query ty = .ok plan) :
    CaptureSource (decodedCaptureSource decoded ctx.byteModel) ctx ∧ Plan.SourceShape ty plan :=
  ⟨decoded_context_capture_source document decoded parsed maxDepth ctx prepared,
   prepared_plan_source_shape _ roots ty plan planned⟩

/-- A decoded array request supplies its own plan shape, exact context-resolved
element type, source count, value shape and actual compact encoding fold. -/
theorem decoded_source_array_encoding (document : Lean.Json) (decoded : Module)
    (parsed : module document = .ok decoded) (maxDepth : Nat) (ctx : EvalContext)
    (prepared : contextOf decoded maxDepth = .ok ctx) (roots : List Ty)
    (id : TyId) (count : Nat) (expected : Ty) (resolved : ctx.types id = some expected)
    (plan : Plan)
    (planned : (AggregateMemory.prepare (decodedCaptureSource decoded ctx.byteModel) roots).query
      (.Array id count) = .ok plan)
    (model : ByteModel) (order : FunctionAddressOrder) (value : Value) (image : Image)
    (encoded : encode model order plan value false = .ok image) :
    ∃ layout element values, plan = .array (.Array id count) layout count element ∧
      element.ty = expected ∧ value = .array values ∧ values.size = count ∧
      ArrayImageEncoded (fun child => do
        pure (← encode model order element child false).bytes) values.tree image.bytes := by
  have associated := decoded_context_capture_source document decoded parsed maxDepth ctx prepared
  obtain ⟨layout,element,values,shape,_,valueShape,census,fold⟩ :=
    prepared_source_array_encoding _ roots id count plan planned model order value image encoded
  have typed := prepared_array_context_element _ ctx associated roots id count expected resolved
    (.Array id count) layout count element (by simpa only [shape] using planned)
  exact ⟨layout,element,values,shape,typed,valueShape,census,fold⟩

end TrustIrEval

/-- info: 'TrustIrEval.decoded_plan_source_shape' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIrEval.decoded_plan_source_shape

/-- info: 'TrustIrEval.decoded_source_array_encoding' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIrEval.decoded_source_array_encoding
