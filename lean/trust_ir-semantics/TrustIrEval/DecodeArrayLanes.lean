-- Copyright 2026 Andrew Yates | Apache-2.0
import TrustIrEval.DecodePlanKinds

namespace TrustIrEval
open TrustIr SourceLayout AggregateMemory

/-- Actual decoded planning and ordinary encoding retain readable bytes along
certified mixed field/array paths. Array steps certify both a logical slot and
physical bounds; padding outside the final lane is not declared initialized. -/
theorem decoded_plan_covered_array_bytes (document : Lean.Json) (decoded : Module)
    (parsed : module document = .ok decoded) (maxDepth : Nat) (ctx : EvalContext)
    (prepared : contextOf decoded maxDepth = .ok ctx) (roots : List Ty) (ty : Ty) (plan : Plan)
    (planned : (AggregateMemory.prepare (decodedCaptureSource decoded ctx.byteModel) roots).query ty = .ok plan)
    (offset count : Nat) (covered : plan.CoversLane offset count)
    (order : FunctionAddressOrder) (value : Value) (image : Image)
    (encoded : encode ctx.byteModel order plan value false = .ok image) :
    CaptureSource (decodedCaptureSource decoded ctx.byteModel) ctx ∧ Plan.SourceShape ty plan ∧
      ∃ bytes : List UInt8, bytes.length = count ∧ InitializedLane image.bytes offset count bytes :=
  ⟨decoded_context_capture_source document decoded parsed maxDepth ctx prepared,
   prepared_plan_source_shape _ roots ty plan planned,
   covered.initialized ctx.byteModel order value image encoded⟩

end TrustIrEval

/-- info: 'TrustIrEval.decoded_plan_covered_array_bytes' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIrEval.decoded_plan_covered_array_bytes
