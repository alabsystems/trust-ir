-- Copyright 2026 Andrew Yates | Apache-2.0
import TrustIrEval.DecodeEnumAdmission
import TrustIr.Proofs.SourceEnumOmission

namespace TrustIrEval
open TrustIr SourceLayout

/-- Actual wire admission, context construction and indexed compiler selection
    exclude omission of any initialized active capture accepted by the checker. -/
theorem decoded_enum_omission_refuses_initialized (document : Lean.Json) (decoded : Module)
    (parsed : module document = .ok decoded) (maxDepth : Nat) (ctx : EvalContext)
    (prepared : contextOf decoded maxDepth = .ok ctx) (admitted : enumAdmission document = .ok true)
    (id : EnumId) (definition : EnumDef) (resolved : ctx.enums id = some definition)
    (sourcePosition : Nat)
    (indexed : (Index.ofEnvironment (decodedCaptureSource decoded ctx.byteModel)).enumPositions.find id.index = some sourcePosition)
    (layoutDefinition : EnumDef) (row : decoded.enums.get? sourcePosition = some layoutDefinition)
    (tag : Value) (payload : List Value) (position : Nat)
    (tagSelects : EnumTagSelects definition tag position)
    (omitted : (enumPhysicalSelection layoutDefinition (layoutDefinition.variants.map (fun variant =>
      variantUninhabited (Index.ofEnvironment (decodedCaptureSource decoded ctx.byteModel))
        (uninhabitedFacts (Index.ofEnvironment (decodedCaptureSource decoded ctx.byteModel))) variant.fields))).any
      (fun active => position != active) = true)
    (initialized : (Value.aggregate (tag :: payload)).Initialized) (fuel : Nat)
    (checked : checkClosureValueAt ctx (fuel + 1) (.Enum id) (.aggregate (tag :: payload)) = .ok ()) : False :=
  enum_execution_omission_refuses_initialized _ ctx
    (decoded_context_capture_source document decoded parsed maxDepth ctx prepared)
    (enumAdmission_decoded_true document decoded parsed admitted) id definition resolved sourcePosition indexed
    layoutDefinition row tag payload position tagSelects omitted initialized fuel checked

/-- The accepted value retains an authenticated active tag/variant witness at
    which the real compiler's omission condition is false. -/
theorem decoded_enum_active_not_omitted (document : Lean.Json) (decoded : Module)
    (parsed : module document = .ok decoded) (maxDepth : Nat) (ctx : EvalContext)
    (prepared : contextOf decoded maxDepth = .ok ctx) (admitted : enumAdmission document = .ok true)
    (id : EnumId) (definition : EnumDef) (resolved : ctx.enums id = some definition)
    (sourcePosition : Nat)
    (indexed : (Index.ofEnvironment (decodedCaptureSource decoded ctx.byteModel)).enumPositions.find id.index = some sourcePosition)
    (layoutDefinition : EnumDef) (row : decoded.enums.get? sourcePosition = some layoutDefinition)
    (fuel : Nat) (values : List Value) (initialized : (Value.aggregate values).Initialized)
    (checked : checkClosureValueAt ctx (fuel + 1) (.Enum id) (.aggregate values) = .ok ()) :
    ∃ tag payload position variant, values = tag :: payload ∧ EnumTagSelects definition tag position ∧
      definition.variants.get? position = some variant ∧
      (enumPhysicalSelection layoutDefinition (layoutDefinition.variants.map (fun variant =>
        variantUninhabited (Index.ofEnvironment (decodedCaptureSource decoded ctx.byteModel))
          (uninhabitedFacts (Index.ofEnvironment (decodedCaptureSource decoded ctx.byteModel))) variant.fields))).any
        (fun active => position != active) = false :=
  enum_capture_active_not_omitted _ ctx
    (decoded_context_capture_source document decoded parsed maxDepth ctx prepared)
    (enumAdmission_decoded_true document decoded parsed admitted) id definition resolved sourcePosition indexed
    layoutDefinition row fuel values initialized checked

end TrustIrEval

/-- info: 'TrustIrEval.decoded_enum_omission_refuses_initialized' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIrEval.decoded_enum_omission_refuses_initialized

/-- info: 'TrustIrEval.decoded_enum_active_not_omitted' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIrEval.decoded_enum_active_not_omitted
