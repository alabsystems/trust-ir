-- Copyright 2026 Andrew Yates | Apache-2.0
import TrustIrEval.DecodeRecordKeys
import TrustIrEval.EnumAdmission
import TrustIr.Proofs.SourceEnumAdmission

namespace TrustIrEval
open TrustIr SourceLayout

/-- Exact result of the actual wire-facing check for a decoded module. -/
theorem enumAdmission_of_decoded (document : Lean.Json) (decoded : Module)
    (parsed : module document = .ok decoded) :
    enumAdmission document = .ok (enumIdsAdmitted decoded.enums) := by
  simp [enumAdmission, parsed, Except.bind, Except.pure, Bind.bind, Pure.pure]

/-- Successful wire-facing admission retains the actual decoded source. -/
theorem enumAdmission_source (document : Lean.Json) (admitted : enumAdmission document = .ok true) :
    ∃ decoded, module document = .ok decoded ∧ enumIdsAdmitted decoded.enums = true := by
  cases parsed : module document with
  | error error => simp [enumAdmission, parsed, Except.bind, Bind.bind] at admitted
  | ok decoded =>
    exact ⟨decoded, rfl, Except.ok.inj ((enumAdmission_of_decoded document decoded parsed).symm.trans admitted)⟩

theorem enumAdmission_decoded_true (document : Lean.Json) (decoded : Module)
    (parsed : module document = .ok decoded) (admitted : enumAdmission document = .ok true) :
    enumIdsAdmitted decoded.enums = true :=
  Except.ok.inj ((enumAdmission_of_decoded document decoded parsed).symm.trans admitted)

/-- Admission inspects the actual decoded enum rows. Successful original
    decoding/context construction supplies source identity and record keys;
    no producer-supplied validity bit or separate lookup premise is trusted. -/
theorem decoded_enum_lookup_agrees (document : Lean.Json) (decoded : Module)
    (parsed : module document = .ok decoded) (maxDepth : Nat) (ctx : EvalContext)
    (prepared : contextOf decoded maxDepth = .ok ctx)
    (admitted : enumAdmission document = .ok true)
    (id : EnumId) (definition : EnumDef) (resolved : ctx.enums id = some definition) :
    EnumLookupAgrees (decodedCaptureSource decoded ctx.byteModel) id definition :=
  enum_lookup_agrees_of_admission _ ctx
    (decoded_context_capture_source document decoded parsed maxDepth ctx prepared)
    (enumAdmission_decoded_true document decoded parsed admitted) id definition resolved

theorem decoded_enum_execution_position (document : Lean.Json) (decoded : Module)
    (parsed : module document = .ok decoded) (maxDepth : Nat) (ctx : EvalContext)
    (prepared : contextOf decoded maxDepth = .ok ctx)
    (admitted : enumAdmission document = .ok true)
    (id : EnumId) (definition : EnumDef) (resolved : ctx.enums id = some definition)
    (position : Nat)
    (indexed : (Index.ofEnvironment (decodedCaptureSource decoded ctx.byteModel)).enumPositions.find id.index = some position) :
    (trustIrListGet? decoded.enums position) = some definition :=
  enum_execution_position_resolves _ id definition
    (decoded_enum_lookup_agrees document decoded parsed maxDepth ctx prepared admitted id definition resolved)
    position indexed

/-- Wire entry to exact physical-row selection. The finite original-row
    admission result replaces the prior abstract definition-agreement premise. -/
theorem decoded_enum_execution_active (document : Lean.Json) (decoded : Module)
    (parsed : module document = .ok decoded) (maxDepth : Nat) (ctx : EvalContext)
    (prepared : contextOf decoded maxDepth = .ok ctx)
    (admitted : enumAdmission document = .ok true)
    (id : EnumId) (definition : EnumDef) (resolved : ctx.enums id = some definition)
    (position : Nat)
    (indexed : (Index.ofEnvironment (decodedCaptureSource decoded ctx.byteModel)).enumPositions.find id.index = some position)
    (layoutDefinition : EnumDef) (row : (trustIrListGet? decoded.enums position) = some layoutDefinition)
    (descriptor : EnumLayoutDescriptor) (selected : Nat)
    (valid : singleInhabitedValid layoutDefinition descriptor
      (layoutDefinition.variants.map (fun variant => variantUninhabited
        (Index.ofEnvironment (decodedCaptureSource decoded ctx.byteModel))
        (uninhabitedFacts (Index.ofEnvironment (decodedCaptureSource decoded ctx.byteModel))) variant.fields))
      selected = true)
    (fuel : Nat) (values : List Value) (initialized : (Value.aggregate values).Initialized)
    (checked : checkClosureValueAt ctx (fuel + 1) (.Enum id) (.aggregate values) = .ok ()) :
    ∃ tag payload variant, values = tag :: payload ∧ EnumTagSelects definition tag selected ∧
      (trustIrListGet? definition.variants selected) = some variant ∧
      variantUninhabited (Index.ofEnvironment (decodedCaptureSource decoded ctx.byteModel))
        (uninhabitedFacts (Index.ofEnvironment (decodedCaptureSource decoded ctx.byteModel))) variant.fields = false :=
  enum_execution_active_of_admission _ ctx
    (decoded_context_capture_source document decoded parsed maxDepth ctx prepared)
    (enumAdmission_decoded_true document decoded parsed admitted) id definition resolved position indexed layoutDefinition row descriptor selected valid
    fuel values initialized checked

end TrustIrEval

/- Historical legacy printer record, preserved verbatim:
/-- info: 'TrustIrEval.enumAdmission_of_decoded' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIrEval.enumAdmission_of_decoded
-/
#print axioms TrustIrEval.enumAdmission_of_decoded
#trustIrAxiomsByCompiler TrustIrEval.enumAdmission_of_decoded == [propext] modern [propext, Classical.choice, Quot.sound]

/- Historical legacy printer record, preserved verbatim:
/-- info: 'TrustIrEval.enumAdmission_source' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIrEval.enumAdmission_source
-/
#print axioms TrustIrEval.enumAdmission_source
#trustIrAxiomsByCompiler TrustIrEval.enumAdmission_source == [propext] modern [propext, Classical.choice, Quot.sound]

/- Historical legacy printer record, preserved verbatim:
/-- info: 'TrustIrEval.enumAdmission_decoded_true' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIrEval.enumAdmission_decoded_true
-/
#print axioms TrustIrEval.enumAdmission_decoded_true
#trustIrAxiomsByCompiler TrustIrEval.enumAdmission_decoded_true == [propext] modern [propext, Classical.choice, Quot.sound]

/- Historical legacy printer record, preserved verbatim:
/-- info: 'TrustIrEval.decoded_enum_lookup_agrees' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIrEval.decoded_enum_lookup_agrees
-/
#print axioms TrustIrEval.decoded_enum_lookup_agrees
#trustIrAxiomsPinned TrustIrEval.decoded_enum_lookup_agrees == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

/- Historical legacy printer record, preserved verbatim:
/-- info: 'TrustIrEval.decoded_enum_execution_position' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIrEval.decoded_enum_execution_position
-/
#print axioms TrustIrEval.decoded_enum_execution_position
#trustIrAxiomsPinned TrustIrEval.decoded_enum_execution_position == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

/- Historical legacy printer record, preserved verbatim:
/-- info: 'TrustIrEval.decoded_enum_execution_active' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIrEval.decoded_enum_execution_active
-/
#print axioms TrustIrEval.decoded_enum_execution_active
#trustIrAxiomsPinned TrustIrEval.decoded_enum_execution_active == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]
