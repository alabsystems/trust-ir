-- Copyright 2026 Andrew Yates | Apache-2.0
import TrustIrEval.DecodeEnumOmission
import TrustIr.Proofs.SourceEnumGraph

namespace TrustIrEval
open TrustIr SourceLayout

/-- A real source-session query preserves the initialized active capture in
    the actual returned flag table, after source-bound wire admission. -/
theorem decoded_session_enum_capture_flag_false (document : Lean.Json) (decoded : Module)
    (parsed : module document = .ok decoded) (maxDepth : Nat) (ctx : EvalContext)
    (prepared : contextOf decoded maxDepth = .ok ctx) (admitted : enumAdmission document = .ok true)
    (session next : Session) (history : Session.Reachable (decodedCaptureSource decoded ctx.byteModel) session)
    (mode : Mode) (id : EnumId) (definition : EnumDef) (resolved : ctx.enums id = some definition)
    (value : Summary) (enumeration : Enumeration) (present : value.enumeration = some enumeration)
    (run : session.query mode (.Enum id) = .ok (value, next)) (fuel : Nat) (values : List Value)
    (initialized : (Value.aggregate values).Initialized)
    (checked : checkClosureValueAt ctx (fuel + 1) (.Enum id) (.aggregate values) = .ok ()) :
    ∃ tag payload position variant, values = tag :: payload ∧ EnumTagSelects definition tag position ∧
      (trustIrListGet? definition.variants position) = some variant ∧ (trustIrListGet? enumeration.uninhabited position) = some false :=
  history.query_enum_capture_active_flag_false ctx
    (decoded_context_capture_source document decoded parsed maxDepth ctx prepared)
    (enumAdmission_decoded_true document decoded parsed admitted) mode id definition resolved value enumeration
    present run fuel values initialized checked

theorem decoded_query_enum_capture_flag_false (document : Lean.Json) (decoded : Module)
    (parsed : module document = .ok decoded) (maxDepth : Nat) (ctx : EvalContext)
    (prepared : contextOf decoded maxDepth = .ok ctx) (admitted : enumAdmission document = .ok true)
    (mode : Mode) (id : EnumId) (definition : EnumDef) (resolved : ctx.enums id = some definition)
    (value : Summary) (enumeration : Enumeration) (present : value.enumeration = some enumeration)
    (run : query (decodedCaptureSource decoded ctx.byteModel) mode (.Enum id) = .ok value)
    (fuel : Nat) (values : List Value) (initialized : (Value.aggregate values).Initialized)
    (checked : checkClosureValueAt ctx (fuel + 1) (.Enum id) (.aggregate values) = .ok ()) :
    ∃ tag payload position variant, values = tag :: payload ∧ EnumTagSelects definition tag position ∧
      (trustIrListGet? definition.variants position) = some variant ∧ (trustIrListGet? enumeration.uninhabited position) = some false :=
  query_enum_capture_active_flag_false _ ctx
    (decoded_context_capture_source document decoded parsed maxDepth ctx prepared)
    (enumAdmission_decoded_true document decoded parsed admitted) mode id definition resolved value enumeration
    present run fuel values initialized checked

end TrustIrEval

/- Historical legacy printer record, preserved verbatim:
/-- info: 'TrustIrEval.decoded_session_enum_capture_flag_false' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIrEval.decoded_session_enum_capture_flag_false
-/
#print axioms TrustIrEval.decoded_session_enum_capture_flag_false
#trustIrAxiomsPinned TrustIrEval.decoded_session_enum_capture_flag_false == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

/- Historical legacy printer record, preserved verbatim:
/-- info: 'TrustIrEval.decoded_query_enum_capture_flag_false' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIrEval.decoded_query_enum_capture_flag_false
-/
#print axioms TrustIrEval.decoded_query_enum_capture_flag_false
#trustIrAxiomsPinned TrustIrEval.decoded_query_enum_capture_flag_false == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]
