-- Copyright 2026 Andrew Yates | Apache-2.0
import TrustIr.Proofs.SourceRecursiveReadbackFixtureData

/- Enable kernel reduction through the imported mutual compiler equations.
The metadata is local to these proofs; no executable definition is replaced. -/
run_cmd do
  if Lean.versionString == "4.30.0-rc2" then
    let env ← Lean.getEnv
    let mut registered := 0
    for (n, _) in env.constants.map₁.toList do
      if n.toString.endsWith "TrustIr.SourceLayout.compileTy.eq_def" ||
         n.toString.endsWith "TrustIr.SourceLayout.compileTypes.eq_def" then
        Lean.Elab.Command.elabCommand (← `(command| attribute [local cbv_eval] $(Lean.mkIdent n):ident))
        registered := registered + 1
    unless registered == 2 do
      Lean.throwError "expected the two original layout compiler equations"
  else if Lean.versionString != "4.8.0" then
    Lean.throwError "unsupported compiler for layout equation reduction"

namespace TrustIr.AggregateMemory.RecursiveReadbackControls
open SourceLayout
open FixtureData
set_option maxHeartbeats 4000000
set_option maxRecDepth 4096







private def charSource : Environment := { types := [] }
private def charInput : Value := .int 32 128512
private def charStored : Image :=
  { bytes := ByteImage.ofList ((encodeIntBytes (truncateUnsigned 128512 32) 4).map some) }
private theorem charAdmitted : ReadbackInput .le64 none memory character charInput :=
  .scalar (.integer .Char ⟨4,4⟩ 32 128512 rfl rfl rfl)
private theorem charReady : TopCharReady character charInput := by
  intro layout width raw shape inputShape
  cases shape
  cases inputShape
  decide

theorem valid_top_character_readback :
    ∃ output, decode .le64 none memory character charStored.bytes = .ok output ∧ ValueReadback .le64 memory charInput output := by
  trustIrCompilerProof {
    exact prepared_recursive_readback charSource [] .Char character rfl .le64 none memory charInput charAdmitted charReady charStored rfl
  } {
    exact prepared_recursive_readback charSource [] .Char character (by trustIrReduce) .le64 none memory charInput charAdmitted charReady charStored (by trustIrReduce)
  }

theorem invalid_top_character_has_no_ready_certificate : ¬ TopCharReady character (.int 32 55296) := by
  intro ready
  have invalid : ¬ validChar (truncateUnsigned 55296 32).toNat := by decide
  exact invalid (ready ⟨4,4⟩ 32 55296 rfl rfl)

theorem invalid_top_character_still_refuses :
    decode .le64 none memory character (ByteImage.ofList [some 0,some 216,some 0,some 0]) =
      .error (.ub "memory decode: invalid Unicode scalar value") := by
  trustIrCompilerProof {
    exact rfl
  } {
    exact by trustIrReduce
  }

theorem float_is_not_implicitly_admitted (value : Float) : ¬ ScalarReadbackInput .le64 (.leaf .F64 ⟨8,8⟩) (.float value) := by
  intro admitted
  cases admitted

theorem unwritten_is_not_implicitly_admitted : ¬ ReadbackInput .le64 none memory byte .uninit := by
  intro admitted
  cases admitted with
  | scalar scalar => cases scalar
  | function function => cases function

theorem target32_overflow_has_no_scalar_certificate :
    ¬ ScalarReadbackInput .le32 (.leaf .Ptr ⟨4,4⟩) (.ptr 4294967296 none) := by
  intro admitted
  cases admitted with
  | pointer ty layout address provenance pointer bound extent =>
    have impossible : ¬ 4294967296 < ByteModel.le32.addressLimit := by decide
    exact impossible bound

private def badInfo : Enumeration :=
  { tag := .u8, discriminants := [10,20], encoding := .niche 0 1 1 1 0 .u8, variants := [[],[]], uninhabited := [false,false] }
private def badVariants : List (Option (List (Nat × Plan))) := [some [],some []]
private def badPlan : Plan := .enumeration (.Enum ⟨0⟩) ⟨1,1⟩ badInfo badVariants

theorem uninitialized_carrier_has_no_selection_certificate :
    ¬ (∀ image, encode .le64 none badPlan (.aggregate [.int 8 10]) false = .ok image → EnumDecodingSelects badInfo image.bytes 0) := by
  trustIrCompilerProof {
    intro certificate
    have selected := certificate { bytes := ByteImage.fill 1 none } rfl
    cases selected
  } {
    intro certificate
    have selected := certificate { bytes := ByteImage.fill 1 none } (by trustIrReduce)
    cases selected
  }

private def overlappingFields : List (Nat × Plan) := [(0,byte),(0,byte)]
private def overlapping : Plan := .fields (.Tuple [.U8,.U8]) ⟨1,1⟩ overlappingFields

theorem overlapping_plan_has_no_source_origin (environment : Environment) :
    ¬ Plan.Origin (SourceElement environment) (ActualSummary environment) (.Tuple [.U8,.U8]) overlapping := by
  intro origin
  have separated := (origin.fields_child_placement 0 0 byte rfl).2
  have impossible := separated (0,byte) (by change (0,byte) ∈ [(0,byte)]; exact .head [])
  change true = false at impossible
  cases impossible

end TrustIr.AggregateMemory.RecursiveReadbackControls
