-- Copyright 2026 Andrew Yates | Apache-2.0
import TrustIr.Proofs.SourceRecursiveReadbackFixtureData
import TrustIr.Proofs.SourceRecursiveReadbackMixed
import TrustIr.Proofs.SourceRecursiveReadbackEnumerationPreparation

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

























private theorem except_success_projection {ε : Type _} {α : Type _}
    (result : Except ε α) (fallback : α) (success : ∃ value, result = .ok value) :
    result = .ok (match result with | .ok value => value | .error _ => fallback) := by
  obtain ⟨value, run⟩ := success
  cases run
  rfl
/-- Unconditional equality with the original actual-result/fallback projection.
The encoder result remains symbolic; neither branch is evaluated concretely. -/
private theorem except_value_projection_eq {ε : Type _} {α : Type _}
    (result : Except ε α) (fallback : α) :
    result.toOption.getD fallback =
      (match result with | .ok value => value | .error _ => fallback) := by
  cases result <;> rfl

/-- Actual success yields the same result under the shared projection spelling. -/
private theorem except_success_value {ε : Type _} {α : Type _}
    (result : Except ε α) (fallback : α) (success : ∃ value, result = .ok value) :
    result = .ok (result.toOption.getD fallback) := by
  obtain ⟨value, run⟩ := success
  cases run
  rfl

/-- The actual successful encoder projection is read back while the complete
plan and input remain symbolic. The success premise is an actual child-built
encoder result; no parent readback or parent success oracle is introduced. -/
private theorem prepared_projected_readback
    (source : Environment) (roots : List Ty) (ty : Ty) (plan : Plan)
    (prepared : (prepare source roots).query ty = .ok plan)
    (model : ByteModel) (order : FunctionAddressOrder) (memory : Memory) (input : Value)
    (admitted : ReadbackInput model order memory plan input)
    (ready : TopCharReady plan input)
    (success : ∃ image : Image, encode model order plan input false = .ok image)
    (fallback : Image) :
    ∃ output,
      decode model order memory plan
        ((encode model order plan input false).toOption.getD fallback).bytes = .ok output ∧
      ValueReadback model memory input output :=
  prepared_recursive_readback source roots ty plan prepared model order memory input
    admitted ready
    ((encode model order plan input false).toOption.getD fallback)
    (except_success_value (encode model order plan input false) fallback success)

private theorem rootReady : ReadbackInput .le64 none memory root input :=
  (show ReadbackInput .le64 none memory root input ∧
      ∃ image : Image, encode .le64 none root input false = .ok image from
    mixed_root_fixture_support).1





private def enumInput : Value := .aggregate [.int 8 5,input]


private def enumStored : Image :=
  (encode .le64 none enumPlan enumInput false).toOption.getD
    { bytes := ByteImage.empty }
private theorem enumPrepared : (prepare enumSource []).query (.Enum ⟨0⟩) = .ok enumPlan :=
  enum_preparation_fixture_support


/-- Construct the actual single-payload enum image while the child plan, value
and successful image remain symbolic. No parent-encoder success is assumed. -/
private theorem single_payload_encode_exists
    (model : ByteModel) (order : FunctionAddressOrder) (ty : Ty)
    (layout : MemoryTypeLayout) (info : Enumeration) (tag : Value)
    (child : Plan) (value : Value)
    (selected : EnumEncodingSelects info tag 0)
    (untagged : info.encoding = .untagged)
    (extent : child.layout.size = layout.size)
    (success : ∃ image : Image, encode model order child value false = .ok image) :
    ∃ image : Image,
      encode model order (.enumeration ty layout info [some [(0,child)]])
        (.aggregate [tag,value]) false = .ok image := by
  obtain ⟨childImage,childEncoded⟩ := success
  have childExtent : childImage.bytes.size = layout.size :=
    (encode_extent model order child value false childImage childEncoded).trans extent
  have tagBuilt : EnumTagPrefix layout.size info 0 tag (ByteImage.fill layout.size none) :=
    EnumTagPrefix.untagged_exists layout.size info tag untagged
  have fits : 0 + childImage.bytes.size ≤ (ByteImage.fill layout.size none).size := by
    rw [childExtent, ByteImage.size_fill, Nat.zero_add]
    all_goals exact Nat.le_refl _
  obtain ⟨bytes,written⟩ :=
    ImageOverwrite.exists_of_fits (ByteImage.fill layout.size none) 0 childImage.bytes fits
  let before : Image := { bytes := ByteImage.fill layout.size none }
  let after : Image := { bytes := bytes, unwritten := before.unwritten ++ childImage.unwritten.map (fun (start,count) => (0 + start,count)) }
  have fields : FieldsEncoded model order [(0,child)] [value] false before after := by
    apply FieldsEncoded.cons_iff.mpr
    refine ⟨childImage,bytes,childEncoded,written,?_⟩
    exact FieldsEncoded.nil_iff.mpr ⟨rfl,rfl⟩
  have payload : VariantEncoded model order [some [(0,child)]] 0 [value] before after :=
    VariantEncoded.of_fields_zero model order [(0,child)] [] [value] before after fields
  have checked : NichePayloadChecked info 0 after.bytes :=
    NichePayloadChecked.of_untagged info 0 after.bytes untagged
  exact ⟨after,encode_enumeration_of_components model order ty layout info
    [some [(0,child)]] tag [value] 0 false (ByteImage.fill layout.size none)
    after selected tagBuilt payload checked⟩

private theorem enumEncodingSuccess :
    ∃ image : Image, encode .le64 none enumPlan enumInput false = .ok image := by
  have selected : EnumEncodingSelects enumInfo (.int 8 5) 0 :=
    EnumEncodingSelects.of_lookup enumInfo 8 5 0 rfl rfl rfl
  exact single_payload_encode_exists .le64 none (.Enum ⟨0⟩) ⟨88,8⟩ enumInfo (.int 8 5)
    root input selected rfl rfl mixed_root_fixture_support.2


private theorem prefixSound : EnumPrefixSound 88 enumInfo 0 (.int 8 5) := by
  refine ⟨⟨ByteImage.fill 88 none,rfl⟩,?_⟩
  intro initial built image
  exact EnumDecodingSelects.untagged enumInfo image rfl rfl (by decide)
private theorem enumReady : ReadbackInput .le64 none memory enumPlan enumInput :=
  ReadbackInput.enumeration_of_prefix ⟨0⟩ ⟨88,8⟩ enumInfo enumVariants (.int 8 5) [input] 0 5 [(0,root)]
    rfl rfl rfl rfl (.integer 8 5) (.cons rootReady .nil) prefixSound True.intro (fun _ _ => True.intro)

theorem recursive_enum_payload_readback :
    ∃ output, decode .le64 none memory enumPlan enumStored.bytes = .ok output ∧ ValueReadback .le64 memory enumInput output := by
  delta enumStored
  exact prepared_projected_readback enumSource [] (.Enum ⟨0⟩) enumPlan enumPrepared .le64 none memory enumInput enumReady
    (by intro layout width raw impossible; cases impossible) enumEncodingSuccess { bytes := ByteImage.empty }
end TrustIr.AggregateMemory.RecursiveReadbackControls
