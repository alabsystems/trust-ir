-- Copyright 2026 Andrew Yates | Apache-2.0
import TrustIr.Proofs.SourceReadbackPolicy

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

namespace TrustIr.AggregateMemory.VectorReadbackControls
open SourceLayout

theorem all_fixed_lanes_classified :
    [.Bool,.I8,.U8,.I16,.U16,.I32,.U32,.I64,.U64].all vectorReadbackLane = true := rfl

theorem boolean_mask_image : encodeVectorLanes .Bool [.bool true,.bool false,.bool true] = .ok [255,0,255] := rfl

theorem vector_and_scalar_boolean_images_differ :
    encodeVectorLane .Bool (.bool true) = .ok [255] ∧
    encodeMemoryWithFunctions .le64 none .Bool (.bool true) = .ok [1] := ⟨rfl,rfl⟩

theorem signed_lane_residue : encodeScalarVectorAt 2 .I8 (.vector [.int 8 (-1),.int 8 (-128)]) = .ok [255,128] := rfl

theorem signed_lane_readback : decodeScalarVectorAt 2 .I8 [255,128] = .ok (.vector [.int 8 255,.int 8 128]) := rfl

theorem u16_little_endian : encodeScalarVectorAt 2 .U16 (.vector [.int 16 513,.int 16 7]) = .ok [1,2,7,0] := rfl

theorem u64_full_width : decodeScalarVectorAt 1 .U64 [255,255,255,255,255,255,255,255] =
    .ok (.vector [.int 64 18446744073709551615]) := rfl

theorem unchecked_lane_wraps : encodeScalarVectorAt 1 .U8 (.vector [.int 8 257]) = .ok [1] := rfl

theorem source_rejects_unbounded_lane : checkClosureValueAt EvalContext.empty 3 (.Vector 1 .U8) (.vector [.int 8 257]) =
    .error (.typeError "closure value does not match its declared type") := rfl

theorem wrong_lane_width_refused : encodeScalarVectorAt 1 .U16 (.vector [.int 8 1]) =
    .error (.typeError "vector integer lane has the wrong type or width") := rfl

theorem boolean_integer_carrier_refused : encodeScalarVectorAt 1 .Bool (.vector [.int 8 1]) =
    .error (.typeError "vector integer lane has the wrong type or width") := rfl

theorem zero_count_refused : encodeScalarVectorAt 0 .U8 (.vector []) =
    .error (.unsupported .vectorShape "zero-lane vectors are not executable") := rfl

theorem wrong_lane_count_refused : encodeScalarVectorAt 2 .U8 (.vector [.int 8 1]) =
    .error (.typeError "vector value lane count does not match its declared type") := rfl

theorem trailing_bytes_refused : decodeScalarVectorAt 1 .U8 [1,2] =
    .error (.typeError "vector image byte count does not match its declared type") := rfl

theorem truncated_bytes_refused : decodeScalarVectorAt 2 .U16 [1,2,3] =
    .error (.typeError "vector image byte count does not match its declared type") := rfl

theorem pointer_lane_refused : vectorReadbackLane .Ptr = false := rfl

theorem target_sized_lane_refused : vectorReadbackLane .Usize = false := rfl

theorem wide_lane_refused : vectorReadbackLane .U128 = false := rfl

theorem float_lane_refused : vectorReadbackLane .F32 = false := rfl

theorem nested_lane_refused : vectorReadbackLane (.Vector 2 .U8) = false := rfl

theorem wrong_width_certificate_impossible (model : ByteModel) (layout : MemoryTypeLayout) :
    ¬ ScalarReadbackInput model (.leaf (.Vector 1 .U16) layout) (.vector [.int 8 1]) := by
  intro admitted
  cases admitted with
  | vector count ty layout inputs lane size typed positive census extent ready =>
    have bad : (some 16 : Option Nat) = some 8 := (ready (.int 8 1) ((trustIrListMemConsSelf _ _))).2
    cases bad

theorem zero_count_certificate_impossible (model : ByteModel) (layout : MemoryTypeLayout) :
    ¬ ScalarReadbackInput model (.leaf (.Vector 0 .U8) layout) (.vector []) := by
  intro admitted
  cases admitted with
  | vector count ty layout inputs lane size typed positive census extent ready => exact positive rfl

theorem wrong_extent_certificate_impossible (model : ByteModel) :
    ¬ ScalarReadbackInput model (.leaf (.Vector 1 .U16) ⟨1,1⟩) (.vector [.int 16 1]) := by
  intro admitted
  cases admitted with
  | vector count ty layout inputs lane size typed positive census extent ready =>
    change (some 2 : Option Nat) = some size at typed
    cases typed
    change 1 = 1 * 2 at extent
    omega

theorem checked_boolean_vector_reloads (ctx : EvalContext) :
    ∃ values, Value.vector [.bool true,.bool false] = .vector values ∧ values.length = 2 ∧
      decodeScalarVectorAt 2 .Bool [255,0] = .ok (.vector (values.map vectorLaneResult)) :=
  checked_vector_codec_readback ctx 3 2 .Bool (.vector [.bool true,.bool false]) .boolean [255,0] rfl rfl

private def source (model : ByteModel) : Environment := { model, types := [some (.Vector 2 .U16)] }
private def context (model : ByteModel) : EvalContext :=
  { EvalContext.empty with byteModel := model, valueSource := FunctionItemPresence.prepare { EvalContext.empty.valueSource.source with types := [some (.Vector 2 .U16)] } }
private def booleanPlan : Plan := .leaf (.Vector 3 .Bool) ⟨3,1⟩
private def integerPlan : Plan := .leaf (.Vector 2 .U16) ⟨4,2⟩
private def arrayPlan : Plan := .array (.Array ⟨0⟩ 2) ⟨8,2⟩ 2 integerPlan
private def rootTy : Ty := .Tuple [.Vector 3 .Bool,.Array ⟨0⟩ 2]
private def root : Plan := .fields rootTy ⟨12,2⟩ [(0,booleanPlan),(4,arrayPlan)]
private def integerInput : Value := .vector [.int 16 513,.int 16 7]
private def input : Value := .aggregate [.vector [.bool true,.bool false,.bool true], .array (.uniform 2 integerInput)]
private def stored (model : ByteModel) : Image := match encode model none root input false with
  | .ok image => image
  | .error _ => { bytes := ByteImage.empty }

private theorem prepared (model : ByteModel) : (prepare (source model) []).query rootTy = .ok root := by
  trustIrCompilerProof {
    cases model <;> rfl
  } {
    cases model <;> trustIrReduce
  }
private theorem encoded (model : ByteModel) : encode model none root input false = .ok (stored model) := by
  trustIrCompilerProof {
    cases model <;> rfl
  } {
    cases model <;> trustIrReduce
  }
private theorem checked (model : ByteModel) : checkClosureValue (context model) root.ty input = .ok () := by
  trustIrCompilerProof {
    cases model <;> rfl
  } {
    cases model <;> trustIrReduce
  }

private theorem checkedAt (model : ByteModel) : checkClosureValueAt (context model) 5 root.ty input = .ok () := by
  cases model <;> rfl

theorem nested_policy_computed (model : ByteModel) : sourceReadbackPolicy (source model) (context model) root = true := by
  cases model <;> trustIrReduce

theorem prepared_nested_vectors_readback (model : ByteModel) :
    ∃ output, decode model none Memory.empty root (stored model).bytes = .ok output ∧
      ValueReadback model Memory.empty input output :=
  prepared_policy_checked_value_readback (source model) [] rootTy root (prepared model) (context model)
    (nested_policy_computed model) Memory.empty input (stored model) (checked model) (encoded model)

theorem complete_receiving_window_readback (model : ByteModel) :
    ∃ output, decode model none Memory.empty root (ByteImage.source 12 (stored model).bytes.get) = .ok output ∧
      ValueReadback model Memory.empty input output := by
  have extent : (stored model).bytes.size = 12 := encode_extent model none root input false (stored model) (encoded model)
  apply source_checked_nominal_readback (sourceReadbackPolicy_sound _ _ _ (nested_policy_computed model))
    (prepared_plan_origin (source model) [] rootTy root (prepared model)).own
    5 none Memory.empty input (stored model) (checkedAt model) (encoded model)
    (ByteImage.source 12 (stored model).bytes.get) rfl
  intro index
  have same := source_image_observations (stored model).bytes index
  rw [extent] at same
  exact same

end TrustIr.AggregateMemory.VectorReadbackControls
