-- Copyright 2026 Andrew Yates | Apache-2.0
import TrustIr.Proofs.FunctionEncodedAdmission

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

namespace TrustIr.AggregateMemory.EncodedAdmissionControls
open SourceLayout

private def code : Plan := .leaf (.Func ⟨0⟩) ⟨8,8⟩
private def array : Plan := .array (.Array ⟨0⟩ 3) ⟨24,8⟩ 3 code
private def rootTy : Ty := .Tuple [.Func ⟨0⟩,.Array ⟨0⟩ 3]
private def fields : List (Nat × Plan) := [(0,code),(8,array)]
private def root : Plan := .fields rootTy ⟨32,8⟩ fields
private def source : Environment := { types := [some (.Func ⟨0⟩)], enums := [] }
private def order : FunctionAddressOrder := some [⟨42⟩,⟨7⟩,⟨42⟩]
private def input : Value := .aggregate [.nullPtr,.array (.uniform 3 (.fnDef ⟨0⟩ ⟨42⟩))]
private def stored : Image := match encode .le64 order root input false with
  | .ok image => image
  | .error _ => { bytes := ByteImage.empty }
private theorem prepared : (prepare source []).query rootTy = .ok root := by
  trustIrCompilerProof {
    exact rfl
  } {
    exact (by trustIrReduce)
  }

private theorem encoded : encode .le64 order root input false = .ok stored := by
  trustIrCompilerProof {
    exact rfl
  } {
    exact (by trustIrReduce)
  }

private theorem shape : FunctionReadbackPlan root := by
  apply FunctionReadbackPlan.fields rootTy ⟨32,8⟩ fields
  intro offset child member
  change (offset,child) ∈ [(0,code),(8,array)] at member
  cases member with
  | head => exact .function ⟨0⟩ ⟨8,8⟩
  | tail _ member =>
    cases member with
    | head => exact .array (.Array ⟨0⟩ 3) ⟨24,8⟩ 3 code (.function ⟨0⟩ ⟨8,8⟩)
    | tail _ impossible => cases impossible

theorem parent_store_supplies_recursive_admission : ReadbackInput .le64 order Memory.empty root input :=
  shape.admit .le64 order Memory.empty input stored encoded

theorem prepared_parent_readback_without_value_certificates :
    ∃ output, decode .le64 order Memory.empty root stored.bytes = .ok output ∧ ValueReadback .le64 Memory.empty input output :=
  prepared_function_plan_readback source [] rootTy root prepared shape .le64 order Memory.empty input stored encoded

private def leaf32 : Plan := .leaf (.Func ⟨0⟩) ⟨4,4⟩
private def value : Value := .fnDef ⟨0⟩ ⟨42⟩
private def image32 : Image := { bytes := ByteImage.ofList [some 1,some 0,some 0,some 0] }
private theorem encoded32 : encode .le32 order leaf32 value false = .ok image32 := by
  trustIrCompilerProof {
    exact rfl
  } {
    exact (by trustIrReduce)
  }

theorem target32_store_supplies_admission : FunctionReadbackInput .le32 order leaf32 value :=
  .of_encoded .le32 order ⟨0⟩ ⟨4,4⟩ value image32 encoded32

theorem distinct_image_exact_function_readback :
    decode .le32 order Memory.empty leaf32 (ByteImage.source 4 image32.bytes.get) = .ok value ∧
      ValueReadback .le32 Memory.empty value value := by
  trustIrCompilerProof {
    exact encoded_function_readback .le32 order Memory.empty ⟨0⟩ ⟨4,4⟩ value image32 encoded32
      (ByteImage.source 4 image32.bytes.get) rfl (source_image_observations image32.bytes)
  } {
    exact encoded_function_readback .le32 order Memory.empty ⟨0⟩ ⟨4,4⟩ value image32 encoded32
      (ByteImage.source 4 image32.bytes.get) (by trustIrReduce) (source_image_observations image32.bytes)
  }

theorem table_free_null_store_supplies_admission :
    FunctionReadbackInput .le64 none code .nullPtr := by
  trustIrCompilerProof {
    exact .of_encoded .le64 none ⟨0⟩ ⟨8,8⟩ .nullPtr { bytes := ByteImage.ofList (List.replicate 8 (some 0)) } rfl
  } {
    exact .of_encoded .le64 none ⟨0⟩ ⟨8,8⟩ .nullPtr { bytes := ByteImage.ofList (List.replicate 8 (some 0)) } (by trustIrReduce)
  }

theorem missing_table_cannot_supply_store (image : Image) :
    encode .le64 none code value false ≠ .ok image := by
  trustIrCompilerProof {
    have refusal : encode .le64 none code value false =
        .error (.unsupported .layout "function pointer Store requires a source function table") := rfl
    rw [refusal]
    intro impossible
    cases impossible
  } {
    have refusal : encode .le64 none code value false =
        .error (.unsupported .layout "function pointer Store requires a source function table") := (by trustIrReduce)
    rw [refusal]
    intro impossible
    cases impossible
  }

theorem mismatched_signature_cannot_supply_store (image : Image) :
    encode .le64 order code (.fnDef ⟨1⟩ ⟨42⟩) false ≠ .ok image := by
  trustIrCompilerProof {
    have refusal : encode .le64 order code (.fnDef ⟨1⟩ ⟨42⟩) false =
        .error (.typeError "Store: function pointer signature does not match type") := rfl
    rw [refusal]
    intro impossible
    cases impossible
  } {
    have refusal : encode .le64 order code (.fnDef ⟨1⟩ ⟨42⟩) false =
        .error (.typeError "Store: function pointer signature does not match type") := (by trustIrReduce)
    rw [refusal]
    intro impossible
    cases impossible
  }

theorem wrong_extent_cannot_supply_store (image : Image) :
    encode .le64 order (.leaf (.Func ⟨0⟩) ⟨4,4⟩) value false ≠ .ok image := by
  trustIrCompilerProof {
    have refusal : encode .le64 order (.leaf (.Func ⟨0⟩) ⟨4,4⟩) value false =
        .error (.typeError "memory image: leaf byte count mismatch") := rfl
    rw [refusal]
    intro impossible
    cases impossible
  } {
    have refusal : encode .le64 order (.leaf (.Func ⟨0⟩) ⟨4,4⟩) value false =
        .error (.typeError "memory image: leaf byte count mismatch") := (by trustIrReduce)
    rw [refusal]
    intro impossible
    cases impossible
  }

theorem empty_array_ignores_unused_unwritten_template :
    ReadbackInput .le64 none Memory.empty (.array (.Array ⟨0⟩ 0) ⟨0,8⟩ 0 code) (.array (.uniform 0 .uninit)) := by
  trustIrCompilerProof {
    exact (FunctionReadbackPlan.array (.Array ⟨0⟩ 0) ⟨0,8⟩ 0 code (.function ⟨0⟩ ⟨8,8⟩)).admit .le64 none Memory.empty
      (.array (.uniform 0 .uninit)) { bytes := ByteImage.empty } rfl
  } {
    exact (FunctionReadbackPlan.array (.Array ⟨0⟩ 0) ⟨0,8⟩ 0 code (.function ⟨0⟩ ⟨8,8⟩)).admit .le64 none Memory.empty
      (.array (.uniform 0 .uninit)) { bytes := ByteImage.empty } (by trustIrReduce)
  }

end TrustIr.AggregateMemory.EncodedAdmissionControls
