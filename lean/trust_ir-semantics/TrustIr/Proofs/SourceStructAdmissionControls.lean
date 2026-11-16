-- Copyright 2026 Andrew Yates | Apache-2.0
import TrustIr.Proofs.SourceStructAdmission

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

namespace TrustIr.AggregateMemory.SourceStructAdmissionControls
open SourceLayout

private def first : StructDef := { id := ⟨1⟩, name := "First", fields := [{ name := "flag", ty := .Bool, offset := some 0 }], size := some 1, align := some 1 }
private def packed : StructDef := { id := ⟨1⟩, name := "Packed", fields := [{ name := "byte", ty := .U8, offset := some 2 }, { name := "word", ty := .U16, offset := some 0 }], size := some 3, align := some 1, repr := .packed 1 }
private def canonical : StructDef := { id := ⟨17⟩, name := "Canonical", fields := [{ name := "packed", ty := .Struct ⟨1⟩, offset := none }, { name := "flag", ty := .Bool, offset := none }], size := none, align := none }
private def source : Environment := { types := [some (.Struct ⟨17⟩)], structs := [first,packed,canonical] }
private def byte : Plan := .leaf .U8 ⟨1,1⟩
private def word : Plan := .leaf .U16 ⟨2,2⟩
private def boolean : Plan := .leaf .Bool ⟨1,1⟩
private def packedFields : List (Nat × Plan) := [(2,byte),(0,word)]
private def packedPlan : Plan := .fields (.Struct ⟨1⟩) ⟨3,1⟩ packedFields
private def canonicalFields : List (Nat × Plan) := [(0,packedPlan),(3,boolean)]
private def canonicalPlan : Plan := .fields (.Struct ⟨17⟩) ⟨4,1⟩ canonicalFields
private def array : Plan := .array (.Array ⟨0⟩ 2) ⟨8,1⟩ 2 canonicalPlan
private def rootTy : Ty := .Tuple [.Struct ⟨17⟩,.Array ⟨0⟩ 2]
private def rootFields : List (Nat × Plan) := [(0,canonicalPlan),(4,array)]
private def root : Plan := .fields rootTy ⟨12,1⟩ rootFields
private def context (base : EvalContext) : EvalContext :=
  { base with byteModel := .le64, valueSource := FunctionItemPresence.prepare { base.valueSource.source with types := [some (.Struct ⟨17⟩)], structs := [packed, canonical] } }
private def packedInput : Value := .aggregate [.int 8 7,.int 16 513]
private def canonicalInput : Value := .aggregate [packedInput,.bool true]
private def input : Value := .aggregate [canonicalInput,.array (.uniform 2 canonicalInput)]
private def stored (order : FunctionAddressOrder) : Image := match encode .le64 order root input false with
  | .ok image => image
  | .error _ => { bytes := ByteImage.empty }

theorem shape_selects_first_duplicate : (Index.ofEnvironment source).structShapePositions.find 1 = some 0 := rfl
theorem execution_selects_matching_duplicate : (Index.ofEnvironment source).structPositions.find 1 = some 1 := rfl
theorem execution_selects_sparse_id : (Index.ofEnvironment source).structPositions.find 17 = some 2 := rfl

private theorem prepared : (prepare source []).query rootTy = .ok root := by
  trustIrCompilerProof {
    dsimp only [source,first,packed,canonical,rootTy,root,rootFields,canonicalPlan,canonicalFields,packedPlan,packedFields,byte,word,boolean,array]
    rfl
  } {
    dsimp only [source,first,packed,canonical,rootTy,root,rootFields,canonicalPlan,canonicalFields,packedPlan,packedFields,byte,word,boolean,array]
    trustIrReduce
  }

private theorem encoded (order : FunctionAddressOrder) : encode .le64 order root input false = .ok (stored order) := by
  trustIrCompilerProof {
    dsimp only [stored,root,rootTy,rootFields,canonicalPlan,canonicalFields,packedPlan,packedFields,byte,word,boolean,array,input,canonicalInput,packedInput]
    simp only [encode]
    rfl
  } {
    dsimp only [stored,root,rootTy,rootFields,canonicalPlan,canonicalFields,packedPlan,packedFields,byte,word,boolean,array,input,canonicalInput,packedInput]
    simp only [encode]
    trustIrReduce
  }

private theorem packedAgreement (base : EvalContext) : StructContextAgreement source (context base) ⟨1⟩ := by
  intro position definition selected row
  change some 1 = some position at selected
  cases selected
  change some packed = some definition at row
  cases row
  rfl
private theorem canonicalAgreement (base : EvalContext) : StructContextAgreement source (context base) ⟨17⟩ := by
  intro position definition selected row
  change some 2 = some position at selected
  cases selected
  change some canonical = some definition at row
  cases row
  rfl

private theorem packedShape (base : EvalContext) : SourceNominalReadbackShape source (context base) packedPlan := by
  apply SourceNominalReadbackShape.nominal ⟨1⟩ ⟨3,1⟩ packedFields (packedAgreement base)
  intro offset child member
  change (offset,child) ∈ [(2,byte),(0,word)] at member
  simp only [List.mem_cons,List.not_mem_nil,or_false,Prod.mk.injEq] at member
  rcases member with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · exact .existing (.scalar (.integer .U8 ⟨1,1⟩ rfl))
  · exact .existing (.scalar (.integer .U16 ⟨2,2⟩ rfl))
private theorem canonicalShape (base : EvalContext) : SourceNominalReadbackShape source (context base) canonicalPlan := by
  apply SourceNominalReadbackShape.nominal ⟨17⟩ ⟨4,1⟩ canonicalFields (canonicalAgreement base)
  intro offset child member
  change (offset,child) ∈ [(0,packedPlan),(3,boolean)] at member
  simp only [List.mem_cons,List.not_mem_nil,or_false,Prod.mk.injEq] at member
  rcases member with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · exact packedShape base
  · exact .existing (.scalar .boolean)
private theorem rootShape (base : EvalContext) : SourceNominalReadbackShape source (context base) root := by
  apply SourceNominalReadbackShape.tuple _ ⟨12,1⟩ rootFields
  intro offset child member
  change (offset,child) ∈ [(0,canonicalPlan),(4,array)] at member
  simp only [List.mem_cons,List.not_mem_nil,or_false,Prod.mk.injEq] at member
  rcases member with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · exact canonicalShape base
  · exact .array ⟨0⟩ ⟨8,1⟩ 2 canonicalPlan rfl (canonicalShape base)

private theorem checkedAt (base : EvalContext) : checkClosureValueAt (context base) 6 rootTy input = .ok () := by
  dsimp only [context,rootTy,input,canonicalInput,packedInput,packed,canonical]
  rfl

theorem nested_structs_admitted_from_real_checker_and_store (base : EvalContext) (order : FunctionAddressOrder) :
    ReadbackInput .le64 order Memory.empty root input :=
  (rootShape base).admit order Memory.empty (prepared_plan_origin source [] rootTy root prepared).own
    6 input (stored order) (checkedAt base) (encoded order)

private def wrongContext (base : EvalContext) : EvalContext :=
  { context base with valueSource := FunctionItemPresence.prepare { (context base).valueSource.source with structs := [first] } }
theorem duplicate_context_disagreement_refused (base : EvalContext) : ¬ StructContextAgreement source (wrongContext base) ⟨1⟩ := by
  intro agreement
  have same := agreement 1 packed rfl rfl
  have lengths := congrArg (fun row => row.map (fun definition => definition.fields.length)) same
  change some 1 = some 2 at lengths
  cases lengths


private theorem inputDepth : input.depth = 5 := by
  trustIrCompilerProof {
    simp [Value.depth,input,canonicalInput,packedInput,Value.depthSpec,valueListDepthSpec,arrayTreeDepthRangeSpec,CompactArray.Packed.uniform]
    rfl
  } {
    simp [Value.depth,input,canonicalInput,packedInput,Value.depthSpec,valueListDepthSpec,arrayTreeDepthRangeSpec,CompactArray.Packed.uniform]
  }

theorem actual_entry_checks_nested_structs (base : EvalContext) :
    checkClosureValue (context base) rootTy input = .ok () := by
  unfold checkClosureValue
  rw [inputDepth]
  exact checkedAt base

theorem prepared_nested_struct_readback (base : EvalContext) :
    ∃ output, decode .le64 (context base).functionOrder Memory.empty root (stored (context base).functionOrder).bytes = .ok output ∧
      ValueReadback .le64 Memory.empty input output :=
  prepared_checked_nominal_value_readback source [] rootTy root prepared (context base) (rootShape base) Memory.empty input
    (stored (context base).functionOrder) (actual_entry_checks_nested_structs base) (encoded (context base).functionOrder)

private theorem storedSize (order : FunctionAddressOrder) : (stored order).bytes.size = 12 :=
  encode_extent .le64 order root input false (stored order) (encoded order)
private theorem reconstructedObservations (order : FunctionAddressOrder) (index : Nat) :
    (ByteImage.source 12 (stored order).bytes.get).get index = (stored order).bytes.get index := by
  have observed := source_image_observations (stored order).bytes index
  rw [storedSize order] at observed
  exact observed

theorem complete_external_image_readback (base : EvalContext) (order : FunctionAddressOrder) :
    ∃ output, decode .le64 order Memory.empty root (ByteImage.source 12 (stored order).bytes.get) = .ok output ∧
      ValueReadback .le64 Memory.empty input output :=
  source_checked_nominal_readback (rootShape base) (prepared_plan_origin source [] rootTy root prepared).own
    6 order Memory.empty input (stored order) (checkedAt base) (encoded order)
    (ByteImage.source 12 (stored order).bytes.get) rfl (reconstructedObservations order)

theorem wrong_duplicate_row_fails_real_checker (base : EvalContext) :
    checkClosureValueAt (wrongContext base) 3 (.Struct ⟨1⟩) packedInput =
      .error (.typeError "closure value does not match its declared type") := rfl

end TrustIr.AggregateMemory.SourceStructAdmissionControls
