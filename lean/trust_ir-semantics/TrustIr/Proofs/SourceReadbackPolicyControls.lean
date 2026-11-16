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

namespace TrustIr.AggregateMemory.SourceReadbackPolicyControls
open SourceLayout

private def row : StructDef := { id := ⟨1⟩, name := "Byte", fields := [{ name := "value", ty := .U8, offset := none }], size := none, align := none }
private def shadow : StructDef := { row with name := "Shadow", fields := [{ name := "flag", ty := .Bool, offset := none }] }
private def source : Environment := { structs := [shadow,row], types := [some (.Struct ⟨1⟩)] }
private def context : EvalContext := { EvalContext.empty with valueSource := FunctionItemPresence.prepare { EvalContext.empty.valueSource.source with structs := [row], types := [some (.Struct ⟨1⟩)] } }
private def contextWithStructs (rows : List StructDef) : EvalContext :=
  { context with valueSource := FunctionItemPresence.prepare { context.valueSource.source with structs := rows } }
private def contextWithTypes (rows : List (Option Ty)) : EvalContext :=
  { context with valueSource := FunctionItemPresence.prepare { context.valueSource.source with types := rows } }
private def byte : Plan := .leaf .U8 ⟨1,1⟩
private def nominal : Plan := .fields (.Struct ⟨1⟩) ⟨1,1⟩ [(0,byte)]
private def array : Plan := .array (.Array ⟨0⟩ 2) ⟨2,1⟩ 2 nominal
private def rootTy : Ty := .Tuple [.Struct ⟨1⟩,.Array ⟨0⟩ 2]
private def root : Plan := .fields rootTy ⟨3,1⟩ [(0,nominal),(1,array)]

theorem scalar_accepted : sourceReadbackPolicy source context byte = true := rfl

theorem canonical_bool_accepted : sourceReadbackPolicy source context (.leaf .Bool ⟨1,1⟩) = true := rfl

theorem oversized_bool_refused : sourceReadbackPolicy source context (.leaf .Bool ⟨2,1⟩) = false := rfl

theorem misaligned_unit_refused : sourceReadbackPolicy source context (.leaf .Unit ⟨0,2⟩) = false := rfl

theorem float_refused : sourceReadbackPolicy source context (.leaf .F64 ⟨8,8⟩) = false := rfl

theorem pointer_vector_refused : sourceReadbackPolicy source context (.leaf (.Vector 4 .Ptr) ⟨32,8⟩) = false := rfl

theorem pointer_accepted : sourceReadbackPolicy source context (.leaf .Ptr ⟨8,8⟩) = true := rfl

theorem char_accepted : sourceReadbackPolicy source context (.leaf .Char ⟨4,4⟩) = true := rfl

theorem function_accepted : sourceReadbackPolicy source context (.leaf (.Func ⟨42⟩) ⟨8,8⟩) = true := rfl

theorem fat_pointer_accepted : sourceReadbackPolicy source context (.leaf (.FatPtr .Str) ⟨16,8⟩) = true := rfl

theorem enumeration_refused (ty : Ty) (layout : MemoryTypeLayout) (info : Enumeration)
    (variants : List (Option (List (Nat × Plan)))) :
    sourceReadbackPolicy source context (.enumeration ty layout info variants) = false := by
  rw [sourceReadbackPolicy]

theorem record_refused : sourceReadbackPolicy source context (.fields (.Record ⟨1⟩) ⟨0,1⟩ []) = false := rfl

theorem duplicate_selects_execution_row : selectedStructAgrees source context ⟨1⟩ = true := by trustIrReduce

theorem first_duplicate_refused : selectedStructAgrees source (contextWithStructs [shadow]) ⟨1⟩ = false := rfl

theorem full_row_metadata_bound : selectedStructAgrees source (contextWithStructs [{ row with name := "Renamed" }]) ⟨1⟩ = false := rfl

theorem absent_nominal_refused : selectedStructAgrees source context ⟨8⟩ = false := rfl

theorem absent_evaluator_row_refused : selectedStructAgrees source (contextWithStructs []) ⟨1⟩ = false := rfl

theorem wrong_array_type_refused : sourceReadbackPolicy source (contextWithTypes [some .Bool]) array = false := by trustIrReduce

theorem absent_array_type_refused : sourceReadbackPolicy source (contextWithTypes []) array = false := rfl

theorem array_count_mismatch_refused : sourceReadbackPolicy source context (.array (.Array ⟨0⟩ 3) ⟨2,1⟩ 2 nominal) = false := rfl

theorem unused_empty_template_accepted : sourceReadbackPolicy source EvalContext.empty
    (.array (.Array ⟨999⟩ 0) ⟨0,1⟩ 0 (.leaf .F64 ⟨8,8⟩)) = true := rfl

theorem unsupported_nested_child_refused : sourceReadbackPolicy source context
    (.fields (.Tuple [.F64]) ⟨8,8⟩ [(0,.leaf .F64 ⟨8,8⟩)]) = false := rfl

theorem nested_nominal_policy_accepted : sourceReadbackPolicy source context root = true := by trustIrReduce

private theorem prepared : (prepare source []).query rootTy = .ok root := by
  trustIrCompilerProof {
    exact rfl
  } {
    trustIrReduce
  }
private def input : Value := .aggregate [.aggregate [.int 8 7], .array (.uniform 2 (.aggregate [.int 8 9]))]
private def stored : Image := match encode context.byteModel context.functionOrder root input false with
  | .ok image => image
  | .error _ => { bytes := ByteImage.empty }
private theorem encoded : encode context.byteModel context.functionOrder root input false = .ok stored := by
  trustIrCompilerProof {
    exact rfl
  } {
    trustIrReduce
  }
private theorem checked : checkClosureValue context root.ty input = .ok () := by
  trustIrCompilerProof {
    exact rfl
  } {
    trustIrReduce
  }

theorem prepared_readback_without_manual_shape :
    ∃ output, decode context.byteModel context.functionOrder Memory.empty root stored.bytes = .ok output ∧
      ValueReadback context.byteModel Memory.empty input output :=
  prepared_policy_checked_value_readback source [] rootTy root prepared context
    nested_nominal_policy_accepted Memory.empty input stored checked encoded

theorem real_origin_policy_equivalence : sourceReadbackPolicy source context root = true ↔
    SourceNominalReadbackShape source context root :=
  sourceReadbackPolicy_iff source context root (prepared_plan_origin source [] rootTy root prepared).own

end TrustIr.AggregateMemory.SourceReadbackPolicyControls
