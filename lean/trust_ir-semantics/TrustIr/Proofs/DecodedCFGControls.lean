-- Copyright 2026 Andrew Yates | Apache-2.0
-- Raw controls are not validator or native execution claims.
import TrustIr.Proofs.DecodedContextLookup

namespace TrustIrEval.DecodedCFG.Controls
open TrustIr

private def signature : FuncTyDef := {params := [], returns := [], isVararg := false}
private def first : BasicBlock := {params := [], body := [], terminator := .Return []}
private def shadowed : BasicBlock := {params := [], body := [], terminator := .Unreachable}
private def rows : List (BlockId × BasicBlock) :=
  [(⟨9⟩, first), (⟨2^128⟩, first), (⟨9⟩, shadowed), (⟨0⟩, shadowed)]
private def function : Function :=
  {id := ⟨17⟩, name := "cfg", ty := ⟨0⟩, entry := ⟨9⟩,
    isDeclaration := false, blocks := .ok rows}

private def converted : D EvalFunction :=
  evalFunctionOfWithTypes #[signature] (fun _ => none) function rows

theorem actual_duplicate_first_row :
    converted.map (fun result => result.cfg ⟨9⟩) = .ok (some first) := by
  simp only [converted, evalFunctionOfWithTypes_eq_listSpec]
  rfl

theorem actual_sparse_high_row :
    converted.map (fun result => result.cfg ⟨2^128⟩) = .ok (some first) := by
  simp only [converted, evalFunctionOfWithTypes_eq_listSpec]
  rfl

theorem actual_neighbor_missing :
    converted.map (fun result => result.cfg ⟨2^128 + 1⟩) = .ok none := by
  simp only [converted, evalFunctionOfWithTypes_eq_listSpec]
  rfl

theorem actual_zero_row :
    converted.map (fun result => result.cfg ⟨0⟩) = .ok (some shadowed) := by
  simp only [converted, evalFunctionOfWithTypes_eq_listSpec]
  rfl

theorem actual_empty_cfg :
    (evalFunctionOfWithTypes #[signature] (fun _ => none) function []).map
      (fun result => result.cfg ⟨9⟩) = .ok none := by
  rw [evalFunctionOfWithTypes_eq_listSpec]
  rfl

theorem original_missing_signature_error :
    evalFunctionOfWithTypes #[] (fun _ => none) function rows =
      .error (.malformed "function cfg: func type 0 not in table") := rfl

private def source : Module :=
  {functions := [function], funcTys := [signature], globals := [], enums := [], structs := [], types := []}

/-- Complete actual context construction, not a separately supplied CFG. -/
theorem complete_context_original_spec (depth : Nat) :
    contextOf source depth = FunctionLookup.listContextSpec source depth :=
  FunctionLookup.contextOf_eq_listContextSpec source depth

end TrustIrEval.DecodedCFG.Controls
