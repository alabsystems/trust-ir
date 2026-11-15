-- Copyright 2026 Andrew Yates | Apache-2.0
-- Raw-table controls intentionally include malformed duplicate occurrences.
import TrustIr.DecodedContext

namespace TrustIrEval.FunctionLookup.Controls
open TrustIr

private def executable (entry : Nat) : EvalFunction :=
  { body := {paramTys := [], returnTys := [], isVararg := false}
    cfg := fun _ => none
    entryBlock := ⟨entry⟩ }

private def row (key : Nat) (declaration : Bool)
    (body : D (List (BlockId × BasicBlock))) : Function :=
  {id := ⟨key⟩, name := "lookup-control", ty := ⟨0⟩, entry := ⟨0⟩,
   isDeclaration := declaration, blocks := body}

private def firstRawError : Prepared := prepare
  [row 7 false (.error (.malformed "raw first")), row 7 false (.ok []), row 7 true (.ok [])]
  [(⟨7⟩, .ok (executable 11)), (⟨7⟩, .ok (executable 99))]

theorem raw_error_and_later_executable_remain_independent :
    (findFunction firstRawError ⟨7⟩).map (fun function => function.entryBlock.index) = some 11 ∧
    findError firstRawError ⟨7⟩ = some (.typeError "function 7 body is malformed: raw first") ∧
    isDeclared firstRawError ⟨7⟩ = true := by
  exact ⟨rfl, rfl, rfl⟩

theorem first_metadata_error_occupies_executable_key :
    let prepared := prepare [row 19 false (.ok [])]
      [(⟨19⟩, .error (.malformed "metadata first")), (⟨19⟩, .ok (executable 99))]
    (findFunction prepared ⟨19⟩).isNone = true ∧
    findError prepared ⟨19⟩ = some (.typeError "metadata first") := by
  exact ⟨rfl, rfl⟩

theorem raw_unsupported_priority_is_interprocedural :
    let prepared := prepare [row 19 false (.error (.unsupported "raw future"))]
      [(⟨19⟩, .error (.unsupported "metadata future"))]
    findError prepared ⟨19⟩ = some (.unsupported .interproceduralCall
      "function 19 body is unsupported: raw future") := rfl

theorem metadata_unsupported_priority_is_ssa_table :
    findError (prepare [row 19 false (.ok [])]
      [(⟨19⟩, .error (.unsupported "metadata future"))]) ⟨19⟩ =
      some (.unsupported .ssaTypeTable "metadata future") := rfl

theorem late_declaration_is_an_or_observation :
    isDeclared (prepare [row 7 false (.ok []), row 19 true (.ok []), row 7 true (.ok [])] []) ⟨7⟩ = true ∧
    isDeclared (prepare [row 7 false (.ok []), row 19 true (.ok [])] []) ⟨7⟩ = false := by
  exact ⟨rfl, rfl⟩

theorem missing_source_does_not_expose_orphan_metadata_error :
    findError (prepare [] [(⟨19⟩, .error (.malformed "orphan"))]) ⟨19⟩ = none := rfl

theorem sparse_full_nat_keys_and_missing_are_distinct :
    let prepared := prepare [row 1208925819614629174706176 false (.ok [])]
      [(⟨1208925819614629174706176⟩, .ok (executable 31))]
    (findFunction prepared ⟨1208925819614629174706176⟩).map (fun function => function.entryBlock.index) = some 31 ∧
    (findFunction prepared ⟨4294967295⟩).isNone = true ∧
    isDeclared prepared ⟨1208925819614629174706176⟩ = false := by
  exact ⟨rfl, rfl, rfl⟩

private def validRows : List (BlockId × BasicBlock) :=
  [(⟨3⟩, {params := [], body := [], terminator := .Return []})]

private def rawModule : Module :=
  { functions := [{row 7 true (.ok []) with ty := ⟨99⟩},
      {row 7 false (.ok validRows) with entry := ⟨3⟩}, row 7 true (.ok [])]
    funcTys := [{params := [], returns := [], isVararg := false}]
    globals := [], enums := [], structs := [], types := [] }

theorem actual_context_keeps_header_executable_and_declaration_views :
    (contextOf rawModule 8).map (fun context =>
      ((context.functions ⟨7⟩).map (fun function => function.entryBlock.index),
       context.functionHeaders ⟨7⟩, context.declared ⟨7⟩, context.functionErrors ⟨7⟩)) =
      .ok (some 3, some (.error (.typeError "function 7: original signature is absent")), true, none) := rfl

theorem actual_context_byte_model_refusal_precedes_table_preparation :
    contextOf {rawModule with byteModel := .error (.unsupported "byte-model-first")} 0 =
      .error (.unsupported "byte-model-first") := rfl

end TrustIrEval.FunctionLookup.Controls
