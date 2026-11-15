-- Copyright 2026 Andrew Yates | Apache-2.0
import TrustIr.Proofs.GenericCoroHeaderMaps

namespace TrustIr.NatRBMapInsert.Controls
open Lean
variable {α : Type}

def insertAllFrom (entries : List (Nat × α)) (initial : RBMap Nat α compare) : RBMap Nat α compare :=
  entries.foldl (fun map row => map.insert row.1 row.2) initial

theorem insertAllFrom_history (entries : List (Nat × α)) (initial : RBMap Nat α compare)
    (history : InsertOnly initial) : InsertOnly (insertAllFrom entries initial) := by
  induction entries generalizing initial with
  | nil => exact history
  | cons head _tail ih => exact ih _ (.insert history head.1 head.2)

def mapOf (entries : List (Nat × Nat)) : RBMap Nat Nat compare := insertAllFrom entries (mkRBMap ..)

theorem mapOf_history (entries : List (Nat × Nat)) : InsertOnly (mapOf entries) :=
  insertAllFrom_history entries _ .empty

theorem four_actual_rotation_paths :
    ([[(3, 30), (2, 20), (1, 10)], [(3, 30), (1, 10), (2, 20)],
      [(1, 10), (3, 30), (2, 20)], [(1, 10), (2, 20), (3, 30)]].map fun entries =>
        [1, 2, 3, 0, 4].map ((mapOf entries).find?)) =
      List.replicate 4 [some 10, some 20, some 30, none, none] := rfl

/-- An inhabited use of the universal actual-map law after balancing. -/
theorem overwrite_after_rotation (query : Nat) :
    ((mapOf [(3, 30), (1, 10), (2, 20)]).insert 2 777).find? query =
      if query = 2 then some 777 else (mapOf [(3, 30), (1, 10), (2, 20)]).find? query :=
  find?_insert (mapOf_history _) 2 query 777

theorem overwrite_exact_others_retained :
    [1, 2, 3].map (((mapOf [(3, 30), (1, 10), (2, 20)]).insert 2 777).find?) =
      [some 10, some 777, some 30] := rfl

theorem sparse_high_keys :
    [4294967295, 0, 65537, 17].map
      ((mapOf [(65537, 12), (4294967295, 13), (0, 14)]).find?) =
        [some 13, some 14, some 12, none] := rfl

theorem duplicate_insert_overwrites_only_selected_key :
    [17, 3, 9].map ((mapOf [(17, 1), (3, 2), (17, 3)]).find?) = [some 3, some 2, none] := rfl

def optionEntries : List (Nat × Option Nat) := [(17, none), (3, some 9), (17, some 42)]

theorem first_none_payload_is_occupied :
    (firstWinsFrom Prod.fst Prod.snd optionEntries (mkRBMap Nat (Option Nat) compare)).find? 17 =
      some none := rfl

theorem first_wins_and_missing (query : Nat) :
    (firstWinsFrom Prod.fst Prod.snd optionEntries (mkRBMap Nat (Option Nat) compare)).find? query =
      firstValue Prod.fst Prod.snd optionEntries query :=
  firstWins_empty_find Prod.fst Prod.snd optionEntries query

/-- This unordered raw node is not an insert-only map. It exhibits why the
    ordering invariant proved above is substantive, rather than dispensable. -/
theorem unordered_node_is_not_covered :
    let tree : RBNode Nat (fun _ => Nat) :=
      .node .black (.node .red .leaf 10 100 .leaf) 5 50 .leaf
    tree.find compare 10 = none ∧ lookupRows (rows tree) 10 = some 100 := ⟨rfl, rfl⟩

def function (id ty : Nat) : TrustIrEval.Function :=
  {id := ⟨id⟩, name := "header", ty := ⟨ty⟩, entry := ⟨0⟩,
    isDeclaration := true, blocks := .ok []}

def signatures : Array TrustIr.FuncTyDef := #[
  {params := [.I32], returns := [.I32], isVararg := false},
  {params := [.Ptr], returns := [.Unit], isVararg := false}]

theorem actual_duplicate_function_header_classifier (query : TrustIr.FuncId) :
    let functions := [function 4294967295 9, function 17 1, function 4294967295 0]
    let initial : Lean.RBMap Nat (Option TrustIr.FuncTyDef) compare := Lean.mkRBMap ..
    let headers := functions.foldl (fun table function =>
      if table.contains function.id.index then table
      else table.insert function.id.index ((trustIrArrayGet? signatures function.ty.index))) initial
    (headers.find? query.index).join =
      TrustIr.GenericCoro.ModuleFactory.directHeaders
        (TrustIr.GenericCoro.ModuleFactory.headerIndex signatures functions) query :=
  TrustIr.GenericCoro.HeaderMaps.original_fold_classifier signatures _ query

theorem first_missing_function_signature_not_recovered :
    TrustIr.GenericCoro.ModuleFactory.directHeaders
      (TrustIr.GenericCoro.ModuleFactory.headerIndex signatures
        [function 4294967295 9, function 17 1, function 4294967295 0]) ⟨4294967295⟩ = none := rfl

def module : TrustIrEval.Module :=
  {functions := [function 4294967295 9, function 17 1, function 4294967295 0],
    funcTys := signatures.toList, globals := [], enums := [], structs := [], types := []}

theorem actual_original_helper_duplicate_control :
    (TrustIrEval.localTypeHeadersOf module).2 ⟨4294967295⟩ = none ∧
      (TrustIrEval.localTypeHeadersOf module).2 ⟨17⟩ = (trustIrArrayGet? signatures 1) ∧
      (TrustIrEval.localTypeHeadersOf module).2 ⟨18⟩ = none := ⟨rfl, rfl, rfl⟩

theorem actual_original_helper_instantiates_classifier_bridge :
    TrustIrEval.localTypeHeadersOf module =
      (module.funcTys.toArray,
        TrustIr.GenericCoro.ModuleFactory.directHeaders
          (TrustIr.GenericCoro.ModuleFactory.headerIndex module.funcTys.toArray module.functions)) :=
  TrustIr.GenericCoro.HeaderMaps.localTypeHeadersOf_eq module

end TrustIr.NatRBMapInsert.Controls
