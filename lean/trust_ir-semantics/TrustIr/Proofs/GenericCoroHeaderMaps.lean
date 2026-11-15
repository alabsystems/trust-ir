-- Copyright 2026 Andrew Yates | Apache-2.0
import TrustIr.Proofs.NatRBMapInsert
import TrustIr.Proofs.GenericCoroModuleFactory
import TrustIr.DecodedContext

namespace TrustIr.GenericCoro.HeaderMaps
open Lean TrustIrEval ModuleFactory

theorem firstValue_header (signatures : Array FuncTyDef) (functions : List Function) (query : Nat) :
    NatRBMapInsert.firstValue (fun function : Function => function.id.index)
      (fun function => (trustIrArrayGet? signatures function.ty.index)) functions query =
        ModuleFactory.firstHeader signatures functions query := by
  induction functions with
  | nil => rfl
  | cons head tail ih =>
    simp only [NatRBMapInsert.firstValue, ModuleFactory.firstHeader, ih]

/-- The exact original runner fold, proved against the actual producer's
    NatIndex classifier. Duplicate function ids and missing first signatures
    are included; there is no unique-id or successful-lookup premise. -/
theorem original_fold_classifier (signatures : Array FuncTyDef) (functions : List Function) (id : FuncId) :
    let initial : Lean.RBMap Nat (Option FuncTyDef) compare := Lean.mkRBMap ..
    let headers := functions.foldl (fun table function =>
      if table.contains function.id.index then table
      else table.insert function.id.index ((trustIrArrayGet? signatures function.ty.index))) initial
    (headers.find? id.index).join =
      ModuleFactory.directHeaders (ModuleFactory.headerIndex signatures functions) id := by
  trustIrCompilerProof {
    change ((NatRBMapInsert.firstWinsFrom (fun function : Function => function.id.index)
      (fun function => signatures.get? function.ty.index) functions (mkRBMap ..)).find? id.index).join = _
    rw [NatRBMapInsert.firstWins_empty_find, firstValue_header]
    simp only [ModuleFactory.directHeaders, ModuleFactory.headerIndex_find]
  } {
    change ((NatRBMapInsert.firstWinsFrom (fun function : Function => function.id.index)
      (fun function => (trustIrArrayGet? signatures function.ty.index)) functions (mkRBMap ..)).find? id.index).join = _
    rw [NatRBMapInsert.firstWins_empty_find, firstValue_header]
    simp only [ModuleFactory.directHeaders, ModuleFactory.headerIndex_find]
  }

/-- This names the actual original runner helper, moved verbatim into the
    pure context module. Both classifiers operate on the same original AST. -/
theorem localTypeHeadersOf_direct (module : TrustIrEval.Module) :
    (TrustIrEval.localTypeHeadersOf module).2 =
      ModuleFactory.directHeaders (ModuleFactory.headerIndex module.funcTys.toArray module.functions) := by
  funext id
  exact original_fold_classifier module.funcTys.toArray module.functions id

theorem localTypeHeadersOf_signatures (module : TrustIrEval.Module) :
    (TrustIrEval.localTypeHeadersOf module).1 = module.funcTys.toArray := rfl

theorem localTypeHeadersOf_eq (module : TrustIrEval.Module) :
    TrustIrEval.localTypeHeadersOf module =
      (module.funcTys.toArray,
        ModuleFactory.directHeaders (ModuleFactory.headerIndex module.funcTys.toArray module.functions)) := by
  apply Prod.ext
  · exact localTypeHeadersOf_signatures module
  · exact localTypeHeadersOf_direct module

end TrustIr.GenericCoro.HeaderMaps
