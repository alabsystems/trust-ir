-- Copyright 2026 Andrew Yates | Apache-2.0
import TrustIrRuntime
import TrustIrEval.SourceLayoutSchema
import TrustIr.Semantics.AggregatePlans

namespace TrustIrEval.EnumPlanTests
open Lean (Json toJson)
open TrustIr AggregateMemory

mutual
  private def planJson (plan : Plan) : Json :=
    let layout := plan.layout
    let details := match plan with
      | .leaf _ _ => [("kind",toJson "leaf")]
      | .fields _ _ fields => [("kind",toJson "fields"),("fields",Json.arr (fieldsRows fields).toArray)]
      | .array _ _ count element => [("kind",toJson "array"),("count",toJson count),("element",planJson element)]
      | .enumeration _ _ info variants => [("kind",toJson "enum"),("flags",toJson info.uninhabited),
          ("variants",Json.arr (variantRows variants).toArray)]
    Json.mkObj ([("size",toJson layout.size),("align",toJson layout.alignment)] ++ details)
  termination_by sizeOf plan
  private def fieldsRows (fields : List (Nat × Plan)) : List Json :=
    match fields with
    | [] => []
    | (offset,plan) :: rest => Json.mkObj [("offset",toJson offset),("plan",planJson plan)] :: fieldsRows rest
  termination_by sizeOf fields
  private def variantRows (variants : List (Option (List (Nat × Plan)))) : List Json :=
    match variants with
    | [] => []
    | none :: rest => Json.null :: variantRows rest
    | some fields :: rest => Json.arr (fieldsRows fields).toArray :: variantRows rest
  termination_by sizeOf variants
end

private def answer (service : Service) (ty : Ty) : Json :=
  let (result,work) := service.queryWithWork ty
  let row := match result with
    | .ok plan => [("ok",planJson plan)]
    | .error error => [("error",toJson (toString (repr error)))]
  Json.mkObj (("work",toJson work) :: row)

private def runDocument (document : Json) : D Json := do
  let source ← SourceLayoutSchema.environment (← field document "module")
  let mut accumulated := []
  for request in ← listField document "queries" do
    accumulated := (← TrustIrEval.ty (← field request "ty")) :: accumulated
  let types := accumulated.reverse
  let cold := AggregateMemory.prepare source []
  let warm := AggregateMemory.prepare source types
  pure (Json.arr (types.map (fun ty => Json.mkObj [("cold",answer cold ty),("warm",answer warm ty)])).toArray)

def run (path : String) : IO Unit := do
  let contents ← IO.FS.readFile path
  let document ← match Json.parse contents with
    | .ok value => pure value
    | .error error => throw (IO.userError error)
  let documents ← match document.getArr? with
    | .ok rows => pure rows.toList
    | .error error => throw (IO.userError error)
  let mut answers := []
  for document in documents do
    match runDocument document with
    | .ok result => answers := result :: answers
    | .error error => throw (IO.userError (toString (repr error)))
  IO.println ((Json.arr answers.reverse.toArray).compress)
end TrustIrEval.EnumPlanTests

def main (args : List String) : IO Unit := do
  match args with
  | [path] => TrustIrEval.EnumPlanTests.run path
  | _ => throw (IO.userError "usage: EnumPlanTests request.json")
