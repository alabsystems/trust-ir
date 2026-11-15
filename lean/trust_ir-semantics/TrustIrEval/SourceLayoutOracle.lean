-- Copyright 2026 Andrew Yates | Apache-2.0
import TrustIrRuntime
import TrustIrEval.SourceLayoutSchema

namespace TrustIrEval.SourceLayoutOracle
open Lean (Json toJson)
open TrustIr
open TrustIr.SourceLayout

private def errorClass : Error → String
  | .missingType _ | .missingStruct _ | .missingEnum _ | .missingClosure _ => "missing"
  | .missingMetadata _ _ _ => "missing_metadata"
  | .incoherent _ _ => "incoherent"
  | .missingTarget _ | .scalarTarget => "target"
  | .sizeOverflow => "overflow"
  | .cycle _ => "cycle"
  | .unsupported _ => "unsupported"

private def jsonSummary (value : Summary) : Json := Json.mkObj [
  ("size", toJson value.size), ("align", toJson value.align),
  ("fields", toJson (value.fields.map (·.offset))),
  ("variants", toJson (value.enumeration.map (fun enumeration =>
    enumeration.variants.map (fun fields => fields.map (·.offset))))),
  ("uninhabited", toJson (value.enumeration.map (·.uninhabited))),
  ("tag_bits", toJson (value.enumeration.map (fun enumeration => tagBits enumeration.tag))),
  ("discriminants", toJson (value.enumeration.map (fun enumeration =>
    enumeration.discriminants.map toString)))]

private def answer (session : Session) (mode : Mode) (ty : Ty) : Json × Session :=
  match session.query mode ty with
  | .ok (value, session) => (Json.mkObj [("ok", jsonSummary value)], session)
  | .error error => (Json.mkObj [("error", toJson (errorClass error)),
      ("detail", toJson (toString (repr error)))], session)

private def runDocument (document : Json) : D Json := do
  let source ← SourceLayoutSchema.environment (← field document "module")
  let mut session := prepare source
  let mut answers := []
  for request in ← listField document "queries" do
    let modeName ← strField request "mode"
    if modeName == "validate_tuple_rows" || modeName == "validate_closure_rows" then
      let result := if modeName == "validate_tuple_rows" then validateTupleRows source else validateClosureRows source
      let answer := match result with
        | .ok () => Json.mkObj [("valid", toJson true)]
        | .error error => Json.mkObj [("error", toJson (errorClass error)), ("detail", toJson (toString (repr error)))]
      answers := answer :: answers
    else
      let mode ← match modeName with
        | "shape" => pure Mode.shape
        | "execution" => pure Mode.execution
        | other => malformed s!"unknown layout mode {other}"
      let ty ← TrustIrEval.ty (← field request "ty")
      let (result, next) := answer session mode ty
      session := next
      answers := result :: answers
  pure (Json.arr answers.reverse.toArray)

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

end TrustIrEval.SourceLayoutOracle

def main (args : List String) : IO Unit := do
  match args with
  | [path] => TrustIrEval.SourceLayoutOracle.run path
  | _ => throw (IO.userError "usage: SourceLayoutOracle request.json")
