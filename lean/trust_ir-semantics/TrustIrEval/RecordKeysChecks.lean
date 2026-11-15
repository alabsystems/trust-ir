-- Copyright 2026 Andrew Yates | Apache-2.0
-- Functional decoder fixtures; not proof authority for native execution.
import TrustIrEval.RecordKeysReplay

namespace TrustIrEval.RecordKeysChecks
open Lean (Json)
open TrustIr

private def record (id : Json) (fields : Array Json) (name : Json := .str "Record") : Json :=
  Json.mkObj [("id", id), ("name", name), ("fields", .arr fields)]

private def field (ty : String) : Json := Json.mkObj [("name", .str "value"), ("ty", .str ty)]
private def number (value : Nat) : Json := Lean.toJson value

private def document (records : Array Json) : Json :=
  Json.mkObj [("functions", .arr #[]), ("func_types", .arr #[]), ("globals", .arr #[]),
    ("enums", .arr #[]), ("structs", .arr #[]), ("types", .arr #[]), ("records", .arr records)]

private def coherent (decoded : Module) : Bool :=
  decoded.records.all (fun (key, payload) => payload.all (fun definition => definition.id == key))

private def check (label : String) (input : Json) (expected : D Module → Bool) : IO Unit := do
  let parsed := module input
  unless expected parsed do throw (IO.userError s!"record-key fixture failed: {label}")
  match parsed with
  | .error _ => pure ()
  | .ok decoded =>
      unless coherent decoded do throw (IO.userError s!"incoherent retained record: {label}")

def runChecks : IO Unit := do
  check "supported-field" (document #[record (number 7) #[field "U8"]]) (fun parsed =>
    match parsed with
    | .ok decoded => match decoded.records with
      | [(key, some definition)] => key.index == 7 && definition.id.index == 7 &&
          definition.fields.any (fun f => match f.ty with | .U8 => true | _ => false)
      | _ => false
    | _ => false)
  check "sparse-id" (document #[record (number 65537) #[]]) (fun parsed =>
    match parsed with
    | .ok decoded => match decoded.records with
      | [(key, some definition)] => key.index == 65537 && definition.id.index == 65537
      | _ => false
    | _ => false)
  check "unsupported-row-retained" (document #[record (number 7) #[field "FutureType"]]) (fun parsed =>
    match parsed with
    | .ok decoded => match decoded.records with | [(key, none)] => key.index == 7 | _ => false
    | _ => false)
  check "unsupported-first-shadow" (document #[record (number 7) #[field "FutureType"], record (number 7) #[]])
    (fun parsed => match parsed with
    | .ok decoded => match decoded.records, contextOf decoded 0 with
      | [(_, none), (_, some _)], .ok ctx => (ctx.records ⟨7⟩).isNone
      | _, _ => false
    | _ => false)
  check "duplicate-first-kept" (document #[record (number 7) #[], record (number 7) #[field "U8"]])
    (fun parsed => match parsed with
    | .ok decoded => match decoded.records, contextOf decoded 0 with
      | [(_, some _), (_, some _)], .ok ctx => (ctx.records ⟨7⟩).any (fun d => d.fields.isEmpty)
      | _, _ => false
    | _ => false)
  check "malformed-id-before-unsupported-fields"
    (document #[record (.str "not-an-id") #[field "FutureType"]])
    (fun parsed => match parsed with | .error (.malformed _) => true | _ => false)
  check "malformed-name" (document #[record (number 7) #[] (.bool true)])
    (fun parsed => match parsed with | .error (.malformed _) => true | _ => false)
  IO.println "WIRE_RECORD_KEYS_NATIVE_PASS cases=7"

end TrustIrEval.RecordKeysChecks

/-- info: WIRE_RECORD_KEYS_NATIVE_PASS cases=7 -/
#guard_msgs in
#eval TrustIrEval.RecordKeysChecks.runChecks
