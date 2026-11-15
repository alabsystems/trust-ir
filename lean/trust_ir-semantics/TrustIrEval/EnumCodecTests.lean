-- Copyright 2026 Andrew Yates | Apache-2.0
import TrustIrRuntime
import TrustIr.DecodedContext
import TrustIrEval.EnumAdmission

namespace TrustIrEval.EnumCodecTests
open Lean (Json toJson)
open TrustIr

private def resultError (error : SemError) : Json := toJson (toString (repr error))

private def runDocument (document : Json) : D Json := do
  let wire ← field document "module"
  let decoded ← TrustIrEval.module wire
  let admitted ← enumAdmission wire
  let ctx ← contextOf decoded 128
  let service ← match ctx.memoryService with
    | some service => pure service
    | none => malformed "enum codec: actual decoded memory service is absent"
  let mut answers := []
  for request in ← listField document "queries" do
    let id : EnumId := ⟨← natField request "id"⟩
    let width ← natField request "width"
    let raw ← wideInt "tag.raw" (← field request "raw")
    let (payload,detailed) ← match request.getObjVal? "payload" with
      | .error _ => pure ([],false)
      | .ok entries => do
        let fields ← (← arr "payload" entries).mapM (fun entry => do
          match entry.getObjVal? "bool" with
          | .ok value => pure (Value.bool (← bool "payload.bool" value))
          | .error _ => pure (Value.int (← natField entry "width") (← wideInt "payload.raw" (← field entry "raw"))))
        pure (fields,true)
    let value := Value.aggregate (Value.int width raw :: payload)
    let checked := checkClosureValueAt ctx 64 (.Enum id) value
    let checkRows := match checked with
      | .ok _ => [("checked",toJson true)]
      | .error error => [("checked",toJson false),("check_error",resultError error)]
    let rows := match service.query (.Enum id) with
      | .error error => ("plan_error",resultError error) :: checkRows
      | .ok plan =>
        match AggregateMemory.encode ctx.byteModel ctx.functionOrder plan value with
        | .error error => ("encoded",toJson false) :: ("encode_error",resultError error) :: checkRows
        | .ok image =>
          let decoded := match AggregateMemory.decode ctx.byteModel ctx.functionOrder Memory.empty plan image.bytes with
            | .ok (.aggregate (.int actualWidth actualRaw :: fields)) =>
              [("decoded_width",toJson actualWidth),("decoded_raw",toJson (toString actualRaw))] ++
              (if detailed then [("decoded_payload",Json.arr (fields.map (fun value => match value with
                | .int width raw => Json.mkObj [("width",toJson width),("raw",toJson (toString raw))]
                | .bool value => Json.mkObj [("bool",toJson value)]
                | _ => Json.null)).toArray)] else [])
            | .ok _ => [("decode_error",toJson "unexpected decoded value form")]
            | .error error => [("decode_error",resultError error)]
          ("encoded",toJson true) :: ("image_size",toJson image.bytes.size) :: (checkRows ++ decoded ++
            (if detailed then [("encoded_bytes",toJson ((List.range image.bytes.size).map (fun index =>
              (image.bytes.get index).map UInt8.toNat)))] else []))
    answers := Json.mkObj (("admitted",toJson admitted) :: rows) :: answers
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
    | .ok answer => answers := answer :: answers
    | .error error => throw (IO.userError (toString (repr error)))
  IO.println ((Json.arr answers.reverse.toArray).compress)
end TrustIrEval.EnumCodecTests

def main (args : List String) : IO Unit := do
  match args with
  | [path] => TrustIrEval.EnumCodecTests.run path
  | _ => throw (IO.userError "usage: EnumCodecTests request.json")
