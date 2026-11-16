-- Copyright 2026 Andrew Yates | Apache-2.0
import TrustIrEval.RawJson
import TrustIrEval.Run

namespace TrustIrEval.RawBoundary
open Lean (Json)
open TrustIr
private abbrev RawNode := RawJson.Node

private def malformedRaw {α : Type} (message : String) : D α :=
  malformed s!"raw serde: {message}"

private def fieldCheck (node : RawNode) (name : String) (check : RawNode → D Unit) : D Unit :=
  match node.field? name with
  | none => pure () -- The unchanged schema decoder reports missing fields.
  | some child => check child

private def each (node : RawNode) (check : RawNode → D Unit) : D Unit :=
  node.elements.forM check
private def rows (node : RawNode) (name : String) (check : RawNode → D Unit) : D Unit :=
  fieldCheck node name (fun children => each children check)

/-- Only unsigned INTEGER lexemes denote serde u32/u64, including when an
    exponent or negative zero would erase to a nonnegative native Json number. -/
private def unsigned (context : String) (bits : Nat) (node : RawNode) : D Unit := do
  match node with
  | .scalar _ value (some token) =>
    if token.isEmpty || !token.toList.all (fun char => '0' ≤ char && char ≤ '9') then
      malformedRaw s!"{context}: expected unsigned JSON integer token"
    let n ← nat context value
    if n ≥ 2 ^ bits then malformedRaw s!"{context}: outside u{bits} range"
  | _ => malformedRaw s!"{context}: expected unsigned JSON integer token"

private def storage (node : RawNode) : D Unit := do
  match node with
  | .array _ [size, alignment] =>
    unsigned "Storage.size_bytes" 64 size
    unsigned "Storage.align_bytes" 64 alignment
  | .array _ _ => malformedRaw "Storage: expected a 2-tuple"
  | .object _ fields =>
    let mut seenSize := false
    let mut seenAlign := false
    for (name, _, value) in fields do
      if name == "size_bytes" then
        if seenSize then malformedRaw "Storage: duplicate field size_bytes"
        unsigned "Storage.size_bytes" 64 value
        seenSize := true
      else if name == "align_bytes" then
        if seenAlign then malformedRaw "Storage: duplicate field align_bytes"
        unsigned "Storage.align_bytes" 64 value
        seenAlign := true
      -- Unknown fields, even repeated names and nested pseudo-types, are ignored.
    if !seenSize then malformedRaw "Storage: missing field size_bytes"
    if !seenAlign then malformedRaw "Storage: missing field align_bytes"
  | _ => malformedRaw "Storage: expected a record or 2-tuple"

private def taggedNode (context : String) (node : RawNode) : D (Option (String × RawNode)) := do
  match node with
  | .object _ [(name, _, payload)] => pure (some (name, payload))
  | .object _ _ => malformedRaw s!"{context}: expected a single-variant object"
  | _ => pure none -- Unit tags and wrong shapes retain the old decoder's result.

private partial def type (node : RawNode) : D Unit := do
  match node with
  | .scalar _ (.str tag) _ =>
    if tag == "Storage" || tag == "FnItem" then malformedRaw s!"{tag}: missing payload"
  | _ => pure ()
  match ← taggedNode "Ty" node with
  | none => pure ()
  | some (tag, payload) =>
    match tag with
    | "Storage" => storage payload
    | "FnItem" => unsigned "FnItem" 32 payload
    | "Tuple" => each payload type
    | "Vector" =>
      match payload.elements with
      | child :: _ => type child
      | [] => pure ()
    | "Ref" | "RefMut" | "PtrConst" | "PtrMut" | "Rc" => type payload
    | _ => pure ()

private partial def constant (node : RawNode) : D Unit := do
  match node with
  | .scalar _ (.str "FnItem") _ => malformedRaw "Constant.FnItem: missing payload"
  | _ => pure ()
  match ← taggedNode "Constant" node with
  | none => pure ()
  | some (tag, payload) =>
    match tag with
    | "FnItem" => unsigned "Constant.FnItem" 32 payload
    | "Aggregate" | "Array" | "Vector" | "Sequence" | "Set" => each payload constant
    | "Splat" => fieldCheck payload "elem" constant
    | "Record" => each payload (fun row =>
      match row.elements with
      | _ :: child :: _ => constant child
      | _ => pure ())
    | "Closure" => rows payload "captures" constant
    | _ => pure ()

private def binding (node : RawNode) : D Unit :=
  rows node "slots" (fun slot => fieldCheck slot "ty" type)

-- This table is audited against all34 actual inst branches/37 inline t-fields.
private def instTypeFields : String → List String
  | "BinOp" => ["ty"]
  | "UnOp" => ["ty"]
  | "Overflow" => ["ty"]
  | "ICmp" => ["ty"]
  | "FCmp" => ["ty"]
  | "Cast" => ["src_ty", "dst_ty"]
  | "Load" => ["ty"]
  | "Store" => ["ty"]
  | "Alloca" => ["ty"]
  | "HeapAlloc" => ["ty"]
  | "GEP" => ["pointee_ty"]
  | "PtrData" => ["ptr_ty"]
  | "PtrMetadata" => ["ptr_ty", "metadata_ty"]
  | "PtrFromParts" => ["ptr_ty", "metadata_ty"]
  | "AtomicLoad" => ["ty"]
  | "AtomicStore" => ["ty"]
  | "AtomicRMW" => ["ty"]
  | "CmpXchg" => ["ty"]
  | "ExtractField" => ["ty"]
  | "InsertField" => ["ty"]
  | "ArraySplat" => ["ty"]
  | "MakeAggregate" => ["ty"]
  | "ExtractElement" => ["ty"]
  | "InsertElement" => ["ty"]
  | "Const" => ["ty"]
  | "Undef" => ["ty"]
  | "Copy" => ["ty"]
  | "Select" => ["ty"]
  | "SeqMapAddK" => ["ty"]
  | "SeqMapNot" => ["ty"]
  | "SeqMap" => ["ty"]
  | "Drop" => ["ty"]
  | "DropInvoke" => ["ty"]
  | "LoadSlot" => ["ty"]
  | _ => []

private def instruction (node : RawNode) : D Unit := do
  match ← taggedNode "Inst" node with
  | none => pure ()
  | some (tag, payload) =>
    (instTypeFields tag).forM (fun name => fieldCheck payload name type)
    match tag with
    | "Const" => fieldCheck payload "value" constant
    | "Switch" => rows payload "cases" (fun row => fieldCheck row "value" constant)
    | "OpenFrame" => fieldCheck payload "def" binding
    | "DialectOp" => rows payload "result_tys" type
    | _ => pure ()

private def block (node : RawNode) : D Unit := do
  rows node "params" (fun parameter =>
    match parameter.elements with
    | _ :: ty :: _ => type ty
    | _ => pure ())
  rows node "body" (fun row => fieldCheck row "inst" instruction)

private def module (node : RawNode) : D Unit := do
  rows node "functions" (fun function => rows function "blocks" block)
  rows node "func_types" (fun signature => do
    rows signature "params" type
    rows signature "returns" type)
  rows node "closure_types" (fun closure => rows closure "captures" type)
  rows node "globals" (fun global => do
    fieldCheck global "ty" type
    fieldCheck global "initializer" constant)
  rows node "enums" (fun enumeration =>
    rows enumeration "variants" (fun variant => rows variant "fields" type))
  rows node "structs" (fun definition =>
    rows definition "fields" (fun field => fieldCheck field "ty" type))
  rows node "records" (fun record =>
    rows record "fields" (fun field => fieldCheck field "ty" type))
  rows node "types" type
  rows node "drop_glue" (fun row => fieldCheck row "ty" type)

private def subst (node : RawNode) : D Unit := do
  fieldCheck node "ty" type
  rows node "params" type
  rows node "holes" type
  fieldCheck node "expected" type

private def paired (raw : RawNode) (values : List Json) : D (List (RawNode × Json)) := do
  let nodes := raw.elements
  if nodes.length != values.length then malformedRaw "array projection mismatch"
  pure (nodes.zip values)

private def rawField (raw : RawNode) (name : String) : D RawNode :=
  match raw.field? name with
  | some node => pure node
  | none => malformedRaw s!"missing metadata for projected field {name}"

-- The actual Run.batch prefix below is copied verbatim through the choices
-- calculation. Only the module ingress is extended; no evaluation is copied.
private def batch (raw : RawNode) (j : Json) : D Batch := do
  let rows ← listField j "runs"
  let runs ← rows.mapM (fun r => do
    pure (← funcId "function" (← field r "function"),
          ← (← listField r "args").mapM argValue))
  let choices ← rows.mapM (fun r => do
    match r.getObjVal? "float_zero_choices" with
    | .error _ => pure []
    | .ok value =>
      (← arr "float_zero_choices" value).mapM (fun item =>
        match item with
        | .bool value => pure value
        | _ => malformed "float_zero_choices: expected Boolean entries"))
  let wire ← field j "module"
  module (← rawField raw "module")
  pure { module := ← TrustIrEval.module wire, runs := runs, floatZeroChoices := choices }

private def batches (raw : RawNode) (j : Json) : D (List Batch) := do
  let projected ← listField j "batches"
  let pairs ← paired (← rawField raw "batches") projected
  pairs.mapM (fun (raw, value) => batch raw value)

-- Header expressions and their field order are exactly Run.request's.
private def request (raw : RawNode) (j : Json) : D Request := do
  pure { fuel := ← natField j "fuel"
         callDepth := ← natField j "call_depth"
         strategy := ← panicStrategyField j
         batches := ← batches raw j }

private def checkedRows (raw : RawNode) (key : String) (values : List Json)
    (check : RawNode → D Unit) (run : Json → D Json) : Json :=
  match do paired (← rawField raw key) values with
  | .error error => renderDecodeError error
  | .ok pairs => .arr (pairs.map (fun (node, value) =>
      match do check node; run value with
      | .ok value => value
      | .error error => renderDecodeError error)).toArray

/-- Same native projected selector/array priority and row cardinality as Run. -/
private def runRequest (raw : RawNode) (j : Json) : Json :=
  match j.getObjVal? "template_subst" with
  | .ok (.arr cases) => checkedRows raw "template_subst" cases.toList subst substCase
  | _ =>
    match j.getObjVal? "enum_id_admission" with
    | .ok (.arr documents) =>
      checkedRows raw "enum_id_admission" documents.toList module (fun document => do
        pure (obj [("enum_ids_admitted", .bool (← enumAdmission document))]))
    | .ok _ => renderDecodeError (.malformed "enum_id_admission: expected array")
    | .error _ =>
      match request raw j with
      | .error error => renderDecodeError error
      | .ok req => .arr (req.batches.map (runBatch req.fuel req.callDepth req.strategy)).toArray

/-- Native syntax errors retain their old message; metadata errors never fall back. -/
def runText (contents : String) : Json :=
  match RawJson.parse contents with
  | .error (.syntax error) => obj [("error", jstr s!"request is not JSON: {error}")]
  | .error (.correspondence error) => obj [("error", jstr s!"raw JSON correspondence: {error}")]
  | .ok document => runRequest document.raw document.json

end TrustIrEval.RawBoundary
