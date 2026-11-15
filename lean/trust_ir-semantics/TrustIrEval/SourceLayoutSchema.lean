-- Copyright 2026 Andrew Yates | Apache-2.0
import TrustIrEval.Decode
import TrustIr.Layout.Service

namespace TrustIrEval.SourceLayoutSchema
open Lean (Json)
open TrustIr
open TrustIr.SourceLayout

private def rows (document : Json) (name : String) : D (List Json) :=
  match document.getObjVal? name with
  | .ok value => arr name value
  | .error _ => pure []

private def word (document : Json) (name : String) : D Nat := do
  let value ← natField document name
  if value ≤ word64Max then pure value else malformed s!"{name}: outside u64"

def closureLayout (document : Json) : D ClosureLayoutDescriptor := do
  let closure ← natField document "closure"
  if closure ≥ 2 ^ 32 then malformed "closure: outside u32"
  let captureOffsets ← (← listField document "capture_offsets").mapM (fun value => do
    let offset ← nat "capture_offset" value
    if offset ≤ word64Max then pure offset else malformed "capture_offset: outside u64")
  pure { closure := ⟨closure⟩, size := ← word document "size", align := ← word document "align", captureOffsets }

/-- Decode only actual layout/source tables. Functions, CFGs, SSA metadata,
    globals and executable bodies are deliberately never inspected. No
    fabricated closure frame or tuple layout is installed in the evaluator. -/
def environment (document : Json) : D Environment := do
  let (model, canonical, present) ← match document.getObjVal? "target_info" with
    | .error _ | .ok .null => pure (.le64, true, false)
    | .ok target => do
      let bytes ← natField target "pointer_size"
      let little := (← strField target "endianness") == "Little"
      let model ← match ByteModel.ofRepresentation bytes little with
        | some model => pure model
        | none => unsupported "target.byte_model"
      let triple ← strField target "triple"
      let canonical := match model with
        | .le64 => true
        | .le32 => (triple.splitOn "-").headD "" == "wasm32"
      pure (model, canonical, true)
  let sourceTypes := (← rows document "types").map (fun value =>
    match ty value with | .ok value => some value | .error _ => none)
  let closures ← (← rows document "closure_types").mapM (fun row => do
    pure ({ func := ⟨← natField row "func"⟩, captures := ← (← listField row "captures").mapM ty } : ClosureTy))
  pure {
    model := model
    canonicalScalars := canonical
    hasTargetInfo := present
    types := sourceTypes
    structs := ← (← rows document "structs").mapM structDef
    enums := ← (← rows document "enums").mapM enumDef
    records := ← (← rows document "records").mapM recordDef
    closures := closures
    tupleLayouts := ← (← rows document "tuple_layouts").mapM tupleLayoutDescriptor
    closureLayouts := ← (← rows document "closure_layouts").mapM closureLayout }

end TrustIrEval.SourceLayoutSchema
