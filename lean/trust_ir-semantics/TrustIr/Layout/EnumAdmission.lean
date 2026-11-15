-- Copyright 2026 Andrew Yates | Apache-2.0
import TrustIr.Layout.Index

namespace TrustIr.SourceLayout

/-- Sparse, source-order ID admission. A repeated physical enum ID refuses,
    including a repeated identical definition. This checks original rows,
    never a deduplicated lookup table or a producer-supplied validity bit.
    Every admitted ID also belongs to Rust's u32 nominal namespace. -/
def enumIdScan (seen : NatIndexTree Unit) : List EnumDef → Bool
  | [] => true
  | row :: rest =>
    if row.id.index < 2 ^ 32 then
      match seen.find row.id.index with
      | some _ => false
      | none => enumIdScan (seen.insert row.id.index ()) rest
    else false

def enumIdsAdmitted (rows : List EnumDef) : Bool := enumIdScan .empty rows

end TrustIr.SourceLayout
