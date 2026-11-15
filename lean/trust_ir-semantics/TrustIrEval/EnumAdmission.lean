-- Copyright 2026 Andrew Yates | Apache-2.0
import TrustIrEval.Decode
import TrustIr.Layout.EnumAdmission

namespace TrustIrEval
open TrustIr.SourceLayout

/-- Recheck original physical enum IDs after actual module decoding. This
    checks distinct u32 IDs only; it is not a whole-module validator or a validity bit
    supplied by a producer. Parse failures retain their original class. -/
def enumAdmission (document : Lean.Json) : D Bool := do
  let decoded ← module document
  pure (enumIdsAdmitted decoded.enums)

end TrustIrEval
