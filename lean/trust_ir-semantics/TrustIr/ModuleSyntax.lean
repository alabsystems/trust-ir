-- Copyright 2026 Andrew Yates | Apache-2.0
-- Original module data, independent of evaluation and source preparation.
import TrustIr.Inst

namespace TrustIr

/-- A basic block: parameters, body instructions, and terminator. -/
structure BasicBlock where
  params     : List (ValueId × Ty)     -- Block parameters
  body       : List Inst               -- Non-terminator instructions
  /-- Result destinations for `body`, positionally mirroring Rust
      `InstrNode.results`.  Older Lean fixtures that only rely on fresh
      sequential SSA ids leave this empty. -/
  bodyResultDests : List (List ValueId) := []
  terminator : Inst                    -- Terminator instruction
  /-- Result destinations for a value-producing TERMINATOR (`Inst.Invoke`:
      the callee's returns bind the invoke node's own results on the normal
      edge), mirroring Rust `InstrNode.results`. Empty for ordinary
      terminators. -/
  terminatorResultDests : List ValueId := []
  deriving Repr

/-- A module-level global's definition (type + optional initializer), carried by
    the evaluator context so `GlobalAddr` can reserve the global's TRUE byte size
    and write its initializer with full storage fidelity. Mirrors Rust `Global`. -/
structure GlobalDef where
  ty          : Ty
  initializer : Option Constant
  /-- The DECLARED over-alignment (`Global.align`), if any. -/
  align       : Option Nat := none

/-- A control flow graph: mapping from BlockId to BasicBlock. -/
def CFG := BlockId → Option BasicBlock

end TrustIr
