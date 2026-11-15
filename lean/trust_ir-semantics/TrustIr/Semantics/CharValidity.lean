-- Copyright 2026 Andrew Yates | Apache-2.0
import TrustIr.Semantics.LocalTypes
import TrustIr.Semantics.ClosureTypes

namespace TrustIr

trustIrDenseMatch
/-- Rust's top-level SSA validity rule: only a literal Char declaration and
    an integer payload are inspected. Width, poison and aggregate contents
    are not new policies at this boundary. -/
def checkSSACharValue : Ty → Value → Except SemError Unit
  | .Char, .int _ raw =>
    if raw < 0 then .error (.ub "char value is not a Unicode scalar value")
    else if validChar raw.toNat then .ok ()
    else .error (.ub "char value is not a Unicode scalar value")
  | _, _ => .ok ()

trustIrDenseMatch
def checkSSACharValues : List Ty → List Value → Except SemError Unit
  | [], [] => .ok ()
  | ty :: tys, value :: values => do
    checkSSACharValue ty value
    checkSSACharValues tys values
  | _, _ => .error (.typeError "SSA types: result/value count mismatch")

trustIrDenseMatch
/-- Resolve the bridge's actual ordered result classification. A manual
    context without declarations cannot invent a Borrow root's type. -/
def ssaResultSourceType (original : Option LocalTypeTable) :
    LocalTypeSource → Except SemError Ty
  | .declared ty => .ok ty
  | .borrow operand =>
    match original with
    | none => .error (.unsupported .ssaTypeTable
        "SSA result types: Borrow requires original declarations")
    | some table =>
      match table operand with
      | none => .error (.typeError "SSA types: borrowed value has no declaration")
      | some (.FatPtr kind) => .ok (.FatPtr kind)
      | some _ => .ok .Ptr

/-- Original tables are checked against the instruction's source declaration,
    including every actual destination. Only a genuinely absent manual table
    uses ordered instruction/header declarations directly. No runtime carrier
    supplies a type or an SSA association. -/
def ssaInstructionResultTypes (original : Option LocalTypeTable)
    (direct : FuncId → Option FuncTyDef) (indirect : FuncTyTable)
    (inst : Inst) (dests : List ValueId) (produced : Nat) : Except SemError (List Ty) := do
  let recorded ← match original with
    | none => pure none
    | some table => do
      if dests.length != produced then
        throw (.typeError "instruction result count mismatch")
      let types ← dests.mapM (fun dest => match table dest with
        | some ty => .ok ty
        | none => .error (.typeError "SSA types: result destination has no declaration"))
      pure (some types)
  let sources ← match localResultTypes direct indirect inst with
    | .ok sources => pure sources
    | .error _ => throw (.unsupported .ssaTypeTable
        "SSA result types: original callee header is unavailable")
  if sources.length != produced then
    throw (.typeError "SSA types: instruction result classification count mismatch")
  let expected ← sources.mapM (ssaResultSourceType original)
  match recorded with
  | none => pure expected
  | some recorded =>
    if (recorded.zip expected).any (fun pair => !(closureTyEq pair.fst pair.snd)) then
      throw (.typeError "SSA types: result destination conflicts with instruction declaration")
    else pure expected

end TrustIr

#trustIrAxiomsExact TrustIr.checkSSACharValue == []
#trustIrAxiomsExact TrustIr.checkSSACharValues == []
#trustIrAxiomsExact TrustIr.ssaResultSourceType == []
