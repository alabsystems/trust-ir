-- Correctness-only control for one frozen integer-only eight-block module.
-- It constructs the real context and queries its converted function's CFG.
import TrustIrRuntime
import TrustIrEval.Run

open TrustIr TrustIrEval

private def number (value : Nat) : Lean.Json := Lean.toJson value
private def object (fields : List (String × Lean.Json)) : Lean.Json := Lean.Json.mkObj fields
private def ids (values : List ValueId) : Lean.Json := .arr (values.map (fun id => number id.index)).toArray

private def requireDecoded {α : Type} (label : String) (value : D α) : IO α :=
  match value with
  | .ok result => pure result
  | .error error => throw (IO.userError s!"{label}: {repr error}")

/-- Only constructors present in the fixed queried rows are admitted here.
    Full IDs, values, targets and argument lists are represented explicitly. -/
private def instruction : Inst → Except String Lean.Json
  | .Const .I32 (.int value) => pure (object [("constructor", .str "Const"),
      ("ty", .str "I32"), ("integer", .str (toString value))])
  | .ICmp .Ne .I32 lhs rhs => pure (object [("constructor", .str "ICmp"),
      ("op", .str "Ne"), ("ty", .str "I32"), ("lhs", number lhs.index), ("rhs", number rhs.index)])
  | .Br target args => pure (object [("constructor", .str "Br"),
      ("target", number target.index), ("args", ids args)])
  | .CondBr cond yes yesArgs no noArgs => pure (object [("constructor", .str "CondBr"),
      ("condition", number cond.index), ("then_target", number yes.index), ("then_args", ids yesArgs),
      ("else_target", number no.index), ("else_args", ids noArgs)])
  | _ => .error "mapping probe: unexpected instruction outside fixed fixture"

private def block (value : BasicBlock) : Except String Lean.Json := do
  let params ← value.params.mapM fun (id, ty) =>
    match ty with
    | .I32 => pure (object [("id", number id.index), ("ty", .str "I32")])
    | _ => .error "mapping probe: unexpected parameter type"
  let body ← value.body.mapM instruction
  let term ← instruction value.terminator
  pure (object [("params", .arr params.toArray), ("body", .arr body.toArray),
    ("body_result_destinations", .arr (value.bodyResultDests.map ids).toArray),
    ("terminator", term), ("terminator_result_destinations", ids value.terminatorResultDests)])

private def optionalBlock (value : Option BasicBlock) : Except String Lean.Json :=
  match value with | none => pure .null | some value => block value
private def decodedBlock (value : Except String Lean.Json) : IO Lean.Json :=
  match value with
  | .ok value => pure value
  | .error error => throw (IO.userError error)
private def coarse : Option BasicBlock → Nat
  | none => 0
  | some value => 1 + value.params.length + value.body.length +
      value.bodyResultDests.length + value.terminatorResultDests.length

private def observed (mode : String) (cfg : CFG) (query : Nat) : Option BasicBlock :=
  if mode == "swap34" then
    if query == 3 then cfg ⟨4⟩ else if query == 4 then cfg ⟨3⟩ else cfg ⟨query⟩
  else if mode == "duplicate3at4" && query == 4 then cfg ⟨3⟩
  else cfg ⟨query⟩

private def fixtureRows (rows : List (BlockId × BasicBlock)) : IO Unit := do
  unless rows.length == 8 do throw (IO.userError "mapping probe: expected eight rows")
  let some third := TrustIrEval.cfgOf rows ⟨3⟩ | throw (IO.userError "mapping probe: missing raw row3")
  let some fourth := TrustIrEval.cfgOf rows ⟨4⟩ | throw (IO.userError "mapping probe: missing raw row4")
  unless third.params.map (fun p => p.1.index) == [8, 9] &&
      fourth.params.map (fun p => p.1.index) == [10, 11] do
    throw (IO.userError "mapping probe: frozen parameter IDs changed")
  match third.terminator, fourth.terminator with
  | .Br target args, .Br other later =>
    unless target.index == 4 && args.map (·.index) == [8, 9] &&
        other.index == 5 && later.map (·.index) == [10, 11] do
      throw (IO.userError "mapping probe: frozen branch identities changed")
  | _, _ => throw (IO.userError "mapping probe: expected two distinct raw Br rows")
  unless coarse (some third) == 3 && coarse (some fourth) == 3 do
    throw (IO.userError "mapping probe: coarse-sample blindspot disappeared")

def main (argv : List String) : IO UInt32 := do
  let [path, mode] := argv | throw (IO.userError "usage: REQUEST.json actual|swap34|duplicate3at4")
  unless ["actual", "swap34", "duplicate3at4"].contains mode do throw (IO.userError "mapping probe mode")
  let sourceText ← IO.FS.readFile path
  let request ← match Lean.Json.parse sourceText with
    | .ok value => pure value
    | .error error => throw (IO.userError error)
  let [batch] ← requireDecoded "batches" (listField request "batches")
    | throw (IO.userError "mapping probe: one batch required")
  let source ← requireDecoded "module" (do TrustIrEval.module (← field batch "module"))
  let [raw] := source.functions | throw (IO.userError "mapping probe: one source function required")
  unless raw.id.index == 0 && raw.name == "cfg_64_8_0_dense" && !raw.isDeclaration do
    throw (IO.userError "mapping probe: frozen source identity changed")
  let rows ← requireDecoded "raw blocks" raw.blocks
  fixtureRows rows
  let ctx ← requireDecoded "actual context" (contextOf source 8)
  unless ctx.byteModel == .le64 do throw (IO.userError "mapping probe: expected64 context")
  let some converted := ctx.functions ⟨0⟩ | throw (IO.userError "mapping probe: actual converted function absent")
  let mut observations : Array Lean.Json := #[]
  for query in [0, 3, 4, 7, 4294967294] do
    let expectedRaw := TrustIrEval.cfgOf rows ⟨query⟩
    let actualRaw := observed mode converted.cfg query
    let expected ← decodedBlock (optionalBlock expectedRaw)
    let actual ← decodedBlock (optionalBlock actualRaw)
    let row := object [("query", number query), ("expected", expected), ("actual", actual),
      ("expected_coarse", number (coarse expectedRaw)), ("actual_coarse", number (coarse actualRaw))]
    observations := observations.push row
    if actual != expected then
      IO.eprintln s!"mapping mismatch at block{query} mode={mode}"
      IO.println (Lean.Json.compress (object [("pass", .bool false), ("mode", .str mode),
        ("mismatch_query", number query), ("observations", .arr observations)]))
      return 1
  IO.println (Lean.Json.compress (object [("pass", .bool true), ("mode", .str mode),
    ("observations", .arr observations), ("scope", .str "one frozen module; five actual converted CFG lookups")]))
  return 0
