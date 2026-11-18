-- Copyright 2026 Andrew Yates | Apache-2.0
-- Proof-input wire DATA. This is not a program AST or a new evaluator.
-- An untrusted proposer supplies syntax; the kernel can check its exact compact
-- byte spelling before the total decoder constructs the canonical Module.
import TrustIrEval.ClosureDecode

namespace TrustIrEval.ClosureWire
open Lean TrustIr

inductive Syntax where
  | null
  | bool (value : Bool)
  | nat (value : Nat)
  | string (value : String)
  | array (values : List Syntax)
  | object (fields : List (String × Syntax))
  deriving Inhabited

/-- Explicit ASCII wire subset. Unsupported Unicode/control spellings refuse;
    no quoting, escaping or normalization is delegated to an opaque parser. -/
def quotedAscii (value : String) : D String := do
  let pieces ← value.toList.mapM (fun ch =>
    if ch == '"' then pure "\\\""
    else if ch == '\\' then pure "\\\\"
    else if ch == '\n' then pure "\\n"
    else if ch == '\r' then pure "\\r"
    else if ch == '\t' then pure "\\t"
    else if 32 ≤ ch.toNat && ch.toNat < 127 then pure (String.singleton ch)
    else unsupported "closure_wire.ascii_string")
  pure ("\"" ++ String.join pieces ++ "\"")

/-- Construct the standard Lean Json value and its exact compact wire together.
    Object order stays in the wire; duplicate keys refuse before mkObj could
    discard their occurrence. The bound is syntax depth, never evaluator fuel. -/
def materialize : Nat → Syntax → D (String × Json)
  | 0, _ => unsupported "closure_wire.depth"
  | fuel + 1, input => do
    match input with
    | .null => pure ("null", Json.null)
    | .bool value => pure (if value then "true" else "false", Json.bool value)
    | .nat value => pure (toString value, toJson value)
    | .string value => pure (← quotedAscii value, Json.str value)
    | .array values =>
      let values ← values.mapM (materialize fuel)
      pure ("[" ++ String.intercalate "," (values.map (·.1)) ++ "]",
        Json.arr (values.map (·.2)).toArray)
    | .object fields =>
      let names := fields.map (·.1)
      if names.eraseDups.length != names.length then
        unsupported "closure_wire.duplicate_key"
      let values ← fields.mapM (fun row => do
        let key ← quotedAscii row.1
        let (value, json) ← materialize fuel row.2
        pure (key ++ ":" ++ value, (row.1, json)))
      pure ("{" ++ String.intercalate "," (values.map (·.1)) ++ "}",
        Json.mkObj (values.map (·.2)))

def indent (level : Nat) : String := String.join (List.replicate level "  ")

def prettyRows (level : Nat) (left right : String) (rows : List String) : String :=
  if rows.isEmpty then left ++ right else
    left ++ "\n" ++ String.intercalate ",\n" (rows.map (fun row => indent (level + 1) ++ row)) ++
      "\n" ++ indent level ++ right

/-- The author's source-fixed mutant DATA uses direct serde pretty spelling.
    It retains the same ordered object/array grammar and duplicate-key guard;
    this is not Python normalization or a substituted compact artifact. -/
def materializePretty : Nat → Nat → Syntax → D (String × Json)
  | 0, _, _ => unsupported "closure_wire.depth"
  | fuel + 1, level, input => do
    match input with
    | .array values =>
      let values ← values.mapM (materializePretty fuel (level + 1))
      pure (prettyRows level "[" "]" (values.map (·.1)), Json.arr (values.map (·.2)).toArray)
    | .object fields =>
      let names := fields.map (·.1)
      if names.eraseDups.length != names.length then unsupported "closure_wire.duplicate_key"
      let values ← fields.mapM (fun row => do
        let key ← quotedAscii row.1
        let (value, json) ← materializePretty fuel (level + 1) row.2
        pure (key ++ ": " ++ value, (row.1, json)))
      pure (prettyRows level "{" "}" (values.map (·.1)), Json.mkObj (values.map (·.2)))
    | other => materialize (fuel + 1) other

/-- Pure extraction after a checked constructor tag. There is no default
    module/context and no assumed returning run hidden behind this accessor. -/
def checkedValue {α : Type} (result : D α) : result.toOption.isSome = true → α :=
  match result with
  | .ok value => fun _ => value
  | .error _ => fun impossible => nomatch impossible

theorem checkedValue_eq {α : Type} (result : D α) (checked : result.toOption.isSome = true) :
    result = .ok (checkedValue result checked) := by
  cases result with
  | ok value => rfl
  | error error => cases checked

/-- Exact wire comparison is mandatory. No native JSON parser, digest or
    successful source-producer label can establish this equality. -/
def decodeFrom (materializer : Syntax → D (String × Json))
    (actualWire : String) (proposed : Syntax) : D Module := do
  let (wire, json) ← materializer proposed
  if wire = actualWire then ClosureDecode.module json
  else malformed "closure_wire.bytes_mismatch"

def decode (depth : Nat) (wire : String) (proposed : Syntax) : D Module :=
  decodeFrom (materialize depth) wire proposed

def decodePretty (depth : Nat) (wire : String) (proposed : Syntax) : D Module :=
  decodeFrom (materializePretty depth 0) wire proposed

/-- A successful total decode uses the actual wire and the actual standard
    Json value produced with it. This is a codec fact, not a returning-run or
    source-refinement premise, and returns no admission capability. -/
theorem decodeFrom_uses_exact_wire (materializer : Syntax → D (String × Json))
    (wire : String) (proposed : Syntax) (decoded : Module)
    (actual : decodeFrom materializer wire proposed = .ok decoded) :
    ∃ json, materializer proposed = .ok (wire, json) ∧
      ClosureDecode.module json = .ok decoded := by
  unfold decodeFrom at actual
  cases held : materializer proposed with
  | error error => simp only [held, bind, Except.bind] at actual <;> cases actual
  | ok pair =>
    obtain ⟨encoded, json⟩ := pair
    simp only [held, bind, Except.bind] at actual
    by_cases same : encoded = wire
    · subst encoded
      exact ⟨json, rfl, by simpa using actual⟩
    · simp only [if_neg same] at actual <;>
        change Except.error (DecodeError.malformed "closure_wire.bytes_mismatch") =
          Except.ok decoded at actual <;> cases actual

theorem decode_uses_exact_wire (depth : Nat) (wire : String) (proposed : Syntax)
    (decoded : Module) (actual : decode depth wire proposed = .ok decoded) :
    ∃ json, materialize depth proposed = .ok (wire, json) ∧
      ClosureDecode.module json = .ok decoded :=
  decodeFrom_uses_exact_wire _ _ _ _ actual

theorem decodePretty_uses_exact_wire (depth : Nat) (wire : String) (proposed : Syntax)
    (decoded : Module) (actual : decodePretty depth wire proposed = .ok decoded) :
    ∃ json, materializePretty depth 0 proposed = .ok (wire, json) ∧
      ClosureDecode.module json = .ok decoded :=
  decodeFrom_uses_exact_wire _ _ _ _ actual

#print axioms decodeFrom_uses_exact_wire
end TrustIrEval.ClosureWire
