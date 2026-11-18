-- Copyright 2026 Andrew Yates | Apache-2.0
-- Exact JSON byte DATA paired with the canonical evaluator projection.
-- No native parser, source-refinement or admission capability is used here.
import TrustIrEval.ClosureWire
namespace TrustIrEval.ClosureWireBytes
open Lean TrustIr ClosureWire
abbrev Wire := List UInt8

def quotedChars : List Char → D Wire
  | [] => pure []
  | ch :: rest => do
    let head ←
      if ch == '"' then pure [92, 34]
      else if ch == '\\' then pure [92, 92]
      else if ch == '\n' then pure [92, 110]
      else if ch == '\r' then pure [92, 114]
      else if ch == '\t' then pure [92, 116]
      else if 32 ≤ ch.toNat && ch.toNat < 127 then pure [UInt8.ofNat ch.toNat]
      else unsupported "closure_wire.ascii_string"
    pure (head ++ (← quotedChars rest))

def quoted (value : String) : D Wire := do
  pure ([34] ++ (← quotedChars value.toList) ++ [34])

def number (value : Nat) : Wire :=
  (toString value).toList.map (fun ch => UInt8.ofNat ch.toNat)

def joinTail (separator : Wire) : List Wire → Wire
  | [] => []
  | row :: rest => separator ++ row ++ joinTail separator rest

def join (separator : Wire) : List Wire → Wire
  | [] => []
  | row :: rest => row ++ joinTail separator rest

def spaces (level : Nat) : Wire := List.replicate (2 * level) 32

def prettyRows (level : Nat) (left right : Wire) (rows : List Wire) : Wire :=
  if rows.isEmpty then left ++ right else
    left ++ [10] ++ join [44, 10] (rows.map (fun row => spaces (level + 1) ++ row)) ++
      [10] ++ spaces level ++ right

def materialize : Nat → ClosureWire.Syntax → D (Wire × Json)
  | 0, _ => unsupported "closure_wire.depth"
  | fuel + 1, input => do
    match input with
    | .null => pure ([110, 117, 108, 108], Json.null)
    | .bool value => pure (if value then [116, 114, 117, 101] else [102, 97, 108, 115, 101], Json.bool value)
    | .nat value => pure (number value, toJson value)
    | .string value => pure (← quoted value, Json.str value)
    | .array values =>
      let values ← values.mapM (materialize fuel)
      pure ([91] ++ join [44] (values.map (·.1)) ++ [93], Json.arr (values.map (·.2)).toArray)
    | .object fields =>
      let names := fields.map (·.1)
      if names.eraseDups.length != names.length then unsupported "closure_wire.duplicate_key"
      let values ← fields.mapM (fun row => do
        let key ← quoted row.1
        let (value, json) ← materialize fuel row.2
        pure (key ++ [58] ++ value, (row.1, json)))
      pure ([123] ++ join [44] (values.map (·.1)) ++ [125], Json.mkObj (values.map (·.2)))

def materializePretty : Nat → Nat → ClosureWire.Syntax → D (Wire × Json)
  | 0, _, _ => unsupported "closure_wire.depth"
  | fuel + 1, level, input => do
    match input with
    | .array values =>
      let values ← values.mapM (materializePretty fuel (level + 1))
      pure (prettyRows level [91] [93] (values.map (·.1)), Json.arr (values.map (·.2)).toArray)
    | .object fields =>
      let names := fields.map (·.1)
      if names.eraseDups.length != names.length then unsupported "closure_wire.duplicate_key"
      let values ← fields.mapM (fun row => do
        let key ← quoted row.1
        let (value, json) ← materializePretty fuel (level + 1) row.2
        pure (key ++ [58, 32] ++ value, (row.1, json)))
      pure (prettyRows level [123] [125] (values.map (·.1)), Json.mkObj (values.map (·.2)))
    | other => materialize (fuel + 1) other

/-- The fixed byte renderer is mandatory, never supplied by a caller. -/
def decode (depth : Nat) (actual : Wire) (proposed : ClosureWire.Syntax) : D Module := do
  let (wire, json) ← materialize depth proposed
  if wire == actual then ClosureDecode.module json else malformed "closure_wire.bytes_mismatch"

def decodePretty (depth : Nat) (actual : Wire) (proposed : ClosureWire.Syntax) : D Module := do
  let (wire, json) ← materializePretty depth 0 proposed
  if wire == actual then ClosureDecode.module json else malformed "closure_wire.bytes_mismatch"

theorem decode_uses_exact_wire (depth : Nat) (wire : Wire) (proposed : ClosureWire.Syntax)
    (decoded : Module) (actual : decode depth wire proposed = .ok decoded) :
    ∃ json, materialize depth proposed = .ok (wire, json) ∧
      ClosureDecode.module json = .ok decoded := by
  unfold decode at actual
  cases held : materialize depth proposed with
  | error error => simp only [held, bind, Except.bind] at actual <;> cases actual
  | ok pair =>
    obtain ⟨encoded, json⟩ := pair
    simp only [held, bind, Except.bind] at actual
    by_cases same : encoded == wire
    · have equal : encoded = wire := eq_of_beq same
      subst encoded
      exact ⟨json, rfl, by simpa using actual⟩
    · simp only [if_neg same] at actual <;>
        change Except.error (DecodeError.malformed "closure_wire.bytes_mismatch") =
          Except.ok decoded at actual <;> cases actual

theorem decodePretty_uses_exact_wire (depth : Nat) (wire : Wire) (proposed : ClosureWire.Syntax)
    (decoded : Module) (actual : decodePretty depth wire proposed = .ok decoded) :
    ∃ json, materializePretty depth 0 proposed = .ok (wire, json) ∧
      ClosureDecode.module json = .ok decoded := by
  unfold decodePretty at actual
  cases held : materializePretty depth 0 proposed with
  | error error => simp only [held, bind, Except.bind] at actual <;> cases actual
  | ok pair =>
    obtain ⟨encoded, json⟩ := pair
    simp only [held, bind, Except.bind] at actual
    by_cases same : encoded == wire
    · have equal : encoded = wire := eq_of_beq same
      subst encoded
      exact ⟨json, rfl, by simpa using actual⟩
    · simp only [if_neg same] at actual <;>
        change Except.error (DecodeError.malformed "closure_wire.bytes_mismatch") =
          Except.ok decoded at actual <;> cases actual

#print axioms decode_uses_exact_wire
end TrustIrEval.ClosureWireBytes
