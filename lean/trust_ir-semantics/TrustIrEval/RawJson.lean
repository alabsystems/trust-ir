-- Copyright 2026 Andrew Yates | Apache-2.0
import Lean.Data.Json

namespace TrustIrEval.RawJson
open Lean (Json)

/-- Actual native object-parser occurrence policy, not a value-equality search. -/
macro "rawJsonFirstWins" : term => do
  if Lean.versionString == "4.8.0" then `(true)
  else if Lean.versionString == "4.30.0-rc2" then `(false)
  else Lean.Macro.throwError "unsupported Lean compiler for raw JSON occurrence selection"

def firstWins : Bool := rawJsonFirstWins

structure Span where
  start : Nat
  stop : Nat
  deriving Repr, Inhabited

/-- Object entries retain decoded keys, key spans and every source occurrence. -/
inductive Node where
  | scalar (span : Span) (value : Json) (numberToken : Option String)
  | array (span : Span) (values : List Node)
  | object (span : Span) (fields : List (String × Span × Node))
  deriving Inhabited

partial def Node.project : Node → Json
  | .scalar _ value _ => value
  | .array _ values => .arr (values.map Node.project).toArray
  | .object _ fields =>
    let fields := fields.map (fun entry => (entry.1, entry.2.2.project))
    Json.mkObj (if firstWins then fields.reverse else fields)

/-- Pick the native parser's actual occurrence even if several values compare equal. -/
def Node.field? (node : Node) (name : String) : Option Node :=
  match node with
  | .object _ fields =>
    let selected := if firstWins then fields else fields.reverse
    (selected.find? (fun entry => entry.1 == name)).map (fun entry => entry.2.2)
  | _ => none

def Node.elements : Node → List Node
  | .array _ values => values
  | _ => []

private abbrev Scan := StateT Nat (Except String)
private def fail {α : Type} (message : String) : Scan α := throw message
private def byte? (source : ByteArray) : Scan (Option UInt8) := do
  let index ← get
  pure (if index < source.size then some (source.get! index) else none)
private def advance : Scan Unit := modify (· + 1)
private def whitespace (byte : UInt8) : Bool :=
  byte == 32 || byte == 9 || byte == 10 || byte == 13
private partial def ws (source : ByteArray) : Scan Unit := do
  match ← byte? source with
  | some byte => if whitespace byte then advance; ws source
  | none => pure ()
private def expect (source : ByteArray) (expected : UInt8) : Scan Unit := do
  if (← byte? source) != some expected then fail "raw JSON scanner: delimiter mismatch"
  advance
private def text (source : ByteArray) (start stop : Nat) : Scan String :=
  match String.fromUTF8? (source.extract start stop) with
  | some value => pure value
  | none => fail "raw JSON scanner: invalid UTF-8 span"
private def scalar (source : ByteArray) (start stop : Nat) : Scan Json := do
  match Json.parse (← text source start stop) with
  | .ok value => pure value
  | .error error => fail s!"raw JSON scanner: scalar mismatch: {error}"
private partial def stringEnd (source : ByteArray) : Scan Unit := do
  match ← byte? source with
  | none => fail "raw JSON scanner: unterminated string"
  | some 34 => advance
  | some 92 =>
    advance
    if (← byte? source).isNone then fail "raw JSON scanner: incomplete escape"
    advance
    stringEnd source
  | some _ => advance; stringEnd source
private def string (source : ByteArray) : Scan (String × Span × Json) := do
  let start ← get
  expect source 34
  stringEnd source
  let stop ← get
  let value ← scalar source start stop
  match value with
  | .str name => pure (name, ⟨start, stop⟩, value)
  | _ => fail "raw JSON scanner: string projection mismatch"
private partial def atomEnd (source : ByteArray) : Scan Unit := do
  match ← byte? source with
  | none => pure ()
  | some byte =>
    if whitespace byte || byte == 44 || byte == 93 || byte == 125 then pure ()
    else advance; atomEnd source

mutual
  private partial def value (source : ByteArray) : Scan Node := do
    ws source
    let start ← get
    match ← byte? source with
    | some 123 =>
      advance; ws source
      if (← byte? source) == some 125 then
        advance
        pure (.object ⟨start, ← get⟩ [])
      else objectTail source start []
    | some 91 =>
      advance; ws source
      if (← byte? source) == some 93 then
        advance
        pure (.array ⟨start, ← get⟩ [])
      else arrayTail source start []
    | some 34 =>
      let (_, span, projected) ← string source
      pure (.scalar span projected none)
    | some byte =>
      atomEnd source
      let stop ← get
      if stop == start then fail "raw JSON scanner: empty atom"
      let projected ← scalar source start stop
      let token ← text source start stop
      let number := if byte == 45 || (48 ≤ byte && byte ≤ 57) then some token else none
      pure (.scalar ⟨start, stop⟩ projected number)
    | none => fail "raw JSON scanner: value missing"

  private partial def arrayTail (source : ByteArray) (start : Nat)
      (reversed : List Node) : Scan Node := do
    let child ← value source
    ws source
    match ← byte? source with
    | some 93 => advance; pure (.array ⟨start, ← get⟩ (child :: reversed).reverse)
    | some 44 => advance; arrayTail source start (child :: reversed)
    | _ => fail "raw JSON scanner: array delimiter mismatch"

  private partial def objectTail (source : ByteArray) (start : Nat)
      (reversed : List (String × Span × Node)) : Scan Node := do
    ws source
    let (name, keySpan, _) ← string source
    ws source; expect source 58
    let child ← value source
    ws source
    match ← byte? source with
    | some 125 =>
      advance
      pure (.object ⟨start, ← get⟩ ((name, keySpan, child) :: reversed).reverse)
    | some 44 => advance; objectTail source start ((name, keySpan, child) :: reversed)
    | _ => fail "raw JSON scanner: object delimiter mismatch"
end

structure Document where
  /-- Always the original native Json.parse result, never the scanner's replacement. -/
  json : Json
  raw : Node

inductive ParseError where
  | syntax (message : String)
  | correspondence (message : String)

/-- A source scanner/projection disagreement refuses; it never falls back to erased input. -/
def parse (contents : String) : Except ParseError Document := do
  let projected ← (Json.parse contents).mapError ParseError.syntax
  let source := contents.toUTF8
  let (raw, stop) ← (do
    let raw ← value source
    ws source
    pure raw : Scan Node).run 0 |>.mapError ParseError.correspondence
  if stop != source.size then throw (.correspondence "raw JSON scanner: unconsumed input")
  if raw.project != projected then throw (.correspondence "raw JSON scanner: projection mismatch")
  pure ⟨projected, raw⟩

end TrustIrEval.RawJson
