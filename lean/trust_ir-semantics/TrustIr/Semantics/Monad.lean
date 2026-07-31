-- Copyright 2026 Andrew Yates
-- Author: Andrew Yates <andrewyates.name@gmail.com>
-- Licensed under the Apache License, Version 2.0
--
-- The semantic monad: State + Error.
-- Reference: designs/2026-04-16-trust_ir-semantics-lean-architecture.md, Section 2
--
-- Following the Aeneas model (Ho & Protzenko, ICFP 2022):
-- monadic small-step operational semantics with explicit error propagation.

import TrustIr.State.MachineState

namespace TrustIr

/-!
# Semantic Monad

The core monad for TrustIr semantics:

    Sem a := MachineState → Except SemError (a × MachineState)

This is `StateT MachineState (Except SemError)`.

## Error types

- `ub`: Undefined behavior (e.g., null dereference, out-of-bounds)
- `panic`: Assertion failure (TrustIr `Assert` instruction)
- `typeError`: Type mismatch (ill-formed IR)
- `unsupported`: Well-formed IR outside the executable reference subset
- `outOfFuel`: Fuel exhausted (for termination proofs)
-/

/-- Unsupported executable-reference feature class.  The constructor
    identity is the stable part; the detail string remains diagnostic. -/
inductive UnsupportedFeature where
  | dialectOp : UnsupportedFeature
  | interproceduralCall : UnsupportedFeature
  | interproceduralIndirectCall : UnsupportedFeature
  | vectorType : UnsupportedFeature
  | vectorShape : UnsupportedFeature
  -- Host-unwinder interaction (`Inst.Resume`): the executable model, like
  -- the reference interpreter, does not model in-flight host exceptions.
  | hostUnwind : UnsupportedFeature
  deriving Repr, DecidableEq, BEq

namespace UnsupportedFeature

/-- Stable reason-code suffix for unsupported executable cases. -/
def code : UnsupportedFeature → String
  | .dialectOp => "dialect_op"
  | .interproceduralCall => "interprocedural_call"
  | .interproceduralIndirectCall => "interprocedural_indirect_call"
  | .vectorType => "vector_type"
  | .vectorShape => "vector_shape"
  | .hostUnwind => "host_unwind"

end UnsupportedFeature

/-- Semantic error type. -/
inductive SemError where
  | ub        : String → SemError    -- Undefined behavior
  | panic     : String → SemError    -- Assertion failure
  | typeError : String → SemError    -- Type mismatch (ill-formed IR)
  | unsupported : UnsupportedFeature → String → SemError
  | outOfFuel : SemError              -- Fuel exhausted
  deriving Repr

namespace SemError

/-- Stable error code for conformance fixtures and compiler gates. -/
def code : SemError → String
  | .ub _ => "ub"
  | .panic _ => "panic"
  | .typeError _ => "type_error"
  | .unsupported feature _ => "unsupported." ++ feature.code
  | .outOfFuel => "out_of_fuel"

/-- Diagnostic detail paired with the stable error code. -/
def detail : SemError → String
  | .ub msg => msg
  | .panic msg => msg
  | .typeError msg => msg
  | .unsupported _ msg => msg
  | .outOfFuel => "fuel exhausted"

/-- Stable code plus diagnostic detail.  Tests that need fully stable
    diagnostics should normally compare `code`; this string is for
    evidence comments and local debugging. -/
def stable : SemError → String
  | err => err.code ++ ":" ++ err.detail

end SemError

instance : ToString SemError where
  toString
    | .ub msg        => s!"UB: {msg}"
    | .panic msg     => s!"Panic: {msg}"
    | .typeError msg => s!"TypeError: {msg}"
    | .unsupported feature msg =>
      s!"Unsupported({feature.code}): {msg}"
    | .outOfFuel     => "OutOfFuel"

/-- The semantic monad: state + error.
    Equivalent to `StateT MachineState (Except SemError)`. -/
abbrev Sem (a : Type) := StateT MachineState (Except SemError) a

/-- Throw a UB error. -/
def Sem.throwUB {α : Type} (msg : String) : Sem α :=
  throw (SemError.ub msg)

/-- Throw a panic error. -/
def Sem.throwPanic {α : Type} (msg : String) : Sem α :=
  throw (SemError.panic msg)

/-- Throw a type error. -/
def Sem.throwTypeError {α : Type} (msg : String) : Sem α :=
  throw (SemError.typeError msg)

/-- Throw a structured unsupported-subset error. -/
def Sem.throwUnsupported {α : Type}
    (feature : UnsupportedFeature) (msg : String) : Sem α :=
  throw (SemError.unsupported feature msg)

/-- Get the current machine state. -/
def Sem.getState : Sem MachineState :=
  StateT.get

/-- Replace the machine state. -/
def Sem.setState (s : MachineState) : Sem Unit :=
  StateT.set s

/-- Modify the machine state. -/
def Sem.modifyState (f : MachineState → MachineState) : Sem Unit := do
  let s ← StateT.get
  StateT.set (f s)

/-- Lookup an SSA value, throwing a type error if not found. -/
def Sem.lookupValue (id : ValueId) : Sem Value := do
  let s ← Sem.getState
  match s.lookupValue id with
  | some v => pure v
  | none   => Sem.throwTypeError s!"undefined SSA value: {repr id}"

/-- Poison guard: mirror of the Rust reference interpreter's `reject_partial`
    (crates/trust-ir/src/interpret.rs, commit 530fdd5). A partially-initialized
    (poison) value may only be TRANSPORTED (`Copy` / non-strict `Store`);
    INSPECTING its content is undefined behaviour and faults here at the true
    use site. A no-op on every fully-defined value. Called at each
    content-consuming instruction (arithmetic / comparison / cast / branch /
    switch / select condition / field projection). -/
def Sem.rejectPartial (v : Value) (op : String) : Sem Unit :=
  match v with
  | .partial _ =>
    Sem.throwUB s!"{op}: use of an uninitialized value (poison read; poison may only be copied or stored, never inspected)"
  | _ => pure ()

/-- Bind a fresh SSA value and return its ValueId. -/
def Sem.bindFresh (v : Value) : Sem ValueId := do
  let s ← Sem.getState
  let (id, s') := s.bindValue v
  Sem.setState s'
  pure id

/-- Run a Sem computation on a given state. -/
def Sem.run {α : Type} (m : Sem α) (s : MachineState) : Except SemError (α × MachineState) :=
  StateT.run m s

/-- Sem.run of pure is Except.ok. -/
theorem Sem.run_pure {α : Type} (x : α) (s : MachineState) :
    Sem.run (pure x) s = .ok (x, s) := rfl

/-- Sem.run of bind commutes with Except.bind. -/
theorem Sem.run_bind {α β : Type} (m : Sem α) (f : α → Sem β) (s : MachineState) :
    Sem.run (m >>= f) s = (Sem.run m s).bind (fun (x, s') => Sem.run (f x) s') := rfl

end TrustIr
