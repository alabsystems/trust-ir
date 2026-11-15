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
import TrustIr.StringCompat

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
  -- Host-unwinder interaction (`Inst.Resume`, a `LandingPad` with no
  -- exception in hand): refused under `PanicStrategy.abort`, the panic=abort
  -- projection, exactly as the reference interpreter refuses them. Under
  -- `.unwind` (amendment D, Part 2) the contextual evaluator models them.
  | hostUnwind : UnsupportedFeature
  -- Link-time relocatable address (`Constant.symbolAddr`): the value is only
  -- assigned by the linker, so neither the executable model nor the reference
  -- interpreter can produce it (WS2.18).
  | linkTimeAddress : UnsupportedFeature
  -- A float operation or byte image the model does not compute faithfully
  -- (binary16 arithmetic/codec; any exposure of a NaN's bits). Mirrors the
  -- reference interpreter's `unsupported_float`
  -- (`InterpretErrorCode::UnsupportedFloat`): the model
  -- refuses rather than answering at the wrong precision or with a fabricated
  -- byte image (docs/ub-numerics-policy.md §2, §7 item 6).
  | float : UnsupportedFeature
  -- A cast whose source or destination type is outside the executable set the
  -- model reinterprets (`Transmute` off `transmuteScalarTy`, WS2.9). Mirrors
  -- the reference interpreter's `InterpretErrorCode::UnsupportedCast`: the
  -- model refuses rather than binding a value of the wrong shape at the
  -- destination type (lowering-target subset v3, structural condition 1).
  | cast : UnsupportedFeature
  -- A typed memory operation (`Alloca` / `HeapAlloc` / `Load` / `Store` /
  -- `GEP` / the atomics / `GlobalAddr`) at a type whose BYTE IMAGE the model
  -- does not state: `Ty.byteSize` is `none` for aggregates (Struct, Array,
  -- Tuple, Enum), the ty-supremacy carriers (Sequence, Set, Record, Closure),
  -- and Never — the model has no
  -- struct-layout or declared-tuple-layout table, so such an access is
  -- UNMODELLED, not ill-formed. Until WS2.19 every one of these sites was a
  -- `typeError` ("type has no byte size"), which the Lean-execution oracle
  -- reads as a DISAGREEMENT with the validator on a module the validator
  -- accepted; a structured refusal is counted as coverage instead (the
  -- reference interpreter executes these through its layout queries). Func
  -- words have a fixed target layout, but their nonzero images additionally
  -- require the original module function order; an absent table is also an
  -- explicit layout boundary rather than a fabricated code address.
  | layout : UnsupportedFeature
  -- An aggregate construction whose result depends on a MODULE DEFINITION
  -- TABLE the machine state does not carry (WS3.5 `Inst.MakeAggregate` of
  -- an enum, whose tag lane is `discriminants[variant]`, or of a record,
  -- whose lanes are named by its `RecordDef`). The Rust reference
  -- interpreter resolves both through the module; the executable model
  -- refuses rather than fabricate a tag or a field name (B3 depth ledger).
  | enumDefTable : UnsupportedFeature
  | closureDefTable : UnsupportedFeature
  -- Destructors (`Inst.Drop`): the executable model, like the reference
  -- interpreter, has no destructor model. A drop frees and can run arbitrary
  -- user code, so evaluating it as a no-op would model a different program.
  | destructor : UnsupportedFeature
  | callUnwindBoundary : UnsupportedFeature
  -- A WEAK compare-exchange (`Inst.CmpXchg .. (weak := true)`): it may fail
  -- spuriously, which is a nondeterministic choice `Sem` cannot make. The
  -- reference interpreter refuses it too; stepping it as strong would delete
  -- the spurious-failure executions.
  | weakCmpXchg : UnsupportedFeature
  -- Amendment D, Part 2: a landing pad with a TYPED catch clause (any clause
  -- index other than 0, trust-cg's empty filter included) entered by an
  -- unwinding under `PanicStrategy.unwind`. The format has no typeinfo model,
  -- so which clause matches is not decidable here; both engines refuse it.
  | typedCatch : UnsupportedFeature
  /-- A typed contextual operation needs the original function's SSA declarations. -/
  | ssaTypeTable : UnsupportedFeature
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
  | .linkTimeAddress => "link_time_address"
  | .float => "float"
  | .cast => "cast"
  | .layout => "layout"
  | .enumDefTable => "enum_def_table"
  | .closureDefTable => "closure_def_table"
  | .destructor => "destructor"
  | .callUnwindBoundary => "call_unwind_boundary"
  | .weakCmpXchg => "weak_cmpxchg"
  | .typedCatch => "typed_catch"
  | .ssaTypeTable => "ssa_type_table"

end UnsupportedFeature

-- `PanicLoc` and `PanicOutcomeSite` live in `TrustIr/State/MachineState.lean`
-- (amendment D, Part 2): the machine state's exception table records the
-- panic outcome each raise reported, and the state layer cannot import this
-- file.

/-- Semantic error type. A `panic` carries its message and, for a sited
    check (amendment P), its resolved site: the normative panic outcome is
    (kind, operand values, entry, location), of which the message renders the
    first two. -/
inductive SemError where
  | ub        : String → SemError    -- Undefined behavior
  | panic     : String → Option PanicOutcomeSite → SemError  -- Assertion failure
  | typeError : String → SemError    -- Type mismatch (ill-formed IR)
  | unsupported : UnsupportedFeature → String → SemError
  | outOfFuel : SemError              -- Fuel exhausted
  /-- Target address-space exhaustion is a model resource refusal, not UB or
      a successful program outcome. Distinct from the instruction fuel cap. -/
  | outOfMemory : String → SemError
  /-- Amendment D, Part 2 (`PanicStrategy.unwind` only): an unwinding in
      flight, carrying its exception object's address and the machine state
      at the throw. The state rides in the error because `Sem` is `StateT`
      over `Except` and a throw drops it, while a catching invoke must resume
      from the memory the unwinding left. Never produced under
      `PanicStrategy.abort`; `evalFunctionInContext` reports one that escapes
      the entry as the panic its raise recorded. -/
  | unwinding : Addr → MachineState → SemError
  deriving Repr

namespace SemError

/-- Stable error code for conformance fixtures and compiler gates. -/
def code : SemError → String
  | .ub _ => "ub"
  | .panic _ _ => "panic"
  | .typeError _ => "type_error"
  | .unsupported feature _ => trustIrStringBuild ("unsupported." ++ feature.code)
  | .outOfFuel => "out_of_fuel"
  | .outOfMemory _ => "out_of_memory"
  | .unwinding _ _ => "unwinding"

/-- Diagnostic detail paired with the stable error code. -/
def detail : SemError → String
  | .ub msg => msg
  | .panic msg _ => msg
  | .typeError msg => msg
  | .unsupported _ msg => msg
  | .outOfFuel => "fuel exhausted"
  | .outOfMemory msg => msg
  | .unwinding exn _ => s!"unwinding in flight (exception object at {exn})"

/-- Stable code plus diagnostic detail.  Tests that need fully stable
    diagnostics should normally compare `code`; this string is for
    evidence comments and local debugging. -/
def stable : SemError → String
  | err => err.code ++ ":" ++ err.detail

end SemError

instance : ToString SemError where
  toString
    | .ub msg        => s!"UB: {msg}"
    | .panic msg _   => s!"Panic: {msg}"
    | .typeError msg => s!"TypeError: {msg}"
    | .unsupported feature msg =>
      s!"Unsupported({feature.code}): {msg}"
    | .outOfFuel     => "OutOfFuel"
    | .outOfMemory msg => s!"OutOfMemory: {msg}"
    | .unwinding exn _ => s!"Unwinding(exception object at {exn})"

/-- The semantic monad: state + error.
    Equivalent to `StateT MachineState (Except SemError)`. -/
abbrev Sem (a : Type) := StateT MachineState (Except SemError) a

/-- Throw a UB error. -/
def Sem.throwUB {α : Type} (msg : String) : Sem α :=
  throw (SemError.ub msg)

/-- Throw a panic error; a sited check (amendment P) passes its resolved
    site. -/
def Sem.throwPanic {α : Type} (msg : String) (site : Option PanicOutcomeSite := none) :
    Sem α :=
  throw (SemError.panic msg site)

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
  | none   => Sem.throwTypeError (trustIrStringBuild s!"undefined SSA value: {repr id}")

trustIrDenseMatch
/-- Poison guard: mirror of the Rust reference interpreter's `reject_partial`
    (crates/trust-ir/src/interpret.rs, commit 530fdd5). A poison value — a
    partially-initialized image (`.partial`) or an `Undef` (`.undef`, roadmap
    WS2.10) — may only be TRANSPORTED (`Copy` / non-strict `Store`);
    INSPECTING its content is undefined behaviour and faults here at the true
    use site. A no-op on every fully-defined value. Called at each
    content-consuming instruction (arithmetic / comparison / cast / branch /
    switch / select condition / field projection). -/
def Sem.rejectPartial (v : Value) (op : String) : Sem Unit :=
  match v with
  | .partial _ =>
    Sem.throwUB (trustIrStringBuild s!"{op}: use of an uninitialized value (poison read; poison may only be copied or stored, never inspected)")
  | .undef _ =>
    Sem.throwUB (trustIrStringBuild s!"{op}: use of an uninitialized value (undef (poison) inspected; poison may only be copied or stored, never inspected)")
  -- Crystal lane (E3b): an unwritten aggregate lane is never a value of its own; reading it out of
  -- its aggregate (`semExtractField`) is where this fires.
  | .uninit =>
    Sem.throwUB (trustIrStringBuild s!"{op}: read of an unwritten aggregate lane (uninit)")
  | _ => pure ()

/-- Poison guard over a whole call boundary: the arguments passed into a
    callee, or the values it returns. Crossing a call/return boundary INSPECTS
    every value, so any poison among them is undefined behaviour — mirror of
    the Rust interpreter's `check_signature_values` ("A poison value may not
    cross a call/return boundary"). Poison crosses a call only through
    memory. A no-op when no value is poison. -/
def Sem.rejectPoisonValues (vs : List Value) (op : String) : Sem Unit :=
  if vs.any Value.isPoison then
    Sem.throwUB (trustIrStringBuild s!"{op}: use of an uninitialized value (poison may not cross a call/return boundary)")
  else
    pure ()


/-- Bind a fresh SSA value and return its ValueId. -/
def Sem.bindFresh (v : Value) : Sem ValueId := do
  let s ← Sem.getState
  let (id, s') := s.bindValue v
  Sem.setState s'
  pure id

/-- Read the next explicit signed-zero min/max choice, without changing any
    program value, allocation, permission, global or exception state. -/
def Sem.nextFloatZeroChoice : Sem Bool := do
  let s ← Sem.getState
  Sem.setState { s with floatZeroChoiceCursor := s.floatZeroChoiceCursor + 1 }
  pure (s.floatZeroChoices.choose s.floatZeroChoiceCursor)

/-- Bind TWO fresh SSA values, in order, and return both ids. This is the one
    spelling of a two-result instruction's outcome (`Overflow`, `CmpXchg`;
    WS2.24): each component is its own SSA value, bound positionally to the
    node's result destinations by the evaluator, exactly as Rust
    `InstrNode.results` — never one packed `Value.aggregate`. -/
def Sem.bindFreshPair (first second : Value) : Sem (ValueId × ValueId) := do
  let firstId ← Sem.bindFresh first
  let secondId ← Sem.bindFresh second
  pure (firstId, secondId)

/-- Run a Sem computation on a given state. -/
def Sem.run {α : Type} (m : Sem α) (s : MachineState) : Except SemError (α × MachineState) :=
  StateT.run m s

/-- Sem.run of pure is Except.ok. -/
theorem Sem.run_pure {α : Type} (x : α) (s : MachineState) :
    Sem.run (pure x) s = .ok (x, s) := rfl

/-- Sem.run of bind commutes with Except.bind. -/
theorem Sem.run_bind {α β : Type} (m : Sem α) (f : α → Sem β) (s : MachineState) :
    Sem.run (m >>= f) s = (Sem.run m s).bind (fun (x, s') => Sem.run (f x) s') := rfl

/-- `bindFreshPair` binds its components at the next two fresh ids. -/
theorem Sem.run_bindFreshPair (first second : Value) (s : MachineState) :
    Sem.run (Sem.bindFreshPair first second) s =
      .ok ((ValueId.mk s.nextValueId, ValueId.mk (s.nextValueId + 1)),
        { s with
          locals := (s.locals.set (ValueId.mk s.nextValueId) first).set
            (ValueId.mk (s.nextValueId + 1)) second
          nextValueId := s.nextValueId + 1 + 1 }) := rfl

/-- The two ids of a `bindFreshPair` are DISTINCT and each looks up exactly its
    own component — no aggregate projection. -/
theorem Sem.bindFreshPair_ok {first second : Value} {s s' : MachineState}
    {ids : ValueId × ValueId}
    (h : Sem.run (Sem.bindFreshPair first second) s = .ok (ids, s')) :
    ids.1 ≠ ids.2 ∧ s'.lookupValue ids.1 = some first ∧
      s'.lookupValue ids.2 = some second := by
  rw [Sem.run_bindFreshPair] at h
  cases h
  refine ⟨?_, ?_, ?_⟩
  · intro hEq
    have hIdx := congrArg ValueId.index hEq
    exact absurd hIdx (Nat.ne_of_lt (Nat.lt_succ_self _))
  · simp only [MachineState.lookupValue, ValueMap.get, ValueMap.set]
    have hne : ¬ (ValueId.mk s.nextValueId = ValueId.mk (s.nextValueId + 1)) := by
      intro hEq
      exact absurd (congrArg ValueId.index hEq) (Nat.ne_of_lt (Nat.lt_succ_self _))
    simp [hne]
  · simp [MachineState.lookupValue, ValueMap.get, ValueMap.set]

/-- A poison-free boundary passes the guard without touching the state. -/
theorem Sem.rejectPoisonValues_run_ok (vs : List Value) (op : String)
    (s : MachineState) (h : vs.any Value.isPoison = false) :
    Sem.run (Sem.rejectPoisonValues vs op) s = .ok ((), s) := by
  unfold Sem.rejectPoisonValues
  rw [h]
  rfl

/-- A boundary carrying poison makes the guard throw. -/
theorem Sem.rejectPoisonValues_run_error (vs : List Value) (op : String)
    (s : MachineState) (h : vs.any Value.isPoison = true) :
    ∃ e, Sem.run (Sem.rejectPoisonValues vs op) s = .error e := by
  unfold Sem.rejectPoisonValues
  rw [h]
  exact ⟨_, rfl⟩

/-- A successful guard run leaves the state unchanged and certifies the
    boundary is poison-free. -/
theorem Sem.rejectPoisonValues_run_ok_inv (vs : List Value) (op : String)
    (s s' : MachineState) (u : Unit)
    (h : Sem.run (Sem.rejectPoisonValues vs op) s = .ok (u, s')) :
    vs.any Value.isPoison = false ∧ s' = s := by
  unfold Sem.rejectPoisonValues at h
  cases hp : vs.any Value.isPoison with
  | true =>
    rw [hp] at h
    exact absurd h (by intro h'; cases h')
  | false =>
    rw [hp] at h
    have h' : (Except.ok ((), s) : Except SemError (Unit × MachineState)) = .ok (u, s') := h
    cases h'
    exact ⟨rfl, rfl⟩

end TrustIr

#trustIrAxiomsExact TrustIr.SemError.code == []
#trustIrAxiomsExact TrustIr.Sem.lookupValue == []

#trustIrAxiomsExact TrustIr.Sem.rejectPartial == []
#trustIrAxiomsExact TrustIr.Sem.rejectPoisonValues == []
