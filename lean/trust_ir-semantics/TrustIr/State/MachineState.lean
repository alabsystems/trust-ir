-- Copyright 2026 Andrew Yates
-- Author: Andrew Yates <andrewyates.name@gmail.com>
-- Licensed under the Apache License, Version 2.0
--
-- Core machine state that the semantic monad operates on.

import TrustIr.Basic
import TrustIr.State.ValueMap
import TrustIr.State.Memory
import TrustIr.State.Permission

namespace TrustIr

/-- An explicit semantic input for the format's signed-zero min/max choices.
    Different dynamic occurrences and vector lanes read different indices.
    Program behavior ranges over all tapes; an executable run supplies one. -/
structure FloatZeroChoiceTape where
  choose : Nat → Bool

instance : Repr FloatZeroChoiceTape where
  reprPrec _ _ := "<float-zero choice tape>"

def FloatZeroChoiceTape.empty : FloatZeroChoiceTape := ⟨fun _ => false⟩

/-- A finite executable witness, extended with right-operand choices. This is
    one tape, not a restriction on the quantified semantic input. -/
def FloatZeroChoiceTape.ofList (choices : List Bool) : FloatZeroChoiceTape :=
  ⟨fun index => choices.getD index false⟩

/-!
# Machine State

The machine state is the core data structure threaded through the
semantic monad. It contains everything needed to evaluate TrustIr
instructions.

For Phase 1 (pure arithmetic), only `locals` and `nextValueId` are
needed. Memory, permissions, and refcounts are included for forward
compatibility with Phases 2-3.
-/

/-- A failed sited check's location, RESOLVED at the failure (amendment P,
    wire v54; `docs/SPEC_RATIFICATIONS.md` §19.1 rule 4). Mirrors Rust
    `trust_ir::PanicLocationValue`. `global g offset`: byte `offset` of module
    global `g` — a `PanicLocation.global g` (offset 0, the global NOT
    materialized), or a run-time pointer into the allocation of a
    materialized global. `other`: a live pointer outside every global. -/
inductive PanicLoc where
  | global (g : GlobalId) (offset : Nat) : PanicLoc
  | other : PanicLoc
  deriving Repr, DecidableEq

/-- The realization of a failed sited check (amendment P): the entry it
    calls and the location it passes. Mirrors Rust
    `trust_ir::InterpretPanicSite`. The entry is never executed. -/
structure PanicOutcomeSite where
  entry : FuncId
  loc : PanicLoc
  deriving Repr, DecidableEq

/-- The complete machine state for TrustIr evaluation. -/
structure MachineState where
  locals       : ValueMap           -- SSA value -> concrete value
  memory       : Memory             -- Heap + stack allocations
  permissions  : PermissionMap      -- Allocation -> permission
  refCounts    : RefCountMap        -- Allocation -> reference count (ARC)
  nextValueId  : Nat                -- Next fresh ValueId index
  /-- `GlobalAddr` cache: a global's base address and the allocation that
      backs it, as the interpreter caches an `InterpretPointer`. -/
  globals      : List (GlobalId × Addr × AllocId)
  /-- Amendment D, Part 2 (`PanicStrategy.unwind`): the exception objects
      this run raised, by address, each with the allocation its pointer
      names and the panic outcome (message and resolved site) its raise
      reported (the interpreter's `UnwindState.exceptions`). An exception
      object is a fresh one-byte allocation, dead from birth, so no memory
      operation through it is defined; `Resume` identifies one BY ADDRESS,
      and an unwinding that escapes the entry is reported as its row's
      panic. Always empty under `PanicStrategy.abort`. -/
  exceptions   : List (Addr × AllocId × String × Option PanicOutcomeSite) := []
  /-- The exception (its address and allocation) and type selector the next
      `LandingPad` binds, put in hand when an unwinding enters a pad's block
      (amendment D, Part 2): selector 1 for a catch-all pad, 0 for a cleanup
      pad. -/
  inHand       : Option (Addr × AllocId × Nat) := none
  /-- Ghost execution input, never a program value or memory byte. -/
  floatZeroChoices : FloatZeroChoiceTape := .empty
  /-- Global dynamic choice position, retained across blocks and call frames. -/
  floatZeroChoiceCursor : Nat := 0
  /-- Open binding-frame lineages; snapshots carry their lineage in Value.frame. -/
  openFrameLineages : List Nat := []
  /-- Monotone runtime frame identity, independent of SSA ids and call frames. -/
  nextFrameLineage : Nat := 0
  deriving Repr

/-- Initial empty machine state. -/
def MachineState.empty : MachineState :=
  { locals      := ValueMap.empty
  , memory      := Memory.empty
  , permissions := PermissionMap.empty
  , refCounts   := RefCountMap.empty
  , nextValueId := 0
  , globals     := [] }

/-- Start an execution with a chosen tape. -/
def MachineState.withFloatZeroChoices (s : MachineState) (choices : FloatZeroChoiceTape) :
    MachineState :=
  { s with floatZeroChoices := choices, floatZeroChoiceCursor := 0 }

/-- Ghost choice input and consumption are not program observations. -/
def MachineState.eraseFloatZeroChoices (s : MachineState) : MachineState :=
  { s with floatZeroChoices := .empty, floatZeroChoiceCursor := 0 }

/-- Look up the cached base address and backing allocation of a global, if
    it has been materialized by a prior `GlobalAddr`. The cache holds at most
    one entry per `GlobalId` (inserted only on the first address-of), so the
    first match is canonical. -/
def MachineState.lookupGlobal (s : MachineState) (g : GlobalId) : Option (Addr × AllocId) :=
  (s.globals.find? (fun p => p.fst == g)).map (·.snd)

/-- Lookup an SSA value in the machine state. -/
def MachineState.lookupValue (s : MachineState) (id : ValueId) : Option Value :=
  s.locals.get id

/-- Bind a fresh SSA value. Returns the new ValueId and updated state. -/
def MachineState.bindValue (s : MachineState) (v : Value) : ValueId × MachineState :=
  let id := ValueId.mk s.nextValueId
  (id, { s with
    locals := s.locals.set id v,
    nextValueId := s.nextValueId + 1 })

end TrustIr
