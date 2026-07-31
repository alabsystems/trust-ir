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

/-!
# Machine State

The machine state is the core data structure threaded through the
semantic monad. It contains everything needed to evaluate TrustIr
instructions.

For Phase 1 (pure arithmetic), only `locals` and `nextValueId` are
needed. Memory, permissions, and refcounts are included for forward
compatibility with Phases 2-3.
-/

/-- The complete machine state for TrustIr evaluation. -/
structure MachineState where
  locals       : ValueMap           -- SSA value -> concrete value
  memory       : Memory             -- Heap + stack allocations
  permissions  : PermissionMap      -- Allocation -> permission
  refCounts    : RefCountMap        -- Allocation -> reference count (ARC)
  nextValueId  : Nat                -- Next fresh ValueId index
  globals      : List (GlobalId × Addr)  -- GlobalAddr address cache (id -> base)
  deriving Repr

/-- Initial empty machine state. -/
def MachineState.empty : MachineState :=
  { locals      := ValueMap.empty
  , memory      := Memory.empty
  , permissions := PermissionMap.empty
  , refCounts   := RefCountMap.empty
  , nextValueId := 0
  , globals     := [] }

/-- Look up the cached base address of a global, if it has been materialized
    by a prior `GlobalAddr`. The cache holds at most one entry per `GlobalId`
    (inserted only on the first address-of), so the first match is canonical. -/
def MachineState.lookupGlobal (s : MachineState) (g : GlobalId) : Option Addr :=
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
