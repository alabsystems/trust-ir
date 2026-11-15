-- Copyright 2026 Andrew Yates
-- Author: Andrew Yates <andrewyates.name@gmail.com>
-- Licensed under the Apache License, Version 2.0
--
-- Typed binding-frame semantics: OpenFrame / BindSlot / LoadSlot / CloseFrame.
--
-- Reference: designs/2026-04-19-binding-frames-lean-semantics.md
-- Issue:     TrustIr#32 (companion to #30 R4; ty supremacy)
--
-- Each snapshot retains its runtime lineage. Closing any handle closes
-- every snapshot of that lineage, while functional slot updates stay local.

import TrustIr.Inst
import TrustIr.Semantics.Monad

namespace TrustIr

/-!
# Binding-frame semantics

OpenFrame allocates a fresh lineage and a poison-initialized slot snapshot.
BindSlot returns a new snapshot with the same lineage. LoadSlot reads that
handle's own snapshot. CloseFrame removes the lineage from the open table.
Copy, select and branch argument transport retain the identity in Value.frame.
The monotone lineage counter is independent of SSA ids and survives calls.
-/

-- =================================================================
-- Frame helpers (pure functions on Value)
-- =================================================================

/-- Functional update on a binding frame: set slot slot to newVal,
    producing a fresh frame value. Returns none if the value is not a
    frame or the slot index is out of bounds. -/
def bindSlot (v : Value) (slot : Nat) (newVal : Value) : Option Value :=
  match v with
  | .frame lineage slots =>
    if slot < slots.length then some (.frame lineage (slots.set slot newVal))
    else none
  | _ => none

/-- Read slot slot from a binding frame. Returns none if the value is
    not a frame or the slot is out of bounds (via optional list indexing). -/
def loadSlot (v : Value) (slot : Nat) : Option Value :=
  match v with
  | .frame _ slots => trustIrListGet? slots slot
  | _ => none

/-- Build the initial frame for an OpenFrame: every slot is set to
    Value.undef with the slot's declared type. -/
def initFrame (lineage : Nat) (slots : List BindingSlot) : Value :=
  .frame lineage (slots.map (fun s => Value.undef s.ty))

-- =================================================================
-- Instruction semantics
-- =================================================================

/-- Update only the runtime frame table and counter. -/
def Sem.setFrameState (openLineages : List Nat) (nextLineage : Nat) : Sem Unit := do
  let state ← Sem.getState
  Sem.setState { state with openFrameLineages := openLineages, nextFrameLineage := nextLineage }

/-- Handle inspection rejects poison before attempting frame classification. -/
def Sem.frameHandle (frameId : ValueId) (op : String) : Sem (Nat × List Value) := do
  let value ← Sem.lookupValue frameId
  Sem.rejectPartial value "frame handle use"
  match value with
  | .frame lineage slots => pure (lineage, slots)
  | _ => Sem.throwTypeError s!"{op}: operand is not a frame"

/-- Runtime frame-lineage width. The exponent remains a computation in compiled code, as `Sem.addrBits`
does for pointer casts. Folding the literal `2^64` into a closed bignum stores
uninitialized MPZ padding in Lean 4.8 `.olean` files. The named exponent is
definitionally 64; the checked UInt64 allocation bound is unchanged. -/
@[simp, noinline] def Sem.frameLineageBits : Nat := 64

/-- Mint a lineage before binding its initial snapshot. Match Rust's checked
UInt64 increment: the maximum counter value cannot be allocated. -/
def semOpenFrame (def_ : BindingFrameDef) : Sem ValueId := do
  let state ← Sem.getState
  if state.nextFrameLineage < 2 ^ Sem.frameLineageBits - 1 then
    Sem.setFrameState (state.nextFrameLineage :: state.openFrameLineages) (state.nextFrameLineage+1)
    Sem.bindFresh (initFrame state.nextFrameLineage def_.slots)
  else Sem.throwUB "OpenFrame: frame id overflow"

/-- Check liveness before reading the value operand, then make a functional
snapshot in the same lineage. The original snapshot remains unchanged. -/
def semBindSlot (frameId : ValueId) (slot : Nat) (valueId : ValueId) : Sem ValueId := do
  let (lineage, slots) ← Sem.frameHandle frameId "BindSlot"
  let state ← Sem.getState
  if state.openFrameLineages.contains lineage then
    let value ← Sem.lookupValue valueId
    if slot < slots.length then Sem.bindFresh (.frame lineage (slots.set slot value))
    else Sem.throwUB s!"BindSlot: slot {slot} out of range for frame of {slots.length} slots"
  else Sem.throwUB "BindSlot: frame is not open"

/-- Liveness applies to the snapshot's lineage; an unbound slot still returns
its original poison. Declared slot typing remains a validation premise. -/
def semLoadSlot (frameId : ValueId) (slot : Nat) (_ty : Ty) : Sem ValueId := do
  let (lineage, slots) ← Sem.frameHandle frameId "LoadSlot"
  let state ← Sem.getState
  if state.openFrameLineages.contains lineage then
    match trustIrListGet? slots slot with
    | some value => Sem.bindFresh value
    | none => Sem.throwUB s!"LoadSlot: slot {slot} out of range for frame of {slots.length} slots"
  else Sem.throwUB "LoadSlot: frame is not open"

/-- Closing either an old or a new snapshot closes the entire lineage.
Repeated close is UB, including a second close through a different alias. -/
def semCloseFrame (frameId : ValueId) : Sem Unit := do
  let (lineage, _) ← Sem.frameHandle frameId "CloseFrame"
  let state ← Sem.getState
  if state.openFrameLineages.contains lineage then
    Sem.setFrameState (state.openFrameLineages.filter (fun id => id != lineage)) state.nextFrameLineage
  else Sem.throwUB "CloseFrame: frame is not open (double close)"

-- =================================================================
-- Predicates (for theorem statements)
-- =================================================================

/-- Predicate: a value is a frame with at least n slots. -/
def hasSlots (v : Value) (n : Nat) : Prop :=
  match v with
  | .frame _ slots => slots.length >= n
  | _ => False

/-- Predicate: a value is a frame (any number of slots). -/
def isFrame (v : Value) : Prop :=
  match v with
  | .frame _ _ => True
  | _ => False

/-- Predicate: BindSlot is safe on this frame at this slot. -/
def bindSlotSafe (v : Value) (slot : Nat) : Prop :=
  match v with
  | .frame _ slots => slot < slots.length
  | _ => False

end TrustIr
