-- Copyright 2026 Andrew Yates
-- Author: Andrew Yates <andrewyates.name@gmail.com>
-- Licensed under the Apache License, Version 2.0
--
-- Typed binding-frame semantics: OpenFrame / BindSlot / LoadSlot / CloseFrame.
--
-- Reference: designs/2026-04-19-binding-frames-lean-semantics.md
-- Issue:     TrustIr#32 (companion to #30 R4; ty supremacy)
--
-- Binding frames are typed heterogeneous records used to lower
-- quantifier constructs (bounded iteration over sets/sequences). The
-- four instructions in this file are SSA-pure with one exception: we
-- mark CloseFrame as side-effecting for DCE purposes, mirroring Rust
-- has_side_effects. The denotation itself is a no-op.

import TrustIr.Inst
import TrustIr.Semantics.Monad

namespace TrustIr

/-!
# Binding-frame Semantics

## Overview

A binding frame is a typed heterogeneous record whose slots are
addressed by natural-number index. Frame values live in SSA registers
(not memory), and updates are functional: each BindSlot returns a
fresh frame handle.

## Value representation

Frame values use the Value.frame constructor (List Value). Slot k is
the k-th element of the list. The constructor is nominally distinct
from Value.aggregate even though both carry List Value -- this prevents
aggregates from flowing into frame-only instructions (and vice versa)
at the step-relation layer, mirroring the Rust-side validation that
forbids Store of a BindingFrame to memory.

## Scope discipline

The dominator-LIFO nesting of OpenFrame / CloseFrame is a Rust-side
validation property. In the denotation, CloseFrame is a no-op: the SSA
value remains reachable (looking it up after CloseFrame is ill-formed
IR, caught by validation, not by the semantics).
-/

-- =================================================================
-- Frame helpers (pure functions on Value)
-- =================================================================

/-- Functional update on a binding frame: set slot slot to newVal,
    producing a fresh frame value. Returns none if the value is not a
    frame or the slot index is out of bounds. -/
def bindSlot (v : Value) (slot : Nat) (newVal : Value) : Option Value :=
  match v with
  | .frame slots =>
    if slot < slots.length then some (.frame (slots.set slot newVal))
    else none
  | _ => none

/-- Read slot slot from a binding frame. Returns none if the value is
    not a frame or the slot is out of bounds (via List.get?). -/
def loadSlot (v : Value) (slot : Nat) : Option Value :=
  match v with
  | .frame slots => slots.get? slot
  | _ => none

/-- Build the initial frame for an OpenFrame: every slot is set to
    Value.undef with the slot's declared type. -/
def initFrame (slots : List BindingSlot) : Value :=
  .frame (slots.map (fun s => Value.undef s.ty))

-- =================================================================
-- Instruction semantics
-- =================================================================

/-- Evaluate an OpenFrame instruction.
    Allocates a fresh frame handle; each slot initialised to
    Value.undef at its declared Ty. This mirrors LLVM-style undef
    semantics: a LoadSlot before a BindSlot yields undef rather than a
    type error.

    Mirrors Rust Inst::OpenFrame. -/
def semOpenFrame (def_ : BindingFrameDef) : Sem ValueId := do
  Sem.bindFresh (initFrame def_.slots)

/-- Evaluate a BindSlot instruction.
    Functional update: returns a fresh frame handle whose chosen slot
    has been replaced by the new value. The input handle is still
    valid (SSA form).

    Errors:
    - UB if the slot is out of bounds for the frame.
    - TypeError if the operand is not a frame. -/
def semBindSlot (frameId : ValueId) (slot : Nat) (valueId : ValueId)
    : Sem ValueId := do
  let frameVal ← Sem.lookupValue frameId
  let newVal   ← Sem.lookupValue valueId
  match bindSlot frameVal slot newVal with
  | some v => Sem.bindFresh v
  | none =>
    match frameVal with
    | .frame _ => Sem.throwUB "BindSlot: slot out of bounds"
    | _        => Sem.throwTypeError "BindSlot: operand is not a frame"

/-- Evaluate a LoadSlot instruction.
    Reads the chosen slot and rebinds the result to a fresh SSA value.
    The expected-type parameter _ty is ignored at the denotation
    level -- validation has already matched it against the slot's
    declared type (like semExtractField's _ty parameter).

    Errors:
    - UB if the slot is out of bounds.
    - TypeError if the operand is not a frame. -/
def semLoadSlot (frameId : ValueId) (slot : Nat) (_ty : Ty)
    : Sem ValueId := do
  let frameVal ← Sem.lookupValue frameId
  match loadSlot frameVal slot with
  | some v => Sem.bindFresh v
  | none =>
    match frameVal with
    | .frame _ => Sem.throwUB "LoadSlot: slot out of bounds"
    | _        => Sem.throwTypeError "LoadSlot: operand is not a frame"

/-- Evaluate a CloseFrame instruction.
    No runtime effect on the machine state: scope discipline (dominator
    LIFO nesting) lives in Rust-side validation. The corresponding
    Rust has_side_effects = true flag is a DCE marker, not a runtime
    discipline. -/
def semCloseFrame (_frameId : ValueId) : Sem Unit := do
  pure ()

-- =================================================================
-- Predicates (for theorem statements)
-- =================================================================

/-- Predicate: a value is a frame with at least n slots. -/
def hasSlots (v : Value) (n : Nat) : Prop :=
  match v with
  | .frame slots => slots.length >= n
  | _ => False

/-- Predicate: a value is a frame (any number of slots). -/
def isFrame (v : Value) : Prop :=
  match v with
  | .frame _ => True
  | _ => False

/-- Predicate: BindSlot is safe on this frame at this slot. -/
def bindSlotSafe (v : Value) (slot : Nat) : Prop :=
  match v with
  | .frame slots => slot < slots.length
  | _ => False

end TrustIr
