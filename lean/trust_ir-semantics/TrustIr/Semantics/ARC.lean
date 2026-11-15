-- Copyright 2026 Andrew Yates
-- Author: Andrew Yates <andrewyates.name@gmail.com>
-- Licensed under the Apache License, Version 2.0
--
-- Swift ARC reference counting semantics.
-- Phase 3 of the formalization roadmap.
--
-- Reference: designs/2026-04-16-trust_ir-semantics-lean-architecture.md, Section 3

import TrustIr.Semantics.Borrow

namespace TrustIr

/-!
# ARC Semantics

This module implements Swift ARC (Automatic Reference Counting) operations
over the shared memory and permission model.

## Instructions

- `semRetain`: increment reference count
- `semRelease`: decrement reference count, deallocate at zero
- `semIsUnique`: check if reference count is exactly 1

## Design

ARC operations require the target allocation to have `Permission.arcRef`.
Reference counts are tracked in `MachineState.refCounts`. When a release
decrements the count to zero, the allocation is marked dead and its
permission/refcount state is cleaned up.

## Pure helpers

- `getRefCount`: look up ref count (default 0)
- `setRefCount`: update ref count
- `deallocARC`: mark allocation dead and clean up state
-/

-- =================================================================
-- ARC helpers
-- =================================================================

/-- Get the reference count for an allocation.
    Untracked allocations default to count 0. -/
def getRefCount (refCounts : RefCountMap) (allocId : AllocId) : Nat :=
  match refCounts allocId with
  | some n => n
  | none => 0

/-- Update the reference count for an allocation. -/
def setRefCount (refCounts : RefCountMap) (allocId : AllocId) (count : Nat) : RefCountMap :=
  fun allocId' => if allocId' == allocId then some count else refCounts allocId'

/-- Remove the permission for an allocation. -/
def clearPermission (permissions : PermissionMap) (allocId : AllocId) : PermissionMap :=
  fun allocId' => if allocId' == allocId then none else permissions allocId'

trustIrDenseMatch
/-- The allocation an ARC operand names: the one the pointer was DERIVED from
    (its provenance), which must be known and live — the interpreter's
    `expect_pointer` + `arc_allocation_mut` / `is_unique`. A null or
    no-provenance pointer is UB. The operand's offset inside that allocation
    is checked by `requireObjectBase`, after `requireArcRef`. -/
def getAllocIdFromPtrARC (ptrVal : Value) : Sem AllocId := do
  let s ← Sem.getState
  match ptrVal with
  | .ptr addr (some id) =>
    match s.memory.lookup id with
    | some a =>
      if a.alive then pure id
      else Sem.throwUB (trustIrStringBuild s!"ARC pointer references a freed allocation: {addr}")
    | none => Sem.throwUB (trustIrStringBuild s!"ARC pointer does not reference a known allocation: {addr}")
  | .ptr addr none =>
    if addr == 0 then Sem.throwUB "ARC operation on null pointer"
    else Sem.throwUB (trustIrStringBuild s!"ARC pointer value {addr} has no allocation provenance")
  | .nullPtr =>
    Sem.throwUB "ARC operation on null pointer"
  | _ =>
    Sem.throwTypeError "ARC operation expects a pointer operand"

trustIrDenseMatch
/-- Check that an allocation currently has ARC permission. -/
def requireArcRef (allocId : AllocId) : Sem Unit := do
  let s ← Sem.getState
  match s.permissions.get allocId with
  | some .arcRef => pure ()
  | some perm =>
    Sem.throwUB (trustIrStringBuild s!"ARC operation requires arcRef permission, found {repr perm}")
  | none =>
    Sem.throwUB (trustIrStringBuild s!"ARC operation on allocation without permission: {repr allocId}")

trustIrDenseMatch
/-- An ARC operand must be at the OBJECT BASE of the reference-counted cell it
    was derived from: offset 0, where the pinned runtime reads its header (SPEC
    "An ARC operation counts only a reference-counted cell", clause 3,
    decided 2026-09-30). Any other offset — interior, one past the end, in or
    past the heap slack tail — is undefined behaviour. The interpreter's
    `InterpretPointer::is_object_base`, read by `arc_allocation_mut`,
    `is_unique` and the host path's `check_rc_cell`. Checked AFTER
    `requireArcRef`, so an operand whose provenance is not a
    reference-counted cell keeps that refusal; the operand is the pointer
    `getAllocIdFromPtrARC` resolved to `allocId`, so its other shapes are
    unreachable here and fail closed. -/
def requireObjectBase (op : String) (ptrVal : Value) (allocId : AllocId) : Sem Unit := do
  let s ← Sem.getState
  match ptrVal, s.memory.lookup allocId with
  | .ptr addr _, some a =>
    if addr == a.base then pure ()
    else Sem.throwUB (trustIrStringBuild s!"{op}: pointer is at offset {addr - a.base} of its cell, not at the object base a runtime object pointer names")
  | _, _ => Sem.throwUB (trustIrStringBuild s!"{op}: operand does not name a known allocation")

/-- Mark an ARC allocation dead and clean up its permission/refcount state. -/
def deallocARC (allocId : AllocId) : Sem Unit := do
  let s ← Sem.getState
  let found := s.memory.allocations.any (fun alloc => alloc.id == allocId && alloc.alive)
  if !found then
    Sem.throwUB (trustIrStringBuild s!"ARC deallocation of dead or unknown allocation: {repr allocId}")
  else
    let memory' :=
      { s.memory with
        allocations := s.memory.allocations.map (fun alloc =>
          if alloc.id == allocId then { alloc with alive := false } else alloc) }
    let permissions' := clearPermission s.permissions allocId
    let refCounts' := setRefCount s.refCounts allocId 0
    Sem.setState { s with
      memory := memory'
      permissions := permissions'
      refCounts := refCounts' }

-- =================================================================
-- ARC semantics
-- =================================================================

/-- Evaluate a Retain instruction (Swift ARC).
    Increments the reference count of the reference-counted cell its operand
    was derived from, through a pointer at the cell's object base. -/
def semRetain (ptrId : ValueId) : Sem Unit := do
  let ptrVal ← Sem.lookupValue ptrId
  let allocId ← getAllocIdFromPtrARC ptrVal
  requireArcRef allocId
  requireObjectBase "Retain" ptrVal allocId
  let s ← Sem.getState
  let count := getRefCount s.refCounts allocId
  let refCounts' := setRefCount s.refCounts allocId (count + 1)
  Sem.setState { s with refCounts := refCounts' }

/-- Evaluate a Release instruction (Swift ARC).
    Decrements the reference count and deallocates at zero, by the same
    operand rule as `semRetain`. -/
def semRelease (ptrId : ValueId) : Sem Unit := do
  let ptrVal ← Sem.lookupValue ptrId
  let allocId ← getAllocIdFromPtrARC ptrVal
  requireArcRef allocId
  requireObjectBase "Release" ptrVal allocId
  let s ← Sem.getState
  let count := getRefCount s.refCounts allocId
  match count with
  | 0 =>
    Sem.throwUB (trustIrStringBuild s!"Release on zero refcount (double free): {repr allocId}")
  | 1 =>
    deallocARC allocId
  | n + 2 =>
    let refCounts' := setRefCount s.refCounts allocId (n + 1)
    Sem.setState { s with refCounts := refCounts' }

/-- Evaluate an IsUnique instruction (Swift ARC).
    Returns true iff the allocation's reference count is exactly 1, by the
    same operand rule as `semRetain`. -/
def semIsUnique (ptrId : ValueId) : Sem ValueId := do
  let ptrVal ← Sem.lookupValue ptrId
  let allocId ← getAllocIdFromPtrARC ptrVal
  requireArcRef allocId
  requireObjectBase "IsUnique" ptrVal allocId
  let s ← Sem.getState
  let count := getRefCount s.refCounts allocId
  Sem.bindFresh (.bool (count == 1))

end TrustIr

#trustIrAxiomsExact TrustIr.getAllocIdFromPtrARC == []
#trustIrAxiomsExact TrustIr.requireArcRef == []
#trustIrAxiomsExact TrustIr.requireObjectBase == []
#trustIrAxiomsExact TrustIr.deallocARC == []
#trustIrAxiomsExact TrustIr.semRelease == []
#trustIrAxiomsExact TrustIr.semRetain == []
#trustIrAxiomsExact TrustIr.semIsUnique == []
