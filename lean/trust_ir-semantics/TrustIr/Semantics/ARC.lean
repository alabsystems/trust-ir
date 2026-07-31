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

/-- Resolve a pointer value to its allocation id via live allocation lookup.
    The pointer must point into a live allocation. -/
def getAllocIdFromPtrARC (ptrVal : Value) : Sem AllocId := do
  let s ← Sem.getState
  match ptrVal with
  | .ptr addr =>
    match s.memory.allocations.find? (fun alloc =>
      alloc.alive && addr >= alloc.base && addr < alloc.base + alloc.size) with
    | some alloc => pure alloc.id
    | none => Sem.throwUB s!"ARC pointer does not refer to a live allocation: {addr}"
  | .nullPtr =>
    Sem.throwUB "ARC operation on null pointer"
  | _ =>
    Sem.throwTypeError "ARC operation expects a pointer operand"

/-- Check that an allocation currently has ARC permission. -/
def requireArcRef (allocId : AllocId) : Sem Unit := do
  let s ← Sem.getState
  match s.permissions.get allocId with
  | some .arcRef => pure ()
  | some perm =>
    Sem.throwUB s!"ARC operation requires arcRef permission, found {repr perm}"
  | none =>
    Sem.throwUB s!"ARC operation on allocation without permission: {repr allocId}"

/-- Mark an ARC allocation dead and clean up its permission/refcount state. -/
def deallocARC (allocId : AllocId) : Sem Unit := do
  let s ← Sem.getState
  let found := s.memory.allocations.any (fun alloc => alloc.id == allocId && alloc.alive)
  if !found then
    Sem.throwUB s!"ARC deallocation of dead or unknown allocation: {repr allocId}"
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
    Increments the reference count of the allocation. -/
def semRetain (ptrId : ValueId) : Sem Unit := do
  let ptrVal ← Sem.lookupValue ptrId
  let allocId ← getAllocIdFromPtrARC ptrVal
  requireArcRef allocId
  let s ← Sem.getState
  let count := getRefCount s.refCounts allocId
  let refCounts' := setRefCount s.refCounts allocId (count + 1)
  Sem.setState { s with refCounts := refCounts' }

/-- Evaluate a Release instruction (Swift ARC).
    Decrements the reference count and deallocates at zero. -/
def semRelease (ptrId : ValueId) : Sem Unit := do
  let ptrVal ← Sem.lookupValue ptrId
  let allocId ← getAllocIdFromPtrARC ptrVal
  requireArcRef allocId
  let s ← Sem.getState
  let count := getRefCount s.refCounts allocId
  match count with
  | 0 =>
    Sem.throwUB s!"Release on zero refcount (double free): {repr allocId}"
  | 1 =>
    deallocARC allocId
  | n + 2 =>
    let refCounts' := setRefCount s.refCounts allocId (n + 1)
    Sem.setState { s with refCounts := refCounts' }

/-- Evaluate an IsUnique instruction (Swift ARC).
    Returns true iff the allocation's reference count is exactly 1. -/
def semIsUnique (ptrId : ValueId) : Sem ValueId := do
  let ptrVal ← Sem.lookupValue ptrId
  let allocId ← getAllocIdFromPtrARC ptrVal
  requireArcRef allocId
  let s ← Sem.getState
  let count := getRefCount s.refCounts allocId
  Sem.bindFresh (.bool (count == 1))

end TrustIr
