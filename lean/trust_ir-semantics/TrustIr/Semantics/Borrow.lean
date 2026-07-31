-- Copyright 2026 Andrew Yates
-- Author: Andrew Yates <andrewyates.name@gmail.com>
-- Licensed under the Apache License, Version 2.0
--
-- Borrow semantics — permission-based model.
-- Phase 3 of the formalization roadmap.
--
-- Reference: designs/2026-04-16-trust_ir-semantics-lean-architecture.md, Section 3
-- Reference: Ho & Protzenko, "Aeneas: Rust verification by functional
--            translation", ICFP 2022
-- Reference: Boyland, "Checking interference with fractional permissions", SAS 2003

import TrustIr.Inst
import TrustIr.Semantics.Monad

namespace TrustIr

/-!
# Borrow Semantics

This module implements the Rust borrow instruction semantics for the
permission-based model.

## Aeneas Relationship

Aeneas eliminates borrows by translating mutable references into
forward/backward function pairs. We take a different approach:

1. **Permission-based model** (this module): tracks what operations are
   allowed on each allocation. This is the ground truth for TrustIr semantics.

2. **Aeneas bridge** (aeneas2 repo): optionally translates Rust-originated
   TrustIr into the pure functional form for Aeneas-style proofs.

The permission-based model handles all three language paradigms:
- Rust borrows: Owned -> UniqueBorrow/SharedBorrow -> Owned
- Swift ARC: ArcRef with reference counting (see TrustIr.Semantics.ARC)
- C raw pointers: RawPtr with no guarantees

## Implemented in this file

- `semBorrow`: Owned -> SharedBorrow(1), SharedBorrow(n) -> SharedBorrow(n+1)
- `semBorrowMut`: Owned -> UniqueBorrow
- `semEndBorrow`: SharedBorrow/UniqueBorrow -> Owned or decremented SharedBorrow

## Pure permission transition helpers

- `borrowPermission`: pure function for the borrow permission transition
- `endBorrowPermission`: pure function for the end-borrow permission transition

These pure helpers are used in BorrowProps.lean for proofs.
-/

/-- Borrow kind for tracking active borrows. -/
inductive BorrowKind where
  | shared  : BorrowKind
  | mutable : BorrowKind
  deriving DecidableEq, Repr

/-- A borrow token tracks an active borrow.
    Created by Borrow/BorrowMut, consumed by EndBorrow. -/
structure BorrowToken where
  targetAlloc : AllocId
  kind        : BorrowKind
  deriving Repr

-- =================================================================
-- Pure permission transition helpers
-- =================================================================

/-- Pure permission transition induced by `Borrow`.
    Owned -> SharedBorrow 1, SharedBorrow n -> SharedBorrow (n+1).
    Returns the input permission unchanged for non-borrowable states. -/
def borrowPermission : Permission → Permission
  | .owned => .sharedBorrow 1
  | .sharedBorrow n => .sharedBorrow (n + 1)
  | p => p

/-- Pure permission transition induced by `EndBorrow`.
    SharedBorrow 1 -> Owned, SharedBorrow (n+2) -> SharedBorrow (n+1),
    UniqueBorrow -> Owned.
    Returns the input permission unchanged for non-borrow states. -/
def endBorrowPermission : Permission → Permission
  | .sharedBorrow n =>
      match n with
      | 0 => .sharedBorrow 0  -- error state, preserved
      | 1 => .owned
      | Nat.succ (Nat.succ k) => .sharedBorrow (k + 1)
  | .uniqueBorrow => .owned
  | p => p

-- =================================================================
-- Borrow helpers
-- =================================================================

/-- Extract the allocation id from a pointer value. -/
def getAllocIdFromPtr (ptrVal : Value) : Sem AllocId := do
  match ptrVal with
  | .ptr addr =>
    pure (AllocId.mk addr)
  | .nullPtr =>
    Sem.throwUB "borrow on null pointer"
  | _ =>
    Sem.throwTypeError "expected pointer value"

/-- Look up the current permission for an allocation. -/
def getPermission (allocId : AllocId) : Sem Permission := do
  let s ← Sem.getState
  match s.permissions.get allocId with
  | some perm => pure perm
  | none =>
    Sem.throwUB s!"missing permission for allocation {repr allocId}"

/-- Update the permission for an allocation. -/
def setPermission (allocId : AllocId) (perm : Permission) : Sem Unit := do
  Sem.modifyState fun s =>
    { s with permissions := s.permissions.set allocId perm }

-- =================================================================
-- Borrow semantics
-- =================================================================

/-- Evaluate a Borrow instruction.
    Creates a shared borrow of the pointed-to allocation.
    Transitions: Owned -> SharedBorrow(1), or SharedBorrow(n) -> SharedBorrow(n+1). -/
def semBorrow (ptrId : ValueId) : Sem ValueId := do
  let ptrVal ← Sem.lookupValue ptrId
  let allocId ← getAllocIdFromPtr ptrVal
  let perm ← getPermission allocId
  match perm with
  | .owned =>
    setPermission allocId (.sharedBorrow 1)
    Sem.bindFresh (.ptr allocId.id)
  | .sharedBorrow n =>
    setPermission allocId (.sharedBorrow (n + 1))
    Sem.bindFresh (.ptr allocId.id)
  | _ =>
    Sem.throwUB s!"Borrow: invalid permission state {repr perm}"

/-- Evaluate a BorrowMut instruction.
    Creates a mutable (unique) borrow of the pointed-to allocation.
    Transitions: Owned -> UniqueBorrow. -/
def semBorrowMut (ptrId : ValueId) : Sem ValueId := do
  let ptrVal ← Sem.lookupValue ptrId
  let allocId ← getAllocIdFromPtr ptrVal
  let perm ← getPermission allocId
  match perm with
  | .owned =>
    setPermission allocId .uniqueBorrow
    Sem.bindFresh (.ptr allocId.id)
  | _ =>
    Sem.throwUB s!"BorrowMut: expected owned permission, got {repr perm}"

/-- Evaluate an EndBorrow instruction.
    Returns the borrow and restores the original permission.
    Transitions: SharedBorrow(1) -> Owned, SharedBorrow(n+1) -> SharedBorrow(n),
                 UniqueBorrow -> Owned. -/
def semEndBorrow (borrowPtrId : ValueId) : Sem Unit := do
  let borrowPtrVal ← Sem.lookupValue borrowPtrId
  let allocId ← getAllocIdFromPtr borrowPtrVal
  let perm ← getPermission allocId
  match perm with
  | .sharedBorrow n =>
    match n with
    | 0 =>
      Sem.throwUB s!"EndBorrow: inconsistent shared borrow count for {repr allocId}"
    | 1 =>
      setPermission allocId .owned
    | Nat.succ (Nat.succ k) =>
      setPermission allocId (.sharedBorrow (Nat.succ k))
  | .uniqueBorrow =>
    setPermission allocId .owned
  | _ =>
    Sem.throwUB s!"EndBorrow: invalid permission state {repr perm}"

end TrustIr
