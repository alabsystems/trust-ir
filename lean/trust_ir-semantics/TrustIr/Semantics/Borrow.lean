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
import TrustIr.Semantics.Memory

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

trustIrDenseMatch
/-- Pure permission transition induced by `Borrow`.
    Owned -> SharedBorrow 1, SharedBorrow n -> SharedBorrow (n+1).
    Returns the input permission unchanged for non-borrowable states. -/
def borrowPermission : Permission → Permission
  | .owned => .sharedBorrow 1
  | .sharedBorrow n => .sharedBorrow (n + 1)
  | p => p

trustIrDenseMatch
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

/-- The allocation whose permission a thin `Borrow` / `BorrowMut` /
    `EndBorrow` operand moves (SPEC "Freeing an allocation under a live borrow
    is undefined behaviour", clause 2): the allocation the pointer was DERIVED
    from (its provenance), and only while that allocation is live and the
    operand lies inside the bytes it requested. Anywhere else — one past the
    end, the heap slack tail, a zero-size or freed allocation — `none`, and the
    instruction moves no permission. The interpreter's `borrow_count_mut`. -/
def Memory.borrowTarget (mem : Memory) (addr : Addr) (id : AllocId) : Option AllocId :=
  match mem.lookup id with
  | some a => if a.alive && a.base ≤ addr && addr - a.base < a.requested then some id else none
  | none => none

trustIrDenseMatch
/-- The operand of `Borrow` / `BorrowMut`: the interpreter's `expect_pointer`
    (null and no-provenance pointers are UB) and then `borrowTarget`. -/
def borrowOperand (op : String) (ptrVal : Value) : Sem (Option AllocId) := do
  let s ← Sem.getState
  match ptrVal with
  | .ptr addr (some id) => pure (s.memory.borrowTarget addr id)
  | .ptr addr none =>
    if addr == 0 then Sem.throwUB (trustIrStringBuild s!"{op}: null pointer dereference")
    else Sem.throwUB (trustIrStringBuild s!"{op}: pointer value {addr} has no allocation provenance")
  | .nullPtr => Sem.throwUB (trustIrStringBuild s!"{op}: null pointer dereference")
  | _ => Sem.throwTypeError "expected pointer value"

trustIrDenseMatch
/-- The allocation an `EndBorrow` operand ends a borrow of: a thin provenance
    pointer's `Memory.borrowTarget`; anything else — a null, no-provenance
    or fat pointer, a non-pointer — names none (the interpreter's `EndBorrow`
    arm never faults). -/
def endBorrowTarget (mem : Memory) : Value → Option AllocId
  | .ptr addr (some id) => mem.borrowTarget addr id
  | _ => none

/-- Look up the current permission for an allocation. -/
def getPermission (allocId : AllocId) : Sem Permission := do
  let s ← Sem.getState
  match s.permissions.get allocId with
  | some perm => pure perm
  | none =>
    Sem.throwUB (trustIrStringBuild s!"missing permission for allocation {repr allocId}")

/-- Update the permission for an allocation. -/
def setPermission (allocId : AllocId) (perm : Permission) : Sem Unit := do
  Sem.modifyState fun s =>
    { s with permissions := s.permissions.set allocId perm }

-- =================================================================
-- Borrow semantics
-- =================================================================

trustIrDenseMatch
/-- Evaluate a Borrow instruction.
    Creates a shared borrow of the allocation the operand was derived from,
    when the operand lies inside that live allocation's requested bytes
    (`borrowOperand` / `Memory.borrowTarget`). Transitions: Owned ->
    SharedBorrow(1), or SharedBorrow(n) -> SharedBorrow(n+1). Any other
    non-null provenance pointer — one past the end, in the heap slack tail,
    in a zero-size or freed allocation — and a fat pointer are passed
    through and move nothing (SPEC "Freeing an allocation under a live borrow
    is undefined behaviour", clause 2). -/
def semBorrow (ptrId : ValueId) : Sem ValueId := do
  let ptrVal ← Sem.lookupValue ptrId
  -- A fat pointer is a verbatim pass-through (interpret.rs
  -- `borrow_of_fat_pointer_value_is_a_verbatim_pass_through`).
  if let .fatPtr .. := ptrVal then Sem.bindFresh ptrVal else
  match ← borrowOperand "Borrow" ptrVal with
  | none => Sem.bindFresh ptrVal
  | some allocId =>
  let perm ← getPermission allocId
  match perm with
  | .owned =>
    setPermission allocId (.sharedBorrow 1)
    Sem.bindFresh ptrVal
  | .sharedBorrow n =>
    setPermission allocId (.sharedBorrow (n + 1))
    Sem.bindFresh ptrVal
  | _ =>
    Sem.throwUB (trustIrStringBuild s!"Borrow: invalid permission state {repr perm}")

trustIrDenseMatch
/-- Evaluate a BorrowMut instruction.
    Creates a mutable (unique) borrow of the allocation the operand was
    derived from, by the same operand rule as `semBorrow`.
    Transitions: Owned -> UniqueBorrow. -/
def semBorrowMut (ptrId : ValueId) : Sem ValueId := do
  let ptrVal ← Sem.lookupValue ptrId
  if let .fatPtr .. := ptrVal then Sem.bindFresh ptrVal else
  match ← borrowOperand "Borrow" ptrVal with
  | none => Sem.bindFresh ptrVal
  | some allocId =>
  let perm ← getPermission allocId
  match perm with
  | .owned =>
    setPermission allocId .uniqueBorrow
    Sem.bindFresh ptrVal
  | _ =>
    Sem.throwUB (trustIrStringBuild s!"BorrowMut: expected owned permission, got {repr perm}")

trustIrDenseMatch
/-- Evaluate an EndBorrow instruction.
    Returns the borrow and restores the original permission of the
    allocation its operand names by the `Memory.borrowTarget` rule.
    Transitions: SharedBorrow(1) -> Owned, SharedBorrow(n+1) -> SharedBorrow(n),
                 UniqueBorrow -> Owned. Any other operand ends nothing and does
    not fault (the interpreter's `EndBorrow` arm). -/
def semEndBorrow (borrowPtrId : ValueId) : Sem Unit := do
  let borrowPtrVal ← Sem.lookupValue borrowPtrId
  let s ← Sem.getState
  -- Any operand other than a provenance pointer inside its allocation's
  -- requested bytes ends nothing and never faults (interpret.rs EndBorrow).
  match endBorrowTarget s.memory borrowPtrVal with
  | none => pure ()
  | some allocId =>
  let perm ← getPermission allocId
  match perm with
  | .sharedBorrow n =>
    match n with
    | 0 =>
      Sem.throwUB (trustIrStringBuild s!"EndBorrow: inconsistent shared borrow count for {repr allocId}")
    | 1 =>
      setPermission allocId .owned
    | Nat.succ (Nat.succ k) =>
      setPermission allocId (.sharedBorrow (Nat.succ k))
  | .uniqueBorrow =>
    setPermission allocId .owned
  | _ =>
    Sem.throwUB (trustIrStringBuild s!"EndBorrow: invalid permission state {repr perm}")

end TrustIr

#trustIrAxiomsExact TrustIr.borrowPermission == []
#trustIrAxiomsExact TrustIr.endBorrowPermission == []

#trustIrAxiomsExact TrustIr.borrowOperand == []
#trustIrAxiomsExact TrustIr.getPermission == []
#trustIrAxiomsExact TrustIr.semBorrow == []
#trustIrAxiomsExact TrustIr.semBorrowMut == []
#trustIrAxiomsExact TrustIr.semEndBorrow == []
