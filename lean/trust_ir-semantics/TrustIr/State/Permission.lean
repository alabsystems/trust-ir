-- Copyright 2026 Andrew Yates
-- Author: Andrew Yates <andrewyates.name@gmail.com>
-- Licensed under the Apache License, Version 2.0
--
-- Permission-based memory access model.
-- Reference: designs/2026-04-16-trust_ir-semantics-lean-architecture.md, Section 3
--
-- This implements the permission-map abstraction that replaces Aeneas's
-- borrow elimination with a more general model that supports all three
-- language paradigms.
--
-- Reference: Boyland, "Checking interference with fractional permissions", SAS 2003
-- Reference: Bornat et al., "Permission accounting in separation logic", POPL 2005

import TrustIr.State.Memory

namespace TrustIr

/-!
# Permission Model

Instead of eliminating borrows (Aeneas approach), TrustIr models memory
access through a permission map. Each allocation has a permission
that determines what operations are allowed.

## Design Decision

Aeneas eliminates borrows by translating mutable references into
forward/backward function pairs. This works well for pure Rust but
does not generalize to Swift ARC or C raw pointers.

Our permission-based model is the ground truth. For Rust-originated
TrustIr, the `aeneas2` tool can optionally translate into the pure
functional form. The permission semantics works for all languages.

See: designs/2026-04-16-trust_ir-semantics-lean-architecture.md, Section 3

## Permission types

| Permission     | Read | Write | Dealloc | Source    |
|---------------|------|-------|---------|-----------|
| Owned         | yes  | yes   | yes     | Rust, C   |
| UniqueBorrow  | yes  | yes   | no      | Rust &mut |
| SharedBorrow  | yes  | no    | no      | Rust &    |
| RawPtr        | *    | *     | *       | C (UB)   |
| ArcRef        | yes  | no    | managed | Swift     |

(* = allowed but may be UB; requires explicit proof annotation)
-/

/-- Permission on a memory allocation.
    Determines what operations are allowed. -/
inductive Permission where
  | owned        : Permission                -- Full ownership
  | uniqueBorrow : Permission                -- Mutable borrow (Rust &mut T)
  | sharedBorrow : Nat → Permission          -- Shared borrow with count (Rust &T)
  | rawPtr       : Permission                -- C raw pointer (no guarantees)
  | arcRef       : Permission                -- ARC reference (Swift)
  deriving DecidableEq, Repr

/-- The permission map: allocation -> permission. -/
def PermissionMap := AllocId → Option Permission

/-- Empty permission map. -/
def PermissionMap.empty : PermissionMap := fun _ => none

/-- Get the permission for an allocation. -/
def PermissionMap.get (pm : PermissionMap) (id : AllocId) : Option Permission := pm id

/-- Set the permission for an allocation. -/
def PermissionMap.set (pm : PermissionMap) (id : AllocId) (p : Permission) : PermissionMap :=
  fun id' => if id' == id then some p else pm id'

/-- Check if a permission allows reading. -/
def Permission.canRead : Permission → Bool
  | .owned         => true
  | .uniqueBorrow  => true
  | .sharedBorrow _ => true
  | .rawPtr        => true    -- allowed but may be UB
  | .arcRef        => true

/-- Check if a permission allows writing. -/
def Permission.canWrite : Permission → Bool
  | .owned         => true
  | .uniqueBorrow  => true
  | .sharedBorrow _ => false
  | .rawPtr        => true    -- allowed but may be UB
  | .arcRef        => false

/-- Check if a permission allows deallocation. -/
def Permission.canDealloc : Permission → Bool
  | .owned         => true
  | .uniqueBorrow  => false
  | .sharedBorrow _ => false
  | .rawPtr        => true    -- allowed but may be UB
  | .arcRef        => false   -- managed by refcount

/-- Reference count map for ARC (Swift) semantics. -/
def RefCountMap := AllocId → Option Nat

/-- Empty reference count map. -/
def RefCountMap.empty : RefCountMap := fun _ => none

instance : Repr PermissionMap where
  reprPrec _ _ := "<PermissionMap>"

instance : Repr RefCountMap where
  reprPrec _ _ := "<RefCountMap>"

end TrustIr
