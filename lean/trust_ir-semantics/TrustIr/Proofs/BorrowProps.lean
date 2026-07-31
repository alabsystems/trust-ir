-- Copyright 2026 Andrew Yates
-- Author: Andrew Yates <andrewyates.name@gmail.com>
-- Licensed under the Apache License, Version 2.0
--
-- Borrow safety properties for the permission-based memory model.
-- Phase 3 proofs from the formalization roadmap.
--
-- Reference: designs/2026-04-16-trust_ir-semantics-lean-architecture.md, Section 3
-- Reference: Boyland, "Checking interference with fractional permissions", SAS 2003

import TrustIr.Semantics.Borrow

namespace TrustIr

/-!
# Borrow Properties

These theorems establish key safety properties of TrustIr's borrow model.
They operate on pure permission helpers (`borrowPermission`,
`endBorrowPermission`) and permission predicates (`canRead`, `canWrite`,
`canDealloc`).

## Proved properties

1. Shared borrows are read-only (no writes)
2. UniqueBorrow is the exclusive read-write-but-no-dealloc permission
3. EndBorrow restores Owned from SharedBorrow(1) and UniqueBorrow
4. Shared borrow nesting is well-formed (borrow/end are inverse)
5. Owned allows both read and write
6. Borrows never allow deallocation

## Design note

These proofs operate on pure functions (Permission predicates and
transition helpers) rather than the monadic wrappers (semBorrow, etc.).
This keeps the proofs clean and composable. Lifting to the monadic
level is mechanical.
-/

-- =================================================================
-- Permission safety
-- =================================================================

/-- Shared borrows are read-only: they never allow writes. -/
theorem shared_borrow_read_only (n : Nat) :
    Permission.canWrite (Permission.sharedBorrow n) = false := by
  simp [Permission.canWrite]

/-- `uniqueBorrow` is the only permission that allows read and write
    but not deallocation. This characterizes the mutable borrow. -/
theorem unique_borrow_exclusive (p : Permission) :
    (Permission.canRead p = true ∧
      Permission.canWrite p = true ∧
      Permission.canDealloc p = false) ↔
      p = Permission.uniqueBorrow := by
  cases p <;> simp [Permission.canRead, Permission.canWrite, Permission.canDealloc]

-- =================================================================
-- EndBorrow restores ownership
-- =================================================================

/-- Ending the last shared borrow restores ownership. -/
theorem end_borrow_restores_shared :
    endBorrowPermission (Permission.sharedBorrow 1) = Permission.owned := by
  simp [endBorrowPermission]

/-- Ending a unique borrow restores ownership. -/
theorem end_borrow_restores_unique :
    endBorrowPermission Permission.uniqueBorrow = Permission.owned := by
  simp [endBorrowPermission]

-- =================================================================
-- Shared borrow nesting
-- =================================================================

/-- Borrowing from Owned produces SharedBorrow 1. -/
theorem borrow_from_owned :
    borrowPermission Permission.owned = Permission.sharedBorrow 1 := by
  simp [borrowPermission]

/-- Taking another shared borrow increments the shared borrow count. -/
theorem shared_borrow_nesting_borrow (n : Nat) :
    borrowPermission (Permission.sharedBorrow n) = Permission.sharedBorrow (n + 1) := by
  simp [borrowPermission]

/-- Ending one nested shared borrow decrements the shared borrow count. -/
theorem shared_borrow_nesting_end (n : Nat) :
    endBorrowPermission (Permission.sharedBorrow (Nat.succ (Nat.succ n))) =
      Permission.sharedBorrow (n + 1) := by
  simp [endBorrowPermission]

/-- Borrowing from an already-shared allocation and then ending that
    borrow restores the original shared permission (for count >= 1). -/
theorem shared_borrow_nesting_roundtrip (n : Nat) :
    endBorrowPermission (borrowPermission (Permission.sharedBorrow (n + 1))) =
      Permission.sharedBorrow (n + 1) := by
  simp [borrowPermission, endBorrowPermission]

/-- Borrowing from Owned and then ending restores Owned. -/
theorem borrow_end_roundtrip_owned :
    endBorrowPermission (borrowPermission Permission.owned) = Permission.owned := by
  simp [borrowPermission, endBorrowPermission]

-- =================================================================
-- Owned permission capabilities
-- =================================================================

/-- Owned permission allows reads. -/
theorem owned_can_read :
    Permission.canRead Permission.owned = true := by
  simp [Permission.canRead]

/-- Owned permission allows writes. -/
theorem owned_can_write :
    Permission.canWrite Permission.owned = true := by
  simp [Permission.canWrite]

/-- Owned permission allows both reads and writes. -/
theorem owned_read_write :
    Permission.canRead Permission.owned = true ∧
      Permission.canWrite Permission.owned = true := by
  simp [Permission.canRead, Permission.canWrite]

-- =================================================================
-- Deallocation restrictions
-- =================================================================

/-- Shared borrows never allow deallocation. -/
theorem shared_no_dealloc (n : Nat) :
    Permission.canDealloc (Permission.sharedBorrow n) = false := by
  simp [Permission.canDealloc]

/-- Unique borrows never allow deallocation. -/
theorem unique_no_dealloc :
    Permission.canDealloc Permission.uniqueBorrow = false := by
  simp [Permission.canDealloc]

end TrustIr
